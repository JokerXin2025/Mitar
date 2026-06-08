import re, tomllib
from pathlib import Path

CURRENT_DIR = Path(__file__).absolute().parent
CONFIG_PATH = CURRENT_DIR / "tactics.toml"


# ==========================================
# 抽象语法树 (AST) 节点定义
# 架构说明：我们将 Lean 代码按缩进层级解析成一棵多叉树，
# 不同的策略 (Tactic) 会映射到不同的节点类上，以管理其特定的子作用域。
# ==========================================

class Node:
    """所有语法节点的基类，存储基础的行信息、缩进、记录器集合等"""
    def __init__(self, raw_line):
        self.raw_line = raw_line                 # 原始代码行文本
        self.tag = ""                            # 当前所处证明段的标签
        self.carry_in = ""                       # 准备传给本节点前导目标的附加参数
        self.carry_out = ""                      # 执行本节点后，下放给下一个前导目标的附加参数
        self.post_step_recorders = []            # 【延迟回写区】存放在该节点代码块“结束后”需要挂载的步骤记录器
        self.is_mapped_tactic = False            # 是否为策略型tactic或已注册的步骤型tactic
        self.indent = len(raw_line) - len(raw_line.lstrip())  # 缩进量，用于严格划定作用域边界
        self.indent_str = " " * self.indent      # 缩进空格字符串

# 下列类用于特化表示具有子证明段（嵌套作用域）的特定大型策略
class Theorem(Node): pass     # 根节点：def/theorem/lemma
class Intro(Node): pass       # 引入假设：intro / by_contra
class Induction(Node): pass   # 数学归纳法：induction ... with
class Cases(Node): pass       # 基于 Nat 的分类：cases ... with
class RCases(Node): pass      # 基于模式匹配的分类：rcases ... with
class HaveProof(Node): pass   # 通过策略模式证明的独立目标：have ... := by
class Calc(Node): pass        # 计算块：calc (无嵌套证明段，但有特殊的行解析逻辑)
class Step(Node): pass        # 常规步骤型节点 (可能是被匹配的tactic，也可能只是普通语句)

# ==========================================
# 1. 语法解析器 (Lexing & AST Construction)
# 架构说明：利用 Python 递归扫描代码行的缩进大小，遇到如 `cases`, `induction` 
# 等包含分支或子证明的语句时，开启新的递归，从而将平面代码提升为树形结构 (AST)。
# ==========================================

def parse_body(lines, start_idx, base_indent):
    """
    根据缩进解析连续的代码行，遇到特定策略型语句时进入相应的特化处理逻辑。
    返回：(当前作用域的节点列表, 下一个未处理行的索引)
    """
    nodes = []
    i = start_idx
    while i < len(lines):
        line = lines[i]
        if not line.strip():
            i += 1
            continue
            
        # 若当前行缩进小于基础缩进，说明当前子块已结束，退出递归
        indent = len(line) - len(line.lstrip())
        if indent < base_indent:
            break
            
        stripped = line.strip()

        # 解析 Intro / By_contra
        m = re.match(r'^(intro|by_contra)\s+(\w+)', stripped)
        if m:
            node = Intro(line)
            node.var = m.group(2)
            child_nodes, i = parse_body(lines, i + 1, base_indent)
            node.body = child_nodes
            nodes.append(node)
            break

        # 解析 Have Proof (要求必须是由 by 唤起)
        m = re.match(r'^have\s+(\w+)\s*:(.*?):=\s*by', stripped)
        if m:
            node = HaveProof(line)
            node.prop = m.group(1)
            child_nodes, i = parse_body(lines, i + 1, indent + 1)
            node.body = child_nodes
            nodes.append(node)
            continue

        # 解析 Induction
        m = re.match(r'^induction\s+(\w+)\s+with', stripped)
        if m:
            node = Induction(line)
            node.var = m.group(1)
            i += 1
            # 抓取 base (zero) 分支
            while i < len(lines) and not lines[i].strip().startswith('|'): i += 1
            node.zero_line = lines[i]
            b_indent = len(node.zero_line) - len(node.zero_line.lstrip())
            node.zero_body, i = parse_body(lines, i + 1, b_indent + 1)
            # 抓取 inductive (succ) 分支
            while i < len(lines) and not lines[i].strip().startswith('|'): i += 1
            node.succ_line = lines[i]
            m_succ = re.search(r'succ\s+(\w+)\s+(\w+)', node.succ_line)
            node.succ_args = (m_succ.group(1), m_succ.group(2))
            node.succ_body, i = parse_body(lines, i + 1, b_indent + 1)
            nodes.append(node)
            continue

        # 解析 Cases (类似于 Induction)
        m = re.match(r'^cases\s+(\w+)\s+with', stripped)
        if m:
            node = Cases(line)
            node.var = m.group(1)
            i += 1
            while i < len(lines) and not lines[i].strip().startswith('|'): i += 1
            node.zero_line = lines[i]
            b_indent = len(node.zero_line) - len(node.zero_line.lstrip())
            node.zero_body, i = parse_body(lines, i + 1, b_indent + 1)
            while i < len(lines) and not lines[i].strip().startswith('|'): i += 1
            node.succ_line = lines[i]
            m_succ = re.search(r'succ\s+(\w+)', node.succ_line)
            node.succ_arg = m_succ.group(1)
            node.succ_body, i = parse_body(lines, i + 1, b_indent + 1)
            nodes.append(node)
            continue

        # 解析 RCases (基于 `·` 分界符的多分支模式)
        m = re.match(r'^rcases\s+(\w+)\s+with\s+(.*)', stripped)
        if m:
            node = RCases(line)
            node.var = m.group(1)
            i += 1
            node.branches = []
            
            class Branch: pass
            
            while i < len(lines):
                while i < len(lines) and not lines[i].strip(): i += 1
                if i >= len(lines): break
                
                b_line = lines[i]
                b_indent = len(b_line) - len(b_line.lstrip())
                if b_indent < indent or not b_line.strip().startswith('·'): break
                
                # 为了不破坏原有缩进层级的递归解析，将 `·` 抹除为空格并一同送入后续行
                branch_lines = []
                dot_idx = b_line.find('·')
                modified_first = b_line[:dot_idx] + ' ' + b_line[dot_idx+1:]
                branch_lines.append(modified_first)
                
                j = i + 1
                while j < len(lines):
                    if not lines[j].strip():
                        branch_lines.append(lines[j])
                        j += 1
                        continue
                    curr_indent = len(lines[j]) - len(lines[j].lstrip())
                    if curr_indent <= b_indent:
                        break
                    branch_lines.append(lines[j])
                    j += 1
                
                branch = Branch()
                branch.dot_indent = b_indent
                branch.dot_idx = dot_idx
                # 对提取出的当前分支代码块进行独立的 AST 递归解析
                sb, _ = parse_body(branch_lines, 0, 0)
                branch.body = sb
                node.branches.append(branch)
                i = j
            nodes.append(node)
            continue

        # 解析 Calc 计算块
        if stripped == 'calc':
            node = Calc(line)
            i += 1
            calc_lines = []
            while i < len(lines):
                if not lines[i].strip():
                    i += 1; continue
                c_indent = len(lines[i]) - len(lines[i].lstrip())
                if c_indent <= indent: break
                calc_lines.append(lines[i])
                i += 1
            node.calc_lines = calc_lines
            nodes.append(node)
            continue

        # 普通步骤 Tactic 或代码行
        nodes.append(Step(line))
        i += 1
        
    return nodes, i

# ==========================================
# 2. 上下文与策略解析器 (Instrumentation & Context Propagation)
# 架构说明：树被建好后，我们从上而下遍历该树。通过维护一个深度上下文(Context)，
# 将特定的前缀标签 (`__proof` / `___cases`等) 赋予给不同的作用域。
# 并利用 “延迟回写/LIFO倒置” (`post_step_recorders` 等) 将结尾语句挂载在最后一步上。
# ==========================================

class Context:
    """环境上下文：跟踪当前嵌套段的标签和下探深度"""
    def __init__(self, tag, depth=0):
        self.tag = tag
        self.depth = depth

def get_terminal(nodes):
    """
    寻找当前 AST 子树中执行顺序处于“最后”的有效节点。
    用于策略段结束时，把结束记录器挂载在这个终端节点代码的紧后方。
    """
    for node in reversed(nodes):
        if isinstance(node, (Step, Calc)): return node
        if isinstance(node, Intro): return get_terminal(node.body)
        if isinstance(node, Induction): return get_terminal(node.succ_body)
        if isinstance(node, Cases): return get_terminal(node.succ_body)
        if isinstance(node, RCases): return get_terminal(node.branches[-1].body) if node.branches else None
        if isinstance(node, HaveProof): return get_terminal(node.body)
    return None

def resolve(nodes, ctx, config):
    """
    核心插桩逻辑：
    - 给节点打标 `tag`
    - 根据 toml 正则匹配普通 `Step` 节点
    - 在进入子树前为策略设定 `setup_records`
    - 离开子树后将其结束语注册到终端节点的 `post_step_recorders` 中
    """
    suppress_next = False  # 状态机：如果前一步骤向后抛出了 carry_out(如替换目标)，则抑制下个节点的原始 _goal_
    
    for node in nodes:
        node.tag = ctx.tag
        
        # 将上一节点的抑制指令传给下一个合法的 mapped_tactic，避免出现重复的目标记录器
        if getattr(node, 'is_mapped_tactic', False) or getattr(node, '__class__', None) in [Intro, Induction, Cases, RCases, HaveProof, Calc]:
            if suppress_next:
                node.suppress_goal = True
                suppress_next = False

        if isinstance(node, Step):
            # 扫描并应用 TOML 的配置
            for t_name, t_cfg in config.items():
                m = re.match(t_cfg['regex'], node.raw_line.strip())
                if m:
                    node.is_mapped_tactic = True
                    node.position = t_cfg.get("position", "before")
                    node.tactic_name = t_name
                    args_str = ""
                    for arg in t_cfg.get("args", []):
                        val = m.group(arg['match'])
                        if not val: continue
                        if "label" in arg:
                            args_str += f' {val}("{arg["label"]}")'
                            # 如果配置要求携带至下一句，激活 suppress_next 机制
                            if arg.get("carry", False):
                                node.carry_out = f'{val}("last_{arg["label"]}")'
                                suppress_next = True  
                        else:
                            args_str += f' {val}'
                    node.step_recorder = f'Lean2TeX {ctx.tag} <- "{t_name}"{args_str}'.strip()
                    break

        elif isinstance(node, Intro):
            node.is_mapped_tactic = True
            prefix = "_" * (ctx.depth + 1)
            info_var = prefix + "info"
            sub_tag = prefix + "proof"
            node.setup_records = [f"Lean2TeX {info_var} <- {node.var}(\"h_contra\")"]
            resolve(node.body, Context(sub_tag, ctx.depth + 1), config)
            term = get_terminal(node.body)
            if term: term.post_step_recorders.append(f"Lean2TeX {ctx.tag} <- \"Contradiction\" *{info_var}(\"info\") &{sub_tag}(\"proof\")")

        elif isinstance(node, Induction):
            node.is_mapped_tactic = True
            prefix = "_" * (ctx.depth + 1)
            info_var = prefix + "info"
            b_tag = prefix + "base"
            s_tag = prefix + "induct"
            node.setup_records = [f"Lean2TeX {info_var} <- {node.var} (\"on\")"]
            resolve(node.zero_body, Context(b_tag, ctx.depth + 1), config)
            if node.succ_body:
                node.succ_body[0].carry_in = f'{node.succ_args[0]}("assume_on") {node.succ_args[1]}("assume_h")'
            resolve(node.succ_body, Context(s_tag, ctx.depth + 1), config)
            term = get_terminal(node.succ_body)
            if term: term.post_step_recorders.append(f"Lean2TeX {ctx.tag} <- \"Induction\" *{info_var}(\"info\") &{b_tag}(\"base\") &{s_tag}(\"inductive\")")

        elif isinstance(node, Cases):
            node.is_mapped_tactic = True
            prefix = "_" * (ctx.depth + 1)
            info_var = prefix + "info"
            cases_var = prefix + "cases"
            z_tag = prefix + "zero"
            s_tag = prefix + "succ"
            node.setup_records = [f"Lean2TeX {info_var} <- {node.var}(\"NaturalNumber\")"]
            resolve(node.zero_body, Context(z_tag, ctx.depth + 1), config)
            if node.succ_body:
                node.succ_body[0].carry_in = f'{node.succ_arg}("n-1")'
            resolve(node.succ_body, Context(s_tag, ctx.depth + 1), config)
            term = get_terminal(node.succ_body)
            if term:
                term.post_step_recorders.append(f"Lean2TeX vals {cases_var} <- &{z_tag} &{s_tag}")
                term.post_step_recorders.append(f"Lean2TeX {ctx.tag} <- \"Cases\" *{info_var}(\"info\") &{cases_var}(\"cases\")")

        elif isinstance(node, RCases):
            node.is_mapped_tactic = True
            prefix = "_" * (ctx.depth + 1)
            info_var = prefix + "info"
            cases_var = prefix + "cases"
            node.setup_records = [f"Lean2TeX {info_var} <- {node.var}(\"principle\")"]
            b_tags = []
            for i, branch in enumerate(node.branches):
                b_tag = f"{prefix}case{i+1}"
                b_tags.append(b_tag)
                resolve(branch.body, Context(b_tag, ctx.depth + 1), config)
            term = get_terminal(node.branches[-1].body) if node.branches else None
            cases_list = " ".join([f"&{t}" for t in b_tags])
            if term:
                term.post_step_recorders.append(f"Lean2TeX vals {cases_var} <- {cases_list}")
                term.post_step_recorders.append(f"Lean2TeX {ctx.tag} <- \"Cases\" *{info_var}(\"info\") &{cases_var}(\"cases\")")

        elif isinstance(node, HaveProof):
            node.is_mapped_tactic = True
            # 将硬编码的 _proof_ 修改为带有前缀深度叠加规则的动态 _proof 标签
            prefix = "_" * (ctx.depth + 1)
            sub_tag = prefix + "proof"
            # 开启新子树，传递叠加后的 depth (+1)
            resolve(node.body, Context(sub_tag, ctx.depth + 1), config)
            term = get_terminal(node.body)
            if term: term.post_step_recorders.append(f"Lean2TeX {ctx.tag} <- \"have\" &{sub_tag}(\"proof\")")

        elif isinstance(node, Calc):
            node.is_mapped_tactic = True
            lhs = None
            op_map = {'=': '$=$', '≤': '$\\\\leqslant$', '≥': '$\\\\geqslant$', '<': '$<$', '>': '$>$'}
            step_idx = 1
            node.calc_setups = []
            for line in node.calc_lines:
                if ":=" not in line: continue
                eq_part = line.split(":=")[0].strip()
                m = re.search(r'([=≤≥<>])', eq_part)
                if not m: continue
                op, right = m.group(1), eq_part[m.end():].strip()
                if lhs is None:
                    lhs = eq_part[:m.start()].strip()
                    node.calc_setups.append(f"{node.indent_str}let _lhs_ := {lhs}")
                    node.calc_setups.append(f"{node.indent_str}let _rhs1_ := {right}")
                    node.calc_setups.append(f"{node.indent_str}Lean2TeX _calc_ <- \"{op_map[op]}\" _lhs_(\"lhs\") _rhs1_(\"rhs\")")
                else:
                    node.calc_setups.append(f"{node.indent_str}let _rhs{step_idx}_ := {right}")
                    node.calc_setups.append(f"{node.indent_str}Lean2TeX _calc_ <- \"{op_map[op]}\" _rhs{step_idx}_(\"rhs\")")
                step_idx += 1
            node.calc_setups.append(f"{node.indent_str}Lean2TeX {ctx.tag} <- \"calc\" &_calc_(\"calc_steps\")")

# ==========================================
# 3. 代码生成器 (Code Generation)
# 架构说明：后序遍历 AST，根据节点中被附加的修饰、记录器等指令，
# 生成带有 Lean2TeX 插桩标记的最终 Lean 文本数组。
# ==========================================

def emit(node):
    res = []
    ind = getattr(node, 'indent_str', "")
    
    # 1. 打印常规模板的前导 _goal_ 目标记录器 (排除 Theorem 本身且目标未被抑制)
    if getattr(node, 'is_mapped_tactic', False) and not isinstance(node, Theorem):
        if not getattr(node, 'suppress_goal', False):
            carry_str = f" {node.carry_in}" if getattr(node, 'carry_in', "") else ""
            res.append(f"{ind}Lean2TeX {node.tag} <- _goal_{carry_str}")
        
        # 2. 打印初始化设定语句 (注: Intro因要求需放本体后，在此跳过)
        if not isinstance(node, Intro) and hasattr(node, 'setup_records'):
            res.extend([f"{ind}{r}" for r in node.setup_records])
            
    # 下方负责递归输出本体及其子节点
    if isinstance(node, Theorem):
        res.append(node.raw_line)
        for child in node.body: res.extend(emit(child))
        
    elif isinstance(node, Intro):
        res.append(node.raw_line)
        # 按照规则要求，反证法/Intro信息的注入应放在本体执行之后
        if hasattr(node, 'setup_records'):
            res.extend([f"{ind}{r}" for r in node.setup_records])
        for child in node.body: res.extend(emit(child))
        
    elif isinstance(node, Induction):
        res.append(node.raw_line)
        res.append(node.zero_line)
        for c in node.zero_body: res.extend(emit(c))
        res.append(node.succ_line)
        for c in node.succ_body: res.extend(emit(c))
        
    elif isinstance(node, Cases):
        res.append(node.raw_line)
        res.append(node.zero_line)
        for c in node.zero_body: res.extend(emit(c))
        res.append(node.succ_line)
        for c in node.succ_body: res.extend(emit(c))
        
    elif isinstance(node, RCases):
        res.append(node.raw_line)
        for branch in node.branches:
            b_res = []
            for c in branch.body:
                b_res.extend(emit(c))
            if b_res:
                # 寻找并在本分支解析出的第一个非空行前精确覆盖恢复原本被抹除的 `·` 分界符
                for k in range(len(b_res)):
                    if b_res[k].strip():
                        line_content = b_res[k].lstrip()
                        b_res[k] = " " * branch.dot_idx + "· " + line_content
                        break
            res.extend(b_res)
            
    elif isinstance(node, HaveProof):
        res.append(node.raw_line)
        for child in node.body: res.extend(emit(child))
        
    elif isinstance(node, Calc):
        res.extend(node.calc_setups)
        # Calc无子节点但需输出积累的回写信息
        for r in node.post_step_recorders: res.append(f"{ind}{r}")
        res.append(node.raw_line)
        res.extend(node.calc_lines)
        
    elif isinstance(node, Step):
        if getattr(node, 'is_mapped_tactic', False):
            # 处理 "本体前" / "本体后" 的位置规则
            if node.position == "before":
                res.append(f"{ind}{node.step_recorder}")
                for r in node.post_step_recorders: res.append(f"{ind}{r}")
                res.append(node.raw_line)
                # 策略如果要求carry_out参数传递，立即在此输出替换的目标记录器
                if getattr(node, 'carry_out', ""):
                    res.append(f"{ind}Lean2TeX {node.tag} <- _goal_ {node.carry_out}")
            else:
                res.append(node.raw_line)
                res.append(f"{ind}{node.step_recorder}")
                for r in node.post_step_recorders: res.append(f"{ind}{r}")
        else:
            # 即便是不认识的Tactic/代码，它也可能是一个Terminal节点，身上背负了回写指令
            for r in getattr(node, 'post_step_recorders', []): res.append(f"{ind}{r}")
            res.append(node.raw_line)
            
    return res

def Lean2TeX_init(input_file: Path):
    """文件主控逻辑：读取文件，解析树，进行树遍历插桩，并输出文本"""

    try:
        with open(CONFIG_PATH, 'rb') as f:
            config = tomllib.load(f).get("tactics", {})
    except FileNotFoundError:
        print(f"[Error] File '{CONFIG_PATH}' not found!")
        return

    lines = input_file.read_text(encoding = "utf-8").splitlines()

    # 1. 第一趟扫描：查找所有定理/引理根节点，并建树
    root_nodes = []
    i = 0
    while i < len(lines):
        line = lines[i]
        # 匹配定理、引理
        m = re.match(r'^(theorem|lemma)\s+(\w+)', line)
        if m:
            node = Theorem(line)
            # 自动将 theorem / lemma 关键字替换成 def
            node.raw_line = re.sub(r'^(theorem|lemma)', 'def', line)
            node.name = m.group(2)
            node.tag = node.name

            b_lines, i = parse_body(lines, i + 1, 2)
            node.body = b_lines
            root_nodes.append(node)
        else:
            root_nodes.append(Step(line))
            i += 1

    # 2. 第二趟遍历：对每个根定理执行插桩策略挂载
    theorems = []
    for node in root_nodes:
        if isinstance(node, Theorem):
            theorems.append(node.name)
            resolve(node.body, Context(node.name, 0), config)

    # 3. 追加文件末尾导出信息
    if theorems:
        last_term = None
        for node in reversed(root_nodes):
            if isinstance(node, Theorem):
                last_term = get_terminal(node.body)
                if last_term: break
        if last_term:
            thm_list = " ".join([f"&{t}" for t in theorems])
            last_term.post_step_recorders.append(f"Lean2TeX vals {input_file.stem} <- {thm_list}")

    # 4. 生成新代码
    out_lines = []

    # 自动在生成的文件最开头加入依赖
    if not any("import Lean2TeX" in line for line in lines):
        out_lines.append("import Lean2TeX")

    for node in root_nodes:
        out_lines.extend(emit(node))

    # 写入最终的导出命令
    if theorems:
        out_lines.append(f"\nLean2TeX {input_file.stem} => \"Calculus@Mitar/{input_file.stem}.json\"")

    output_file = input_file.with_name(f"{input_file.stem}_Lean2TeX.lean")
    output_file.write_text("\n".join(out_lines) + "\n")


if __name__ == "__main__":

    Lean2TeX_init(CURRENT_DIR / "TEST.lean")
