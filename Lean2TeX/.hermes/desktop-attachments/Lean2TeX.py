import re, time
from pathlib import Path
from Mitar.utils import len_indent

CURRENT_DIR = Path(__file__).absolute().parent

RELATION_SYMBOL = {
    "=": "$=$",
    "<": "$<$",
    ">": "$>$",
    "≤": "$\\\\leqslant$",
    "≥": "$\\\\geqslant$",
    "=?": "$\\\\textcolor{lightgrey}=$",
}


# AST node
class Node:
    def __init__(self, raw = ""):
        self.raw = raw
        self.post_recorders = []
        # self.tag (All)

#  Theorem / Lemma
class Root(Node): pass
#  Normal Tactic
class Tactic(Node): pass
#  Calculation
class Calc(Node): pass
#  New Goal
class NewGoal(Node): pass
#  Contradiction
class Contra(Node): pass
#  Induction
class Induct(Node): pass
#  Cases on Natural Number
class Cases_Nat(Node): pass
#  Cases by Principle
class CasesP(Node): pass
#  Others
class Other(Node): pass

SUBTREE_CONFIG = {
    NewGoal: {
        "branches": ["proof"],
        "ahead": False,
    },
    Contra: {
        "branches": ["proof"],
        "ahead": True,
    },
    Induct: {
        "branches": ["base", "induct"],
        "ahead": False,
    },
    Cases_Nat: {
        "branches": ["zero", "succ"],
        "ahead": False,
    },
    CasesP: {
        "branches": [],
        "ahead": False,
    }
}


def __parser(lines, start, basic_indent: int, tactics_cfg, contra = False):

    """
    ### Return Value
    (当前作用域的节点列表, 下一个未处理行的索引)
    """

    nodes = []

    i = start
    while i < len(lines):

        line = lines[i]

        # Exit the recursion
        if len_indent(line) < basic_indent:
            break

        # Skip the blank line unless it's root parser
        if not line.strip() and start != 0:
            i += 1
            continue

        # Parse: Theorem / Lemma
        match = re.match(r'^(?:theorem|lemma)\s+(\w+)', line)
        if match and start == 0:
            raw = line
            # 修复：先检查当前行是否已经包含了 ':= by'
            if not re.search(r':=\s*by', line):
                i += 1
                while i < len(lines):
                    # retain raw codes while skipping the blank line
                    if lines[i].strip():
                        raw += ("\n" + lines[i])
                    if re.search(r':=\s*by', lines[i]):
                        i += 1
                        break
                    i += 1
            else:
                i += 1
                
            # Substitute `def` for `theorem` or `lemma`
            # to avoid some problems caused by parallel processing of Lean
            node = Root(re.sub(r'^(?:theorem|lemma)', 'def', raw))
            node.name = match.group(1)
            node.steps, i = __parser(lines, i, 1, tactics_cfg)
            nodes.append(node)
            continue

        # Parse: Calculation
        if line.strip() == "calc":
            node = Calc(line)
            node.raw_calsteps = []
            i += 1
            while i < len(lines):
                # Exit the recursion
                if len_indent(lines[i]) <= len_indent(line):
                    break
                # retain calculation steps while skipping the blank line
                if lines[i].strip():
                    node.raw_calsteps.append(lines[i])
                i += 1
            nodes.append(node)
            break

        # Parse: New Goal
        match = re.match(r'^have\s+(\w+)\s*:(.*?):=\s*by', line.strip())
        if match:
            node = NewGoal(line)
            node.proof = Node()
            node.proof.steps, i = __parser(lines, i + 1, len_indent(line) + 1, tactics_cfg)
            nodes.append(node)
            continue

        # Parse: Contradiction
        match = re.match(r'^(?:intro|by_contra)\s+(\w+)', line.strip())
        if match:
            node = Contra(line)
            node.args = match.group(1)
            # get branch "base"
            node.proof = Node()
            node.proof.steps, i = __parser(lines, i + 1, basic_indent, tactics_cfg)
            nodes.append(node)
            break

        # Parse: Induction
        match = re.match(r'^induction\s+(\w+)\s+with', line.strip())
        if match:
            node = Induct(line)
            node.args = match.group(1)
            i += 1
            # get branch "base"
            while i < len(lines) and not lines[i].strip().startswith('|'):
                i += 1
            node.base = Node(lines[i])
            base_indent = len_indent(node.base.raw)
            node.base.steps, i = __parser(lines, i + 1, base_indent + 1, tactics_cfg)
            # get branch "inductive"
            while i < len(lines) and not lines[i].strip().startswith('|'):
                i += 1
            node.induct = Node(lines[i])
            match_induct = re.search(r'succ\s+(\w+)\s+(\w+)', node.induct.raw)
            node.induct.args = (match_induct.group(1), match_induct.group(2))
            induct_indent = len_indent(node.induct.raw)
            node.induct.steps, i = __parser(lines, i + 1, induct_indent + 1, tactics_cfg)
            nodes.append(node)
            break

        # Parse: Cases on Natural Number
        match = re.match(r'^cases\s+(\w+)\s+with', line.strip())
        if match:
            node = Cases_Nat(line)
            node.args = match.group(1)
            i += 1
            # get branch "zero"
            while i < len(lines) and not lines[i].strip().startswith('|'):
                i += 1
            node.zero = Node(lines[i])
            node.zero.steps, i = __parser(lines, i + 1, len_indent(node.zero.raw) + 1, tactics_cfg)
            # get branch "succ"
            while i < len(lines) and not lines[i].strip().startswith('|'):
                i += 1
            node.succ = Node(lines[i])
            match_succ = re.search(r'succ\s+(\w+)', node.succ.raw)
            node.succ.arg = match_succ.group(1)
            node.succ.steps, i = __parser(lines, i + 1, len_indent(node.succ.raw) + 1, tactics_cfg)
            nodes.append(node)
            break

        # Parse: Cases by Principle
        match = re.match(r'^rcases\s+(\w+)\s+with\s+(.*)', line.strip())
        if match:
            node = CasesP(line)
            node.args = match.group(1)
            i += 1
            n = 0
            # get branches
            while i < len(lines):
                while i < len(lines) and not lines[i].strip():
                    i += 1
                if i >= len(lines):
                    break
                b_line = lines[i]
                if len_indent(b_line) < len_indent(line) or not b_line.strip().startswith('·'):
                    break
                # 为了不破坏原有缩进层级的递归解析，将 `·` 抹除为空格并一同送入后续行
                branch_lines = []
                dot_idx = b_line.find('·')
                modified_first = b_line[:dot_idx] + ' ' + b_line[dot_idx+1:]
                branch_lines.append(modified_first)
                i += 1
                while i < len(lines):
                    if not lines[i].strip():
                        branch_lines.append(lines[i])
                        i += 1
                        continue
                    if len_indent(lines[i]) <= len_indent(b_line):
                        break
                    branch_lines.append(lines[i])
                    i += 1
                n += 1
                branch = Node(" " * len_indent(b_line) + f"· -- case {n}")
                branch.dot_indent = len_indent(b_line)
                branch.dot_idx = dot_idx
                branch.steps, _ = __parser(branch_lines, 0, 0, tactics_cfg)
                setattr(node, f"case{n}", branch)
                SUBTREE_CONFIG[CasesP]["branches"].append(f"case{n}")
            nodes.append(node)
            break

        # Parse: Normal Tactic / Others
        node = None
        for tactic in tactics_cfg:
            regex = tactic.get("regex", "$.").replace(
                "@{ident}", "[a-zA-Z0-9_'?!]+"
            )
            match = re.match(regex, line.strip())
            if match:
                node = Tactic(line)
                node.name = tactic.get("name", "")
                node.put_off = tactic.get("put_off", False)
                node.args = []
                for name, label in tactic.get("args", {}).items():
                    var_name = match.group(name)
                    if var_name and name in tactic.get("relay_args", []):
                        node.args.append((label, var_name, True))
                    elif var_name:
                        node.args.append((label, var_name, False))
                break
        node = Other(line) if node == None else node
        nodes.append(node)
        i += 1

    return nodes, i


def __get_terminal(nodes):

    """
    ## Get the terminal node in the AST's subtree
    Note that `NewGoal` and `Other` nodes won't be regarded as valid step.
    """

    for node in reversed(nodes):
        if node.__class__ in [Tactic, Calc]:
            return node
        elif node.__class__ == Root:
            return __get_terminal(node.steps)
        elif node.__class__ == Contra:
            return __get_terminal(node.proof.steps)
        elif node.__class__ == Induct:
            return __get_terminal(node.induct.steps)
        elif node.__class__ == Cases_Nat:
            return __get_terminal(node.succ.steps)
        elif node.__class__ == CasesP:
            return __get_terminal(getattr(node, SUBTREE_CONFIG[CasesP]["branches"][-1]).steps)
    return None


def __resolve(nodes: list, tag: str, depth: int):

    """
    # 核心插桩逻辑：
    - 给节点打标 `tag`
    - 根据 toml 正则匹配普通 `Tactic` 节点
    - 在进入子树前为策略设定 `setup`
    - 离开子树后将其结束语注册到终端节点的 `post_recorders` 中
    """

    for n, node in enumerate(nodes):
        node.tag = tag

        if node.__class__ == Root:
            __resolve(node.steps, node.name, 0)

        elif node.__class__ == Tactic:

            args_str = ""
            for label, var_name, carry in node.args:
                if label:
                    args_str += f""" {var_name}(\"{label}\")"""
                    if carry and n + 1 < len(nodes):
                        nodes[n+1].step_args = f""" {var_name}(\"last_{label}\")"""
                else:
                    args_str += f' {var_name}'
            node.step_info = f'Lean2TeX {tag} <- "{node.name}"{args_str}'.strip()

        elif node.__class__ == Calc:
            node.calc_info = []
            # 1. 把所有计算步骤拼接为一整段文本，并移除单行注释，防止干扰
            full_text = "\n".join(node.raw_calsteps)
            clean_text = re.sub(r'--.*', '', full_text)
            # 2. 全局匹配 calc 步骤
            # 匹配逻辑：(行首或换行) + 空白 + (可选的下划线) + (关系符) + 空白 + (表达式) + := 
            pattern = r'(?:^|\n)\s*(?:_\s+)?([=≤≥<>]|=\?)\s+(.*?)\s+:='
            matches = list(re.finditer(pattern, clean_text, re.DOTALL))
            lhs = None
            step_idx = 1
            for match in matches:
                rel = match.group(1).strip()
                # 压缩表达式内的多余换行和空格，防止插入 let 语句时引发缩进错误
                rhs = " ".join(match.group(2).split())
                # 如果是新的关系符(如 =?)，去字典拿 TeX 映射，没有则保留原样
                tex_rel = RELATION_SYMBOL.get(rel, rel)
                if lhs is None:
                    # 第一次匹配：提取第一行的 LHS (从文本开头到第一个关系符之前)
                    lhs_raw = clean_text[:match.start()]
                    lhs = " ".join(lhs_raw.split())
                    node.calc_info.append(f"""let _lhs_ := {lhs}""")
                    node.calc_info.append(f"""let _rhs1_ := {rhs}""")
                    node.calc_info.append(f"""Lean2TeX _calc_ <- \"{tex_rel}\" _lhs_(\"lhs\") _rhs1_(\"rhs\")""")
                else:
                    node.calc_info.append(f"""let _rhs{step_idx}_ := {rhs}""")
                    node.calc_info.append(f"""Lean2TeX _calc_ <- \"{tex_rel}\" _rhs{step_idx}_(\"rhs\")""")
                step_idx += 1
            node.calc_info.append(f"""Lean2TeX {tag} <- \"calc\" &_calc_(\"calc_steps\")""")

        elif node.__class__ == NewGoal:

            prefix = "_" * (depth + 1)
            proof_tag = prefix + "proof"

            __resolve(node.proof.steps, proof_tag, depth + 1)
            terminal = __get_terminal(node.proof.steps)
            terminal.post_recorders.append(f"""Lean2TeX {tag} <- \"have\" &{proof_tag}(\"proof\")""")

        elif node.__class__ == Contra:

            prefix = "_" * (depth + 1)
            info_tag = prefix + "info"
            proof_tag = prefix + "proof"

            node.setup = f"""Lean2TeX {info_tag} <- {node.args}(\"h_contra\")"""
            __resolve(node.proof.steps, proof_tag, depth + 1)
            terminal = __get_terminal(node.proof.steps)
            terminal.post_recorders.append(f"""Lean2TeX {tag} <- \"Contradiction\" *{info_tag}(\"info\") &{proof_tag}(\"proof\")""")

        elif node.__class__ == Induct:

            prefix = "_" * (depth + 1)
            info_tag = prefix + "info"
            base_tag = prefix + "base"
            induct_tag = prefix + "induct"

            node.setup = f"""Lean2TeX {info_tag} <- {node.args} (\"on\")"""
            __resolve(node.base.steps, base_tag, depth + 1)
            node.induct.steps[0].step_args = f""" {node.induct.args[0]}(\"assume_on\") {node.induct.args[1]}(\"assume_h\")"""
            __resolve(node.induct.steps, induct_tag, depth + 1)
            terminal = __get_terminal(node.induct.steps)
            terminal.post_recorders.append(f"""Lean2TeX {tag} <- \"Induction\" *{info_tag}(\"info\") &{base_tag}(\"base\") &{induct_tag}(\"inductive\")""")

        elif node.__class__ == Cases_Nat:

            prefix = "_" * (depth + 1)
            info_tag = prefix + "info"
            cases_var = prefix + "cases"
            zero_tag = prefix + "zero"
            succ_tag = prefix + "succ"

            node.setup = f"""Lean2TeX {info_tag} <- {node.args}(\"NaturalNumber\")"""
            __resolve(node.zero.steps, zero_tag, depth + 1)
            if node.succ.steps:
                node.succ.steps[0].step_args = f""" {node.succ.arg}(\"n-1\")"""
            __resolve(node.succ.steps, succ_tag, depth + 1)
            terminal = __get_terminal(node.succ.steps)
            terminal.post_recorders.append(f"""Lean2TeX vals {cases_var} <- &{zero_tag} &{succ_tag}""")
            terminal.post_recorders.append(f"""Lean2TeX {tag} <- \"Cases\" *{info_tag}(\"info\") &{cases_var}(\"cases\")""")

        elif node.__class__ == CasesP:

            prefix = "_" * (depth + 1)
            info_tag = prefix + "info"
            cases_var = prefix + "cases"

            node.setup = f"""Lean2TeX {info_tag} <- {node.args}(\"principle\")"""
            b_tags = []
            for branch in SUBTREE_CONFIG[CasesP]["branches"]:
                b_tag = prefix + branch
                b_tags.append(b_tag)
                __resolve(getattr(node, branch).steps, b_tag, depth + 1)
            terminal = __get_terminal(getattr(node, SUBTREE_CONFIG[CasesP]["branches"][-1]).steps)
            cases_list = " ".join([f"&{t}" for t in b_tags])
            terminal.post_recorders.append(f"""Lean2TeX vals {cases_var} <- {cases_list}""")
            terminal.post_recorders.append(f"""Lean2TeX {tag} <- \"Cases\" *{info_tag}(\"info\") &{cases_var}(\"cases\")""")


def __output(node):

    output = []
    indent = " " * len_indent(node.raw)

    def output_extend(lines: str):
        for line in lines:
            output.append(indent + line)

    # Print leading goal recorder
    if not node.__class__ in [Root, Other]:
        step_args = getattr(node, "step_args", "")
        output.append(indent + f"""Lean2TeX {node.tag} <- _goal_{step_args}""")

    if node.__class__ == Root:
        output.append(node.raw)
        for child in node.steps:
            output.extend(__output(child))

    elif node.__class__ == Tactic:
        if not node.put_off:
            output.append(indent + node.step_info)
            output_extend(node.post_recorders)
            output.append(node.raw)
        else:
            output.append(node.raw)
            output.append(indent + node.step_info)

    elif node.__class__ == Calc:
        output_extend(node.calc_info)
        output_extend(node.post_recorders)
        output.append(node.raw)
        output.extend(node.raw_calsteps)

    elif node.__class__ in [NewGoal, Contra, Induct, Cases_Nat, CasesP]:
        if hasattr(node, "setup") and not SUBTREE_CONFIG[node.__class__]["ahead"]:
            output.append(indent + node.setup)
        output.append(node.raw)
        if hasattr(node, "setup") and SUBTREE_CONFIG[node.__class__]["ahead"]:
            output.append(indent + node.setup)
        branches = SUBTREE_CONFIG[node.__class__]["branches"]
        for branch in branches:
            # Print branch's raw code if the branch isn't unique
            if len(branches) > 1:
                output.append(getattr(node, branch).raw)
            for child in getattr(getattr(node, branch), "steps", []):
                output.extend(__output(child))

    elif node.__class__ == Other:
        output.append(node.raw)

    return output


def Lean2TeX_init(input_file: Path, tactics_cfg: list):

    """
    ## Initialize Lean2TeX
    Generate an instrumented transcript of the input file with the suffix
    `_Lean2TeX.lean` and add it to the project's library entry file as a module.
    ### Return Value
    - 0: Succeed
    - 1: Configuration file not found
    - 2: Input file not found
    """

    json_file = input_file.with_name(f"{input_file.stem}_Lean2TeX.json")
    output_file = input_file.with_name(f"{input_file.stem}_Lean2TeX.lean")

    # Read the input file
    if input_file.exists():
        lines = input_file.read_text(encoding = "utf-8").splitlines()
    else:
        return 1

    # Build Lean2TeX AST
    root_nodes, _ = __parser(lines, 0, 0, tactics_cfg)
    __resolve(root_nodes, "", 0)

    # Merge Lean2TeX's data
    terminal = __get_terminal(root_nodes)
    if terminal:
        prop_list = ""
        for node in root_nodes:
            if node.__class__ == Root:
                prop_list += f" &{node.name}"
        terminal.post_recorders.append(f"""Lean2TeX vals Lean2TeX_Data <-{prop_list}""")
    else:
        print("未找到terminal!")

    output_lines = []

    # Add Lean2TeX dependence
    if not any("import Lean2TeX" in line for line in lines):
        output_lines.append("import Lean2TeX")

    # Instrument the source code
    for node in root_nodes:
        output_lines.extend(__output(node))

    # Add Lean2TeX's export command
    output_lines.append(f"""\nLean2TeX Lean2TeX_Data => \"{json_file}\"""")

    # Record the current timestamp
    # to avoid some problems caused by cache invocation of Lean
    output_lines.append(f"""\n-- Lean2TeX {time.time()}""")

    # Output
    output_file.write_text("\n".join(output_lines) + "\n")
    return 0


if __name__ == "__main__":

    # Test with `TEST.lean`
    Lean2TeX_init("TEST.lean", None)
