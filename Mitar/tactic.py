import re
import tomllib
from string import Template
from pathlib import Path

from Mitar.i18n import SUPPORTED_LANGUAGES
from Mitar.utils import HANDLERS, register_rule

CURRENT_DIR = Path(__file__).absolute().parent
CONFIG_DIR = CURRENT_DIR / "Tactic"

MAP_CONDITION = {
    "Final": "mark_list",
    "NonFinal": "not mark_list",
    "Contra": "proof.is_contradiction(previous.get(\"goal\", \"\"))"
}

MAP_ARGS_BASIC = {
    "${goal}": "{goal}",
    "${goal'}": "{goal_}"
}

TPL_CONTENT = Template('''\
from Mitar.utils import register_rule
from Mitar.engine import render_step

@register_rule("${name}")
def rule_${name}(step, previous, subsequent, mark_list, proof):

    goal = previous.get("goal", "")
    goal_ = subsequent.get("goal", "")
    tag = proof.tactic_text("${name}", "tag", ${tag_template})
    content = ""

${codes}

    return render_step(
        tag = tag,
        content = content,
        mark_list = mark_list
    )
''')


class Rules(list):

    def __init__(self, data):
        super().__init__(data)

    def traverse(self, table, path):
        for key, value in table.items():
            if key == "language":
                continue
            if isinstance(value, dict):
                self.traverse(value, path + (key,))
            elif key == "content":
                self.append((path, value))

    def reorder(self):
        self.sort(
            key = lambda x: len(x[0])
        )


def generate_codes(tactic: dict):

    lines = []
    map_args = MAP_ARGS_BASIC.copy()

    # Extract arg labels from the syntax pattern (`name:type` 对里的名字)
    #   "provide proof:term"              → labels = ["proof"]
    #   "unfold definitions:(colGt ident)+" → labels = ["definitions"]
    #   "quot_induction q:term with a:ident" → labels = ["q", "a"]
    syntax = tactic.get("syntax", "")
    labels = re.findall(r'(\w+)\s*:', syntax)
    for arg in labels:
        # 参数值现在是 ExprJSON AST（或 neither 的 {before, after} / ident+ 的数组），
        # 经 `proof.tex_param` 渲染成 TeX 字符串。
        lines.append(
            f"    {arg} = proof.tex_param(step.get(\"{arg}\", \"\"))\n"
        )
        map_args[f"${{{arg}}}"] = f"{{{arg}}}"

    rules = Rules([])
    if "content" in tactic:
        rules.append(((), tactic["content"]))
    language = tactic.get("language")
    if isinstance(language, dict) and all(isinstance(value, dict) for value in language.values()):
        localized_content = {
            key: value["content"]
            for key, value in language.items()
            if isinstance(value.get("content"), str)
        }
        if localized_content:
            rules.append(((), localized_content))
    for key, value in tactic.items():
        if key in {"content", "language", "name", "syntax", "tag", "tag_language"}:
            continue
        if isinstance(value, dict):
            if "content" in value:
                rules.append(((key,), value["content"]))
            nested_language = value.get("language")
            if isinstance(nested_language, dict) and "content" in nested_language:
                rules.append(((key,), {lang: item.get("content", "") for lang, item in nested_language.items() if isinstance(item, dict)}))
    rules.reorder()
    rules.reorder()

    for condition_tuple, content in rules:
        if isinstance(content, dict):
            content = {language: _prepare_template(value, map_args) for language, value in content.items()}
        else:
            content = {"zh": _prepare_template(content, map_args)}
        if not set(content).intersection(SUPPORTED_LANGUAGES):
            raise ValueError(f"TAC001: tactic {tactic.get('name', '')} condition {condition_tuple} has no supported language content")
        conditions = " and ".join(
            ["True"] + [MAP_CONDITION.get(condition, "True") for condition in condition_tuple]
        )
        lines.append(
            f"    if {conditions}:"
        )
        lines.append(
            f'        content = proof.tactic_text({tactic.get("name", "")!r}, "content", {content!r}, goal=goal, goal_=goal_, {", ".join(f"{arg}={arg}" for arg in labels)})'
        )

    return "\n".join(lines)


def _prepare_template(content, map_args):
    content = str(content).replace("$$", "$")
    for old, new in map_args.items():
        content = content.replace(old, new)
    return content


def tactic_register_dir(dirpath: Path):
    """Load all TOML files recursively from a Tactic configuration directory."""
    from Mitar.utils import HANDLERS
    for child in sorted(dirpath.rglob("*.toml")):
        with open(child, "rb") as rule_f:
            tactic = tomllib.load(rule_f)
        name = tactic.get("name", "")
        if name in HANDLERS:
            continue
        if "content" not in tactic:
            if not isinstance(tactic.get("language"), dict):
                continue
        exec_codes = TPL_CONTENT.substitute(
            name = name,
            tag_template = repr(_tag_template(tactic)),
            codes = generate_codes(tactic)
        )
        exec(exec_codes, globals())


def _tag_template(tactic: dict):
    language = tactic.get("language")
    if isinstance(language, dict):
        if not set(language).intersection(SUPPORTED_LANGUAGES):
            raise ValueError(f"TAC002: tactic {tactic.get('name', '')} has no supported language tag")
        return {key: value.get("tag", "") for key, value in language.items() if isinstance(value, dict)}
    return tactic.get("tag", "")


GENERIC_TACTICS = {
    "assumption": ("由假设", "By assumption,"),
    "have": ("引入事实", "Introducing the fact,"),
    "exact": ("直接证明", "By the supplied proof,"),
    "contradiction": ("由矛盾", "By contradiction,"),
    "exfalso": ("转化为矛盾", "Reducing to a contradiction,"),
    "rfl": ("由自反性", "By reflexivity,"),
    "simp_only": ("化简", "By simplification,"),
    "intro_var": ("引入变量", "Introducing a variable,"),
    "prove_left": ("证明左支", "It suffices to prove the left disjunct,"),
    "prove_right": ("证明右支", "It suffices to prove the right disjunct,"),
    "left": ("选择左支", "Choosing the left disjunct,"),
    "right": ("选择右支", "Choosing the right disjunct,"),
    "obtain_exist": ("解构存在性", "Unpacking the existential hypothesis,"),
    "unpack_and": ("解构合取", "Unpacking the conjunction,"),
    "unpack_iff": ("解构等价", "Unpacking the equivalence,"),
    "funext": ("函数外延", "By function extensionality,"),
    "embed": ("嵌入定理", "Embedding the theorem proof,"),
    "continuity": ("连续性", "By continuity,"),
    "exact_mod_cast": ("类型转换", "By exact modular casting,"),
    "gcongr": ("广义同余", "By generalized congruence,"),
    "itaotu": ("命题自动推理", "By propositional automation,"),
    "itaotu!": ("命题自动推理", "By propositional automation,"),
    "itauto": ("命题自动推理", "By propositional automation,"),
    "itauto!": ("命题自动推理", "By propositional automation,"),
    "linarith!": ("线性算术", "By linear arithmetic,"),
    "measurability": ("可测性", "By measurability,"),
    "nlinarith!": ("非线性算术", "By nonlinear arithmetic,"),
    "norm_cast": ("规范化类型转换", "By normalizing casts,"),
    "positivity": ("正性", "By positivity,"),
    "push_cast": ("推进类型转换", "By pushing casts,"),
    "qify": ("有理数化", "By rationalizing casts,"),
    "rify": ("实数化", "By realifying casts,"),
    "zify": ("整数化", "By integerizing casts,"),
    "ring!": ("环正规化", "By ring normalization,"),
    "ring_nf": ("环正规化", "By ring normalization,"),
    "ring_nf!": ("环正规化", "By ring normalization,"),
    "tauto": ("命题逻辑", "By propositional logic,"),
    "wlog": ("不失一般性", "Without loss of generality,"),
    "wlog!": ("不失一般性", "Without loss of generality,"),
    "rw": ("变形", "By rewriting,"),
    "admit": ("暂作公理", "Admitting the claim,"),
    "cite": ("引用定理", "Citing the theorem,"),
    "constructor": ("应用构造器", "By the constructor,"),
    "constructor!": ("应用指定构造器", "By the specified constructor,"),
    "svg": ("插入 SVG", "Inserting the SVG,"),
    "latex": ("插入 LaTeX", "Inserting the LaTeX figure,"),
    "calc": ("计算", "By calculation,"),
    "infer": ("推导", "By inference,"),
    "apply": ("应用定理", "Applying the theorem,"),
    "change": ("改变目标", "Changing the goal,"),
    "unfold": ("展开定义", "Unfolding the definition,"),
    "simp": ("化简", "Simplifying,"),
    "quot_induction": ("商归纳", "By quotient induction,"),
    "norm_num": ("数值化简", "By numerical normalization,"),
    "field": ("域运算", "By field normalization,"),
    "nlinarith": ("非线性算术", "By nonlinear arithmetic,"),
    "linarith": ("线性算术", "By linear arithmetic,"),
    "ring": ("环正规化", "By ring normalization,"),
    "exact_mod_cast": ("类型转换", "By exact modular casting,"),
}


def register_generic_tactics() -> None:
    from Mitar.engine import render_step

    for name, labels in GENERIC_TACTICS.items():
        if name in HANDLERS:
            continue

        def render(step, previous, subsequent, mark_list, proof, labels=labels):
            tag = labels[1] if proof.language == "en" else labels[0]
            goal = previous.get("goal", "")
            next_goal = subsequent.get("goal", "")
            content = ""
            if goal and next_goal and goal != next_goal:
                content = (
                    f"to prove {goal}, it suffices to prove {next_goal}."
                    if proof.language == "en"
                    else f"要证明{goal}，只需证明{next_goal}"
                )
            return render_step(tag, content, mark_list)

        register_rule(name)(render)


if __name__ == "__main__":
    tactic_register_dir(CONFIG_DIR)
