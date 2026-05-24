import textwrap
from makepage.utils import TPL_DETAILS, TPL_STRATEGY, register_rule, render_step

@register_rule("Induction")
def rule_induction(tactic, final_mark, proof):
    n = tactic.get("on", "<code>n</code>")
    m = tactic.get("assumed_m", "<code>m</code>")
    introduce_step = render_step(
        tag = "归纳对象",
        content = f"对自然数 ${n}$ 使用<span class='ref-link'>数学归纳法</span>",
        final_mark = None
    )
    base_case_proof = proof.render(tactic.get("base_case_proof"), "Induction")
    base_case_details = TPL_DETAILS.substitute(
        open_attr = "open",
        tag = "基础情形",
        title = "验证命题对 $0$ 成立",
        line_class = " with-line",
        content = textwrap.indent(f"\n{base_case_proof}\n", "        ")
    )
    inductive_proof = proof.render(tactic.get("inductive_proof"), "Induction")
    inductive_details = TPL_DETAILS.substitute(
        open_attr = "open",
        tag = "归纳步骤",
        title = f"假设命题对 ${m}$ 成立, 下面证明命题对 ${m}+1$ 成立",
        line_class = " with-line",
        content = textwrap.indent(f"\n{inductive_proof}\n", "        ")
    )
    return TPL_STRATEGY.substitute(
        strategy_class = "induction",
        strategy_name = "数学归纳法",
        content = textwrap.indent(f"\n{introduce_step}\n\n{base_case_details}\n\n{inductive_details}\n", "        ")
    )