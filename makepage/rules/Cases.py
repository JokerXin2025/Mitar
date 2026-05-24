import textwrap
from makepage.utils import TPL_DETAILS, TPL_STRATEGY, register_rule, render_step, to_roman

@register_rule("Cases")
def rule_cases(tactic, final_mark, proof):
    principle = tactic.get("on", "<code>n</code>")
    principle_step = render_step(
        tag = "分类依据",
        content = f"{principle}",
        final_mark = None
    )
    cases_list = []
    cases_data = tactic.get("cases", [])
    for i, case_proof in enumerate(cases_data):
        roman_idx = to_roman(i + 1)
        if tactic.get("principle") == "h_class_nat":
            title = query_lean_state(f"case_nat_{i}")
            open_attr = "close" if i == 0 else "open"
        else:
            title = query_lean_state(f"case_m_{i}")
            open_attr = "open"
        proof_html = proof.render(case_proof, "Cases")
        cases_list.append(
            TPL_DETAILS.substitute(
                open_attr = open_attr,
                tag = f"情形 {roman_idx}",
                title = title,
                line_class = " with-line", 
                content = textwrap.indent(f"\n{proof_html}\n", "        ")
            )
        )
    inner_content = f"\n{principle_step}\n\n" + "\n\n".join(cases_list) + "\n"
    return TPL_STRATEGY.substitute(
        strategy_class = "cases",
        strategy_name = "分类讨论",
        content = textwrap.indent(inner_content, "        ")
    )