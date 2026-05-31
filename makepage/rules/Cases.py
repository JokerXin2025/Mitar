from makepage.utils import register_rule, render_step, render_details, render_strategy, to_roman

@register_rule("Cases")
def rule_Cases(strategy, previous, subsequent, mark_list, proof):
    goal_init = previous.get("goal", "<code>goal_init</code>")
    principle = strategy.get("on", "<code>principle</code>")
    principle_step = render_step(
        tag = "分类依据",
        content = f"{principle}",
        goal_before = goal_init,
        goal_after = "",
        mark_list = []
    )
    cases_list = []
    cases_data = strategy.get("cases", [])
    for i, case_proof in enumerate(cases_data):
        if tactic.get("principle") == "h_class_nat":
            title = query_lean_state(f"case_nat_{i}")
            open = (i == 0)
        else:
            title = query_lean_state(f"case_m_{i}")
            open = True
        proof_html = proof.render(case_proof, "Cases")
        cases_list.append(
            render_details(
                open = open,
                tag = f"情形 {to_roman(i + 1)}",
                title = title,
                line = True,
                content = f"\n{proof_html}\n"
            )
        )
    return render_strategy(
        sort = "cases",
        tag = "分类讨论",
        content = f"\n{principle_step}\n\n" + "\n\n".join(cases_list) + "\n"
    )