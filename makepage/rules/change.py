from makepage.utils import register_rule, render_step

@register_rule("change")
def rule_change(tactic, final_mark, proof):
    proof.tactic_counter["change"] += 1
    h_before = tactic.get("h")
    if h_before:
        h_after = tactic.get("expr", "<code>h_after</code>")
        content = f"条件 {h_before} 又可写为 {h_after}"
    else:
        goal_after = tactic.get("expr", "<code>goal_after</code>")
        content = f"原命题等价于 {goal_after}"
    return render_step(
        tag = "改写",
        content = content,
        final_mark = final_mark
    )