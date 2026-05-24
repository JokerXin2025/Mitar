from makepage.utils import register_rule, render_step

@register_rule("nlinarith")
def rule_nlinarith(tactic, final_mark, proof):
    proof.tactic_counter["nlinarith"] += 1
    goal_before = tactic.get("goal", "<code>goal_before</code>")
    # `final_mark` is always not `None`
    if goal_before == "矛盾":
        content = "导出不等式矛盾"
    else:
        content = f"通过不等式推导即可证明 {goal_before}"
    return render_step(
        tag = "nnlinarith",
        content = content,
        final_mark = final_mark
    )