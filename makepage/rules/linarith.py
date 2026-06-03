from makepage.utils import register_rule, render_step

@register_rule("linarith")
def rule_linarith(step, previous, subsequent, mark_list, proof):
    # `mark_list` is always not `None`
    goal_before = previous.get("goal", "<code>goal_before</code>")
    if goal_before == "矛盾":
        content = "导出不等式矛盾"
    else:
        content = f"通过不等式推导即可证明{goal_before}"
    return render_step(
        tag = "linarith",
        content = content,
        goal_before = goal_before,
        goal_after = "",
        mark_list = mark_list
    )