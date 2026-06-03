from makepage.utils import register_rule, render_step

@register_rule("ring")
def rule_ring(step, previous, subsequent, mark_list, proof):
    # `mark_list` is always not `None`
    # `goal_before` is always not `"矛盾"`
    goal_before = previous.get("goal", "<code>goal_before</code>")
    return render_step(
        tag = "ring",
        content = f"通过代数推导即可证明{goal_before}",
        goal_before = goal_before,
        goal_after = "",
        mark_list = mark_list
    )