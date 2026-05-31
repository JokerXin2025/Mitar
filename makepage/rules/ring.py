from makepage.utils import register_rule, render_step

"""

step
----------
step        : ring

previous
----------
goal        : goal_before

"""

@register_rule("ring")
def rule_ring(step, previous, subsequent, mark_list, proof):
    # `mark_list` is always not `None`
    # `goal_before` is always not `"矛盾"`
    goal_before = previous.get("goal", "<code>goal_before</code>")
    content = f"通过代数推导即可证明 {goal_before}"
    return render_step(
        tag = "ring",
        content = content,
        goal_before = goal_before,
        goal_after = "",
        mark_list = mark_list
    )