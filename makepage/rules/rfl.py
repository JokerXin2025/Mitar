from makepage.utils import register_rule, render_step

@register_rule("rfl")
def rule_rfl(step, previous, subsequent, mark_list, proof):
    # `mark_list` is always not `None`
    # `goal_before` is always not `"矛盾"`
    goal_before = previous.get("goal", "<code>goal_before</code>")
    return render_step(
        tag = "显然",
        content = "该命题显然成立",
        goal_before = goal_before,
        goal_after = "",
        mark_list = mark_list
    )