from makepage.utils import register_rule, render_step

@register_rule("gcongr")
def rule_gcongr(step, previous, subsequent, mark_list, proof):
    goal_before = previous.get("goal", "<code>goal_before</code>")
    goal_after = subsequent.get("goal", "<code>goal_after</code>")
    if mark_list:
        content = f"不等式{goal_before}可通过对已知条件进行保序变换得到"
    else:
        content = f"要证明{goal_before}, 只需证明{goal_after}即可"
    return render_step(
        tag = "放缩",
        content = content,
        goal_before = goal_before,
        goal_after = goal_after,
        mark_list = mark_list
    )