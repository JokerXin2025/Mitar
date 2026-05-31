from makepage.utils import register_rule, render_step

"""

step
----------
step        : change
arg_1?      : h_before

previous
----------
goal        : goal_before

subsequent
----------
goal(!final): goal_after
id_1(arg_1) : h_after

"""

@register_rule("change")
def rule_change(step, previous, subsequent, mark_list, proof):
    goal_before = previous.get("goal", "<code>goal_before</code>")
    goal_after = subsequent.get("goal", "<code>goal_after</code>")
    h_before = step.get("arg_1")
    if h_before:
        h_after = subsequent.get("id_1", "<code>h_after</code>")
        content = f"条件 {h_before} 又可写为 {h_after}"
    else:
        content = f"原命题等价于 {goal_after}"
    return render_step(
        tag = "改写",
        content = content,
        goal_before = goal_before,
        goal_after = goal_after,
        mark_list = mark_list
    )