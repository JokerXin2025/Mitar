from makepage.utils import register_rule, render_step

"""

step
----------
step        : norm_num
arg_1?      : h_before

previous
----------
goal        : goal_before

subsequent
----------
goal(!final): goal_after
id_1(arg_1) : h_after

"""

@register_rule("norm_num")
def rule_norm_num(step, previous, subsequent, mark_list, proof):
    goal_before = previous.get("goal", "<code>goal_before</code>")
    goal_after = subsequent.get("goal", "<code>goal_after</code>")
    h_before = step.get("arg_1")
    if mark_list:
        if goal_before == "矛盾":
            if h_before:
                content = f"算式 {h_before} 不成立"
            else:
                content = "通过数值计算获得矛盾"
        else:
            content = f"通过数值计算即可证明 {goal_before}"
    else:
        if h_before:
            h_after = subsequent.get("id_1", "<code>h_after</code>")
            content = f"通过计算可得 {h_after}"
        else:
            content = f"目标可转化为 {goal_after}"
    return render_step(
        tag = "计算",
        content = content,
        goal_before = goal_before,
        goal_after = goal_after,
        mark_list = mark_list
    )