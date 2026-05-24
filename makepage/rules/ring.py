from makepage.utils import register_rule, render_step

@register_rule("ring")
def rule_ring(tactic, final_mark, proof):
    proof.tactic_counter["ring"] += 1
    goal_before = tactic.get("goal", "<code>goal_before</code>")
    # `final_mark` is always not `None`
    # `goal_before` is always not `"矛盾"`
    content = f"通过代数推导即可证明 {goal_before}"
    return render_step(
        tag = "ring",
        content = content,
        final_mark = final_mark
    )