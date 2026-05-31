from makepage.utils import register_rule, render_step, render_strategy

@register_rule("Contradiction")
def rule_Contradiction(strategy, previous, subsequent, mark_list, proof):
    goal_init = previous.get("goal", "<code>goal_init</code>")
    h_contra = strategy.get("h_contra", "<code>h_contra</code>")
    hypothesis_step = render_step(
        tag = "假设",
        content = f"假设结论不成立, 即 {h_contra}",
        goal_before = goal_init,
        goal_after = "",
        mark_list = []
    )
    remaining_steps = proof.render(strategy.get("proof"), mark_list.append("Contradiction"))
    return render_strategy(
        sort = "contradiction",
        tag = "反证法",
        content = f"\n{hypothesis_step}\n\n{remaining_steps}\n"
    )