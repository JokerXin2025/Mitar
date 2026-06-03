from makepage.utils import register_rule, render_step, render_strategy

@register_rule("Contradiction")
def rule_Contradiction(strategy, previous, subsequent, mark_list, proof):
    goal_init = previous.get("goal", "<code>goal_init</code>")
    _info = strategy.get("info", {})
    _proof = strategy.get("proof", [])
    h_contra = _info.get("h_contra", "<code>h_contra</code>")
    hypothesis_step = render_step(
        tag = "假设",
        content = f"假设结论不成立, 即{h_contra}",
        goal_before = goal_init,
        goal_after = goal_init,
        mark_list = []
    )
    contradictive_proof = proof.render(_proof, mark_list + ["Contradiction"])
    return render_strategy(
        sort = "contradiction",
        tag = "反证法",
        pre_content = hypothesis_step,
        content = contradictive_proof
    )