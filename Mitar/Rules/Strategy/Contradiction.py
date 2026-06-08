from Mitar.utils import register_rule
from Mitar.engine import render_step, render_strategy

@register_rule("Contradiction")
def rule_Contradiction(strategy, previous, subsequent, mark_list, proof):
    _info = strategy.get("info", {})
    _proof = strategy.get("proof", [])
    h_contra = _info.get("h_contra", "<code>h_contra</code>")
    hypothesis_step = render_step(
        tag = "假设",
        content = f"假设结论不成立, 即{h_contra}",
        mark_list = []
    )
    contradictive_proof = proof.render(_proof, mark_list + ["Contradiction"])
    return render_strategy(
        sort = "contradiction",
        tag = "反证法",
        content = hypothesis_step + "\n\n" + contradictive_proof
    )
