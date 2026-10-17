from Mitar.utils import register_rule
from Mitar.engine import render_details


@register_rule("have")
def rule_have(subgoal, previous, subsequent, mark_list, proof):
    info = subgoal.get("info", {}) if isinstance(subgoal.get("info"), dict) else {}
    title = proof.tex(subgoal.get("type", info.get("type")))
    content = proof.render(subgoal.get("proof", []), ["Local"])
    return render_details(
        open = True,
        tag = proof.text("strategy.have"),
        title = title,
        content = content
    )
