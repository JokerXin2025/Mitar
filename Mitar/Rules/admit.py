from Mitar.utils import register_rule
from Mitar.engine import render_annotation


@register_rule("admit")
def rule_admit(admit, previous, subsequent, mark_list, proof):
    text = admit.get("reason", "")
    if not text:
        return "<!-- Silent Step: admit (empty) -->"
    return render_annotation(
        sort="admit",
        icon="<i class=\"codicon codicon-workspace-unknown\"></i>",
        content=text,
    )
