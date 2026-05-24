import textwrap
from makepage.utils import TPL_STRATEGY, register_rule, render_step

@register_rule("Contradiction")
def rule_contradiction(tactic, final_mark, proof):
    h_contra = MOCK_MAP_JSON.get(tactic["h_contra"])
    hypothesis_step = render_step(
        tag = "假设",
        content = f"假设结论不成立, 即 {h_contra}",
        final_mark = None
    )
    remaining_steps = proof.render(tactic["proof"], "Contradiction")
    inner_content = f"\n{hypothesis_step}\n\n{remaining_steps}\n"
    return TPL_STRATEGY.substitute(
        strategy_class = "contradiction",
        strategy_name = "反证法",
        content = textwrap.indent(inner_content, "        ")
    )