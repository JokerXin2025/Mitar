def rule_unknown(step, previous, subsequent, mark_list, proof):
    from Mitar.engine import render_step

    return render_step(
        tag = proof.text("strategy.unknown"),
        content = "",
        mark_list = [],
        sort = "unknown",
    )
