from Mitar.engine import render_details, render_step
from Mitar.project import MitarError
from Mitar.utils import register_rule
from Mitar.highlight import highlight_code


@register_rule("embed")
def rule_embed(step, previous, subsequent, mark_list, proof):
    theorem = step.get("theorem", "")
    proof_value = step.get("proof")
    args = step.get("args", [])
    arg_kinds = step.get("argKinds", [])
    argument_text = []
    if isinstance(args, list):
        for index, value in enumerate(args):
            rendered = proof.tex_param(value)
            kind = arg_kinds[index] if isinstance(arg_kinds, list) and index < len(arg_kinds) else ""
            argument_text.append(f"{kind}: {rendered}" if kind and rendered else rendered)
    summary = ", ".join(value for value in argument_text if value)

    if isinstance(proof_value, list):
        content = proof.render(proof_value, ["Local"])
    elif isinstance(proof_value, dict) and "$resource" in proof_value:
        if proof.resource_loader is None:
            raise MitarError("Embedded proof resource requires a project root")
        loaded = proof.resource_loader.load_proof(proof_value)
        if loaded.path in proof.resource_stack:
            raise MitarError(f"Cyclic embedded proof resource: {loaded.path}")
        child = type(proof)(
            loaded.proof,
            language=proof.language,
            project_root=proof.project_root,
            expression_resolver=loaded.resolver,
            resource_loader=proof.resource_loader,
            resource_stack=proof.resource_stack + (loaded.path,),
        )
        if loaded.proof is None:
            highlighted, _ = highlight_code(loaded.code, "lean4", theme="light")
            content = f'<pre class="page-code code-highlighted">{highlighted}</pre>'
        else:
            content = child.render(loaded.proof, ["Local"])
            proof.diagnostics.extend(child.diagnostics)
    else:
        content = render_step(
            "嵌入定理" if proof.language == "zh" else "Embedded theorem",
            summary,
            [],
        )

    title = str(theorem)
    if summary:
        title = f"{title} ({summary})"
    return render_details(
        open=True,
        tag="嵌入证明" if proof.language == "zh" else "Embedded proof",
        title=title,
        content=content,
    )
