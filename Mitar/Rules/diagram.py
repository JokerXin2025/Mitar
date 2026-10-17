from string import Template
from pathlib import Path
from textwrap import indent
from Mitar.utils import register_rule
from Mitar.engine import render_annotation
from Mitar.Rules.media import render_latex

CURRENT_DIR = Path(__file__).absolute().parent
TEMPLATE_DIAGRAM = Template((CURRENT_DIR.parent / "Templates/diagram.html").read_text())


@register_rule("svg")
def rule_svg(svg, previous, subsequent, mark_list, proof):
    code = svg.get("code", "")
    if not code:
        return "<!-- Silent Step: svg (empty) -->"
    figure = TEMPLATE_DIAGRAM.substitute(svg_code = indent(code, "    "))
    return render_annotation(
        sort = "diagram",
        icon = "<i class=\"codicon codicon-symbol-color\"></i>",
        content = figure
    )


@register_rule("latex")
def rule_latex(value, previous, subsequent, mark_list, proof):
    rendered, diagnostics = render_latex(
        value, proof.project_root, proof.resource_loader
    )
    proof.diagnostics.extend(diagnostics)
    return render_annotation(
        sort="diagram",
        icon="<i class=\"codicon codicon-symbol-color\"></i>",
        content=rendered,
    )
