"""Public Lean2TeX facade: ExprJSON -> DisplayTree -> TeX."""

from __future__ import annotations

import tomllib
from pathlib import Path

from .expr import flatten_app
from .macros import MacroRegistry, load_macros_toml
from .model import DisplayNode, RenderDiagnostic
from .renderer import LayoutRenderer
from .semantic import SemanticConverter
from .variable import VarTypeConfig, VariableAllocator


def auto_wrap(tex: str, node_type: str, role: str, parent: str) -> str:
    """Legacy wrapping helper retained for external callers during migration."""
    if node_type == "Add" and parent == "Mul":
        tex = f"\\left({tex}\\right)"
    if role == "base" and parent == "Supscript" and node_type in ("Add", "Mul", "Supscript"):
        tex = f"\\left({tex}\\right)"
    if node_type != "Text" and parent == "Text":
        tex = f" ${tex}$ "
    if node_type == "Text" and parent != "Text":
        tex = f"\\text{{{tex}}}"
    return tex


class Expr2TeX:
    """Compatibility facade over the semantic converter and layout renderer."""

    def __init__(self, registry: MacroRegistry | None = None, allocator: VariableAllocator | None = None):
        self.registry = registry or MacroRegistry()
        self.allocator = allocator or VariableAllocator()
        self.converter = SemanticConverter(self.registry, self.allocator)
        self.layout = LayoutRenderer(self.registry)
        self.diagnostics: list[RenderDiagnostic] = []

    def reset(self) -> None:
        self.allocator.reset()
        self.diagnostics.clear()

    def diagnostics_dict(self) -> list[dict]:
        return [diagnostic.as_dict() for diagnostic in self.diagnostics]

    def convert(
        self,
        node: dict,
        fvars: dict[str, str] | None = None,
        bvar_env: list[str] | None = None,
    ) -> DisplayNode:
        """Convert one ExprJSON object into a renderer-independent DisplayTree."""
        display = self.converter.convert(node, fvars, bvar_env)
        self.diagnostics = list(self.converter.diagnostics)
        return display

    def render_display(
        self,
        node: DisplayNode,
        style: str = "formula",
        *,
        parent: str = "Text",
        language: str = "zh",
    ) -> str:
        parent_mode = "text" if parent == "Text" else "formula"
        tex = self.layout.render(node, style, parent_mode, language=language)
        self.diagnostics.extend(self.layout.diagnostics)
        return tex

    def render(
        self,
        node: dict,
        role: str = "only",
        parent: str = "Text",
        styles: tuple[str, ...] = ("Root",),
        fvars: dict[str, str] | None = None,
        bvar_env: list[str] | None = None,
        style: str = "formula",
        language: str = "zh",
    ) -> str:
        """Render ExprJSON while retaining the historical call signature."""
        display = self.convert(node, fvars, bvar_env)
        return self.render_display(display, style, parent=parent, language=language)

    def render_relation(self, relation: object) -> str:
        """Render a calc relation through a stable public API."""
        if not isinstance(relation, dict):
            return "" if relation is None else str(relation)
        exported_head = relation.get("headConstant")
        if isinstance(exported_head, str):
            return self.registry.rel_symbol(exported_head)
        head, _ = flatten_app(relation)
        if head.get("kind") == "const":
            return self.registry.rel_symbol(str(head.get("name", "")))
        return self.render(relation)


def load(
    variable_path: str | Path | None = None,
    macros_path: str | Path | None = None,
) -> Expr2TeX:
    """Load semantic macros and variable configuration."""
    here = Path(__file__).parent
    variable_path = Path(variable_path) if variable_path else here / "config" / "variable.toml"
    macros_path = Path(macros_path) if macros_path else here / "config" / "macros.toml"
    allocator = VariableAllocator(_load_variable_toml(variable_path))
    registry = load_macros_toml(macros_path)
    return Expr2TeX(registry, allocator)


def _load_variable_toml(path: Path) -> list[VarTypeConfig]:
    try:
        with path.open("rb") as stream:
            data = tomllib.load(stream)
    except FileNotFoundError:
        return []
    return [
        VarTypeConfig(entry["name"], entry.get("default", ""), list(entry.get("var_names", [])))
        for entry in data.get("type", [])
    ]
