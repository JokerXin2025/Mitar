"""Semantic macro configuration, aliases, normalization, and validation."""

from __future__ import annotations

import re
import tomllib
from pathlib import Path

from .model import Macro, MacroStyle, Normalization


FIXITIES = {"atom", "prefix", "postfix", "infix", "binder", "application", "custom"}
ASSOCIATIVITIES = {"left", "right", "none"}
MODES = {"formula", "text"}
_PLACEHOLDER = re.compile(r"#(\d+)")


class MacroRegistry:
    def __init__(self, macros: dict[str, Macro] | None = None, aliases: dict[str, str] | None = None, normalizations: dict[str, Normalization] | None = None, relations: dict[str, str] | None = None, phrases: dict[str, dict[str, str]] | None = None):
        self.macros = macros or {}
        self.aliases = aliases or {}
        self.normalizations = normalizations or {}
        self.relations = relations or {}
        self.phrases = phrases or {}

    def rel_symbol(self, name: str) -> str:
        return self.relations.get(name, name)

    def get(self, name: str) -> Macro | None:
        return self.macros.get(self.resolve_alias(name))

    def resolve_alias(self, name: str) -> str:
        seen: set[str] = set()
        current = name
        while current in self.aliases:
            if current in seen:
                raise ValueError(f"L2T007: alias cycle involving {current}")
            seen.add(current)
            current = self.aliases[current]
        return current

    def add(self, macro: Macro, *, replace: bool = False) -> None:
        if macro.name in self.macros and not replace:
            raise ValueError(f"L2T005: duplicate macro {macro.name}")
        self.macros[macro.name] = macro

    def style(self, macro: Macro, requested: str) -> MacroStyle:
        for style in macro.styles:
            if style.name == requested:
                return style
        for fallback in ("formula",):
            for style in macro.styles:
                if style.name == fallback:
                    return style
        raise ValueError(f"L2T006: macro {macro.name} has no usable style")

    def phrase(self, name: str, language: str) -> str | None:
        values = self.phrases.get(name, {})
        return values.get(language) or values.get("en") or values.get("zh")


def load_macros_toml(path: str | Path) -> MacroRegistry:
    path = Path(path)
    if not path.is_file():
        return MacroRegistry()
    with path.open("rb") as stream:
        data = tomllib.load(stream)
    registry = MacroRegistry()
    registry.relations.update({entry["name"]: entry.get("symbol", entry["name"]) for entry in data.get("relation", [])})
    registry.phrases.update({
        entry["name"]: {language: value for language, value in entry.items() if language != "name" and isinstance(value, str)}
        for entry in data.get("phrase", [])
        if isinstance(entry.get("name"), str)
    })
    for entry in data.get("alias", []):
        name, target = entry.get("name"), entry.get("target")
        if not isinstance(name, str) or not isinstance(target, str):
            raise ValueError("L2T005: alias requires name and target")
        registry.aliases[name] = target
    for name in registry.aliases:
        registry.resolve_alias(name)
    for entry in data.get("normalization", []):
        operation = entry.get("operation")
        if operation not in {"select", "rename", "drop", "reorder"}:
            raise ValueError(f"L2T008: invalid normalization operation {operation}")
        registry.normalizations[entry["name"]] = Normalization(
            entry["name"], operation, entry.get("argument"), entry.get("target"), tuple(entry.get("arguments", []))
        )
    for entry in data.get("macro", []):
        arguments = entry.get("arguments", [])
        if arguments != "explicit":
            if not isinstance(arguments, list) or not all(isinstance(i, int) and i >= 0 for i in arguments):
                raise ValueError(f"L2T002: invalid arguments for macro {entry.get('name')}")
            arguments = tuple(arguments)
        styles = tuple(_parse_style(entry["name"], raw, bool(entry.get("dynamic_arity", False))) for raw in entry.get("styles", []))
        if not styles:
            raise ValueError(f"L2T004: macro {entry['name']} has no styles")
        if len({style.name for style in styles}) != len(styles):
            raise ValueError(f"L2T005: duplicate style in macro {entry['name']}")
        if isinstance(arguments, tuple):
            for style in styles:
                refs = [int(value) for value in _PLACEHOLDER.findall(style.template)]
                if refs and max(refs) >= len(arguments):
                    raise ValueError(f"L2T004: template references a missing child in macro {entry['name']}")
        registry.add(Macro(
            entry["name"], entry.get("kind", "const"), arguments, styles,
            bool(entry.get("dynamic_arity", False)),
        ))
    return registry


def _parse_style(macro_name: str, raw: dict, dynamic: bool) -> MacroStyle:
    mode = raw.get("mode", "formula")
    fixity = raw.get("fixity", "custom")
    associativity = raw.get("associativity", "none")
    precedence = raw.get("precedence", 100)
    template = raw.get("template", "")
    if mode not in MODES or fixity not in FIXITIES or associativity not in ASSOCIATIVITIES:
        raise ValueError(f"L2T008: invalid layout for macro {macro_name}")
    if not isinstance(precedence, int) or not 0 <= precedence <= 100:
        raise ValueError(f"L2T008: invalid precedence for macro {macro_name}")
    has_dynamic = "#*" in template
    if dynamic != has_dynamic:
        raise ValueError(f"L2T004: dynamic placeholder mismatch for macro {macro_name}")
    refs = sorted({int(value) for value in _PLACEHOLDER.findall(template)})
    if not dynamic and refs and refs != list(range(refs[-1] + 1)):
        raise ValueError(f"L2T004: non-contiguous placeholders for macro {macro_name}")
    return MacroStyle(
        raw.get("name", "formula"), mode, template, fixity, precedence,
        associativity, tuple(raw.get("child_roles", [])), raw.get("separator", ", "),
    )
