"""Unified TOML-driven strategy renderer."""

from __future__ import annotations

import re
import tomllib
from dataclasses import dataclass
from pathlib import Path

from Mitar.engine import render_details, render_step, render_strategy
from Mitar.i18n import language_fallbacks, normalize_language
from Mitar.utils import register_rule, to_roman


_PLACEHOLDER = re.compile(r"\$\{([A-Za-z_][A-Za-z0-9_]*)\}")
SUPPORTED_KINDS = {"induction", "cases", "contradiction", "decompose"}
CURRENT_DIR = Path(__file__).resolve().parent
CONFIG_DIR = CURRENT_DIR / "Strategy"


@dataclass(frozen=True)
class StrategyConfig:
    name: str
    kind: str
    nodes: tuple[str, ...]
    dynamic_nodes: bool
    languages: dict[str, dict[str, str]]
    source: Path | None = None

    def text(self, key: str, language: str, **values) -> str:
        for candidate in language_fallbacks(language):
            template = self.languages.get(candidate, {}).get(key)
            if isinstance(template, str):
                return _format(template, values)
        return ""


def load_strategy_configs(directory: Path = CONFIG_DIR) -> dict[str, StrategyConfig]:
    configs = {}
    for path in sorted(directory.glob("*.toml")):
        with path.open("rb") as stream:
            data = tomllib.load(stream)
        strategy = data.get("strategy", {})
        if not isinstance(strategy, dict):
            continue
        name = strategy.get("name", path.stem)
        kind = strategy.get("kind", name)
        if not isinstance(name, str) or not name:
            raise ValueError(f"STR001: strategy name is required in {path}")
        if kind not in SUPPORTED_KINDS:
            raise ValueError(f"STR002: unsupported strategy kind {kind!r} in {path}")
        nodes = strategy.get("nodes", [])
        if not isinstance(nodes, list) or not all(isinstance(node, str) and node for node in nodes):
            raise ValueError(f"STR003: nodes must be a list of non-empty strings in {path}")
        languages = data.get("language", {})
        if not isinstance(languages, dict):
            languages = {}
        if not isinstance(languages, dict) or not {"zh", "en"}.issubset(languages):
            raise ValueError(f"STR004: strategy {name} must define zh and en language templates in {path}")
        configs[name] = StrategyConfig(
            name=name,
            kind=kind,
            nodes=tuple(nodes),
            dynamic_nodes=bool(strategy.get("dynamic_nodes", False)),
            languages={
                language: values
                for language, values in languages.items()
                if isinstance(values, dict)
            },
            source=path,
        )
        _validate_strategy_texts(configs[name])
    return configs


def _format(template: str, values: dict[str, object]) -> str:
    rendered = _PLACEHOLDER.sub(
        lambda match: str(values.get(match.group(1), match.group(0))), template
    )
    for key, value in values.items():
        rendered = rendered.replace(f"{{{key}}}", str(value))
    return rendered


def _validate_strategy_texts(config: StrategyConfig) -> None:
    required = {
        "induction": ("tag", "method", "intro_tag", "intro", "base_tag", "base_title", "step_tag", "step_title"),
        "cases": ("tag", "basis_tag", "basis_content", "case_tag"),
        "contradiction": ("tag", "assumption_tag", "assumption_content"),
        "decompose": ("tag", "intro_tag", "intro_content", "subgoal_tag"),
    }[config.kind]
    for language in ("zh", "en"):
        missing = [key for key in required if not isinstance(config.languages[language].get(key), str)]
        if missing:
            raise ValueError(f"STR005: strategy {config.name} is missing {language} templates: {', '.join(missing)}")
    allowed = {
        "induction": {"n", "method"},
        "cases": {"p", "case"},
        "contradiction": {"hypothesis"},
        "decompose": {"case"},
    }[config.kind]
    for language, values in config.languages.items():
        for key, template in values.items():
            unknown = sorted(set(_PLACEHOLDER.findall(template)) - allowed)
            if unknown:
                raise ValueError(f"STR006: unknown placeholders in {config.name}.{language}.{key}: {', '.join(unknown)}")


def _render_induction(strategy, mark_list, proof, config: StrategyConfig):
    language = proof.language
    info = strategy.get("info", {}) if isinstance(strategy.get("info", {}), dict) else {}
    n = proof.tex_param(info.get("n")) if info.get("n") is not None else "<code>n</code>"
    method = config.text("method", language)
    intro = config.text("intro", language, n=n, method=method)
    introduce_step = render_step(config.text("intro_tag", language), intro, [])

    base = proof.render(strategy.get("zero", []), ["Induction"])
    base_details = render_details(
        open=True,
        tag=config.text("base_tag", language),
        title=config.text("base_title", language),
        content=base,
    )

    inductive = proof.render(strategy.get("succ", []), mark_list + ["Induction"])
    inductive_details = render_details(
        open=True,
        tag=config.text("step_tag", language),
        title=config.text("step_title", language),
        content=inductive,
    )
    return render_strategy(
        sort="induction",
        tag=config.text("tag", language),
        content="\n\n".join((introduce_step, base_details, inductive_details)),
    )


def _render_cases(strategy, mark_list, proof, config: StrategyConfig):
    language = proof.language
    info = strategy.get("info", {}) if isinstance(strategy.get("info", {}), dict) else {}
    subject = info.get("p", info.get("value", info.get("h")))
    p = proof.tex_param(subject) if subject is not None else "<code>p</code>"
    basis = render_step(
        config.text("basis_tag", language),
        config.text("basis_content", language, p=p),
        [],
    )
    nodes = _strategy_nodes(strategy, config)
    branches = [strategy.get(node, []) for node in nodes]
    details = [basis]
    for index, branch in enumerate(branches, 1):
        details.append(render_details(
            open=True,
            tag=config.text("case_tag", language, case=to_roman(index)),
            title="",
            content=proof.render(branch, mark_list),
        ))
    return render_strategy(
        sort="cases",
        tag=config.text("tag", language),
        content="\n\n".join(details),
    )


def _render_contradiction(strategy, mark_list, proof, config: StrategyConfig):
    language = proof.language
    info = strategy.get("info", {}) if isinstance(strategy.get("info", {}), dict) else {}
    hypothesis = "<code>h</code>"
    h_node = info.get("h")
    if isinstance(h_node, dict) and h_node.get("type") is not None:
        hypothesis = proof.tex(h_node["type"])
    step = render_step(
        config.text("assumption_tag", language),
        config.text("assumption_content", language, hypothesis=hypothesis),
        [],
    )
    body = proof.render(strategy.get("proof", []), mark_list + ["Contradiction"])
    return render_strategy(
        sort="contradiction",
        tag=config.text("tag", language),
        content=step + "\n\n" + body,
    )


def _render_decompose(strategy, mark_list, proof, config: StrategyConfig):
    language = proof.language
    intro = render_step(
        config.text("intro_tag", language),
        config.text("intro_content", language),
        [],
    )
    details = [intro]
    for index, node in enumerate(_strategy_nodes(strategy, config), 1):
        details.append(render_details(
            open=True,
            tag=config.text("subgoal_tag", language, case=to_roman(index)),
            title="",
            content=proof.render(strategy.get(node, []), mark_list),
        ))
    return render_strategy(
        sort="decompose",
        tag=config.text("tag", language),
        content="\n\n".join(details),
    )


def _strategy_nodes(strategy, config: StrategyConfig):
    if not config.dynamic_nodes:
        return config.nodes
    reserved = {"name", "info"}
    return tuple(
        key for key, value in strategy.items()
        if key not in reserved and isinstance(value, list)
    )


def render_strategy_rule(strategy, previous, subsequent, mark_list, proof):
    name = strategy.get("name", "")
    config = STRATEGIES.get(name)
    if config is None:
        raise ValueError(f"Unknown strategy configuration: {name}")
    renderers = {
        "induction": _render_induction,
        "cases": _render_cases,
        "contradiction": _render_contradiction,
        "decompose": _render_decompose,
    }
    renderer = renderers.get(config.kind)
    if renderer is None:
        raise ValueError(f"Unsupported strategy kind: {config.kind}")
    return renderer(strategy, mark_list, proof, config)


def register_strategies(configs: dict[str, StrategyConfig] | None = None) -> None:
    if configs:
        STRATEGIES.update(configs)
    for name in (configs or STRATEGIES):
        register_rule(name)(render_strategy_rule)


STRATEGIES = load_strategy_configs()
register_strategies()
