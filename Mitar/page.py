import html
import json
import os
import re
from dataclasses import dataclass
from pathlib import Path

from Mitar.engine import ERROR, SORRY, ProofEngine, render_module_navigation, render_page
from Mitar.highlight import highlight_code
from Mitar.project import MitarError
from Mitar.Rules.proof_text import ProofTextRenderer
from Mitar.Rules.media import render_figure, render_latex
from Mitar.Rules.references import render_references
from Mitar.schema import ExpressionResolver, ResourceLoader
from Mitar.Rules.computation import render_computation


SUPPORTED_SCHEMA_MAJOR = 0
SUPPORTED_COMPUTATION_SCHEMA_VERSION = "1.1.0"
ANCHOR_CHARS = re.compile(r"[^A-Za-z0-9_-]+")


@dataclass(frozen = True)
class Page:
    path: Path
    project_info: dict
    module: str
    source: Path
    components: list

    @property
    def output_path(self) -> Path:
        parts = self.module.split(".")
        if len(parts) == 1:
            return Path("index.html")
        return Path(*parts[:-1]) / f"{parts[-1]}.html"


@dataclass(frozen = True)
class LabelTarget:
    output_path: Path
    anchor: str
    source: Path
    line: int


@dataclass(frozen=True)
class TheoremTarget:
    declaration: str
    title: str
    output_path: Path
    anchor: str
    proof_path: Path


def _schema_major(version) -> int:
    if not isinstance(version, str):
        raise MitarError("Page schemaVersion must be a semantic-version string")
    try:
        major, _minor, _patch = version.split(".", 2)
        return int(major)
    except (TypeError, ValueError):
        raise MitarError(f"Invalid page schemaVersion: {version}") from None


def load_page(path: Path, project_root: Path) -> Page:
    try:
        data = json.loads(path.read_text(encoding = "utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise MitarError(f"Failed to read page JSON {path}: {error}") from error

    if not isinstance(data, dict):
        raise MitarError(f"Page JSON must be an object: {path}")
    if _schema_major(data.get("schemaVersion")) != SUPPORTED_SCHEMA_MAJOR:
        raise MitarError(f"Unsupported page schema version {data.get('schemaVersion')} in {path}")
    module = data.get("module")
    project_info = data.get("ProjectInfo")
    source = data.get("source")
    components = data.get("components")
    if not isinstance(module, str) or not module:
        raise MitarError(f"Page module must be a non-empty string: {path}")
    if not isinstance(project_info, dict):
        raise MitarError(f"Page ProjectInfo must be an object: {path}")
    if not isinstance(source, str) or not source:
        raise MitarError(f"Page source must be a non-empty string: {path}")
    if not isinstance(components, list):
        raise MitarError(f"Page components must be an array: {path}")

    source_path = Path(source)
    if not source_path.is_absolute():
        source_path = project_root / source_path
    return Page(path, project_info, module, source_path, components)


def discover_pages(project_root: Path) -> list[Page]:
    output_root = project_root / ".ProofScript" / "pages"
    if not output_root.is_dir():
        raise MitarError(f"ProofScript output directory not found: {output_root}")
    paths = list(output_root.rglob("*.json"))
    pages = [load_page(path, project_root) for path in paths]
    pages.sort(key = lambda page: page.module)
    if not pages:
        raise MitarError(f"No ProofScript page JSON found in {output_root}")
    return pages


def build_label_index(pages: list[Page]) -> dict[tuple[str, str], LabelTarget]:
    labels = {}
    for page in pages:
        for component in page.components:
            data = component.get("data", {}) if isinstance(component, dict) else {}
            if "text" in data:
                value = data.get("text", {}).get("value", {})
                _collect_heading_labels(value.get("blocks", []), page, labels)
            elif "theorem" in data or "lemma" in data:
                declaration_kind = "theorem" if "theorem" in data else "lemma"
                value = data.get(declaration_kind, {}).get("value", {})
                label = value.get("label")
                name = value.get("name")
                proof = value.get("proof")
                if isinstance(label, str):
                    _add_label(labels, "theorem", label, page, f"theorem-{label}")
                declaration = _declaration_name(page.module, proof)
                if declaration is not None:
                    anchor = f"theorem-{label}" if isinstance(label, str) else _theorem_anchor(proof, name)
                    _add_label(labels, "theorem-name", declaration, page, anchor)
            elif "figure" in data or "latex" in data:
                tag = "figure" if "figure" in data else "latex"
                value = data.get(tag, {}).get("value", {})
                label = value.get("metadata", {}).get("label")
                if isinstance(label, str):
                    _add_label(labels, "figure", label, page, f"figure-{label}")
    return labels


def build_theorem_dependency_index(pages: list[Page], project_root: Path):
    targets = {}
    proof_targets = {}
    for page in pages:
        for component in page.components:
            data = component.get("data", {}) if isinstance(component, dict) else {}
            declaration_kind = "theorem" if "theorem" in data else "lemma" if "lemma" in data else None
            value = data.get(declaration_kind, {}).get("value", {}) if declaration_kind else {}
            if not isinstance(value, dict):
                continue
            proof = value.get("proof")
            declaration = _declaration_name(page.module, proof)
            if declaration is None:
                continue
            proof_path = Path(proof)
            if not proof_path.is_absolute():
                proof_path = project_root / proof_path
            label = value.get("label")
            anchor = f"theorem-{label}" if isinstance(label, str) else _theorem_anchor(proof, value.get("name"))
            target = TheoremTarget(
                declaration=declaration,
                title=str(value.get("name") or declaration.rsplit(".", 1)[-1]),
                output_path=page.output_path,
                anchor=anchor,
                proof_path=proof_path.resolve(),
            )
            targets[declaration] = target
            proof_targets[target.proof_path] = declaration

    dependencies = {declaration: set() for declaration in targets}
    for declaration, target in targets.items():
        try:
            document = json.loads(target.proof_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        referenced = set()
        _collect_dependency_names(document.get("proof", []), referenced, proof_targets, project_root)
        code = document.get("code")
        if isinstance(code, str):
            for candidate in targets:
                short_name = candidate.rsplit(".", 1)[-1]
                if candidate in code or re.search(
                    rf"(?<![A-Za-z0-9_']){re.escape(short_name)}(?![A-Za-z0-9_'])", code
                ):
                    referenced.add(candidate)
        expressions = document.get("expressions", {})
        if isinstance(expressions, dict):
            _collect_constant_names(expressions, referenced)
        else:
            _collect_constant_names(document.get("proof", []), referenced)
        dependencies[declaration] = (referenced & targets.keys()) - {declaration}

    dependents = {declaration: set() for declaration in targets}
    for declaration, required in dependencies.items():
        for dependency in required:
            dependents[dependency].add(declaration)
    return {
        declaration: {
            "target": target,
            "dependencies": tuple(sorted(dependencies[declaration])),
            "dependents": tuple(sorted(dependents[declaration])),
            "targets": targets,
        }
        for declaration, target in targets.items()
    }


def _collect_constant_names(value, names):
    if isinstance(value, list):
        for child in value:
            _collect_constant_names(child, names)
    elif isinstance(value, dict):
        if value.get("kind") == "const" and isinstance(value.get("name"), str):
            names.add(value["name"])
        for child in value.values():
            _collect_constant_names(child, names)


def _collect_dependency_names(value, names, proof_targets, project_root):
    if isinstance(value, list):
        for child in value:
            _collect_dependency_names(child, names, proof_targets, project_root)
        return
    if not isinstance(value, dict):
        return
    if value.get("_step_") == "embed":
        theorem = value.get("theorem")
        if isinstance(theorem, str):
            names.add(theorem)
        resource = value.get("proof", {}).get("$resource", {}) if isinstance(value.get("proof"), dict) else {}
        path = resource.get("path") if isinstance(resource, dict) else None
        if isinstance(path, str):
            names.add(proof_targets.get((project_root / path).resolve(), ""))
    for child in value.values():
        _collect_dependency_names(child, names, proof_targets, project_root)


def _collect_heading_labels(blocks, page, labels):
    for block in blocks if isinstance(blocks, list) else []:
        if not isinstance(block, dict):
            continue
        if "heading" in block:
            label = block["heading"].get("label")
            if isinstance(label, str):
                _add_label(labels, "heading", label, page, f"heading-{label}")
        elif "quote" in block:
            _collect_heading_labels(block["quote"].get("content", []), page, labels)
        elif "orderedList" in block or "unorderedList" in block:
            key = "orderedList" if "orderedList" in block else "unorderedList"
            for item in block[key].get("items", []):
                _collect_heading_labels(item.get("content", []), page, labels)


def _add_label(labels, kind, label, page, anchor):
    key = (kind, label)
    if key in labels:
        raise MitarError(f"Duplicate {kind} label: {label}")
    location = _component_location(page, kind, label)
    labels[key] = LabelTarget(page.output_path, anchor, page.source, location)


def _component_location(page, kind, label):
    for component in page.components:
        data = component.get("data", {}) if isinstance(component, dict) else {}
        if kind == "theorem" and "theorem" in data:
            value = data["theorem"].get("value", {})
            if value.get("label") != label:
                continue
        elif kind == "heading" and "text" in data:
            continue
        else:
            continue
        start = component.get("source", {}).get("start", 0)
        try:
            return page.source.read_bytes()[:start].count(b"\n") + 1
        except OSError:
            return 0
    return 0


class PageRenderer:
    def __init__(self, project_root: Path, build_root: Path, labels, pages = None, default_language="zh", theorem_dependencies=None):
        self.project_root = project_root
        self.build_root = build_root
        self.labels = labels
        self.pages = list(pages or [])
        self.default_language = default_language if default_language in ("zh", "en") else "zh"
        self.diagnostics = []
        self.resources = ResourceLoader(project_root)
        self.theorem_dependencies = theorem_dependencies or build_theorem_dependency_index(self.pages, project_root)

    def render(self, page: Page) -> str:
        current_output = page.output_path
        contents = self.render_components(page, current_output)
        contents.extend(self._descendant_index(page.module, current_output))
        index_href = os.path.relpath(self.build_root / "index.html", (self.build_root / current_output).parent)
        pages = self.pages or [page]
        theorem_navigation = self._theorem_navigation(page, current_output)
        navigation = render_module_navigation(pages, current_output, page.module, index_href, self.default_language, theorem_navigation)
        return render_page(page.module, "\n\n".join(contents), index_href, navigation, self.default_language)

    def _theorem_navigation(self, page, current_output):
        panels = []
        current_dir = current_output.parent
        for component in page.components:
            data = component.get("data", {}) if isinstance(component, dict) else {}
            if "lemma" in data:
                continue
            value = data.get("theorem", {}).get("value", {})
            declaration = _declaration_name(page.module, value.get("proof")) if isinstance(value, dict) else None
            entry = self.theorem_dependencies.get(declaration)
            if entry is None:
                continue
            target = entry["target"]
            levels = []
            for css_class, title_zh, title_en, keys in (
                ("incoming", "当前定理依赖的定理", "Theorems used by the current theorem", entry["dependencies"]),
                ("outgoing", "依赖当前定理的定理", "Theorems using the current theorem", entry["dependents"]),
            ):
                links = []
                for key in keys:
                    other = entry["targets"][key]
                    href = os.path.relpath(other.output_path, current_dir) + f"#{other.anchor}"
                    links.append(
                        f'<li><a class="theorem-dependency-node" href="{html.escape(href, quote=True)}" title="{html.escape(other.declaration, quote=True)}"><span class="theorem-dependency-mark" aria-hidden="true"></span>{html.escape(other.title)}</a></li>'
                    )
                if links:
                    levels.append(
                        f'<ul class="theorem-dependency-level {css_class}" aria-label="{html.escape(title_zh, quote=True)}" data-label-en="{html.escape(title_en, quote=True)}">{"".join(links)}</ul>'
                    )
                else:
                    levels.append("")
            incoming, outgoing = levels
            panels.append(
                f'<div class="theorem-dependency-panel" data-theorem-anchor="{html.escape(target.anchor, quote=True)}" hidden><div class="theorem-dependency-graph">{incoming}<div class="theorem-dependency-current"><span class="theorem-dependency-mark" aria-hidden="true"></span><strong>{html.escape(target.title)}</strong></div>{outgoing}</div></div>'
            )
        if not panels:
            return ""
        return (
            '<section class="theorem-dependency-navigation" hidden>'
            '<h3><span data-language-panel="zh">定理依赖</span><span data-language-panel="en" hidden>Theorem dependencies</span></h3>'
            + "".join(panels) + '</section>'
        )

    def render_components(self, page: Page, current_output: Path) -> list[str]:
        return [self._component(component, page, current_output) for component in page.components]

    def render_directory(self, module: str) -> str:
        current_output = _module_output_path(module)
        contents = self._descendant_index(module, current_output)
        index_href = os.path.relpath(self.build_root / "index.html", (self.build_root / current_output).parent)
        navigation = render_module_navigation(
            self.pages, current_output, module, index_href, self.default_language
        )
        return render_page(module, "\n\n".join(contents), index_href, navigation, self.default_language)

    def _descendant_index(self, module, current_output):
        descendants = [
            page for page in self.pages
            if page.module.startswith(f"{module}.")
        ]
        if not descendants:
            return []
        current_dir = current_output.parent
        tree = {}
        for page in descendants:
            relative = page.module.split(".")[len(module.split(".")):]
            nodes = tree
            for part in relative:
                node = nodes.setdefault(part, {"page": None, "children": {}})
                nodes = node["children"]
            node["page"] = page
        return [
            f'<ul class="module-index-tree">{_render_index_tree(tree, current_dir, module.split("."))}</ul>'
        ]

    def _component(self, component, page, current_output):
        if not isinstance(component, dict) or not isinstance(component.get("data"), dict):
            raise MitarError(f"Invalid component in {page.path}")
        data = component["data"]
        if len(data) != 1:
            raise MitarError(f"Component must contain exactly one tag in {page.path}")
        tag = next(iter(data))
        envelope = data[tag]
        value = envelope.get("value") if isinstance(envelope, dict) else None
        if tag == "text":
            return ProofTextRenderer(self.labels, self.build_root, current_output).render(value)
        if tag in {"theorem", "lemma"}:
            return self._theorem(value, component.get("source", {}), page, tag)
        if tag == "latex":
            rendered, diagnostics = render_latex(value, self.project_root, self.resources)
            self.diagnostics.extend(diagnostics)
            return rendered
        if tag == "figure":
            rendered, diagnostics = render_figure(value, self.project_root)
            self.diagnostics.extend(diagnostics)
            return rendered
        if tag == "computation":
            if not isinstance(value, dict) or value.get("schemaVersion") != SUPPORTED_COMPUTATION_SCHEMA_VERSION:
                self.diagnostics.append({
                    "kind": "computation-error",
                    "message": f"Unsupported computation schema version: {value.get('schemaVersion') if isinstance(value, dict) else None}",
                })
            return render_computation(value)
        if tag == "references":
            panels = []
            for language in ("zh", "en"):
                panel = render_references(value, self.labels, self.build_root, current_output, language)
                hidden = "" if language == self.default_language else " hidden"
                panels.append(f'<div data-language-panel="{language}"{hidden}>{panel}</div>')
            return "\n".join(panels)
        return self._placeholder(tag, value)

    def _theorem(self, value, location, page, declaration_kind="theorem"):
        state = None
        proof_data = []
        code = ""
        name = value.get("name") if isinstance(value, dict) else None
        proof = value.get("proof") if isinstance(value, dict) else None
        sorry_ax = value.get("sorryAx") if isinstance(value, dict) else None
        label = value.get("label") if isinstance(value, dict) else None
        if not isinstance(name, str) or not name:
            name = "Invalid theorem"
            state = ERROR
        if not isinstance(proof, str) or not proof or not isinstance(sorry_ax, bool):
            state = ERROR
        elif sorry_ax:
            state = SORRY

        proof_path = Path(proof) if isinstance(proof, str) and proof else Path("<invalid-proof>")
        if not proof_path.is_absolute():
            proof_path = self.project_root / proof_path
        try:
            proof_document = json.loads(proof_path.read_text(encoding = "utf-8"))
        except (OSError, json.JSONDecodeError):
            proof_document = None
            state = ERROR
        if isinstance(proof_document, dict):
            try:
                if _schema_major(proof_document.get("schemaVersion")) != SUPPORTED_SCHEMA_MAJOR:
                    state = ERROR
            except MitarError:
                state = ERROR
            if isinstance(proof_document.get("code"), str):
                code = proof_document["code"]
            else:
                state = ERROR
            if isinstance(proof_document.get("proof"), list):
                expressions = proof_document.get("expressions", {})
                if not isinstance(expressions, dict):
                    state = ERROR
                else:
                    try:
                        expression_resolver = ExpressionResolver(expressions)
                        proof_data = proof_document["proof"]
                    except MitarError:
                        state = ERROR
            elif isinstance(proof_document.get("code"), str):
                code = proof_document["code"]
                highlighted_code, _applied = highlight_code(code, "lean4", theme="light")
                return _render_code_only_declaration(
                    declaration_kind, name, label,
                    f"theorem-{label}" if isinstance(label, str) else _theorem_anchor(proof, name),
                    highlighted_code,
                    code.count("\n") + (1 if code else 0)
                )
            else:
                state = ERROR
        else:
            state = ERROR

        source_file = Path(location.get("file", page.source)) if isinstance(location, dict) else page.source
        if not source_file.is_absolute():
            source_file = self.project_root / source_file
        anchor = f"theorem-{label}" if isinstance(label, str) else _theorem_anchor(proof, name)
        highlighted_code, _applied = highlight_code(code, "lean4", theme = "light")
        lines = code.count("\n") + (1 if code else 0)
        rendered = []
        for language in ("zh", "en"):
            engine = ProofEngine(
                proof_data,
                language=language,
                project_root=self.project_root,
                expression_resolver=expression_resolver,
                resource_loader=self.resources,
                resource_stack=(proof_path.resolve(),),
            )
            rendered.append(engine.make(
                name,
                source_file,
                lines,
                highlighted_code,
                anchor if language == "zh" else f"{anchor}-en",
                state = state,
                language = language,
                default_language = self.default_language,
            ))
            self.diagnostics.extend({
                "theorem": name,
                "proof": str(proof_path),
                "language": language,
                **diagnostic,
            } for diagnostic in engine.diagnostics)
        return "\n\n".join(rendered)

    @staticmethod
    def _placeholder(tag, value):
        title = tag
        if isinstance(value, dict):
            title = value.get("metadata", {}).get("title") or tag
        preserved = html.escape(json.dumps(value, ensure_ascii=False), quote=True)
        return f'<section class="unsupported-component" data-component="{html.escape(tag, quote = True)}" data-component-value="{preserved}"><strong>{html.escape(str(title))}</strong><span>Component rendering is not supported yet.</span></section>'


def _render_code_only_declaration(kind, name, label, anchor, code, lines):
    return f'''<section class="theorem-proof theorem-code-only" id="{html.escape(anchor, quote=True)}">
  <h2><span>{html.escape(name)}</span></h2>
  <div class="proof-source-card">
    <div class="code-header"><span>{html.escape(kind.title())}</span><span>{lines} 行</span></div>
    <pre class="page-code code-highlighted"><code>{code}</code></pre>
  </div>
</section>'''


def _theorem_anchor(proof, name) -> str:
    stem = Path(proof).stem if isinstance(proof, str) and proof else str(name)
    slug = ANCHOR_CHARS.sub("-", stem).strip("-") or "proof"
    return f"theorem-name-{slug}"


def directory_modules(pages: list[Page]) -> list[str]:
    modules = set()
    for page in pages:
        parts = page.module.split(".")
        modules.update(".".join(parts[:end]) for end in range(1, len(parts)))
    return sorted(modules)


def _module_output_path(module: str) -> Path:
    parts = module.split(".")
    if len(parts) == 1:
        return Path("index.html")
    return Path(*parts[:-1]) / f"{parts[-1]}.html"


def _declaration_name(module, proof) -> str | None:
    if not isinstance(proof, str) or not proof:
        return None
    path = Path(proof)
    try:
        parts = list(path.parts[path.parts.index("proofs") + 1:])
    except ValueError:
        return None
    module_parts = module.split(".")
    if parts[:len(module_parts)] == module_parts:
        parts = parts[len(module_parts):]
    if not parts:
        return None
    parts[-1] = Path(parts[-1]).stem
    declaration = ".".join(parts)
    return declaration if declaration.startswith(f"{module}.") else f"{module}.{declaration}"


def _render_index_tree(nodes, current_dir, prefix):
    items = []
    for name, node in sorted(nodes.items()):
        path = (*prefix, name)
        page = node["page"]
        if page is None:
            output_path = _module_output_path(".".join(path))
        else:
            output_path = page.output_path
        href = os.path.relpath(output_path, current_dir)
        label = (
            f'<a href="{html.escape(href, quote=True)}">'
            f'<span class="module-index-tree-mark" aria-hidden="true"></span>{html.escape(name)}</a>'
        )
        children = _render_index_tree(node["children"], current_dir, path)
        child_list = f'<ul>{children}</ul>' if children else ""
        items.append(f'<li>{label}{child_list}</li>')
    return "".join(items)
