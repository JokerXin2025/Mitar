from dataclasses import dataclass
from pathlib import Path
import tomllib

from Mitar.i18n import DEFAULT_LANGUAGE, normalize_language


class MitarError(Exception):
    pass


@dataclass(frozen = True)
class BuildTarget:
    root: Path
    module: str | None = None

    @property
    def source_file(self) -> Path | None:
        if self.module is None:
            return None
        return self.root.joinpath(*self.module.split(".")).with_suffix(".lean")

    @property
    def page_file(self) -> Path | None:
        if self.module is None:
            return None
        parts = self.module.split(".")
        return self.root / ".ProofScript" / "pages" / Path(*parts[:-1]) / f"{parts[-1]}.json"


def find_project_root(start: Path) -> Path:
    current = start.resolve()
    if current.is_file():
        current = current.parent
    for directory in (current, *current.parents):
        if (directory / "lakefile.toml").is_file() or (directory / "lakefile.lean").is_file():
            return directory
    raise MitarError(f"No Lean project found from {start}")


def project_language(root: Path, override: str | None = None) -> str:
    if override is not None:
        return normalize_language(override)
    config = root / "mitar.toml"
    try:
        with config.open("rb") as stream:
            data = tomllib.load(stream)
    except (FileNotFoundError, tomllib.TOMLDecodeError, OSError):
        return DEFAULT_LANGUAGE
    section = data.get("mitar", {})
    value = section.get("default_language") if isinstance(section, dict) else None
    return normalize_language(value)


def resolve_target(value: str, cwd: Path | None = None) -> BuildTarget:
    cwd = (cwd or Path.cwd()).resolve()
    candidate = (cwd / value).resolve()
    if candidate.is_dir():
        return BuildTarget(find_project_root(candidate))

    root = find_project_root(cwd)
    module = value.strip(".")
    if not module or any(not part for part in module.split(".")):
        raise MitarError(f"Invalid Lean module name: {value}")
    target = BuildTarget(root, module)
    if not target.source_file.is_file():
        raise MitarError(f"Lean module {module} not found at {target.source_file}")
    return target
