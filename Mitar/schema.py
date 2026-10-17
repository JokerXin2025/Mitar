from __future__ import annotations

import json
import re
from dataclasses import dataclass
from pathlib import Path

from Mitar.project import MitarError


EXPRESSION_ID = re.compile(r"^e[0-9]+$")
PROOF_MEDIA_TYPE = "application/vnd.proofscript.proof+json"


class ExpressionResolver:
    """Validate and lazily resolve one proof document's expression DAG."""

    def __init__(self, expressions: dict):
        if not isinstance(expressions, dict):
            raise MitarError("Proof expressions must be an object")
        self.expressions = expressions
        self.cache = {}
        self._validate()

    def _validate(self):
        for reference, node in self.expressions.items():
            if not isinstance(reference, str) or not EXPRESSION_ID.fullmatch(reference):
                raise MitarError(f"Invalid proof expression ID: {reference}")
            if not isinstance(node, dict) or set(node) == {"$ref"}:
                raise MitarError(f"Proof expression {reference} is not a complete node")
            if not isinstance(node.get("kind"), str) or not isinstance(node.get("isProp"), bool):
                raise MitarError(f"Proof expression {reference} is missing kind or isProp")
        checked = set()
        for reference in self.expressions:
            self._check_references(
                self.expressions[reference], frozenset({reference}), checked
            )

    def _check_references(self, value, active, checked):
        if isinstance(value, list):
            for child in value:
                self._check_references(child, active, checked)
            return
        if not isinstance(value, dict):
            return
        if set(value) == {"$ref"}:
            reference = value["$ref"]
            if not isinstance(reference, str) or reference not in self.expressions:
                raise MitarError(f"Unknown proof expression reference: {reference}")
            if reference in active:
                raise MitarError(f"Cyclic proof expression reference: {reference}")
            if reference not in checked:
                self._check_references(
                    self.expressions[reference], active | {reference}, checked
                )
                checked.add(reference)
            return
        for child in value.values():
            self._check_references(child, active, checked)

    def resolve(self, value, active=frozenset()):
        if isinstance(value, list):
            return [self.resolve(child, active) for child in value]
        if not isinstance(value, dict):
            return value
        if set(value) == {"$ref"}:
            reference = value["$ref"]
            if not isinstance(reference, str) or reference not in self.expressions:
                raise MitarError(f"Unknown proof expression reference: {reference}")
            if reference in active:
                raise MitarError(f"Cyclic proof expression reference: {reference}")
            if reference not in self.cache:
                self.cache[reference] = self.resolve(
                    self.expressions[reference], active | {reference}
                )
            return self.cache[reference]
        return {key: self.resolve(child, active) for key, child in value.items()}


def resolve_expressions(value, expressions: dict):
    """Compatibility helper for callers that need one resolved expression value."""
    return ExpressionResolver(expressions).resolve(value)


@dataclass(frozen=True)
class LoadedProof:
    path: Path
    version: str
    code: str
    proof: list | None
    expressions: dict
    resolver: ExpressionResolver | None


class ResourceLoader:
    def __init__(self, project_root: Path):
        self.project_root = project_root.resolve()
        self.text_cache = {}
        self.proof_cache = {}

    def resource_path(self, value, media_type: str | None = None) -> tuple[Path, str]:
        if not isinstance(value, dict) or set(value) != {"$resource"}:
            raise MitarError("Invalid ProofScript resource reference")
        resource = value["$resource"]
        if not isinstance(resource, dict):
            raise MitarError("Invalid ProofScript resource metadata")
        path_value = resource.get("path")
        if not isinstance(path_value, str) or not path_value:
            raise MitarError("ProofScript resource path must be a non-empty string")
        if resource.get("encoding") != "utf-8":
            raise MitarError(f"Unsupported ProofScript resource encoding: {resource.get('encoding')}")
        if media_type is not None and resource.get("mediaType") != media_type:
            raise MitarError(f"Unexpected ProofScript resource media type: {resource.get('mediaType')}")
        expected_hash = resource.get("hash")
        if not isinstance(expected_hash, str) or not expected_hash:
            raise MitarError("ProofScript resource hash must be a non-empty string")

        relative = Path(path_value)
        if relative.is_absolute():
            raise MitarError("ProofScript resource path must be relative")
        path = (self.project_root / relative).resolve()
        resource_root = (self.project_root / ".ProofScript").resolve()
        try:
            path.relative_to(resource_root)
        except ValueError:
            raise MitarError("ProofScript resource escapes the allowed resource root") from None
        return path, expected_hash

    def read_text(self, value, media_type: str | None = None) -> str:
        path, expected_hash = self.resource_path(value, media_type)
        key = (path, expected_hash)
        if key not in self.text_cache:
            try:
                self.text_cache[key] = path.read_text(encoding="utf-8")
            except (OSError, UnicodeError) as error:
                raise MitarError(f"Unable to read ProofScript resource {path}: {error}") from error
        return self.text_cache[key]

    def load_proof(self, value) -> LoadedProof:
        path, expected_hash = self.resource_path(value, PROOF_MEDIA_TYPE)
        key = (path, expected_hash)
        if key in self.proof_cache:
            return self.proof_cache[key]
        content = self.read_text(value, PROOF_MEDIA_TYPE)
        try:
            document = json.loads(content)
        except json.JSONDecodeError as error:
            raise MitarError(f"Invalid embedded proof JSON {path}: {error}") from error
        if not isinstance(document, dict):
            raise MitarError(f"Embedded proof JSON must be an object: {path}")
        version = document.get("schemaVersion")
        try:
            major = int(version.split(".", 1)[0])
        except (AttributeError, ValueError):
            raise MitarError(f"Invalid embedded proof schema version: {version}") from None
        if major != 0:
            raise MitarError(f"Unsupported embedded proof schema version: {version}")
        proof = document.get("proof")
        expressions = document.get("expressions", {})
        code = document.get("code")
        if not isinstance(code, str) or (proof is not None and not isinstance(proof, list)):
            raise MitarError(f"Embedded proof is missing code or has invalid proof records: {path}")
        resolver = ExpressionResolver(expressions) if version.startswith("0.3.") and proof is not None else None
        loaded = LoadedProof(path, version, code, proof, expressions, resolver)
        self.proof_cache[key] = loaded
        return loaded


def read_text_resource(value, project_root: Path, media_type: str | None = None) -> str:
    return ResourceLoader(project_root).read_text(value, media_type)
