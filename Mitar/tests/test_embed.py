import json
import tempfile
import unittest
from pathlib import Path

from Mitar.Rules import Initialize
from Mitar.engine import ProofEngine
from Mitar.schema import ExpressionResolver, ResourceLoader


class EmbedRendererTest(unittest.TestCase):
    def setUp(self):
        Initialize()
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)

    def tearDown(self):
        self.temp.cleanup()

    def resource(self, name, document):
        path = self.root / ".ProofScript" / "proofs" / f"{name}.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(document), encoding="utf-8")
        return {"$resource": {
            "path": f".ProofScript/proofs/{name}.json",
            "hash": name,
            "mediaType": "application/vnd.proofscript.proof+json",
            "encoding": "utf-8",
        }}

    def test_embedded_proof_uses_its_own_expression_table(self):
        child = self.resource("child", {
            "schemaVersion": "0.3.0",
            "code": "trivial",
            "expressions": {"e0": {"kind": "const", "name": "True", "isProp": True}},
            "proof": [{"_goal_": {"$ref": "e0"}}, {"_step_": "trivial"}],
        })
        parent_expressions = {"e0": {"kind": "const", "name": "False", "isProp": True}}
        parent = [
            {"_goal_": {"$ref": "e0"}},
            {"_step_": "embed", "theorem": "child", "proof": child, "args": [], "argKinds": []},
        ]
        rendered = ProofEngine(
            parent,
            project_root=self.root,
            expression_resolver=ExpressionResolver(parent_expressions),
            resource_loader=ResourceLoader(self.root),
        ).make("parent", "test", 1, "")
        self.assertIn("嵌入证明", rendered)
        self.assertIn("显然", rendered)
        self.assertNotIn("proof-mark error", rendered)

    def test_embedded_proof_loader_reuses_document_and_resolver(self):
        resource = self.resource("cached", {
            "schemaVersion": "0.3.0", "code": "trivial",
            "expressions": {"e0": {"kind": "const", "name": "True", "isProp": True}},
            "proof": [{"_goal_": {"$ref": "e0"}}, {"_step_": "trivial"}],
        })
        loader = ResourceLoader(self.root)
        first = loader.load_proof(resource)
        second = loader.load_proof(resource)
        self.assertIs(first, second)
        self.assertIs(first.resolver, second.resolver)

    def test_embedded_proof_cycle_is_reported(self):
        circular = self.resource("cycle", {
            "schemaVersion": "0.3.0",
            "code": "embed",
            "expressions": {"e0": {"kind": "const", "name": "True", "isProp": True}},
            "proof": [
                {"_goal_": {"$ref": "e0"}},
                {"_step_": "embed", "theorem": "cycle", "proof": {
                    "$resource": {
                        "path": ".ProofScript/proofs/cycle.json", "hash": "cycle",
                        "mediaType": "application/vnd.proofscript.proof+json", "encoding": "utf-8",
                    }
                }},
            ],
        })
        engine = ProofEngine(
            [{"_goal_": {}}, {"_step_": "embed", "theorem": "cycle", "proof": circular}],
            project_root=self.root,
            resource_loader=ResourceLoader(self.root),
        )
        rendered = engine.make("cycle", "test", 1, "")
        self.assertIn("proof-mark error", rendered)
        self.assertTrue(any("Cyclic embedded proof resource" in item["message"] for item in engine.diagnostics))


if __name__ == "__main__":
    unittest.main()
