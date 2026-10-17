import tempfile
import unittest
from pathlib import Path

from Mitar.project import MitarError
from Mitar.schema import ExpressionResolver, ResourceLoader, read_text_resource, resolve_expressions


class SchemaTest(unittest.TestCase):
    def test_resolves_expression_dag(self):
        expressions = {
            "e0": {"kind": "fvar", "name": "P", "isProp": True, "type": {"$ref": "e1"}},
            "e1": {"kind": "sort", "isProp": False},
        }

        resolved = resolve_expressions({"_goal_": {"$ref": "e0"}}, expressions)

        self.assertEqual(resolved["_goal_"]["name"], "P")
        self.assertEqual(resolved["_goal_"]["type"]["kind"], "sort")

    def test_rejects_unknown_and_cyclic_expression_refs(self):
        with self.assertRaises(MitarError):
            resolve_expressions({"$ref": "missing"}, {})
        with self.assertRaises(MitarError):
            ExpressionResolver({
                "e0": {"kind": "mdata", "isProp": False, "expr": {"$ref": "e1"}},
                "e1": {"kind": "mdata", "isProp": False, "expr": {"$ref": "e0"}},
            })

    def test_rejects_invalid_expression_ids_and_reference_shell_nodes(self):
        with self.assertRaises(MitarError):
            ExpressionResolver({"bad": {"kind": "sort", "isProp": False}})
        with self.assertRaises(MitarError):
            ExpressionResolver({"e0": {"$ref": "e1"}, "e1": {"kind": "sort", "isProp": False}})

    def test_expression_resolver_reuses_shared_nodes(self):
        resolver = ExpressionResolver({
            "e0": {"kind": "sort", "isProp": False},
        })
        resolved = resolver.resolve([{"$ref": "e0"}, {"$ref": "e0"}])
        self.assertIs(resolved[0], resolved[1])

    def test_reads_project_relative_resource(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            resource = root / ".ProofScript" / "resources" / "svg" / "123.svg"
            resource.parent.mkdir(parents=True)
            resource.write_text("<svg/>", encoding="utf-8")
            value = {"$resource": {
                "path": ".ProofScript/resources/svg/123.svg",
                "hash": "123",
                "mediaType": "image/svg+xml",
                "encoding": "utf-8",
            }}

            self.assertEqual(read_text_resource(value, root, "image/svg+xml"), "<svg/>")

    def test_rejects_resource_escape(self):
        with tempfile.TemporaryDirectory() as directory:
            value = {"$resource": {
                "path": "../outside.svg", "hash": "outside",
                "mediaType": "image/svg+xml", "encoding": "utf-8",
            }}
            with self.assertRaises(MitarError):
                read_text_resource(value, Path(directory), "image/svg+xml")

    def test_rejects_project_file_outside_proof_script_resource_root(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "secret.txt").write_text("secret", encoding="utf-8")
            value = {"$resource": {
                "path": "secret.txt", "hash": "secret",
                "mediaType": "image/svg+xml", "encoding": "utf-8",
            }}
            with self.assertRaises(MitarError):
                read_text_resource(value, root, "image/svg+xml")

    def test_resource_path_may_differ_from_content_hash(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            resource = root / ".ProofScript" / "resources" / "svg" / "456.svg"
            resource.parent.mkdir(parents=True)
            resource.write_text("<svg/>", encoding="utf-8")
            value = {"$resource": {
                "path": ".ProofScript/resources/svg/456.svg", "hash": "123",
                "mediaType": "image/svg+xml", "encoding": "utf-8",
            }}
            self.assertEqual(read_text_resource(value, root, "image/svg+xml"), "<svg/>")

    def test_resource_loader_caches_text(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            resource = root / ".ProofScript" / "resources" / "svg" / "123.svg"
            resource.parent.mkdir(parents=True)
            resource.write_text("first", encoding="utf-8")
            value = {"$resource": {
                "path": ".ProofScript/resources/svg/123.svg", "hash": "123",
                "mediaType": "image/svg+xml", "encoding": "utf-8",
            }}
            loader = ResourceLoader(root)
            self.assertEqual(loader.read_text(value, "image/svg+xml"), "first")
            resource.write_text("second", encoding="utf-8")
            self.assertEqual(loader.read_text(value, "image/svg+xml"), "first")


if __name__ == "__main__":
    unittest.main()
