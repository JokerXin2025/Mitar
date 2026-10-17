from __future__ import annotations

import tempfile
import re
import unittest
from pathlib import Path

from Lean2TeX import load
from Lean2TeX.macros import MacroRegistry, load_macros_toml
from Lean2TeX.model import Macro, MacroStyle


_HTML_DATA = re.compile(r"\\htmlData\{[^{}]+\}\{([^{}]*)\}")
_L2T_REF = re.compile(r"l2t-ref=([a-z0-9-]+)")


def without_html_data(tex):
    return _HTML_DATA.sub(r"\1", tex)


def const(name):
    return {"kind": "const", "name": name, "levels": [], "isProp": False}


def app(fn, arg):
    return {"kind": "app", "fn": fn, "arg": arg}


def apply(name, *args):
    node = const(name)
    for arg in args:
        node = app(node, arg)
    node["headConstant"] = name
    hidden = {
        "HAdd.hAdd": 4, "HSub.hSub": 4, "HMul.hMul": 4,
        "HDiv.hDiv": 4, "HPow.hPow": 4, "Eq": 1,
        "OfNat.ofNat": 1, "Nat.cast": 2, "Int.cast": 2,
    }.get(name, 0)
    node["arguments"] = [
        argument(arg, i >= hidden, False, "default" if i >= hidden else "implicit")
        for i, arg in enumerate(args)
    ]
    return node


def nat(value):
    return {"kind": "lit", "lit": {"kind": "literal.nat", "value": value}, "isProp": False}


def fvar(identifier, type_name="Nat"):
    return {"kind": "fvar", "name": identifier, "id": identifier, "type": const(type_name), "isProp": False}


def binary(name, lhs, rhs):
    typ = const("Nat")
    return apply(name, typ, typ, typ, const("instance"), lhs, rhs)


def enriched_app(name, descriptors):
    node = apply(name, *(descriptor["expr"] for descriptor in descriptors))
    node["headConstant"] = name
    node["arguments"] = descriptors
    return node


def argument(expr, explicit, typeclass=False, binder_info="default"):
    return {
        "expr": expr,
        "binderInfo": binder_info,
        "isExplicit": explicit,
        "isTypeclass": typeclass,
    }


class SemanticTest(unittest.TestCase):
    def setUp(self):
        self.renderer = load()
        self.renderer.reset()

    def test_application_projection_builds_semantic_children(self):
        node = binary("HAdd.hAdd", fvar("x"), nat(1))
        display = self.renderer.convert(node)
        self.assertEqual(display.macro_name, "HAdd.hAdd")
        self.assertEqual(display.metadata["rawArgumentCount"], 6)
        self.assertEqual(display.metadata["selectedArgumentIndices"], [4, 5])
        self.assertEqual([child.kind for child in display.children], ["fvar", "literal"])

    def test_exported_argument_metadata_drives_projection(self):
        descriptors = [
            argument(const("Nat"), False, binder_info="implicit"),
            argument(const("Nat"), False, binder_info="implicit"),
            argument(const("Nat"), False, binder_info="implicit"),
            argument(const("inst"), False, True, "instImplicit"),
            argument(fvar("x"), True),
            argument(nat(1), True),
        ]
        display = self.renderer.convert(enriched_app("HAdd.hAdd", descriptors))
        self.assertEqual(display.metadata["selectedArgumentIndices"], [4, 5])
        self.assertEqual([child.kind for child in display.children], ["fvar", "literal"])

    def test_unknown_argument_metadata_is_preserved_as_over_application(self):
        descriptors = [
            argument(const("Nat"), False, binder_info="implicit"),
            argument(const("Nat"), False, binder_info="implicit"),
            argument(const("Nat"), False, binder_info="implicit"),
            argument(const("inst"), False, True, "instImplicit"),
            argument(nat(1), True),
            argument(nat(2), True),
            argument(nat(3), None, binder_info=None),
        ]
        tex = without_html_data(self.renderer.render(enriched_app("HAdd.hAdd", descriptors)))
        self.assertEqual(tex.strip(), "$\\left(1+2\\right)\\left(3\\right)$")

    def test_binder_has_stable_reference(self):
        node = {
            "kind": "forall", "name": "x", "type": const("Nat"),
            "body": {"kind": "bvar", "index": 0}, "binderInfo": "default",
        }
        display = self.renderer.convert(node)
        bind_id = display.children[0].metadata["bindId"]
        self.assertEqual(bind_id, display.children[2].metadata["bindRef"])
        self.assertRegex(bind_id, r"^e\d+:b0$")
        again = self.renderer.convert(node)
        self.assertEqual(again.children[0].macro_name, "x")
        self.assertNotEqual(bind_id, again.children[0].metadata["bindId"])

    def test_interaction_identity_groups_exact_references(self):
        repeated = apply("Eq", const("Nat"), fvar("same"), fvar("same"))
        fvar_tex = self.renderer.render(repeated)
        fvar_refs = _L2T_REF.findall(fvar_tex)
        self.assertEqual(len(fvar_refs), 2)
        self.assertEqual(fvar_refs[0], fvar_refs[1])
        self.assertIn("l2t-kind=fvar", fvar_tex)

        binder = {
            "kind": "forall", "name": "x", "type": const("Nat"),
            "body": apply("Eq", const("Nat"), {"kind": "bvar", "index": 0}, {"kind": "bvar", "index": 0}),
            "binderInfo": "default",
        }
        binding_tex = self.renderer.render(binder)
        binding_refs = _L2T_REF.findall(binding_tex)
        self.assertEqual(len(binding_refs), 3)
        self.assertEqual(len(set(binding_refs)), 1)
        self.assertIn("l2t-kind=binder", binding_tex)
        self.assertEqual(binding_tex.count("l2t-kind=bvar"), 2)

        next_tex = self.renderer.render(binder)
        self.assertNotEqual(binding_refs[0], _L2T_REF.findall(next_tex)[0])

    def test_shadowed_binder_and_proof_variable_classification(self):
        nested = {
            "kind": "forall", "name": "x", "type": const("Nat"), "binderInfo": "default",
            "body": {"kind": "forall", "name": "x", "type": const("Nat"), "body": {"kind": "bvar", "index": 0}, "binderInfo": "default"},
        }
        display = self.renderer.convert(nested)
        self.assertEqual(display.children[0].macro_name, "x")
        self.assertEqual(display.children[2].children[0].macro_name, "x_1")

        proposition = {"kind": "fvar", "name": "P", "id": "P", "type": {"kind": "sort", "level": {"kind": "level.zero"}}}
        proof = {"kind": "fvar", "name": "h", "id": "h", "type": proposition}
        proof_display = self.renderer.convert(proof)
        self.assertEqual(proof_display.metadata["classification"], "proof")
        self.assertEqual(proof_display.macro_name, "h")

    def test_exported_is_prop_classifies_variables(self):
        prop_sort = {"kind": "sort", "level": {"kind": "level.zero"}, "isProp": False}
        proposition = {"kind": "fvar", "name": "P", "id": "P", "type": prop_sort, "isProp": True}
        proof = {"kind": "fvar", "name": "h", "id": "h", "type": proposition, "isProp": False}
        data = {"kind": "fvar", "name": "x", "id": "x", "type": {**const("Nat"), "isProp": False}, "isProp": False}
        self.assertEqual(self.renderer.convert(proposition).metadata["classification"], "proposition")
        self.assertEqual(self.renderer.convert(proof).metadata["classification"], "proof")
        self.assertEqual(self.renderer.convert(data).metadata["classification"], "data")

    def test_source_range_reaches_display_and_diagnostic(self):
        source_range = {"file": "/project/Example.lean", "start": 120, "stop": 131}
        unknown = {"kind": "future", "sourceRange": source_range, "isProp": False}
        display = self.renderer.convert(unknown)
        self.assertEqual(display.metadata["sourceRange"], source_range)
        self.assertEqual(self.renderer.diagnostics[0].source_range, source_range)
        self.assertEqual(self.renderer.diagnostics_dict()[0]["sourceRange"], source_range)

    def test_unbound_bvar_is_visible_and_diagnosed(self):
        tex = self.renderer.render({"kind": "bvar", "index": 3})
        self.assertIn("unknown", tex)
        self.assertIn("L2T003", {item.code for item in self.renderer.diagnostics})

    def test_unknown_application_is_readable(self):
        tex = self.renderer.render(apply("Example.foo", nat(1), nat(2)))
        self.assertEqual(tex.strip(), "$\\operatorname{foo}\\left(1,2\\right)$")
        self.assertIn("L2T009", {item.code for item in self.renderer.diagnostics})

    def test_configured_macro_preserves_over_application(self):
        descriptors = [
            argument(const("Nat"), False, binder_info="implicit"),
            argument(const("Nat"), False, binder_info="implicit"),
            argument(const("Nat"), False, binder_info="implicit"),
            argument(const("inst"), False, True, "instImplicit"),
            argument(nat(1), True), argument(nat(2), True), argument(nat(3), None, binder_info=None),
        ]
        tex = self.renderer.render(enriched_app("HAdd.hAdd", descriptors))
        self.assertEqual(tex.strip(), "$\\left(1+2\\right)\\left(3\\right)$")

    def test_compatibility_context_is_used(self):
        self.assertEqual(without_html_data(self.renderer.render({"kind": "bvar", "index": 0}, bvar_env=["x"])).strip(), "$x$")
        node = {"kind": "fvar", "name": "old", "id": "id", "type": const("Nat")}
        self.assertEqual(without_html_data(self.renderer.render(node, fvars={"id": "chosen"})).strip(), "$chosen$")

    def test_lambda_let_projection_and_metavariable_fallbacks(self):
        lam = {"kind": "lam", "name": "x", "type": const("Nat"), "body": {"kind": "bvar", "index": 0}, "binderInfo": "default"}
        self.assertIn("\\mapsto", self.renderer.render(lam))
        let = {"kind": "let", "name": "x", "type": const("Nat"), "value": nat(1), "body": {"kind": "bvar", "index": 0}, "nondep": False}
        self.assertIn("operatorname{let}", self.renderer.render(let))
        projection = {"kind": "proj", "structName": "Pair", "fieldName": "Pair.fst", "index": 0, "expr": fvar("p")}
        self.assertIn("operatorname{fst}", self.renderer.render(projection))
        self.assertEqual(self.renderer.render({"kind": "mvar", "id": "?m.1"}).strip(), "$\\square$")
        string = {"kind": "lit", "lit": {"kind": "literal.str", "value": "a_b"}}
        self.assertEqual(self.renderer.render(string), "a\\_b")

    def test_text_macro_nested_in_formula_has_no_nested_math_delimiters(self):
        prop = lambda name: {"kind": "fvar", "name": name, "id": name, "type": {"kind": "sort", "level": {"kind": "level.zero"}}}
        conjunction = apply("And", prop("P"), prop("Q"))
        equality = apply("Eq", const("Prop"), conjunction, prop("R"))
        tex = self.renderer.render(equality)
        self.assertEqual(tex.count("$"), 2)
        self.assertIn("P\\text{ 且 }Q", without_html_data(tex))

    def test_malformed_type_uses_fallback(self):
        node = {"kind": "fvar", "name": "x", "id": "x", "type": []}
        self.assertIn("Expr", self.renderer.convert(node).metadata["typeName"])

    def test_precedence_and_associativity(self):
        a, b, c = fvar("a"), fvar("b"), fvar("c")
        nested = binary("HMul.hMul", binary("HAdd.hAdd", a, b), c)
        self.assertIn("\\left(n+m\\right)\\cdot i", without_html_data(self.renderer.render(nested)))
        power = binary("HPow.hPow", binary("HPow.hPow", a, b), c)
        self.renderer.reset()
        self.assertIn("{\\left({n}^{m}\\right)}^{i}", without_html_data(self.renderer.render(power)))

    def test_calc_relation_public_api(self):
        self.assertEqual(self.renderer.render_relation(app(const("Eq"), const("Nat"))), "=")

    def test_invalid_macro_template_fails_at_load(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "macros.toml"
            path.write_text('''[[macro]]\nname = "Bad"\narguments = [0]\nstyles = [{ name = "formula", template = "#1", mode = "formula" }]\n''', encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "L2T004"):
                load_macros_toml(path)

    def test_alias_and_normalization(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "macros.toml"
            path.write_text('''[[alias]]\nname = "Alias.foo"\ntarget = "Nat"\n[[normalization]]\nname = "Wrapper.foo"\noperation = "select"\nargument = 0\n[[macro]]\nname = "Nat"\narguments = []\nstyles = [{ name = "formula", template = "N", mode = "formula" }]\n''', encoding="utf-8")
            registry = load_macros_toml(path)
            self.assertEqual(registry.resolve_alias("Alias.foo"), "Nat")
            self.assertEqual(registry.normalizations["Wrapper.foo"].operation, "select")

    def test_dynamic_macro_uses_all_children(self):
        registry = MacroRegistry({
            "Tuple": Macro("Tuple", "structure", (), (MacroStyle("formula", "formula", "\\left(#*\\right)", "custom", 100, "none", separator=", "),), True)
        })
        self.renderer.registry = registry
        self.renderer.converter.registry = registry
        self.renderer.layout.registry = registry
        tex = self.renderer.render(apply("Tuple", nat(1), nat(2), nat(3)))
        self.assertIn("1, 2, 3", without_html_data(tex))



if __name__ == "__main__":
    unittest.main()
