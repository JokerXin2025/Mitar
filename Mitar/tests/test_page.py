import json
import tempfile
import unittest
from pathlib import Path

from Mitar.clean import clean
from Mitar.engine import render_module_navigation
from Mitar.page import Page, PageRenderer, build_label_index, build_theorem_dependency_index, directory_modules, discover_pages
from Mitar.project import MitarError, resolve_target


class ProjectTest(unittest.TestCase):
    def test_source_card_css_keeps_existing_flip_back_components_styled(self):
        stylesheet = (Path(__file__).parents[2] / "css" / "code-flip.css").read_text(encoding="utf-8")

        self.assertIn(".proof-flip-back .code-header,", stylesheet)
        self.assertIn(".proof-source-card .code-header", stylesheet)
        self.assertIn(".proof-flip-back pre,", stylesheet)

    def test_resolve_project_and_module(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lakefile.toml").write_text('name = "Paper"', encoding = "utf-8")
            source = root / "Paper" / "Main.lean"
            source.parent.mkdir()
            source.write_text("import ProofScript", encoding = "utf-8")

            self.assertEqual(resolve_target(".", root).root, root.resolve())
            target = resolve_target("Paper.Main", root)
            self.assertEqual(target.module, "Paper.Main")
            self.assertEqual(target.source_file, source.resolve())

    def test_clean_removes_proof_script_and_build_output(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lakefile.toml").write_text('name = "Paper"', encoding = "utf-8")
            (root / ".ProofScript").mkdir()
            (root / ".Mitar" / "build").mkdir(parents = True)

            clean(False, root)

            self.assertFalse((root / ".ProofScript").exists())
            self.assertFalse((root / ".Mitar" / "build").exists())


class PageTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        (self.root / "lakefile.toml").write_text('name = "Paper"', encoding = "utf-8")
        self.source = self.root / "Paper" / "Main.lean"
        self.source.parent.mkdir()
        self.source.write_text("#export theorem main : True := by trivial", encoding = "utf-8")
        asset = self.root / "assets" / "diagram.svg"
        asset.parent.mkdir()
        asset.write_text('<svg xmlns="http://www.w3.org/2000/svg"><circle r="4"/></svg>', encoding = "utf-8")
        proof = self.root / ".ProofScript" / "proofs" / "Paper" / "Main" / "main.json"
        proof.parent.mkdir(parents = True)
        proof.write_text(json.dumps({
            "schemaVersion": "0.2.0",
            "code": "@theorem main : True := script\n  trivial",
            "proof": [{"_goal_": {}}, {"_step_": "trivial"}]
        }), encoding = "utf-8")
        page = {
            "schemaVersion": "0.2.0",
            "ProjectInfo": {
                "title": "Paper Project", "authors": ["Alice"], "abstract": "",
                "keywords": [], "journal": "Journal", "year": "2026", "url": "",
                "license": "", "arxivId": "", "doi": "", "note": "", "extra": []
            },
            "module": "Paper.Main",
            "source": str(self.source),
            "futureField": True,
            "components": [
                {
                    "source": {"file": str(self.source), "start": 0, "stop": 7},
                    "data": {"text": {"value": {
                        "source": "= Intro <intro>",
                        "blocks": [
                            {"heading": {"level": 1, "label": "intro", "content": [{"text": {"value": "Intro"}}]}},
                            {"paragraph": {"content": [{"reference": {"kind": "theorem", "label": "main"}}]}},
                            {"orderedList": {"start": 1, "items": [
                                {"ordinal": None, "content": [{"paragraph": {"content": [{"text": {"value": "First"}}]}}]},
                                {"ordinal": 5, "content": [{"paragraph": {"content": [{"text": {"value": "Fifth"}}]}}]},
                                {"ordinal": None, "content": [{"paragraph": {"content": [{"text": {"value": "Sixth"}}]}}]}
                            ]}}
                        ]
                    }}}
                },
                {
                    "source": {"file": str(self.source), "start": 0, "stop": 0},
                    "data": {"references": {"value": [{
                        "name": "Paper.Main.main",
                        "info": {
                            "project": {
                                "title": "Paper Project", "authors": ["Alice"], "abstract": "",
                                "keywords": [], "journal": "Journal", "year": "2026", "url": "",
                                "license": "", "arxivId": "", "doi": "", "note": "", "extra": []
                            },
                            "name": "Main Theorem", "label": "main", "tags": [], "extra": []
                        }
                    }]}}
                },
                {
                    "source": {"file": str(self.source), "start": 0, "stop": 7},
                    "data": {"theorem": {"value": {
                        "name": "Paper.Main.main",
                        "label": "main",
                        "proof": ".ProofScript/proofs/Paper/Main/main.json",
                        "sorryAx": False
                    }}}
                },
                {
                    "source": {"file": str(self.source), "start": 0, "stop": 0},
                    "data": {"latex": {"value": {
                        "metadata": {"title": "Equation", "label": "equation", "extra": []},
                        "language": "latex", "source": "x^2", "svg": "<svg><text>x²</text></svg>"
                    }}}
                },
                {
                    "source": {"file": str(self.source), "start": 0, "stop": 0},
                    "data": {"figure": {"value": {
                        "metadata": {"title": "Diagram", "label": "diagram", "extra": [["width", "wide"]]},
                        "path": "assets/diagram.svg", "extension": "svg"
                    }}}
                }
            ]
        }
        page_path = self.root / ".ProofScript" / "pages" / "Paper" / "Main.json"
        page_path.parent.mkdir(parents = True, exist_ok = True)
        page_path.write_text(json.dumps(page), encoding = "utf-8")

    def tearDown(self):
        self.temp.cleanup()

    def test_discover_and_render_page(self):
        pages = discover_pages(self.root)
        self.assertEqual([page.module for page in pages], ["Paper.Main"])
        build_root = self.root / ".Mitar" / "build"
        rendered = PageRenderer(self.root, build_root, build_label_index(pages), pages).render(pages[0])
        self.assertIn("Paper.Main.main", rendered)
        self.assertNotIn("Paper.Main.Paper.Main.main", rendered)
        self.assertIn('href="Main.html#theorem-main"', rendered)
        self.assertNotIn("<base ", rendered)
        self.assertIn('href="../assets/css/basic.css"', rendered)
        self.assertIn('class="module-sidebar"', rendered)
        self.assertIn('class="module-directory-scroll"', rendered)
        self.assertIn('class="module-path-prefix"', rendered)
        self.assertIn('class="module-home-button"', rendered)
        self.assertNotIn('class="module-sidebar-index"', rendered)
        self.assertIn('class="module-tree-parent"', rendered)
        self.assertIn('class="module-tree-node is-current"', rendered)
        self.assertIn('id="device-warning"', rendered)
        self.assertIn('class="proof-indent-slider"', rendered)
        self.assertIn('class="language-switcher"', rendered)
        self.assertEqual(rendered.count('class="language-switcher"'), 1)
        self.assertIn('data-language="en"', rendered)
        self.assertIn('<html lang="zh-CN"', rendered)
        self.assertIn('min="15" max="30" value="20"', rendered)
        self.assertIn('/js/proof-indent.js"', rendered)
        self.assertIn("Diagram", rendered)
        self.assertIn("Equation", rendered)
        self.assertIn('id="figure-equation"', rendered)
        self.assertIn('id="figure-diagram"', rendered)
        self.assertIn("data:image/svg+xml;base64,", rendered)
        self.assertIn('data-extra="[[&quot;width&quot;, &quot;wide&quot;]]"', rendered)
        self.assertNotIn("unsupported-component", rendered)
        self.assertIn("theorem", rendered)
        self.assertIn('<li value="5">', rendered)
        self.assertIn("Main Theorem", rendered)
        self.assertIn("Paper Project", rendered)
        self.assertIn("Main.lean:1", rendered)

    def test_module_navigation_renders_parent_siblings_and_current_subtree(self):
        modules = [
            "Root.Parent",
            "Root.Parent.Current",
            "Root.Parent.Current.Child",
            "Root.Parent.Sibling",
            "Root.Other.Hidden",
        ]
        pages = [
            Page(Path(), {}, module, Path(), [])
            for module in modules
        ]

        rendered = render_module_navigation(
            pages,
            Path("Root/Parent/Current.html"),
            "Root.Parent.Current",
            "../../../index.html",
        )

        self.assertNotIn('class="module-absolute-path"', rendered)
        self.assertIn('href="../Parent.html"', rendered)
        self.assertIn('href="Current.html" aria-current="page"', rendered)
        self.assertIn('href="Sibling.html"', rendered)
        self.assertIn('href="Current/Child.html"', rendered)
        self.assertNotIn("Current.Child.", rendered)
        self.assertNotIn("Hidden", rendered)

    def test_module_navigation_shows_only_the_hidden_path_prefix(self):
        page = Page(Path(), {"title": "Project"}, "A.B.C.D.E.F", Path(), [])

        rendered = render_module_navigation(
            [page], Path("A/B/C/D/E/F.html"), page.module, "../../../../../../index.html"
        )

        self.assertIn('<div class="module-path-prefix" aria-hidden="true">A/B/C/D/</div>', rendered)
        self.assertIn('class="module-home-button"', rendered)
        self.assertIn('class="codicon codicon-home"', rendered)
        self.assertNotIn("<svg", rendered)
        self.assertNotIn("当前位置", rendered)

    def test_virtual_directories_are_links_and_render_descendant_indexes(self):
        pages = [
            Page(Path(), {"title": "Project"}, module, Path(), [])
            for module in ("Root.Parent.First", "Root.Parent.Nested.Second")
        ]
        build_root = self.root / ".Mitar" / "build"
        renderer = PageRenderer(self.root, build_root, {}, pages)

        navigation = render_module_navigation(
            pages, Path("Root/Parent/First.html"), "Root.Parent.First", "../../index.html"
        )
        directory = renderer.render_directory("Root.Parent")

        self.assertEqual(directory_modules(pages), ["Root", "Root.Parent", "Root.Parent.Nested"])
        self.assertIn('href="../Parent.html"', navigation)
        self.assertIn('href="Parent/Nested.html"', directory)
        root_index = renderer.render_directory("Root")
        self.assertIn('href="Root/Parent/First.html"', root_index)
        self.assertIn('class="module-index-tree"', root_index)
        self.assertIn('<ul><li>', root_index)
        self.assertIn("First", directory)
        self.assertIn("Second", directory)

    def test_top_level_module_uses_project_index(self):
        root = Page(Path(), {"title": "Project"}, "Root", Path(), [])
        child = Page(Path(), {"title": "Project"}, "Root.Child", Path(), [])

        self.assertEqual(root.output_path, Path("index.html"))
        rendered = render_module_navigation(
            [root, child], Path("index.html"), "Root", "index.html"
        )

        self.assertIn('href="index.html" aria-current="page"', rendered)
        self.assertIn('href="Root/Child.html"', rendered)
        self.assertIn('class="module-home-button" href="index.html"', rendered)

    def test_existing_module_components_precede_descendant_index(self):
        parent = Page(Path(), {}, "Root.Parent", Path(), [
            {"data": {"future": {"value": {"metadata": {"title": "Parent content"}}}}}
        ])
        child = Page(Path(), {}, "Root.Parent.Child", Path(), [])
        renderer = PageRenderer(self.root, self.root / ".Mitar" / "build", {}, [parent, child])

        rendered = renderer.render(parent)

        main = rendered.split('<main id="main-content"', 1)[1]
        self.assertLess(main.index("Parent content"), main.index('href="Parent/Child.html"'))

    def test_reject_unsupported_major_version(self):
        page_path = self.root / ".ProofScript" / "pages" / "Paper" / "Main.json"
        data = json.loads(page_path.read_text(encoding = "utf-8"))
        data["schemaVersion"] = "1.0.0"
        page_path.write_text(json.dumps(data), encoding = "utf-8")
        with self.assertRaises(MitarError):
            discover_pages(self.root)

    def test_sorry_axiom_uses_warning_state(self):
        page_path = self.root / ".ProofScript" / "pages" / "Paper" / "Main.json"
        data = json.loads(page_path.read_text(encoding = "utf-8"))
        data["components"][2]["data"]["theorem"]["value"]["sorryAx"] = True
        page_path.write_text(json.dumps(data), encoding = "utf-8")

        pages = discover_pages(self.root)
        rendered = PageRenderer(
            self.root, self.root / ".Mitar" / "build", build_label_index(pages)
        ).render(pages[0])

        self.assertIn("proof-mark sorry", rendered)
        self.assertNotIn("proof-mark error", rendered)

    def test_invalid_proof_structure_overrides_sorry_warning(self):
        page_path = self.root / ".ProofScript" / "pages" / "Paper" / "Main.json"
        data = json.loads(page_path.read_text(encoding = "utf-8"))
        data["components"][2]["data"]["theorem"]["value"]["sorryAx"] = True
        page_path.write_text(json.dumps(data), encoding = "utf-8")
        proof_path = self.root / ".ProofScript" / "proofs" / "Paper" / "Main" / "main.json"
        proof = json.loads(proof_path.read_text(encoding = "utf-8"))
        proof["proof"] = [{"_step_": "trivial"}]
        proof_path.write_text(json.dumps(proof), encoding = "utf-8")

        pages = discover_pages(self.root)
        rendered = PageRenderer(
            self.root, self.root / ".Mitar" / "build", build_label_index(pages)
        ).render(pages[0])

        self.assertIn("proof-mark error", rendered)
        self.assertIn("未知策略", rendered)

    def test_unknown_tactic_renders_red_step_without_error_state(self):
        proof_path = self.root / ".ProofScript" / "proofs" / "Paper" / "Main" / "main.json"
        proof = json.loads(proof_path.read_text(encoding = "utf-8"))
        proof["proof"] = [{"_goal_": {}}, {"_step_": "future_tactic"}]
        proof_path.write_text(json.dumps(proof), encoding = "utf-8")

        pages = discover_pages(self.root)
        rendered = PageRenderer(
            self.root, self.root / ".Mitar" / "build", build_label_index(pages)
        ).render(pages[0])

        self.assertIn("proof-mark pass", rendered)
        self.assertIn('step-block unknown', rendered)
        self.assertIn("未知策略", rendered)

    def test_schema_0_3_expression_references_render(self):
        proof_path = self.root / ".ProofScript" / "proofs" / "Paper" / "Main" / "main.json"
        proof_path.write_text(json.dumps({
            "schemaVersion": "0.3.0",
            "code": "@theorem main : True := script\n  trivial",
            "expressions": {
                "e0": {"kind": "const", "name": "True", "levels": [], "isProp": True},
            },
            "proof": [{"_goal_": {"$ref": "e0"}}, {"_step_": "trivial"}],
        }), encoding="utf-8")
        page_path = self.root / ".ProofScript" / "pages" / "Paper" / "Main.json"
        data = json.loads(page_path.read_text(encoding="utf-8"))
        data["schemaVersion"] = "0.3.0"
        page_path.write_text(json.dumps(data), encoding="utf-8")

        pages = discover_pages(self.root)
        rendered = PageRenderer(
            self.root, self.root / ".Mitar" / "build", build_label_index(pages), pages
        ).render(pages[0])

        self.assertIn("proof-mark pass", rendered)
        self.assertNotIn("proof-mark error", rendered)

    def test_unknown_component_preserves_complete_value(self):
        page = Page(Path(), {}, "Paper.Custom", Path(), [{
            "data": {"future": {"value": {"metadata": {"title": "Future"}, "payload": "<raw>"}}}
        }])
        rendered = PageRenderer(
            self.root, self.root / ".Mitar" / "build", {}, [page]
        ).render(page)
        self.assertIn('data-component="future"', rendered)
        self.assertIn('&quot;payload&quot;: &quot;&lt;raw&gt;&quot;', rendered)

    def test_computation_component_uses_project_root_for_nested_resources(self):
        page = Page(Path(), {}, "Paper.Nested.Compute", Path(), [{
            "data": {"computation": {"value": {
                "schemaVersion": "1.2.0", "metadata": {"title": "Compute", "label": None, "extra": []},
                "renderer": "proofscript/test-v1", "function": {}, "execution": {
                    "backend": "wasm", "status": "pending", "abi": "proofscript-json-v1",
                    "bundleId": "Paper", "entry": "run", "wrapper": "wrapper", "manifest": "pending.json",
                }, "payload": {},
            }}}
        }])
        rendered = PageRenderer(self.root, self.root / ".Mitar/build", {}, [page]).render(page)
        self.assertIn('data-computation data-renderer="proofscript/test-v1"', rendered)
        self.assertNotIn("unsupported-component", rendered)
        self.assertIn('data-project-base-url="../../"', rendered)
        self.assertIn("/js/computation.js", rendered)

    def test_lemma_and_code_only_declaration_modes(self):
        proof_path = self.root / ".ProofScript" / "proofs" / "Paper" / "lemma.json"
        proof_path.parent.mkdir(parents=True, exist_ok=True)
        proof_path.write_text(json.dumps({
            "schemaVersion": "0.3.0",
            "code": "@lemma support : True := by\n  exact True.intro",
        }), encoding="utf-8")
        lemma = Page(Path(), {}, "Paper.Main", self.source, [{
            "data": {"lemma": {"value": {
                "name": "Supporting lemma", "label": "supporting-lemma",
                "proof": ".ProofScript/proofs/Paper/lemma.json", "sorryAx": False,
            }}}
        }])
        renderer = PageRenderer(
            self.root, self.root / ".Mitar" / "build", {}, [lemma]
        )

        rendered = renderer.render(lemma)

        self.assertIn("theorem-code-only", rendered)
        self.assertIn('class="proof-source-card"', rendered)
        self.assertIn("class=\"page-code code-highlighted\"", rendered)
        code_only = rendered.split("theorem-code-only", 1)[1].split("</section>", 1)[0]
        self.assertNotIn("class=\"flip-btn", code_only)
        self.assertEqual(renderer._theorem_navigation(lemma, lemma.output_path), "")

    def test_lemma_is_dependency_but_not_a_current_navigation_panel(self):
        lemma_path = self.root / ".ProofScript" / "proofs" / "Paper" / "Main" / "support.json"
        theorem_path = self.root / ".ProofScript" / "proofs" / "Paper" / "Main" / "result.json"
        lemma_path.parent.mkdir(parents=True, exist_ok=True)
        lemma_path.write_text(json.dumps({
                    "schemaVersion": "0.3.0", "code": "@lemma support : True := by\n  trivial",
        }), encoding="utf-8")
        theorem_path.write_text(json.dumps({
            "schemaVersion": "0.3.0",
            "code": "@theorem result : True := by\n  exact support",
        }), encoding="utf-8")
        lemma = Page(Path(), {}, "Paper.Main", self.source, [{
            "data": {"lemma": {"value": {
                "name": "Supporting lemma", "label": "support",
                "proof": ".ProofScript/proofs/Paper/Main/support.json", "sorryAx": False,
            }}}
        }])
        theorem = Page(Path(), {}, "Paper.Main", self.source, [{
            "data": {"theorem": {"value": {
                "name": "Main theorem", "label": "result",
                "proof": ".ProofScript/proofs/Paper/Main/result.json", "sorryAx": False,
            }}}
        }])
        graph = build_theorem_dependency_index([lemma, theorem], self.root)
        renderer = PageRenderer(
            self.root, self.root / ".Mitar" / "build", {}, [lemma, theorem],
            theorem_dependencies=graph,
        )

        self.assertEqual(graph["Paper.Main.result"]["dependencies"], ("Paper.Main.support",))
        self.assertEqual(renderer._theorem_navigation(lemma, lemma.output_path), "")
        self.assertIn("Supporting lemma", renderer._theorem_navigation(theorem, theorem.output_path))

    def test_theorem_dependency_navigation_renders_direct_and_reverse_edges(self):
        base_proof = self.root / ".ProofScript" / "proofs" / "Paper" / "Base" / "base.json"
        use_proof = self.root / ".ProofScript" / "proofs" / "Paper" / "Use" / "use.json"
        base_proof.parent.mkdir(parents=True, exist_ok=True)
        use_proof.parent.mkdir(parents=True, exist_ok=True)
        base_proof.write_text(json.dumps({
            "schemaVersion": "0.3.0", "code": "trivial", "expressions": {},
            "proof": [{"_goal_": {}}, {"_step_": "trivial"}],
        }), encoding="utf-8")
        use_proof.write_text(json.dumps({
            "schemaVersion": "0.3.0", "code": "apply_thm", "expressions": {
                "e0": {"kind": "const", "name": "Paper.Base.base", "isProp": False},
            },
            "proof": [{"_goal_": {}}, {"_step_": "apply_thm", "thm": {"$ref": "e0"}}],
        }), encoding="utf-8")
        base = Page(Path(), {}, "Paper.Base", Path(), [{"data": {"theorem": {"value": {
            "name": "Base", "label": "base", "proof": ".ProofScript/proofs/Paper/Base/base.json", "sorryAx": False,
        }}}}])
        use = Page(Path(), {}, "Paper.Use", Path(), [{"data": {"theorem": {"value": {
            "name": "Use", "label": "use", "proof": ".ProofScript/proofs/Paper/Use/use.json", "sorryAx": False,
        }}}}])
        graph = build_theorem_dependency_index([base, use], self.root)
        renderer = PageRenderer(
            self.root, self.root / ".Mitar" / "build", {}, [base, use],
            theorem_dependencies=graph,
        )
        rendered = renderer._theorem_navigation(use, use.output_path)

        self.assertEqual(graph["Paper.Use.use"]["dependencies"], ("Paper.Base.base",))
        self.assertEqual(graph["Paper.Base.base"]["dependents"], ("Paper.Use.use",))
        self.assertIn('data-theorem-anchor="theorem-use"', rendered)
        self.assertIn('href="Base.html#theorem-base"', rendered)
        self.assertIn("theorem-dependency-navigation", rendered)
        self.assertIn("theorem-dependency-level incoming", rendered)
        self.assertIn("theorem-dependency-current", rendered)
        self.assertNotIn("theorem-dependency-group", rendered)


if __name__ == "__main__":
    unittest.main()
