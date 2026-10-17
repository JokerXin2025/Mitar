import json
import os
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from Mitar.Rules.computation import render_computation
from Mitar.make import (
    _build_computations,
    _compile_module_page,
    _compile_missing_pages,
    make,
    _page_computation_modules,
    _pending_computation_modules,
    _publish_computation_resources,
    _publish_runtime_assets,
    _recompile_computation_modules,
)


def resource(path, hash_value="a" * 64, encoding="binary"):
    return {"$resource": {
        "path": path, "hash": hash_value, "mediaType": "application/wasm",
        "encoding": encoding, "byteSize": 1,
    }}


class ComputationTest(unittest.TestCase):
    def test_non_cached_make_clears_all_proof_script_output(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / ".ProofScript/pages/Old.json").parent.mkdir(parents=True)
            (root / ".ProofScript/pages/Old.json").write_text("stale", encoding="utf-8")
            (root / "lakefile.toml").write_text('name = "Paper"', encoding="utf-8")

            with patch("Mitar.make.Initialize"), \
                 patch("Mitar.make.resolve_target", return_value=SimpleNamespace(root=root, module=None)), \
                 patch("Mitar.make.project_language", return_value="zh"), \
                 patch("Mitar.make._run_lake"), \
                 patch("Mitar.make._compile_missing_pages"), \
                 patch("Mitar.make._page_computation_modules", return_value={}), \
                 patch("Mitar.make._pending_computation_modules", return_value={}), \
                 patch("Mitar.make._recompile_computation_modules"), \
                 patch("Mitar.make._build_computations"), \
                 patch("Mitar.make.discover_pages", return_value=[]), \
                 patch("Mitar.make._publish_runtime_assets"), \
                 patch("Mitar.make._publish_computation_resources"):
                make(".")

            self.assertFalse((root / ".ProofScript").exists())

    def value(self, status="ready"):
        execution = {
            "backend": "wasm", "status": status, "abi": "proofscript-json-v1",
            "bundleId": "Paper.Main", "entry": "double", "wrapper": "wrapper",
            "manifest": resource(".ProofScript/resources/computation/hash/bundle.json", encoding="utf-8") if status == "ready" else "pending.json",
        }
        if status == "ready":
            execution.update({
            "module": resource(".ProofScript/resources/computation/hash/bundle.mjs", encoding="utf-8"),
            "wasm": resource(".ProofScript/resources/computation/hash/bundle.wasm"),
            })
        return {
            "schemaVersion": "1.2.0", "metadata": {"title": "Typed <compute>", "label": "typed", "extra": []},
            "renderer": "proofscript/test-json-v1", "function": {"declaration": "double", "type": "Request -> Response"},
            "execution": execution, "payload": {"fallback": "Static <fallback>"},
        }

    def test_ready_component_is_serialized_without_executable_payload(self):
        rendered = render_computation(self.value())
        self.assertIn('data-status="ready"', rendered)
        self.assertIn('data-renderer="proofscript/test-json-v1"', rendered)
        self.assertIn("Static &lt;fallback&gt;", rendered)
        self.assertIn('type="application/json"', rendered)
        document = rendered.split('data-computation-value>', 1)[1].split("</script>", 1)[0]
        parsed = json.loads(document)
        self.assertEqual(parsed["execution"]["entry"], "double")
        self.assertEqual(parsed["payload"]["fallback"], "Static <fallback>")

    def test_pending_component_explains_that_resources_are_not_ready(self):
        rendered = render_computation(self.value("pending"))
        self.assertIn("计算资源尚未完成构建", rendered)
        self.assertIn('data-status="pending"', rendered)

    def test_runtime_does_not_leave_pending_components_in_loading_state(self):
        source = (Path(__file__).resolve().parents[2] / "js/computation.js").read_text(encoding="utf-8")
        self.assertIn('execution.status === "pending"', source)
        self.assertIn('status.textContent = "Computation resources pending"', source)

    def test_pipeline_runs_build_then_finalize_for_pending_manifests(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            pending = root / ".ProofScript/computations/pending/entry.json"
            pending.parent.mkdir(parents=True)
            pending.write_text("{}", encoding="utf-8")
            scripts = root / "ProofScript/scripts"
            scripts.mkdir(parents=True)
            (scripts / "build-computations.mjs").write_text("", encoding="utf-8")
            with patch("Mitar.make._proof_script_root", return_value=scripts.parent), patch("Mitar.make._run_lake") as run:
                _build_computations(root)
            self.assertEqual([Path(call.args[0][1]).name for call in run.call_args_list], ["build-computations.mjs", "finalize-computations.mjs"])

    def test_computation_build_discovers_conventional_lean_wasm_runtime(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            pending = root / ".ProofScript/computations/pending/entry.json"
            pending.parent.mkdir(parents=True)
            pending.write_text("{}", encoding="utf-8")
            scripts = root / "ProofScript/scripts"
            scripts.mkdir(parents=True)
            (scripts / "build-computations.mjs").write_text("", encoding="utf-8")
            (scripts / "finalize-computations.mjs").write_text("", encoding="utf-8")
            with tempfile.TemporaryDirectory() as home:
                runtime = Path(home) / "Developer/lean4-wasm-4.32.0/build/proof-script-emscripten/lib/lean"
                runtime.mkdir(parents=True)
                (runtime / "libleanrt.a").write_bytes(b"")
                with patch("Mitar.make._proof_script_root", return_value=scripts.parent), patch("Mitar.make._run_lake") as run, patch.dict("os.environ", {"HOME": home}, clear=True):
                    _build_computations(root)
                    self.assertEqual(os.environ.get("PROOF_SCRIPT_LEAN_WASM_PREFIX"), str(runtime.parent.parent))
                self.assertEqual([Path(call.args[0][1]).name for call in run.call_args_list], ["build-computations.mjs", "finalize-computations.mjs"])

    def test_computation_build_removes_stale_bundles_before_finalize(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            pending = root / ".ProofScript/computations/pending/entry.json"
            pending.parent.mkdir(parents=True)
            pending.write_text(json.dumps({"bundleId": "Current.Bundle", "entry": "run"}), encoding="utf-8")
            stale = root / ".ProofScript/computations/bundles/Stale.Bundle"
            stale.mkdir(parents=True)
            scripts = root / "ProofScript/scripts"
            scripts.mkdir(parents=True)
            (scripts / "build-computations.mjs").write_text("", encoding="utf-8")
            (scripts / "finalize-computations.mjs").write_text("", encoding="utf-8")
            with patch("Mitar.make._proof_script_root", return_value=scripts.parent), patch("Mitar.make._run_lake"):
                _build_computations(root)
            self.assertFalse(stale.exists())

    def test_missing_page_pass_skips_libraries_and_cached_pages(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            page = root / "Paper/Page.lean"
            cached = root / "Paper/Cached.lean"
            library = root / "Paper/Library.lean"
            page.parent.mkdir(parents=True)
            page.write_text("page_end", encoding="utf-8")
            cached.write_text("page_end", encoding="utf-8")
            library.write_text("def value := 1", encoding="utf-8")
            cached_json = root / ".ProofScript/pages/Paper/Cached.json"
            cached_json.parent.mkdir(parents=True)
            cached_json.write_text("{}", encoding="utf-8")
            with patch("Mitar.make._compile_source") as compile_source:
                _compile_missing_pages(root)
            self.assertEqual(compile_source.call_args_list[0].args, (root, page))
            self.assertEqual(compile_source.call_count, 1)

    def test_missing_page_pass_recognizes_bare_page_end(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "Paper/Page.lean"
            source.parent.mkdir(parents=True)
            source.write_text("@text r#\"page\"#\npage_end", encoding="utf-8")

            with patch("Mitar.make._compile_source") as compile_source:
                _compile_missing_pages(root)

            compile_source.assert_called_once_with(root, source)

    def test_missing_page_pass_does_not_recognize_prefixed_page_end(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "Paper/Page.lean"
            source.parent.mkdir(parents=True)
            source.write_text("#page_end", encoding="utf-8")

            with patch("Mitar.make._compile_source") as compile_source:
                _compile_missing_pages(root)

            compile_source.assert_not_called()

    def test_single_module_build_forces_page_export_after_lake_build(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "Paper/Main.lean"
            page = root / ".ProofScript/pages/Paper/Main.json"
            pending = root / ".ProofScript/computations/pending/Paper/Main/entry.json"
            source.parent.mkdir(parents=True)
            source.write_text("#page_end", encoding="utf-8")
            page.parent.mkdir(parents=True)
            page.write_text("stale", encoding="utf-8")
            pending.parent.mkdir(parents=True)
            pending.write_text("stale", encoding="utf-8")
            target = SimpleNamespace(
                root=root,
                module="Paper.Main",
                source_file=source,
                page_file=page,
            )

            with patch("Mitar.make._run_lake") as run_lake, patch("Mitar.make._compile_source") as compile_source:
                _compile_module_page(target)

            self.assertFalse(page.exists())
            self.assertFalse(pending.exists())
            run_lake.assert_called_once_with(["lake", "build", "Paper.Main"], root)
            compile_source.assert_called_once_with(root, source)

    def test_only_pending_computation_modules_are_recompiled(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "Paper/Compute.lean"
            source.parent.mkdir(parents=True)
            source.write_text("#computation\n#page_end", encoding="utf-8")
            manifest = root / ".ProofScript/computations/pending/Paper/Compute/entry.json"
            manifest.parent.mkdir(parents=True)
            manifest.write_text(json.dumps({
                "module": "Paper.Compute",
                "source": {"file": "Paper/Compute.lean"},
            }), encoding="utf-8")
            page = root / ".ProofScript/pages/Paper/Compute.json"
            page.parent.mkdir(parents=True)
            page.write_text("{}", encoding="utf-8")
            self.assertEqual(_pending_computation_modules(root), {"Paper.Compute": source.resolve()})
            with patch("Mitar.make._compile_source") as compile_source:
                _recompile_computation_modules(root)
            compile_source.assert_called_once_with(root, source.resolve())
            self.assertFalse(page.exists())

    def test_finalized_page_identifies_cached_computation_module(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "Paper/Compute.lean"
            source.parent.mkdir(parents=True)
            source.write_text("#page_end", encoding="utf-8")
            page = root / ".ProofScript/pages/Paper/Compute.json"
            page.parent.mkdir(parents=True)
            page.write_text(json.dumps({
                "module": "Paper.Compute",
                "source": "Paper/Compute.lean",
                "components": [{"data": {"computation": {"value": {}}}}],
            }), encoding="utf-8")
            self.assertEqual(_page_computation_modules(root), {"Paper.Compute": source.resolve()})

    def test_recompile_pass_can_target_only_cached_computation_pages(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            cached = root / "Paper/Cached.lean"
            rebuilt = root / "Paper/Rebuilt.lean"
            cached.parent.mkdir(parents=True)
            cached.write_text("#page_end", encoding="utf-8")
            rebuilt.write_text("#page_end", encoding="utf-8")
            page_modules = {
                "Paper.Cached": cached.resolve(),
                "Paper.Rebuilt": rebuilt.resolve(),
            }
            pending_modules = {"Paper.Rebuilt": rebuilt.resolve()}
            targets = {
                module: source for module, source in page_modules.items()
                if module not in pending_modules
            }
            with patch("Mitar.make._compile_source") as compile_source:
                _recompile_computation_modules(root, targets)
            compile_source.assert_called_once_with(root, cached.resolve())

    def test_publish_copies_only_deployable_computation_resources(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / ".ProofScript/resources/computation/hash/bundle.wasm"
            source.parent.mkdir(parents=True)
            source.write_bytes(b"x")
            build = root / ".Mitar/build"
            _publish_computation_resources(root, build)
            self.assertEqual((build / ".ProofScript/resources/computation/hash/bundle.wasm").read_bytes(), b"x")

    def test_publish_runtime_assets_makes_computation_scripts_http_accessible(self):
        with tempfile.TemporaryDirectory() as directory:
            build = Path(directory) / "build"
            _publish_runtime_assets(build)
            self.assertTrue((build / "assets/js/computation.js").is_file())
            self.assertTrue((build / "assets/js/fibonacci-computation.js").is_file())
            self.assertTrue((build / "assets/js/e8-root-walk.js").is_file())
            self.assertTrue((build / "assets/js/formula-instance-computation.js").is_file())
            self.assertTrue((build / "assets/css/computation.css").is_file())
            self.assertIn("proofscript/e8-root-explorer-v2", (build / "assets/js/e8-computation.js").read_text(encoding="utf-8"))

    def test_fibonacci_renderer_keeps_slider_enabled_and_coalesces_input(self):
        source = (Path(__file__).resolve().parents[2] / "js/fibonacci-computation.js").read_text(encoding="utf-8")
        self.assertNotIn("input.disabled", source)
        self.assertIn("if (!computing) void runLatest()", source)
        self.assertIn("if (n !== requestedN) continue", source)
        self.assertIn("new ResizeObserver(fitValue)", source)
        self.assertIn("maximum * available / required", source)

    def test_e8_renderer_uses_protocol_values_and_validates_radius(self):
        source = (Path(__file__).resolve().parents[2] / "js/e8-computation.js").read_text(encoding="utf-8")
        self.assertIn('proofscript/e8-root-explorer-v2', source)
        self.assertIn('response["radiusAdmissible?"]', source)
        self.assertIn('response.integralCount', source)
        self.assertIn('response.roots', source)
        self.assertIn('coordinates: { x: Number(xSelect.value), y: Number(ySelect.value) }', source)
        self.assertIn('[data-e8-projection]', source)
        self.assertIn('new ResizeObserver', source)
        self.assertIn('data-e8-canvas', source)
        self.assertIn('function redraw()', source)
        self.assertIn('setHover(nearest)', source)
        self.assertIn('familySelect.addEventListener("change", run)', source)
        self.assertIn('addMathText(density', source)
        self.assertIn('\\\\frac{\\\\sqrt{2}}{2}', source)
        self.assertNotIn('data-e8-run', source)
        self.assertNotIn('Click a root to inspect it', source)
        self.assertIn('Draw families in separate passes', source)
        self.assertIn('halfIntegral") { context.moveTo', source)
        self.assertIn('−v  ·  Antipodal root', source)
        self.assertIn('class="e8-axis-control"', source)
        self.assertIn('Unknown computation renderer', (Path(__file__).resolve().parents[2] / "js/computation.js").read_text(encoding="utf-8"))
        self.assertIn("Radius must be a non-negative rational number", source)
        self.assertNotIn("112", source)
        self.assertNotIn("128", source)
        self.assertNotIn("240", source)

    def test_e8_root_walk_renderer_uses_live_compute_protocol(self):
        source = (Path(__file__).resolve().parents[2] / "js/e8-root-walk.js").read_text(encoding="utf-8")
        self.assertIn('proofscript/e8-root-walk-v1', source)
        self.assertIn('compute(input())', source)
        self.assertIn('coordinates: { x: Number(x.value), y: Number(y.value) }', source)
        self.assertIn('stepsComputed', source)
        self.assertIn('availableRoots', source)
        self.assertIn('xNumerator', source)
        self.assertIn('data-e8-walk-canvas', source)

    def test_formula_instance_renderers_are_registered_and_use_structured_results(self):
        source = (Path(__file__).resolve().parents[2] / "js/formula-instance-computation.js").read_text(encoding="utf-8")
        for renderer in (
            "proofscript/packing-scaling-instance-v1",
            "proofscript/periodic-density-instance-v1",
            "proofscript/eisenstein-coefficient-v1",
        ):
            self.assertIn(renderer, source)
        self.assertIn("Number.isSafeInteger", source)
        self.assertIn("BigInt", source)
        self.assertIn("volumeScaleFactor", source)
        self.assertIn("densityCoefficient", source)
        self.assertIn("divisorPowerSum", source)
        self.assertIn("formula-equations", source)
        self.assertIn("sigmaExponent", source)
        self.assertIn('formula-instance-computation.js?v=3', (Path(__file__).resolve().parents[1] / "Templates/page.html").read_text(encoding="utf-8"))
        self.assertNotIn("eval(", source)


if __name__ == "__main__":
    unittest.main()
