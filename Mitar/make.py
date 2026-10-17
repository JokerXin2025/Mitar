import subprocess
import json
import os
import re
import shutil
from pathlib import Path
from Mitar.Rules import Initialize
from Mitar.engine import render_index
from Mitar.page import PageRenderer, build_label_index, build_theorem_dependency_index, directory_modules, discover_pages, load_page
from Mitar.project import MitarError, project_language, resolve_target


def make(target_name: str, cache: bool = False, language: str | None = None):
    Initialize()
    target = resolve_target(target_name)
    language = project_language(target.root, language)
    if not cache:
        print("Running ProofScript pipeline...")
        # A non-cached build must not reuse generated ProofScript output.
        shutil.rmtree(target.root / ".ProofScript", ignore_errors=True)
        if target.module is None:
            _run_lake(["lake", "build"], target.root)
            _compile_missing_pages(target.root)
            computation_modules = _page_computation_modules(target.root)
            pending_modules = _pending_computation_modules(target.root)
            _recompile_computation_modules(
                target.root,
                {module: source for module, source in computation_modules.items()
                 if module not in pending_modules},
            )
        else:
            _compile_module_page(target)
        _build_computations(target.root)
    else:
        print("Using cached ProofScript output; skipping Lean compilation.", flush = True)

    print("Discovering cached pages...", flush = True)
    all_pages = discover_pages(target.root)
    pages = all_pages
    if target.module is not None:
        pages = [page for page in all_pages if page.module == target.module]
        if not pages:
            if target.page_file is None or not target.page_file.is_file():
                raise MitarError(f"Page JSON not found for module {target.module}: {target.page_file}")
            pages = [load_page(target.page_file, target.root)]

    build_root = target.root / ".Mitar" / "build"
    _publish_runtime_assets(build_root)
    _publish_computation_resources(target.root, build_root)
    labels = build_label_index(all_pages)
    theorem_dependencies = build_theorem_dependency_index(all_pages, target.root)
    renderer = PageRenderer(
        target.root, build_root, labels, all_pages,
        default_language=language, theorem_dependencies=theorem_dependencies,
    )
    pages_by_module = {page.module: page for page in all_pages}
    render_pages = {page.module: page for page in pages if "." in page.module}
    directories = directory_modules(all_pages)
    virtual_directories = [
        module for module in directories
        if "." in module and module not in pages_by_module
    ]
    for position, module in enumerate(virtual_directories, 1):
        print(f"[Mitar] Rendering directory {position}/{len(virtual_directories)}: {module}", flush = True)
        output = build_root / Path(*module.split(".")[:-1]) / f"{module.split('.')[-1]}.html"
        output.parent.mkdir(parents = True, exist_ok = True)
        output.write_text(renderer.render_directory(module), encoding = "utf-8")

    for module in directories:
        if "." in module and module in pages_by_module:
            render_pages[module] = pages_by_module[module]

    pages_to_render = list(render_pages.values())
    for position, page in enumerate(pages_to_render, 1):
        print(f"[Mitar] Rendering module {position}/{len(pages_to_render)}: {page.module}", flush = True)
        output = build_root / page.output_path
        output.parent.mkdir(parents = True, exist_ok = True)
        output.write_text(renderer.render(page), encoding = "utf-8")

    build_root.mkdir(parents = True, exist_ok = True)
    print("[Mitar] Rendering project index and diagnostics...", flush = True)
    roots = sorted({page.module.split(".")[0] for page in all_pages})
    root_page = pages_by_module.get(roots[0]) if len(roots) == 1 else None
    root_contents = ""
    root_theorem_navigation = ""
    if root_page is not None:
        root_contents = "\n\n".join(renderer.render_components(root_page, Path("index.html")))
        root_theorem_navigation = renderer._theorem_navigation(root_page, Path("index.html"))
    (build_root / "index.html").write_text(
        render_index(all_pages, language, root_contents, root_theorem_navigation), encoding = "utf-8"
    )
    (build_root / "lean2tex-report.json").write_text(
        json.dumps({
            "summary": _diagnostic_summary(renderer.diagnostics),
            "diagnostics": renderer.diagnostics,
        }, ensure_ascii = False, indent = 2),
        encoding = "utf-8",
    )
    print(f"\n\033[32m\033[1m✓ Output has been saved to \033[4m{build_root}\033[0m\n")
    return build_root


def _diagnostic_summary(diagnostics):
    by_code = {}
    missing_constants = {}
    for diagnostic in diagnostics:
        code = diagnostic.get("code", "unknown")
        by_code[code] = by_code.get(code, 0) + 1
        if code == "L2T001" and diagnostic.get("constant"):
            constant = diagnostic["constant"]
            missing_constants[constant] = missing_constants.get(constant, 0) + 1
    return {
        "total": len(diagnostics),
        "byCode": dict(sorted(by_code.items())),
        "missingConstants": dict(sorted(missing_constants.items(), key = lambda item: (-item[1], item[0]))),
    }


def _run_lake(command, project_root):
    """Run Lake/Lean while forwarding its output as it is produced."""
    process = subprocess.Popen(
        command,
        cwd = project_root,
        text = True,
        stdout = subprocess.PIPE,
        stderr = subprocess.STDOUT,
        bufsize = 1,
    )
    output = []
    assert process.stdout is not None
    try:
        for line in process.stdout:
            output.append(line)
            print(line, end = "", flush = True)
    except KeyboardInterrupt:
        process.terminate()
        process.wait()
        raise
    finally:
        process.stdout.close()
    returncode = process.wait()
    if returncode:
        raise MitarError(f"Lean build failed:\n{''.join(output)}")


def _compile_source(project_root, source):
    print(f"\n[Mitar] Compiling {source.relative_to(project_root)}", flush=True)
    _run_lake(
        ["lake", "env", "lean", str(source.relative_to(project_root))],
        project_root,
    )


def _compile_module_page(target):
    target.page_file.unlink(missing_ok=True)
    pending_bundle = target.root / ".ProofScript" / "computations" / "pending" / Path(*target.module.split("."))
    shutil.rmtree(pending_bundle, ignore_errors=True)
    _run_lake(["lake", "build", target.module], target.root)
    # Lake may reuse its module artifact, so rerun elaboration to refresh
    # ProofScript's page JSON and any pending computation manifests.
    _compile_source(target.root, target.source_file)


def _source_modules(project_root):
    return {
        ".".join(source.relative_to(project_root).with_suffix("").parts): source
        for source in project_root.rglob("*.lean")
        if not any(part.startswith(".") for part in source.relative_to(project_root).parts)
    }


def _compile_missing_pages(project_root):
    pages_root = project_root / ".ProofScript" / "pages"
    for module, source in sorted(_source_modules(project_root).items()):
        try:
            is_page = re.search(
                r"(?m)^\s*page_end\b",
                source.read_text(encoding="utf-8"),
            ) is not None
        except (OSError, UnicodeError) as error:
            raise MitarError(f"Failed to inspect Lean source {source}: {error}") from error
        if not is_page:
            continue
        page = pages_root.joinpath(*module.split(".")).with_suffix(".json")
        # Lake may replay an existing artifact without rerunning elaborators.
        # Re-elaborate missing pages so ProofScript writes output in this
        # project's working directory.
        if not page.is_file():
            _compile_source(project_root, source)


def _pending_computation_modules(project_root):
    pending = project_root / ".ProofScript" / "computations" / "pending"
    modules = {}
    for manifest in pending.rglob("*.json") if pending.is_dir() else []:
        try:
            value = json.loads(manifest.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            raise MitarError(f"Failed to read computation manifest {manifest}: {error}") from error
        module = value.get("module") if isinstance(value, dict) else None
        source_value = value.get("source", {}).get("file") if isinstance(value, dict) else None
        if not isinstance(module, str) or not module or not isinstance(source_value, str):
            raise MitarError(f"Invalid computation manifest: {manifest}")
        source = Path(source_value)
        if not source.is_absolute():
            source = project_root / source
        if not source.is_file():
            raise MitarError(f"Computation source not found for {module}: {source}")
        modules[module] = source.resolve()
    return modules


def _page_computation_modules(project_root):
    modules = {}
    pages_root = project_root / ".ProofScript" / "pages"
    for page in pages_root.rglob("*.json") if pages_root.is_dir() else []:
        try:
            document = json.loads(page.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            raise MitarError(f"Failed to read page JSON {page}: {error}") from error
        components = document.get("components", []) if isinstance(document, dict) else []
        if not any(isinstance(item, dict) and "computation" in item.get("data", {}) for item in components):
            continue
        module = document.get("module")
        source_value = document.get("source")
        if not isinstance(module, str) or not module or not isinstance(source_value, str):
            raise MitarError(f"Invalid computation page: {page}")
        source = Path(source_value)
        if not source.is_absolute():
            source = project_root / source
        if source.is_file():
            modules[module] = source.resolve()
    return modules


def _recompile_computation_modules(project_root, modules=None):
    modules = _pending_computation_modules(project_root) if modules is None else modules
    for module, source in sorted(modules.items()):
        page = project_root / ".ProofScript" / "pages" / Path(*module.split("."))
        page.with_suffix(".json").unlink(missing_ok=True)
        pending_bundle = project_root / ".ProofScript" / "computations" / "pending" / Path(*module.split("."))
        shutil.rmtree(pending_bundle, ignore_errors=True)
        # Lake has already generated this module's C IR. This pass only reruns
        # ProofScript's elaboration-time page and manifest exporters.
        _compile_source(project_root, source)


def _compile_all_sources(project_root):
    """Compatibility helper retained for external callers."""
    for source in sorted(_source_modules(project_root).values()):
        _compile_source(project_root, source)


def _proof_script_root(project_root=None):
    configured = os.environ.get("PROOF_SCRIPT_ROOT")
    candidates = [
        Path(configured).expanduser() if configured else None,
        project_root.parent / "ProofScript" if project_root is not None else None,
        Path.home() / ".ProofScript",
        Path(__file__).resolve().parents[2] / "ProofScript",
    ]
    for candidate in candidates:
        if candidate is not None and (candidate / "scripts" / "build-computations.mjs").is_file():
            return candidate
    raise MitarError("ProofScript computation scripts not found; set PROOF_SCRIPT_ROOT")


def _build_computations(project_root):
    pending = project_root / ".ProofScript" / "computations" / "pending"
    if not pending.is_dir() or not any(pending.rglob("*.json")):
        return
    pending_values = []
    for manifest in pending.rglob("*.json"):
        try:
            value = json.loads(manifest.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            raise MitarError(f"Failed to read pending computation manifest {manifest}: {error}") from error
        if isinstance(value, dict):
            pending_values.append(value)
    pending_bundles = {value.get("bundleId") for value in pending_values}
    bundles = project_root / ".ProofScript" / "computations" / "bundles"
    if bundles.is_dir():
        for bundle in bundles.iterdir():
            if bundle.is_dir() and bundle.name not in pending_bundles:
                shutil.rmtree(bundle)
    proof_script = _proof_script_root(project_root)
    # ProofScript's bundler needs the Lean Wasm runtime. Prefer an explicit
    # environment setting, but make the standard Mitar command work with the
    # conventional local installation as well.
    if not os.environ.get("PROOF_SCRIPT_LEAN_WASM_PREFIX"):
        candidates = [
            Path.home() / "Developer" / "lean4-wasm-4.32.0" / "build" / "proof-script-emscripten",
            Path.home() / "Developer" / "lean4-wasm" / "build" / "proof-script-emscripten",
        ]
        for candidate in candidates:
            if (candidate / "lib" / "lean" / "libleanrt.a").is_file():
                os.environ["PROOF_SCRIPT_LEAN_WASM_PREFIX"] = str(candidate)
                print(f"[Mitar] Using Lean Wasm runtime: {candidate}", flush=True)
                break
    _load_emscripten_environment()
    for script in ("build-computations.mjs", "finalize-computations.mjs"):
        print(f"[Mitar] Running ProofScript {script}", flush=True)
        _run_lake(["node", str(proof_script / "scripts" / script)], project_root)


def _load_emscripten_environment():
    """Load emsdk variables when a local installation is available."""
    if shutil.which("emcc"):
        return
    candidates = [
        Path.home() / "Developer" / "emsdk" / "emsdk_env.sh",
        Path.home() / "emsdk" / "emsdk_env.sh",
    ]
    script = next((candidate for candidate in candidates if candidate.is_file()), None)
    if script is None:
        return
    command = ["/bin/bash", "-c", f"source {str(script)!r} >/dev/null 2>&1 && env -0"]
    try:
        result = subprocess.run(command, capture_output=True, check=True)
    except (OSError, subprocess.CalledProcessError):
        return
    for item in result.stdout.decode().split("\0"):
        if "=" in item:
            key, value = item.split("=", 1)
            os.environ[key] = value
    if not shutil.which("emcc"):
        return
    print(f"[Mitar] Loaded Emscripten environment: {script}", flush=True)


def _publish_computation_resources(project_root, build_root):
    source = project_root / ".ProofScript" / "resources" / "computation"
    destination = build_root / ".ProofScript" / "resources" / "computation"
    if source.is_dir():
        shutil.copytree(source, destination, dirs_exist_ok=True)


def _publish_runtime_assets(build_root):
    source_root = Path(__file__).resolve().parent.parent
    installed_root = Path.home() / ".Mitar"
    destination = build_root / "assets"
    for kind in ("css", "js"):
        source = source_root / kind
        if not source.is_dir():
            source = installed_root / kind
        if not source.is_dir():
            raise MitarError(f"Mitar {kind} assets not found")
        shutil.copytree(source, destination / kind, dirs_exist_ok=True)
