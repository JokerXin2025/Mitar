# Mitar Demo

This project demonstrates every ProofScript component currently rendered by Mitar:

- project metadata and the generated project index;
- all current ProofText inline and block forms;
- build-time code highlighting through Pygments, with plain-text fallback for unknown languages;
- theorem components and proof-tree rendering;
- cross-module theorem references and the references component.
- a real Lean/Wasm Fibonacci computation with a range control, chart, timing, loading, and error states.

Build it from this directory:

```bash
mitar make .
```

The Fibonacci page requires the matching Lean/Wasm runtime:

```bash
source "$HOME/Developer/emsdk/emsdk_env.sh"
export PROOF_SCRIPT_LEAN_WASM_PREFIX="$HOME/Developer/lean4-wasm-4.32.0/build/proof-script-emscripten"
mitar make MitarDemo.Fibonacci
```

The scoped command builds the Fibonacci page and its C IR, finalizes the Wasm bundle, and renders
`.Mitar/build/MitarDemo/Fibonacci.html`. Use `mitar make .` when rebuilding the complete gallery.

Then serve the generated site:

```bash
mitar serve
```

Open `http://127.0.0.1:8000/`. Do not double-click the generated HTML: browsers reject Wasm
resource fetches from a `file://` page. `mitar serve` supplies the required Wasm MIME, COOP, COEP,
and CSP headers.

To expose the demo on the local network:

```bash
mitar serve --lan
```

This prints the machine's LAN URL. Because the computation bundle uses pthreads and
`SharedArrayBuffer`, computation from another device requires trusted HTTPS:

```bash
mitar serve --lan --cert ./localhost+2.pem --key ./localhost+2-key.pem
```

To render the existing ProofScript JSON without compiling Lean again:

```bash
mitar make . --cache
```
