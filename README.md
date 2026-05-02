# Fast Proof Theory

Lean 4 definitions for a small set of proof systems. The Lean library is intentionally minimal: each calculus is an explicit inductive type under `FastProofTheory.Proof`.

## Build

```bash
make build
```

## CLI

```bash
lake exe fast-proof-theory proof-info
```

The `kernel` command remains as a tiny JSON-RPC compatibility surface for metadata:

```bash
cat <<'JSON' | ./.lake/build/bin/fast-proof-theory kernel
{"jsonrpc":"2.0","id":"smoke","method":"proofInfo","params":null}
JSON
```

## MyPA Workflows

CLI verify an existing `.mypa` file:

```bash
make check demo/smoke_linear_gentzen.mypa
```

CLI export one theorem from `.mypa` to Lean4:

```bash
make extract MYPA_FILE=demo/quickstart_linear_gentzen.mypa THEOREM=tensor_right OUT=demo/tensor_right_extracted.lean
lake env lean demo/tensor_right_extracted.lean
```

VSCode interactive proof assistant:

Open `proofAssistant/extensionVSCode` in VSCode and run extension host (`F5`).
The prelaunch task now compiles both the standalone LSP server and the extension automatically.
