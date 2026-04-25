# fast-proof-theory

A proof assistant for multiple weird logics. We allow to choose between reasoning in Intuitionistic Propositional Logic,
Classical Propositional Logic, variants of Linear Logic, and in pure Calculus of Constructions treated as a logic.
We also sometimes provide multiple versions of the same logic - e.g. adding it in natural deduction or in gentzen sequent
calculus style.

In this project, we have a few submodules:
- VSCode client, that provides a Lean-like interface for the logics, e.g. to interactively view proof state when
proving gentzen-style in linear logic.
- LSP server that communicates between VSCode and our backend
- backend for the proof checker written in Lean4
- actual deep embeddings of the logics we are working it, to prove theorems about correctness of the logics we implement,
    e.g. if we want to operate in gentzen style deduction for linear logic, then we are interested in showing that
    soundness and completeness theorems hold for our underlying theory
- an export module that exports from our proof assistant to Lean4-checkable program to verify correctness


## GPT-generated readme:
Current top-level split:

- `client/` = VSCode extension (LSP client)
- `lsp_server/` = thin Node LSP adapter
- `lean_backend/` = Lean backend, including document engine, proof engine, tactics, and kernel

The intended semantic boundary is:

- `client/` owns UI only
- `lsp_server/` owns transport only
- `lean_backend/` owns all logic semantics

Inside `lean_backend/`, the linear-logic code is split so proof search can evolve independently from kernel checking:

- `FastProofTheory/Linear/Engine.lean` = snapshots, parsing, proof-state engine
- `FastProofTheory/Linear/Kernel.lean` = tiny certificate checker boundary
- `FastProofTheory/Linear/Tactics/Interface.lean` = tactic interface
- `FastProofTheory/Linear/Tactics/Search.lean` = proof-search tactic entry point

The current linear backend supports one kernel with profile restrictions:

- `LL` = linear logic without exponentials
- `LL!` / `LL EXP` = linear logic with exponentials

## Proof Profile Syntax

For the linear backend, theorem headers currently support:

```text
theorem <Name> using <PROFILE>
```

Examples:

- `theorem T using LL in GENTZEN with LL`
- `theorem T using LL! in GENTZEN with LL!`
- `theorem T using LL! in GENTZEN with LL!`

## 1) Build Lean backend

From repo root:

```bash
lake build mypa-lean-kernel
```

Expected artifact:

- `.lake/build/bin/mypa-lean-kernel`

## 2) Install and build LSP server

```bash
cd lsp_server
npm install
npm run compile
cd ..
```

Expected artifact:

- `build/lsp_server/server.js`

## 3) Install and build VSCode extension client

```bash
cd client
npm install
npm run compile
cd ..
```

Expected artifact:

- `build/client/extension.js`

## 4) Run in VSCode (development mode)

Opening the repo normally does **not** install/activate `mypa`.
You must run VSCode with the extension development path set to `client/`.

From repo root:

```bash
code --extensionDevelopmentPath="$PWD/client" "$PWD/demo"
```

This opens an **Extension Development Host** window with the local `mypa` extension loaded.

In that window:

1. Open `demo/test.mypa`.
2. Run command palette: `MyPA: Show Goals`.
3. Move cursor through the file and confirm goals update.
4. Introduce an invalid line (for example `foo bar`) and confirm diagnostics appear.

Optional overrides:

- VSCode setting `mypa.lspServerPath`: path to `server.js` (default resolves to `../build/lsp_server/server.js` from `client/`).
- Env var `PROVER_KERNEL_PATH`: path to Lean backend binary (default resolves to `../.lake/build/bin/mypa-lean-kernel` from `build/lsp_server/`).

If `code` CLI is unavailable:

1. Open folder `client/` in VSCode.
2. Press `F5` (or `Run and Debug` -> `Run Extension`) to start an Extension Development Host.
3. In the host window, open the repo's `demo/test.mypa` file and run `MyPA: Show Goals`.

## 5) Quick sanity checks

Lean backend directly:

```bash
cat <<'EOF' | ./.lake/build/bin/mypa-lean-kernel
{"jsonrpc":"2.0","id":"smoke","method":"checkDocument","params":{"uri":"file:///demo/test.mypa","version":1,"text":"theorem Demo using LL in GENTZEN with LL\nhyp h1 : A\ngoal A\naxiom\nend\n","cursor":{"line":3,"character":0}}}
EOF
```

TypeScript compile checks:

```bash
cd lsp_server && npm run compile
cd ../client && npm run compile
```

These checks validate:

- LSP transport compilation
- client compilation
- Lean backend execution and goal output parsing

## 5a) Build the static MyST demo

The repo now includes a local MyST-style tutorial builder under `myst/`, with tutorial content under `myst/demo/`.
It uses the `:::{mypa}` directive syntax, verifies each embedded MyPA block with the Lean backend, precomputes proof states for every cursor position, and emits a read-only browser tutorial.

Build the cache exporter first:

```bash
lake build mypa-export-cache
```

Then build the tutorial:

```bash
npm run build:myst-demo
```

Generated output:

- `build/myst/tutorial.html`
- `build/myst/cache/*.json`

Open `build/myst/tutorial.html` in a browser and click inside a code block to inspect cached proof states.

## 6) If Goals panel shows \"No goals\"

Run:

```bash
./.lake/build/bin/mypa-lean-kernel < /tmp/request.json
```

If this fails, Lean backend execution is broken or misconfigured.

Also note: the LSP `mypa/goals` path now surfaces kernel diagnostics as synthetic goals (instead of silently returning an empty goals list), so launch/runtime errors should appear in the Goals panel.

## Notes

If `npm install` fails due to network restrictions, rerun once registry access is available.

## TODO

- Formalize proper Heyting algebra semantics for IPC using Mathlib's `Mathlib.Order.Heyting.Basic`.
- Prove soundness and completeness of propositional IPC with respect to that semantics.
