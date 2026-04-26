# fast-proof-theory

A proof assistant for multiple weird logics. We allow you to choose between concrete proof systems such as `NJp`,
`NKp`, the linear logic variants, and `SYSTEM_F`. We also sometimes provide multiple versions of the same logic in
natural deduction or Gentzen sequent-calculus style.

In this project, we have a few components:

- `client/`: VSCode client, which provides a Lean-like interface for the logics, e.g. to interactively view proof state when proving Gentzen-style in linear logic.
- `lsp_server/`: LSP server that communicates between VSCode and the Lean backend.
- `lean_backend/FastProofTheory/`: backend for the proof checker written in Lean 4, including the document engine, proof engine, tactics, kernel boundary, and exports.
- `lean_backend/Logic/`: a separate top-level Lean 4 library containing the actual deep embeddings of the logics we are working in, used to prove theorems about correctness of the logics we implement. For example, if we want to operate in Gentzen-style deduction for linear logic, then we are interested in showing that soundness and completeness theorems hold for our underlying theory.
- `FastProofTheory.Linear.Export`: export module that exports from our proof assistant to a Lean 4-checkable program to verify correctness.
- `myst/`: integration with the MyST Markdown system to generate documents with code in our assistants embedded.

The intended dependency boundary is:

- `client/` owns UI only.
- `lsp_server/` owns transport only.
- `lean_backend/Logic/` owns reusable logical syntax, deep embeddings, semantics, and metatheory. It is exposed as the top-level Lean library `Logic`.
- `lean_backend/FastProofTheory/` owns proof-assistant implementation details and depends on `Logic`, not the other way around. It is exposed as the top-level Lean library `FastProofTheory`.

The long-term architecture is a uniform proof-kernel architecture: every logic is
defined by its judgments and Gentzen-style rules, and tactic/proof-search code
must produce certificates checked by the same small trusted boundary. Linear
logic is not intended to be a separate trusted proof engine; the current
`FastProofTheory/Linear/` code is the prototype implementation that should be
refactored into the uniform `Core` layer described in
[`docs/uniform-proof-kernel.md`](docs/uniform-proof-kernel.md).

Inside `lean_backend/FastProofTheory/`, the current linear-logic prototype is split so proof search can evolve independently from kernel checking:

- `FastProofTheory/Linear/Engine.lean` = snapshots, parsing, proof-state engine
- `FastProofTheory/Gentzen/Kernel.lean` = trusted Gentzen certificate checker boundary
- `FastProofTheory/Linear/Kernel.lean` = linear-logic facade over the Gentzen checker
- `FastProofTheory/Linear/Tactics/Interface.lean` = tactic interface
- `FastProofTheory/Linear/Tactics/Search.lean` = proof-search tactic entry point

The current linear backend supports one kernel with profile restrictions:

- `LL` = linear logic without exponentials
- `LL!` / `LL EXP` = linear logic with exponentials

## Proof Profile Syntax

The `p` suffix means propositional. Absence of `p` is reserved for first-order systems with quantifiers.

For the linear backend, theorem headers currently support:

```text
theorem <Name> using <PROFILE>
```

Examples:

- `theorem T using LL in GENTZEN with LL`
- `theorem T using LL! in GENTZEN with LL!`
- `theorem T using NJp with IMP`
- `theorem T using NJp`
- `theorem T using NKp`

System F now uses an explicit typed-term judgment in theorem headers, for example:

- `theorem id using SYSTEM_F in ND : (\x : p. x) has_type p -> p := by`

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

- Formalize proper Heyting algebra semantics for NJp using Mathlib's `Mathlib.Order.Heyting.Basic`.
- Prove soundness and completeness of propositional NJp with respect to that semantics.
