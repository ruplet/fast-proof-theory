# Agent Instructions

Read only the source and docs needed for the task.

Do not read generated or dependency artifacts unless the task is explicitly about build tooling or external dependencies.

Never read:

- `build/`
- `.lake/`
- `.lake/build/`
- `.lake/packages/`
- `.lake/packages/mathlib/`
- `proofAssistant/extensionVSCode/node_modules/`
- `proofAssistant/lsp_server/node_modules/`

Start from source entrypoints instead:

- UI: `proofAssistant/extensionVSCode/src/`
- LSP transport: `proofAssistant/lsp_server/src/`
- MyPA parser + extraction engine: `proofAssistant/index.js`
- Lean core: `FastProofTheory/Proof/`
- Demos: `demo/`

If verification is needed, you may run build commands, but do not inspect generated outputs unless required to debug the build itself.

## Codex MyPA Workflow

For programmatic MyPA proof development and verification, use:

- Verify `.mypa` file:
  - `node proofAssistant/cli.js verify <file.mypa>`
- Export theorem to Lean4:
  - `node proofAssistant/cli.js extract <file.mypa> <theoremName> -o <output.lean>`
- Formally check exported Lean file against core:
  - `lake env lean <output.lean>`

Codex should treat `FastProofTheory/Proof/*` as the trusted kernel and `proofAssistant/*` as user-facing tooling.
