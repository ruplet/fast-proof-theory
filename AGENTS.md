# Agent Instructions

Read only the source and docs needed for the task.

Do not read generated or dependency artifacts unless the task is explicitly about build tooling or external dependencies.

Never read:

- `build/`
- `.lake/`
- `.lake/build/`
- `.lake/packages/`
- `.lake/packages/mathlib/`
- `node_modules/`
- `proofAssistant/extensionVSCode/node_modules/`
- `proofAssistant/lsp_server/node_modules/`
- `proofAssistant/webMonaco/node_modules/`

Start from source entrypoints instead:

- UI: `proofAssistant/extensionVSCode/src/`
- Monaco UI: `proofAssistant/webMonaco/src/`
- LSP transport: `proofAssistant/lsp_server/src/`
- Shared LSP/service code: `proofAssistant/lsp_core/`
- Shared editor language behavior: `proofAssistant/languageSupport/`
- Shared proof-state rendering: `proofAssistant/proofStateUi/`
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

## UI Architecture Rules

Keep host-specific code at host boundaries.

- `lsp_core` must not import `proofAssistant/index.js`, VS Code APIs, Monaco APIs, browser globals, or Node process APIs. It should depend on injected backend interfaces.
- `lsp_server/src/` and `lsp_browser/src/` own transport and backend loading only.
- VS Code and Monaco must share proof-state types/rendering and language behavior through `proofStateUi/` and `languageSupport/`; do not duplicate completions, hovers, keywords, operators, or diagnostics policy per host.
- The VS Code extension must be self-contained when packaged. Do not rely on `context.extensionPath/..` sibling repo layout at runtime.
- Full-document checking/sync is acceptable for now; efficiency is not the priority. Correctness, parity, and clean boundaries are higher priority.
- Designs should scale to new IDEs, browsers, and proof languages by adding adapters/data, not by copying host-specific logic.

## Package And Dependency Policy

Keep the Node package structure minimal:

- Root `package.json`: development tooling, TypeScript, Playwright, workspaces, shared scripts.
- `proofAssistant/webMonaco/package.json`: dependencies needed by users building the static Monaco website.
- `proofAssistant/extensionVSCode/package.json`: dependencies needed by users installing/building the VS Code extension. Do not include Monaco or Playwright here.
- Do not add package files for `lsp_core`, `lsp_server`, `lsp_browser`, or e2e unless the package boundary is intentionally redesigned.
- When package boundaries or scripts change, update `.vscode/tasks.json` and extension launch configs in the same change. F5 debugging must use existing scripts and must not reference removed package manifests.
- Never use `--no-audit`, `--no-fund`, or `--ignore-scripts` for npm commands unless explicitly instructed. Security audits matter.

## UI Verification Policy

For any UI change under `proofAssistant/extensionVSCode/` or `proofAssistant/webMonaco/`, Codex must verify behavior with Playwright instead of relying only on static inspection.

Playwright is a root development dependency so end users of `webMonaco` and the VS Code extension do not install test tooling through their runtime package manifests.

Required commands for Codex when validating Monaco UI:

1. Install UI test tooling (if not installed):
   - `npm run install:e2e:monaco`
2. Start Monaco dev server:
   - `npm run dev:monaco`
3. Run Playwright tests against the active server URL:
   - `PLAYWRIGHT_BASE_URL=http://127.0.0.1:5173 npm run test:e2e:monaco`
   - If Vite selects another port (for example `5174`), use that URL instead.

If sandbox constraints block local ports or browser startup, request escalation and still complete the Playwright run before finalizing.
