# Agent Instructions

Read only the source and docs needed for the task.

Do not read generated or dependency artifacts unless the task is explicitly about build tooling or external dependencies.

Never read:

- `build/`
- `.lake/`
- `.lake/build/`
- `.lake/packages/`
- `.lake/packages/mathlib/`
- `client/node_modules/`
- `lsp_server/node_modules/`

Start from source entrypoints instead:

- UI: `client/src/`
- LSP transport: `lsp_server/src/`
- Lean backend: `lean_backend/`
- Demos: `demo/`

If verification is needed, you may run build commands, but do not inspect generated outputs unless required to debug the build itself.
