# fast-proof-theory

Manual build instructions for the current architecture:

- `client/` = VSCode extension (LSP client)
- `lsp_server/` = Node Language Server
- `kernel/` = C++ prover kernel

## 1) Build C++ kernel

From repo root:

```bash
mkdir -p kernel/build
g++ -std=c++17 -O2 -o kernel/build/mypa-kernel kernel/src/main.cpp
```

Alternative with CMake (if available):

```bash
cmake -S kernel -B kernel/build
cmake --build kernel/build
```

Expected artifact:

- `kernel/build/mypa-kernel`

## 2) Install and build LSP server

```bash
cd lsp_server
npm install
npm run compile
cd ..
```

Expected artifact:

- `lsp_server/out/server.js`

## 3) Install and build VSCode extension client

```bash
cd client
npm install
npm run compile
cd ..
```

Expected artifact:

- `client/out/extension.js`

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

- VSCode setting `mypa.lspServerPath`: path to `server.js` (default resolves to `../lsp_server/out/server.js` from `client/`).
- Env var `PROVER_KERNEL_PATH`: path to kernel binary (default resolves to `../kernel/build/mypa-kernel` from `lsp_server/out/`).

If `code` CLI is unavailable:

1. Open folder `client/` in VSCode.
2. Press `F5` (or `Run and Debug` -> `Run Extension`) to start an Extension Development Host.
3. In the host window, open the repo's `demo/test.mypa` file and run `MyPA: Show Goals`.

## 5) Quick sanity checks

Kernel directly:

```bash
cat /tmp/sample.ir | kernel/build/mypa-kernel
```

TypeScript compile checks:

```bash
cd lsp_server && npm run compile
cd ../client && npm run compile
```

Automated smoke checks (no VSCode required):

```bash
./scripts/e2e_kernel_pipeline.sh
./scripts/e2e_lsp_kernel.sh
```

Expected output:

- `PASS: kernel pipeline smoke check`
- `PASS: LSP logic + kernel smoke check`

These checks validate:

- parser/IR generation from `.mypa` input,
- IR/protobuf encode-decode validation path,
- kernel execution and goal output parsing.

## 6) If Goals panel shows \"No goals\"

Run:

```bash
./scripts/e2e_kernel_pipeline.sh
```

If this fails, kernel execution is broken/misconfigured.

Also note: the LSP `mypa/goals` path now surfaces kernel diagnostics as synthetic goals (instead of silently returning an empty goals list), so launch/runtime errors should appear in the Goals panel.

## Notes

If `npm install` fails due to network restrictions, rerun once registry access is available.
