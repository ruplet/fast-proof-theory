# MyPA Kernel (C++)

This directory contains prover semantics in C++.

## Build

```bash
cmake -S kernel -B kernel/build
cmake --build kernel/build
```

If `cmake` is unavailable, you can compile directly:

```bash
g++ -std=c++17 -O2 -o kernel/build/mypa-kernel kernel/src/main.cpp kernel/src/json_rpc.cpp
```

## Input protocol

The kernel reads one JSON-RPC 2.0 request from `stdin`:

```json
{
  "jsonrpc": "2.0",
  "id": "<request-id>",
  "method": "checkDocument",
  "params": {
    "document": { /* DocumentIR */ }
  }
}
```

`DocumentIR` matches the TypeScript structure used by the LSP (`lsp_server/src/types.ts`).

## Output protocol

The kernel writes one JSON-RPC 2.0 response to `stdout`:

```json
{
  "jsonrpc": "2.0",
  "id": "<request-id>",
  "result": {
    "diagnostics": [ ... ],
    "goals": [ ... ]
  }
}
```

On parse/validation/method errors, the kernel returns a standard JSON-RPC `error` object.
