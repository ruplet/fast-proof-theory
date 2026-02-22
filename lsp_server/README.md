# MyPA LSP Server

- Implements LSP using `vscode-languageserver`.
- Parses MyPA source into `DocumentIR` (see `../proto`).
- Encodes/decodes `DocumentIR` using `protobufjs` delimited messages for schema validation.
- Sends structured IR to the C++ kernel process.

## Build

```bash
npm install
npm run compile
```
