# proofAssistant

Browser/VSCode-friendly JS frontend for MyPA:

- parses `.mypa` theorem blocks
- validates supported linear tactics with diagnostics
- extracts Lean4 files targeting `FastProofTheory.Proof.LinearLogic`

## CLI

```bash
node proofAssistant/cli.js extract <input.mypa> <theoremName> -o <output.lean>
```

## Embedding

```js
const { checkDocument, extractDocument, domainInfo } = require("./proofAssistant/index.js");
```

`index.js` is framework-agnostic JS and can be bundled for browser use.
