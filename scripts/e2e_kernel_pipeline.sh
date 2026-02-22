#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
KERNEL="${PROVER_KERNEL_PATH:-$ROOT/kernel/build/mypa-kernel}"
MYPA="$ROOT/demo/e2e_smoke.mypa"
WIRE="/tmp/mypa_e2e_wire.txt"
OUT="/tmp/mypa_e2e_out.txt"

if [[ ! -x "$KERNEL" ]]; then
  echo "FAIL: kernel binary missing or not executable: $KERNEL" >&2
  exit 1
fi

node - <<'NODE'
const fs = require('fs');
const path = require('path');
const ROOT = process.cwd();
const parser = require(path.join(ROOT, 'lsp_server/out/documentParser.js'));
const wire = require(path.join(ROOT, 'lsp_server/out/irWire.js'));
const filePath = path.join(ROOT, 'demo/e2e_smoke.mypa');
const text = fs.readFileSync(filePath, 'utf8');
const lines = text.split(/\r?\n/);
const prefix = lines.slice(0,3).join('\n');
const ir = parser.parseDocumentToIR(`file://${filePath}`, 1, prefix);
fs.writeFileSync('/tmp/mypa_e2e_wire.txt', wire.documentToKernelWire(ir), 'utf8');
NODE

"$KERNEL" < "$WIRE" > "$OUT"

node - <<'NODE'
const fs = require('fs');
const path = require('path');
const ROOT = process.cwd();
const wire = require(path.join(ROOT, 'lsp_server/out/irWire.js'));
const out = fs.readFileSync('/tmp/mypa_e2e_out.txt','utf8');
const res = wire.parseKernelResponse(out);
if (res.diagnostics.length) {
  console.error('FAIL: diagnostics returned:', res.diagnostics.map(d=>d.message).join(' | '));
  process.exit(1);
}
if (!res.goals.length) {
  console.error('FAIL: expected at least one goal, got none');
  process.exit(1);
}
if (res.goals[0].target !== 'a') {
  console.error('FAIL: expected first goal target = a, got', res.goals[0].target);
  process.exit(1);
}
console.log('PASS: kernel pipeline smoke check');
NODE
