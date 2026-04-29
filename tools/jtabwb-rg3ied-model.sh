#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUTDIR="$ROOT/countermodels/jtabwb"

if [ "${FAST_PROOF_THEORY_IN_DEVCONTAINER:-}" != "1" ]; then
  exec "$ROOT/tools/devcontainer-run.sh" "$ROOT/tools/jtabwb-rg3ied-model.sh" "$@"
fi

mkdir -p "$OUTDIR"

if [ "$#" -lt 2 ]; then
  echo "Usage: $0 NAME FORMULA"
  echo "Example: $0 sample '(p | (p -> false))'"
  exit 2
fi

NAME="$1"
shift
FORMULA="$*"

JTW="$OUTDIR/$NAME.jtw"
OUT="$OUTDIR/$NAME.out"
TRACE="$OUTDIR/$NAME.trace.log"
MODEL="$OUTDIR/$NAME.model.tex"

cat > "$JTW" <<EOF
%------------------------
% File : xxxxx_$NAME
% Status : unprovable
%------------------------
$FORMULA
%------------------------
EOF

rm -f "$ROOT/model.tex" "$MODEL"

(
  cd "$ROOT"
  tools/jtabwb-launch.sh rg3ied -model "$JTW"
) | tee "$OUT"

TRACE_FILE="$(find "$ROOT" -maxdepth 1 -type f -name 'trace-*.log' | tail -1 || true)"
if [ -n "$TRACE_FILE" ]; then
  cp "$TRACE_FILE" "$TRACE"
fi

if [ -f "$ROOT/model.tex" ]; then
  cp "$ROOT/model.tex" "$MODEL"
fi

if grep -q 'proof-search \[SUCCESS\]' "$OUT"; then
  echo "==> RESULT: RG3IED SUCCESS"
else
  echo "==> RESULT: RG3IED FAILURE"
  exit 1
fi
