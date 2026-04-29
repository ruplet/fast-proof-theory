#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
TOOLS="$ROOT/.tools"
OUTDIR="$ROOT/countermodels/jtabwb"

if [ "${FAST_PROOF_THEORY_IN_DEVCONTAINER:-}" != "1" ]; then
  exec "$ROOT/tools/devcontainer-run.sh" "$ROOT/tools/jtabwb-countermodel.sh" "$@"
fi

mkdir -p "$TOOLS" "$OUTDIR"

if [ "$#" -lt 2 ]; then
  echo "Usage: $0 NAME FORMULA"
  echo "Example: $0 2i '((((p -> q) -> r) -> ((p -> r) -> r)) -> q)'"
  exit 2
fi

NAME="$1"
shift
FORMULA="$*"

JTAB="$TOOLS/jtabwb_provers"
ANTLR="$TOOLS/antlr4-runtime-4.5.jar"
COMMONS="$TOOLS/commons-cli-1.6.0.jar"

if [ ! -d "$JTAB/.git" ]; then
  echo "==> Cloning jtabwb_provers..."
  git clone https://github.com/ferram/jtabwb_provers.git "$JTAB"
fi

if [ ! -f "$ANTLR" ]; then
  echo "==> Downloading ANTLR runtime 4.5..."
  curl -L -o "$ANTLR" \
    https://repo1.maven.org/maven2/org/antlr/antlr4-runtime/4.5/antlr4-runtime-4.5.jar
fi

if [ ! -f "$COMMONS" ]; then
  echo "==> Downloading commons-cli..."
  curl -L -o "$COMMONS" \
    https://repo1.maven.org/maven2/commons-cli/commons-cli/1.6.0/commons-cli-1.6.0.jar
fi

RG="$JTAB/ipl_g3ied/rg3ied-1.0.jar"
RT="$JTAB/ipl_g3iswiss/g3iswiss-1.0.jar"

MAIN_R="$(unzip -p "$RG" META-INF/MANIFEST.MF \
  | tr -d '\r' \
  | awk -F': ' '/^Rsrc-Main-Class:/ {print $2}')"

CP="$ANTLR:$RG:$RT:$COMMONS"

JTW="$OUTDIR/$NAME.jtw"

cat > "$JTW" <<EOF
%------------------------
% File : xxxxx_$NAME
% Status : unprovable
%------------------------
$FORMULA
%------------------------
EOF

echo "==> Problem: $NAME"
echo "==> Formula:"
echo "$FORMULA"
echo

MARKER="$OUTDIR/.marker-$NAME"
touch "$MARKER"

(
  cd "$OUTDIR"
  java -cp "$CP" "$MAIN_R" --save-trace "$JTW"
) | tee "$OUTDIR/$NAME.out"

TRACE_FILE="$(find "$OUTDIR" -maxdepth 1 -type f -name 'trace-*.log' -newer "$MARKER" | head -1 || true)"

if [ -n "$TRACE_FILE" ]; then
  cp "$TRACE_FILE" "$OUTDIR/$NAME.trace.log"
  echo
  echo "==> Saved trace:"
  echo "$OUTDIR/$NAME.trace.log"
fi

if grep -q 'proof-search \[SUCCESS\]' "$OUTDIR/$NAME.out"; then
  echo
  echo "==> RESULT: RG3IED SUCCESS: unprovability/countermodel search succeeded."
elif grep -q 'proof-search \[FAILURE\]' "$OUTDIR/$NAME.out"; then
  echo
  echo "==> RESULT: RG3IED FAILURE: it did not find an unprovability proof/countermodel."
else
  echo
  echo "==> RESULT: unknown; inspect $OUTDIR/$NAME.out"
fi
