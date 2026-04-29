#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
TOOLS="$ROOT/.tools"
JTAB="$TOOLS/jtabwb_provers"
ANTLR="$TOOLS/antlr4-runtime-4.5.jar"
COMMONS="$TOOLS/commons-cli-1.6.0.jar"
RT="$JTAB/ipl_g3iswiss/g3iswiss-1.0.jar"

if [ "${FAST_PROOF_THEORY_IN_DEVCONTAINER:-}" != "1" ]; then
  exec "$ROOT/tools/devcontainer-run.sh" "$ROOT/tools/jtabwb-launch.sh" "$@"
fi

if [ "$#" -lt 1 ]; then
  echo "Usage: $0 PROVER [ARGS...]"
  echo "Provers: rg3ied, lsj, g3iswiss, g3ibu"
  exit 2
fi

PROVER="$1"
shift

mkdir -p "$TOOLS"

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

case "$PROVER" in
  rg3ied) JAR="$JTAB/ipl_g3ied/rg3ied-1.0.jar" ;;
  lsj) JAR="$JTAB/ipl_lsj/lsj-1.0.jar" ;;
  g3iswiss) JAR="$JTAB/ipl_g3iswiss/g3iswiss-1.0.jar" ;;
  g3ibu) JAR="$JTAB/ipl_g3ibu/g3ibu-1.0.jar" ;;
  *)
    echo "Unknown prover: $PROVER"
    exit 2
    ;;
esac

if [ ! -f "$JAR" ]; then
  echo "Missing prover jar: $JAR"
  exit 1
fi

MAIN="$(unzip -p "$JAR" META-INF/MANIFEST.MF \
  | tr -d '\r' \
  | awk -F': ' '/^Rsrc-Main-Class:/ {print $2}')"

CP="$ANTLR:$JAR:$RT:$COMMONS"
exec java -cp "$CP" "$MAIN" "$@"
