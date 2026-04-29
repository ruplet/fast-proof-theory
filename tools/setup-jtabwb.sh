#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
TOOLS="$ROOT/.tools"
BIN="$ROOT/bin"

mkdir -p "$TOOLS" "$BIN"

if [ ! -d "$TOOLS/jtabwb_provers/.git" ]; then
  echo "Cloning JTabWb provers..."
  git clone https://github.com/ferram/jtabwb_provers.git "$TOOLS/jtabwb_provers"
fi

write_wrapper() {
  local name="$1"
  local prover="$2"
  cat > "$BIN/$name" <<EOF
#!/usr/bin/env bash
set -euo pipefail
ROOT="\$(cd "\$(dirname "\$0")/.." && pwd)"
exec "\$ROOT/tools/jtabwb-launch.sh" "$prover" "\$@"
EOF
  chmod +x "$BIN/$name"
}

write_wrapper rg3ied rg3ied
write_wrapper lsj lsj
write_wrapper g3iswiss g3iswiss

echo "JTabWb wrappers installed in $BIN"
