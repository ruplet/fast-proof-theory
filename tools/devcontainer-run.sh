#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
CONTAINER_ROOT="/workspace/fast-proof-theory"
IMAGE="fast-proof-theory-devcontainer:latest"

if [ "${FAST_PROOF_THEORY_IN_DEVCONTAINER:-}" = "1" ]; then
  exec "$@"
fi

if [ "$#" -eq 0 ]; then
  echo "Usage: $0 COMMAND [ARGS...]"
  exit 2
fi

if ! command -v docker >/dev/null 2>&1; then
  echo "docker is not available on PATH"
  exit 127
fi

docker build \
  -t "$IMAGE" \
  -f "$ROOT/.devcontainer/Dockerfile" \
  "$ROOT"

args=()
for arg in "$@"; do
  case "$arg" in
    "$ROOT"/*)
      args+=("$CONTAINER_ROOT/${arg#"$ROOT/"}")
      ;;
    *)
      args+=("$arg")
      ;;
  esac
done

exec docker run --rm -t \
  --user "$(id -u):$(id -g)" \
  -e FAST_PROOF_THEORY_IN_DEVCONTAINER=1 \
  -e HOME=/tmp/fast-proof-theory-home \
  -v "$ROOT:/workspace/fast-proof-theory" \
  -w "$CONTAINER_ROOT" \
  "$IMAGE" \
  "${args[@]}"
