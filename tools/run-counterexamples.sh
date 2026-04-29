#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
CM="$ROOT/tools/jtabwb-countermodel.sh"

if [ "${FAST_PROOF_THEORY_IN_DEVCONTAINER:-}" != "1" ]; then
  exec "$ROOT/tools/devcontainer-run.sh" "$ROOT/tools/run-counterexamples.sh" "$@"
fi

# 2(c) left-to-right:
# ¬(¬¬p -> q) -> ¬(p -> q)
# Using explicit negation A -> false to avoid parser ambiguity.
"$CM" 2c '(((~~p -> q) -> false) -> ((p -> q) -> false))'

# 2(h):
# ((a -> c) -> d) -> e, ((b -> c) -> d) -> e ⊬ ((a | b -> c) -> d) -> e
# Encode Gamma ⊬ C as non-theorem A -> (B -> C).
"$CM" 2h '((((a -> c) -> d) -> e) -> ((((b -> c) -> d) -> e) -> (((((a | b) -> c) -> d) -> e))))'

# 2(i):
# (((p -> q) -> r) -> (p -> r) -> r) -> q
"$CM" 2i '((((p -> q) -> r) -> ((p -> r) -> r)) -> q)'

# 3(c):
# ((¬¬p -> p) -> p ∨ ¬p) -> ¬p ∨ ¬¬p
"$CM" 3c '(((~~p -> p) -> (p | (p -> false))) -> ((p -> false) | ~~p))'
