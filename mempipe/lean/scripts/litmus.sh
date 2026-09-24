#!/usr/bin/env bash
# Cross-check the RC11 definitions against herd7's rc11.cat on the litmus
# tests of tools/Litmus.lean. Needs herd7: set HERD7 to the binary and
# HERD_LIBDIR to herdtools7's herd/libdir (defaults: herd7 on PATH, its libdir).
set -euo pipefail
cd "$(dirname "$0")/.."
HERD7=${HERD7:-herd7}
HERD_LIBDIR=${HERD_LIBDIR:-$(dirname "$(command -v "$HERD7")")/../share/herdtools7/herd}
out=$(mktemp -d "${TMPDIR:-/tmp}/mempipe-litmus.XXXXXX")
trap 'rm -rf "$out"' EXIT
lake build ORC11.RC11Dec
lake env lean --run tools/Litmus.lean "$out/litmus" > "$out/lean.txt"
uv run scripts/litmus.py "$out/lean.txt" "$out/litmus" "$HERD7" "$HERD_LIBDIR"
