#!/usr/bin/env bash
# Regenerate rust/src/generated.rs from the Lean definitions, fail if it
# changed (with --check), then build and test the Rust rendering.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build Mempipe.Program
before=$(sha256sum rust/src/generated.rs 2>/dev/null || true)
lake env lean tools/ToRust.lean
after=$(sha256sum rust/src/generated.rs)
if [[ "${1:-}" == "--check" && "$before" != "$after" ]]; then
  echo "FAIL: rust/src/generated.rs is out of date"; exit 1
fi
(cd rust && cargo test --release)
