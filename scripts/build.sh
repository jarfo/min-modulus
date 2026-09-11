#!/usr/bin/env bash
# Bound compiler concurrency without introducing artificial Lean imports.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
exec lake build "$@"
