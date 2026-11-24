#!/usr/bin/env bash
# Run a Lean/Lake command under a machine-wide lock so that at most one Lean
# process runs at a time (8 GB RAM; concurrent builds have crashed the WSL VM).
# Usage: scripts/lean-locked.sh lake build <Module>   |   scripts/lean-locked.sh lake env lean <file>
set -euo pipefail
cd "$(dirname "$0")/.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
exec flock /tmp/pla-lean-build.lock "$@"
