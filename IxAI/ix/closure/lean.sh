#!/usr/bin/env bash
# Lean 4.34.1 with the search path of the Mathlib build in the ixai-aiur worktree (read only).
set -euo pipefail
pkgs=/home/sam/repos/ix.ixai-aiur/.lake/packages
LEAN_PATH="$(ls -d "$pkgs"/*/.lake/build/lib/lean | tr '\n' ':')"
export LEAN_PATH
bin=${IX_LEAN:-/nix/store/xnh27vasww8vbnh7a18g3xkdg1r4kl6w-lean-4.34.1}/bin
export PATH="$bin:$PATH"
exec "$bin/lean" "$@"
