#!/usr/bin/env bash
# Rebuild ixai, regenerate Certified_full.lean, compile it with ix and probe the composition theorem.
set -euo pipefail
export IX_PROFILE=ci-pinned
P="$(cd "$(dirname "$0")/.." && pwd)"
cd "$P"
"$P/ix/heavy.sh" timeout 1800 env PATH="$P/.toolchain/bin:$PATH" lake build ixai 2>&1 | grep -E 'error|Build completed' | head -5
.lake/build/bin/ixai certified ix/bundle full 10 | head -1
cd ix/bundle
"$P/ix/heavy.sh" timeout 2700 env PATH="${IX_LEAN:-/nix/store/xnh27vasww8vbnh7a18g3xkdg1r4kl6w-lean-4.34.1}/bin:$PATH" \
  /usr/bin/time -f "ix compile %es %MKB" ../ixw compile Certified_full.lean --local --no-build --out certified_full.ixe 2>&1 \
  | grep -E "Compiled|error|ix compile" | head -5
