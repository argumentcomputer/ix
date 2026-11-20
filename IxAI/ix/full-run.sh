#!/usr/bin/env bash
# Regenerate, compile, shard and certify the full environment, in sequence.
set -uo pipefail
P="$(cd "$(dirname "$0")/.." && pwd)"
"$P/ix/rebuild-full.sh" > "$P/ix/rebuild-full.log" 2>&1
grep -q 'Compiled and wrote' "$P/ix/rebuild-full.log" || { echo "$(date +%T) compile failed"; exit 1; }
echo "$(date +%T) compiled"
cd "$P/ix/bundle"
IX_PROFILE=ci-pinned ../ixw shard certified_full.ixe --shards "${SHARDS:-150}" --out certified_full.ixes 2>&1 | tail -1
SHARDS="${SHARDS:-150}" ../certify-full.sh certified_full.ixe certified_full.ixes "${LABEL:-full4}"
