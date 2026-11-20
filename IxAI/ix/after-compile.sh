#!/usr/bin/env bash
# Wait for the full compile to finish, then shard and certify the full environment end to end.
set -uo pipefail
P="$(cd "$(dirname "$0")/.." && pwd)"
B=$P/ix/bundle
before=$(stat -c %Y "$B/certified_full.ixe" 2>/dev/null || echo 0)
while pgrep -f 'ix compile Certified_full.lean' > /dev/null || pgrep -f 'rebuild-full.sh' > /dev/null; do sleep 30; done
after=$(stat -c %Y "$B/certified_full.ixe" 2>/dev/null || echo 0)
grep -q 'Compiled and wrote' "$P/ix/rebuild-full.log" || { echo "$(date +%T) compile did not succeed; not certifying"; exit 1; }
echo "$(date +%T) compile finished (ixe mtime $before -> $after)"
cd "$B"
IX_PROFILE=ci-pinned ../ixw shard certified_full.ixe --shards 72 --out certified_full.ixes 2>&1 | tail -2
SHARDS=72 ../certify-full.sh certified_full.ixe certified_full.ixes full3
