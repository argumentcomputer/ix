#!/usr/bin/env bash
# Run a census to completion under the watchdog: when a check exceeds the
# watchdog's limits the census exits with code 3 and records the address in
# <output>.runaway; rerun with every recorded address skipped.
# Usage: check-ixe-guarded.sh <census-binary> <input.ixe> <output.jsonl> [limit] [fuel]
set -u
binary=$1; input=$2; output=$3; shift 3
runaway="$output.runaway"
rm -f "$runaway"
while true; do
  skip=$(paste -sd, "$runaway" 2>/dev/null || true)
  CHECK_IXE_SKIP="$skip" "$binary" "$input" "$output" "$@"
  rc=$?
  if [ "$rc" -ne 3 ]; then exit "$rc"; fi
  echo "check-ixe-guarded: restarting with $(wc -l < "$runaway") skipped" >&2
done
