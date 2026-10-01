#!/usr/bin/env bash
# Run an environment check to completion under the watchdog: when a check exceeds the
# watchdog's limits the environment check exits with code 3 and records the address in
# <output>.runaway; rerun with every recorded address skipped.
# Usage: check-ixe-guarded.sh <binary> <input.ixe> <output.jsonl> [limit] [fuel]
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
