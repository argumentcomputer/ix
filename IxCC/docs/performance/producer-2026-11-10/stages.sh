#!/usr/bin/env bash
# stages.sh TESTS-RECHECK OUTDIR TIMEOUT MODE STEM... : `tests-recheck --perf-stages` on each
# in/STEM.ixe (run from the directory holding in/), with wall time and peak RSS, one log per stem.
set -u
T="$1"; O="$2"; TO="$3"; MODE="$4"; shift 4
mkdir -p "$O"
for s in "$@"; do
  /usr/bin/time -f "TIME %e s %M KB exit %x" -o "$O/$s.$MODE.time" timeout "$TO" "$T" --perf-stages in/$s.ixe in/$s.equations.json "$MODE" > "$O/$s.$MODE.log" 2>&1
  echo "== $s $MODE: $(cat "$O/$s.$MODE.time" | grep TIME)"
  cat "$O/$s.$MODE.log"
done
