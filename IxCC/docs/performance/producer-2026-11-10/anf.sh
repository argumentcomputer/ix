#!/usr/bin/env bash
# anf.sh TESTS-RECHECK TIMEOUT "KIND N K"... : tests-recheck --perf-anf on each shape, with wall time and peak RSS
T="$1"; TO="$2"; shift 2
for s in "$@"; do
  set -- $s
  /usr/bin/time -f "TIME %e s %M KB exit %x" -o "${TMPDIR:-/tmp}"/perf-anf.time timeout "$TO" "$T" --perf-anf $1 $2 $3 > "${TMPDIR:-/tmp}"/perf-anf.log 2>&1
  echo "== $s: $(grep TIME "${TMPDIR:-/tmp}"/perf-anf.time)"; cat "${TMPDIR:-/tmp}"/perf-anf.log
done
