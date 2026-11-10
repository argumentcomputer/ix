#!/usr/bin/env bash
# rep.sh OUTDIR REPS LIST MODES TAG=IXCC... : run cli.sh REPS times over LIST for each binary,
# interleaved (rep 1 of every binary, then rep 2, ...), into OUTDIR/TAG.REP.tsv. Run from an IxCC dir.
set -u
O="$1"; R="$2"; L="$3"; M="$4"; shift 4
mkdir -p "$O"
for r in $(seq 1 "$R"); do
  for tb in "$@"; do
    tag=${tb%%=*}; bin=${tb#*=}
    echo "rep $r $tag: $(date +%T) load $(cut -d' ' -f1-3 /proc/loadavg)"
    "$(dirname "$0")/cli.sh" "$bin" "$O/$tag.$r.tsv" "$L" "$M" 0
  done
done
echo "done $(date +%T) load $(cut -d' ' -f1-3 /proc/loadavg)"
