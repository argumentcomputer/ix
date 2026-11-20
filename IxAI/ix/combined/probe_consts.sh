#!/usr/bin/env bash
# probe_consts.sh OUT_DIR NAME... : certified compile of each named constant's closure, all in
# parallel, each timed and capped (PROBE_CAP seconds, default 900). Writes OUT_DIR/summary.tsv:
# name, exit status, constants in the closure, wall time, peak RSS (kB), compile phase (ms),
# serialized bytes. Run inside one memory-capped scope through the gate.
set -uo pipefail
P=/home/sam/repos/ix-ai-pipeline
out=$1; shift
mkdir -p "$out"; rm -f "$out/summary.tsv" "$out/done"
cd $P/.truthmines/combined/src/Aiur
export IX_PROFILE=ci
i=0
for name in "$@"; do
  i=$((i+1))
  (
    echo "$name" > "$out/c$i.txt"
    /usr/bin/time -v -o "$out/c$i.time" timeout "${PROBE_CAP:-900}" $P/ix/ixw compile IxAICombined.lean \
      --consts-file "$out/c$i.txt" --no-build -v --workers 4 --out "$out/c$i.ixe" > "$out/c$i.log" 2>&1
    st=$?
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$name" "$st" \
      "$(grep -oE '[0-9]+ constants after' "$out/c$i.log" | head -1 | cut -d' ' -f1)" \
      "$(grep Elapsed "$out/c$i.time" | awk '{print $NF}')" \
      "$(grep 'Maximum res' "$out/c$i.time" | awk '{print $NF}')" \
      "$(grep -oE 'compileReport: [0-9]+' "$out/c$i.log" | cut -d' ' -f2)" \
      "$(grep -oE 'serialize \([0-9]+' "$out/c$i.log" | tr -dc 0-9)" >> "$out/summary.tsv"
    rm -f "$out/c$i.ixe"
  ) &
done
wait
echo ok > "$out/done"
