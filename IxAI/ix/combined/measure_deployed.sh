#!/usr/bin/env bash
# measure_deployed.sh [VARIANT] : what the deployed model's card and gate decisions cost IxVM.
#
# Builds `IxAICombined.Deployed` in the combined environment's source tree, compiles the
# environment that includes it (`envc.sh deployed`), and checks four constants on their own with
# the kernel build VARIANT of .truthmines/kernel-subst/bin/ixf (default v5): the model literal
# (a floor: its closure without any evaluation), the model's range lemma, one gate decision and
# the card. `ix check` checks a constant's whole dependency closure, so a constant's own cost is
# its figure minus the floor's. Writes $OUT/summary.tsv: name, exit, queries, wall, peak kB.
# One heavy job; run it through ix/heavy.sh.
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
project="$(dirname "$(dirname "$here")")"
variant="${1:-v5}"
scratch="${SCRATCH:-/opt/dlami/nvme/ix-ai/combined}"
out="$scratch/deployed-cost-$variant"
env="$scratch/compile/deployed.ixe"
mkdir -p "$out"
: > "$out/summary.tsv"

"$here/rebuild_env.sh" IxAICombined.Deployed || { echo "lean build failed: $(tail -3 "$scratch/leanbuild.log")"; exit 1; }
IX_PROFILE=cert "$here/envc.sh" deployed > "$out/compile.out" 2>&1 || { echo "compile failed: $(tail -3 "$out/compile.out")"; exit 1; }
python3 -c "
import json; d = json.load(open('$scratch/compile/deployed.json'))
print('compiled:', {k: d.get(k) for k in ('requested', 'named', 'bytes', 'elapsedMs', 'root')})"

i=0
for name in IxAICombined.Deployed.trainedOutput IxAICombined.Deployed.trainedOutput_ok \
            IxAICombined.Deployed.decision0 IxAICombined.Deployed.cardCertified; do
  i=$((i + 1))
  systemd-run --user --scope -q -p MemoryMax=180G -p MemorySwapMax=0 -- \
    /usr/bin/time -v -o "$out/c$i.time" timeout "${CHECK_CAP:-2400}" \
    "$project/.truthmines/kernel-subst/bin/ixf" "$variant" check --ixe "$env" "$name" > "$out/c$i.log" 2>&1
  st=$?
  printf '%s\t%s\t%s\t%s\t%s\n' "$name" "$st" \
    "$(grep -oE '\(([0-9]+) queries' "$out/c$i.log" | tail -1 | tr -dc 0-9)" \
    "$(grep Elapsed "$out/c$i.time" | awk '{print $NF}')" \
    "$(grep 'Maximum res' "$out/c$i.time" | awk '{print $NF}')" >> "$out/summary.tsv"
done
column -t -s$'\t' "$out/summary.tsv"
