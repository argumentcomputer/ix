#!/usr/bin/env bash
# Differential tests of the GPU trainer against the Lean spec. Run through ix/heavy.sh.
#   gpu/test.sh OUT_DIR
# The trainer is `ixai_gpu`, the Lean host `IxAIGpuHost` in the ix.ixai-aiur Aiur package (built
# with `lake build ixai_gpu ixai_step` there), over the kernels in gpu/cuda.
# * every triage config: final weights equal `ixai weights SIZE`, and every step's hint keys equal
#   `hostStepHintKeys` (`ixai-gpu-export keys`);
# * random single steps of random shapes and values equal `Model.step`, on the default GEMM path
#   and with every GEMM on tensor cores where the operands fit;
# * the full run's `Fixed::step` execution packages equal, byte for byte, the ones the host
#   exports with the same build of the program (`ixai_step all`).
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
out="${1:?usage: test.sh OUT_DIR}"
mkdir -p "$out"
export_="$root/.lake/build/bin/ixai-gpu-export"
gpu="${IXAI_GPU:-/home/sam/repos/ix.ixai-aiur/Aiur/.lake/build/bin/ixai_gpu}"
step="${IXAI_STEP:-/home/sam/repos/ix.ixai-aiur/Aiur/.lake/build/bin/ixai_step}"
ixai="$root/.lake/build/bin/ixai"
# Mirrors `triageConfigs` in Ixai.lean: SEED HIDDEN LR EPOCHS BATCH TRAIN TEST. A drift shows up
# as a weights mismatch against `ixai weights`.
declare -A configs=(
  [tiny]="42 4 2 1 8 16 16"
  [small]="42 8 2 2 16 64 32"
  [medium]="42 16 2 3 20 400 200"
  [large]="42 16 2 10 20 400 200"
  [full]="42 16 2 30 20 400 200"
)
status=0
for size in tiny small medium large full; do
  "$gpu" train ${configs[$size]} > "$out/$size.gpu.weights" 2> "$out/$size.gpu.log"
  "$ixai" weights "$size" > "$out/$size.spec.weights"
  "$export_" keys ${configs[$size]} > "$out/$size.spec.keys"
  "$gpu" keys ${configs[$size]} > "$out/$size.gpu.keys"
  w=$(cmp -s "$out/$size.gpu.weights" "$out/$size.spec.weights" && echo equal || echo DIFFER)
  k=$(cmp -s "$out/$size.gpu.keys" "$out/$size.spec.keys" && echo equal || echo DIFFER)
  steps=$(grep -c '^keys ' "$out/$size.spec.keys")
  echo "$size: $steps steps; final weights $w to ixai weights; hint keys of every step $k ($(cat "$out/$size.gpu.log"))"
  [ "$w$k" = equalequal ] || status=1
done
"$export_" random 20261118 300 > "$out/random.cases"
"$gpu" check "$out/random.cases" || status=1
"$gpu" check "$out/random.cases" 2 || status=1
host="$out/host-packages"
"$step" all "$host" 600 > "$out/host-packages.log"
"$gpu" package "$out/packages" > "$out/packages.log"
same=0; n=0
for f in "$host"/step-*.ixa; do
  n=$((n + 1))
  cmp -s "$f" "$out/packages/$(basename "$f")" && same=$((same + 1))
done
e=$(cmp -s "$out/packages/expected.txt" "$host/expected.txt" && echo equal || echo DIFFER)
echo "full: $same of $n GPU execution packages byte-identical to the host's; expected.txt $e"
[ "$same" = "$n" ] && [ "$n" -gt 0 ] && [ "$e" = equal ] || status=1
exit $status
