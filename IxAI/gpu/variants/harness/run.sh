#!/usr/bin/env bash
# run.sh VARIANT...: every measurement and digest of each variant's prebuilt binaries. Builds nothing.
set -uo pipefail
D=/opt/dlami/nvme/ix-ai/review2-gpu/r2
P=/opt/dlami/nvme/ix-ai/review2-gpu/full.problem
T=/home/sam/repos/ix-ai-pipeline/.truthmines/gpu/test-final
B3=/nix/store/559xmrh264rdimgbp16a0ahgsybqaqp2-b3sum-1.8.7/bin/b3sum
declare -A configs=([tiny]="42 4 2 1 8 16 16" [small]="42 8 2 2 16 64 32" [medium]="42 16 2 3 20 400 200" [large]="42 16 2 10 20 400 200" [full]="42 16 2 30 20 400 200")
for v in "$@"; do
  b=$D/bin/$v; out=$D/results/$v; mkdir -p $out
  {
    echo "== variant $v ($(date +%T)), step.cu $($B3 --no-names $D/src/$v/step.cu | cut -c1-16)"
    nvidia-smi --query-gpu=name,utilization.gpu,memory.used,clocks.sm --format=csv,noheader
    [ -x $b/error_test ] && { $b/error_test; echo "error_test exit $?"; }
    $b/bench full $P 6
    for p in 0 2; do $b/bench shape 8 16 11 20 300 $p; done
    for p in 0 1; do $b/bench shape 1024 1024 1024 1024 20 $p; done
    $b/bench shape 2048 2048 2048 2048 10 0
    $b/bench shape 256 512 128 300 50 0
    $b/bench trace 8 16 11 20 300 0
    $b/bench trace 1024 1024 1024 1024 20 0
    $b/bench trace 2048 2048 2048 2048 10 0
    $b/bench sweep
    for size in tiny small medium large full; do
      $b/ixai_gpu train ${configs[$size]} > $out/$size.weights 2> $out/$size.log
      echo "lean train $size: weights $($B3 --no-names $out/$size.weights | cut -c1-16) $(cmp -s $out/$size.weights $T/$size.spec.weights && echo equal-to-spec || echo DIFFER-from-spec); $(cat $out/$size.log)"
    done
    $b/ixai_gpu keys ${configs[full]} > $out/full.keys
    echo "lean keys full: $($B3 --no-names $out/full.keys | cut -c1-16) $(cmp -s $out/full.keys $T/full.spec.keys && echo equal-to-spec || echo DIFFER-from-spec)"
    for i in 1 2 3; do echo "lean train full timing: $( { /usr/bin/time -f '%e s wall' $b/ixai_gpu train ${configs[full]} > /dev/null; } 2>&1 | tr '\n' ' ')"; done
    $b/ixai_gpu bench 1024 1024 1024 1024 10
    $b/ixai_gpu bench 8 16 11 20 50
    echo "== end $v ($(date +%T))"
  } > $out/run.txt 2>&1
done
