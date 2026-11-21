#!/usr/bin/env bash
# build.sh VARIANT: the timing harness and the Lean trainer `ixai_gpu` from r2/src/VARIANT.
set -euo pipefail
D=/opt/dlami/nvme/ix-ai/review2-gpu/r2
v=$1; src=$D/src/$v; out=$D/bin/$v
mkdir -p $out
C=/usr/local/cuda-13.3
$C/bin/nvcc --std=c++17 -O3 --default-stream=per-thread -gencode=arch=compute_120,code=sm_120 \
  -diag-suppress 177 -I$C/extras/CUPTI/include -DSTEP_CU="\"$src/step.cu\"" -o $out/bench $D/bench2.cu \
  -L$C/extras/CUPTI/lib64 -lcupti -Xlinker -rpath=$C/extras/CUPTI/lib64 > $out/bench.build.log 2>&1 || { cat $out/bench.build.log; exit 1; }
test -x $out/bench
/opt/dlami/nvme/ix-ai/review2-gpu/build/relink.sh $src $out > $out/relink.log 2>&1 || { cat $out/relink.log; exit 1; }
echo "built $out/bench $out/ixai_gpu"
/usr/local/cuda-13.3/bin/nvcc --std=c++17 --default-stream=per-thread -O3 -gencode=arch=compute_120,code=sm_120 \
  -o $out/error_test $src/step.cu $D/error_test.cu > $out/error_test.build.log 2>&1 || { cat $out/error_test.build.log; exit 1; }
echo "built $out/error_test"
