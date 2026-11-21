#!/usr/bin/env bash
# Build ixai_gpu from the current gpu/cuda sources and the Aiur package's existing Lean objects.
set -euo pipefail
D=/opt/dlami/nvme/ix-ai/review2-gpu/build
A=/home/sam/repos/ix.ixai-aiur/Aiur/.lake/build
L=/nix/store/xnh27vasww8vbnh7a18g3xkdg1r4kl6w-lean-4.34.1
src=${1:-/home/sam/repos/ix-ai-pipeline/gpu/cuda}
out=${2:-$D}
mkdir -p $out
/usr/local/cuda-13.3/bin/nvcc -c -o $out/step.o $src/step.cu --std=c++17 --cudart=static --default-stream=per-thread -O3 -lineinfo --compiler-options=-fPIC -gencode=arch=compute_120,code=sm_120
cc -c -o $out/ixai_gpu.o $src/ixai_gpu.c -I $L/include -O2 -fPIC -Wall -Wextra
sed -e "s|\"$A/cuda/ixai_gpu.o\"|\"$out/ixai_gpu.o\"|" -e "s|\"$A/cuda/step.o\"|\"$out/step.o\"|" $A/bin/ixai_gpu.rsp > $out/ixai_gpu.rsp
grep -c "$out/step.o" $out/ixai_gpu.rsp
PATH=/nix/store/nla41igcnyykzirqfs1fi167ssxhc37p-lld-21.1.2/bin:$PATH $L/bin/clang -o $out/ixai_gpu @$out/ixai_gpu.rsp
echo built $out/ixai_gpu
