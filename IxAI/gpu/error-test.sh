#!/usr/bin/env bash
# CUDA error reporting of the kernels' C entry points (`cuda/error_test.cu`). Run through
# ix/heavy.sh.
#   gpu/error-test.sh OUT_DIR
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
out="${1:?usage: error-test.sh OUT_DIR}"
mkdir -p "$out"
"${NVCC:-nvcc}" --std=c++17 --default-stream=per-thread -O3 -arch=native \
  -o "$out/error_test" "$here/cuda/step.cu" "$here/cuda/error_test.cu"
"$out/error_test"
