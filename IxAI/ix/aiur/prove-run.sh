#!/usr/bin/env bash
# Export every SGD step of the full run as an Aiur execution package and prove each one on the GPU.
#   prove-run.sh OUT_DIR COUNT
set -euo pipefail
W=/home/sam/repos/ix.ixai-aiur
out="$1"; count="$2"
mkdir -p "$out"
start=$(date +%s)
"$W/Aiur/.lake/build/bin/ixai_step" all "$out" "$count"
export LD_LIBRARY_PATH="$W/target/release/build/multi-stark-becb7b956815cc03/out"
export LD_PRELOAD=/usr/lib/x86_64-linux-gnu/libcuda.so.1
for pkg in "$out"/step-*.ixa; do
  base="${pkg%.ixa}"
  "$W/target/release/examples/prove" "$pkg" "$base.proof" "$base.report.json" > "$base.log" 2>&1 \
    || { echo "prove failed: $pkg"; exit 1; }
done
echo "exported and proved $count steps in $(( $(date +%s) - start ))s"
