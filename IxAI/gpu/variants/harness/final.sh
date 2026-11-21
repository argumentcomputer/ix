#!/usr/bin/env bash
# final.sh: the project's GPU tests against the installed gpu/cuda sources (trainer prebuilt in bin/final).
set -uo pipefail
D=/opt/dlami/nvme/ix-ai/review2-gpu/r2
R=/home/sam/repos/ix-ai-pipeline
out=$D/results/final; mkdir -p $out
cd $R
echo "== gpu/test.sh ($(date +%T))"
IXAI_GPU=$D/bin/final/ixai_gpu gpu/test.sh $out/test; echo "test.sh exit $?"
echo "== gpu/error-test.sh ($(date +%T))"
PATH=/usr/local/cuda-13.3/bin:$PATH gpu/error-test.sh $out/error; echo "error-test.sh exit $?"
echo "== end ($(date +%T))"
