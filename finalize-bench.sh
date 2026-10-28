#!/usr/bin/env bash
set -euo pipefail
export LEAN_NUM_THREADS=8
export CARGO_BUILD_JOBS=8
unset CARGO_TARGET_DIR IX_SHARING_LIMITS
cd /home/john/runs/perfspec/src
baseline=/home/john/runs/compiler/src/.lake/build/bin/ix
sha256sum "$baseline" > "$RUN_OUT/baseline-before.sha256"
cp "$baseline" "$RUN_OUT/ix-baseline"
sha256sum "$baseline" > "$RUN_OUT/baseline-after.sha256"
cmp "$RUN_OUT/baseline-before.sha256" "$RUN_OUT/baseline-after.sha256"
sha256sum "$RUN_OUT/ix-baseline" > "$RUN_OUT/baseline-copy.sha256"
cp /home/john/runs/compiler/synced.txt "$RUN_OUT/baseline-synced.txt"
lake build --wfail ix IxTests > "$RUN_OUT/build.log" 2>&1 || { tail -80 "$RUN_OUT/build.log"; exit 1; }
.lake/build/bin/IxTests --list > "$RUN_OUT/tests-list.txt" 2>&1
printf '%s\n' 'build complete'
