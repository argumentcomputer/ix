#!/usr/bin/env bash
# Rerun the IxVM cost baseline on the checked-out commit and diff it against a
# recorded one. Run from the repository root inside `nix develop`:
#
#   tools/ixvm/baseline/run.sh OUT [RECORDED.json]
#
# OUT receives: ixvm.ixa (the exported claim artifact), out/ (case files and
# sidecars), *.log, baseline.json and, with RECORDED.json, diff.txt.
# What runs: the 151 pinned claims (`ixvm-kernel-checks`, `ixvm-eval`; their
# FFT lines are authoritative) and, when the commit registers it, the larger
# set `ixvm-s4-bench` (declaration shards, closure checks, Std shards). The
# host writes per-function rows (IXVM_FUNCTION_STATS=1); circuit statistics do
# not depend on it. A pin mismatch is reported in the log and in the diff, and
# does not stop the run. BENCH=0 skips the larger set.
set -u
OUT=${1:?usage: run.sh OUT [RECORDED.json]}; REC=${2:-}
mkdir -p "$OUT"
OUT=$(realpath "$OUT")
PY=${PYTHON:-/usr/bin/python3}
HERE=$(dirname "$(realpath "$0")")
log() { echo "[baseline] $*" | tee -a "$OUT/run.txt"; }
: > "$OUT/run.txt"
log "commit $(git rev-parse HEAD) $(date -u +%FT%TZ)"
lake build --wfail IxTests ixvm/ixvm > "$OUT/build.log" 2>&1 || { log "build failed"; exit 1; }
cargo build --release --locked -p ixvm --bin ixvm-proof --features parallel > "$OUT/host.log" 2>&1 \
  || { log "host build failed"; exit 1; }
cp target/release/ixvm-proof "$OUT/ixvm-proof"
lake env IxVM/.lake/build/bin/ixvm export-claim-trace "$OUT/ixvm.ixa" > "$OUT/export.log" 2>&1 \
  || { log "export failed"; exit 1; }
log "artifact sha256 $(sha256sum "$OUT/ixvm.ixa" | cut -c1-16)"
export IX_AIUR_HOST="$OUT/ixvm-proof" IX_AIUR_ARTIFACT="$OUT/ixvm.ixa" IX_TEST_OUTPUT_DIR="$OUT/out"
export IXVM_FUNCTION_STATS=1
t=$SECONDS
lake test --wfail -- ixvm-kernel-checks ixvm-eval > "$OUT/pins.log" 2>&1
log "pinned suites rc=$? $((SECONDS-t))s; $(grep -c '^FFT ' "$OUT/pins.log") FFT lines, $(grep -c '^FAILED' "$OUT/pins.log") FAILED lines"
logs=("$OUT/pins.log")
if [ "${BENCH:-1}" = 1 ] && grep -q '"ixvm-s4-bench"' Tests/Main.lean; then
  t=$SECONDS
  lake test --wfail -- ixvm-s4-bench > "$OUT/bench.log" 2>&1
  log "bench rc=$? $((SECONDS-t))s; $(grep -c '^FFT ' "$OUT/bench.log") FFT lines"
  logs+=("$OUT/bench.log")
fi
"$PY" "$HERE/baseline.py" extract "$OUT/out" "${logs[@]}" > "$OUT/baseline.json" 2> "$OUT/extract.txt"
log "$(tail -n 1 "$OUT/extract.txt")"
if [ -n "$REC" ]; then
  "$PY" "$HERE/baseline.py" diff "$REC" "$OUT/baseline.json" > "$OUT/diff.txt"
  log "$(head -n 1 "$OUT/diff.txt")"
fi
