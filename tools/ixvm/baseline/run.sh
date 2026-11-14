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
# does not stop the run. BENCH=0 skips the larger set; CORPUS=1 adds Init+Std in 24 shards
# (`corpus initstd shard K` and `corpus initstd total`).
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
if [ "${CORPUS:-0}" = 1 ]; then
  # Init+Std (the certified compile; --no-build, so the Benchmarks project and its Mathlib
  # requirement are not built), 24 static shards, every shard executed with the binding assumed.
  # One FFT line per shard, and the total, enter the baseline (about 20 min, 93 GB tree peak).
  t=$SECONDS
  lake build --wfail ix > "$OUT/corpus-build.log" 2>&1
  IX=$PWD/.lake/build/bin/ix
  lake env "$IX" compile-lean Benchmarks/Compile/CompileInitStd.lean --no-build --out "$OUT/initstd.ixe" \
    > "$OUT/corpus-compile.log" 2>&1
  lake env "$IX" shard "$OUT/initstd.ixe" --shards 24 --out "$OUT/initstd.ixes" > "$OUT/corpus-shard.log" 2>&1
  lake env "$IX" check --ixe "$OUT/initstd.ixe" --ixes "$OUT/initstd.ixes" --aiur-artifact "$OUT/ixvm.ixa" \
    --assume-binding --jobs 3 --keep-going --report "$OUT/initstd.report.json" > "$OUT/corpus-check.log" 2>&1
  "$PY" - "$OUT/initstd.report.json" > "$OUT/corpus.log" <<'PY'
import json, sys
r = json.load(open(sys.argv[1])); tot = 0
for leaf in r["leaves"]:
    for i, p in enumerate(leaf["parts"]):
        if p.get("status"):  # a refused part: no report, and no cost
            print(f"corpus initstd shard {leaf['shard']}.{i} ({len(p['blocks'])} blocks) refused"); continue
        c = (p.get("report") or {}).get("fft-cost") or 0; tot += c
        print(f"FFT corpus initstd shard {leaf['shard']}.{i} ({len(p['blocks'])} blocks): {c} (expected none)")
print(f"FFT corpus initstd total: {tot} (expected none)")
PY
  log "corpus rc=$? $((SECONDS-t))s; $(tail -n 1 "$OUT/corpus.log")"
  logs+=("$OUT/corpus.log")
fi
"$PY" "$HERE/baseline.py" extract "$OUT/out" "${logs[@]}" > "$OUT/baseline.json" 2> "$OUT/extract.txt"
log "$(tail -n 1 "$OUT/extract.txt")"
if [ -n "$REC" ]; then
  "$PY" "$HERE/baseline.py" diff "$REC" "$OUT/baseline.json" > "$OUT/diff.txt"
  log "$(head -n 1 "$OUT/diff.txt")"
fi
