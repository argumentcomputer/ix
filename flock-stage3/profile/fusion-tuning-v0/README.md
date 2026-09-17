# Interpreter fusion measurements

See the [results and checked compositions](../../../docs/IxbyFusion.md) and
[machine-readable report](../cslib-runtime-v2-fusion.json). The input is the
unchanged [runtime-v2 CSLib export](../../../flock-stage4/fixtures/cslib-runtime-v2/README.md).

## Evidence

- `wide-validation-0` through `wide-validation-5`: all 341 original captures,
  with the baseline, small fused class and a larger count-only candidate.
  Each `.time` file records the completed process and its resource use.
- `baseline-proof`, `fused-proof`, `baseline-chain`, `fused-chain`: newly
  measured genuine leaves and every recursive join for clocks 0–20,000,
  covering exactly 4,598 logical steps. Both trees have three leaves.
- `roots/*.statement/.flock`: the final roots. Statements are byte-identical;
  the baseline proof also matches the previously archived `cslib-2048` root.
- `native-differential.log`: 100,000 original microsteps with matching
  state, write order, cells and final roots at every composed boundary.
- `boolean-differential.log`: 10,000 original microsteps with native
  advice also compared against its Boolean plans.
- `*-tests-final.log`, `*-clippy-final.log`: ordinary tests and strict lint.
- `measurement.json`: exact source/binary/log receipts and experiment scope.

Logs lose trailing blank lines only. Their original and normalized receipts
are both retained in the measurement record. Intermediate proofs and all
raw captures remain in the experiment directory; the report pins their
receipts. The earlier [capture bundle](../cslib-tuning-v0/windows/) retains
13 compressed samples. All 341 capture receipts are in the
[complete native report](../cslib-runtime-v2-native.json).

The final checks, census and corrected fused proofs use the immutable v14
binaries from the pinned final source. The baseline measurements reuse v10;
the later changes affect fused wiring only, and the baseline root still
matches the earlier archive byte for byte. Final tests cover the compact-class
capacity fallback and inspect the compiled zero-cell authentication wiring.
Large proof jobs ran sequentially, with one worker, two threads, an 84 GiB cap
and no swap. Final checks and counting finished before corrected fused proofs.

## Build and check

Use the [build-once commands](../cslib-tuning-v0/README.md#build-once) from the
current checkout. They set `experiment`, `fixture` and `timer`, and copy the
release test executables to `$experiment/leaf-tests` and
`$experiment/tree-tests`. Commands here use Bash from the repository root.

```bash
"$experiment/leaf-tests" ixby::paged_exec:: --nocapture
"$experiment/leaf-tests" ixby::execution_order:: --nocapture
"$experiment/leaf-tests" ixby::memory_log:: --nocapture
"$experiment/tree-tests" --nocapture
cargo clippy --offline --locked --manifest-path flock-stage3/Cargo.toml \
  --workspace --all-targets -- -D warnings
cargo clippy --offline --locked --manifest-path flock-stage4/Cargo.toml \
  -p ix-flock-recursion --all-targets -- -D warnings

IXBY_FUSION_FIXTURE="$fixture" IXBY_FUSION_END_CLOCK=100000 \
  "$experiment/leaf-tests" \
  ixby::paged_exec::fusion_tests::original_fused_execution_matches_each_original_boundary \
  --exact --ignored --nocapture
IXBY_FUSION_FIXTURE="$fixture" IXBY_FUSION_END_CLOCK=10000 IXBY_FUSION_COMPARE=1 \
  "$experiment/leaf-tests" \
  ixby::paged_exec::fusion_tests::original_fused_execution_matches_each_original_boundary \
  --exact --ignored --nocapture
```

## Capture census

Reuse the original `.ixqp` captures, or regenerate them with the earlier
[complete-native-run command](../cslib-tuning-v0/README.md#native-profile-and-all-capture-replays).
Set `captures` to that directory. Rust validates each capture's source hashes,
clock, fuel, chip/access widths, address bounds and exact end of file.

```bash
captures=/path/to/original/full
python3 - "$experiment" "$fixture" "$captures" "$timer" <<'PY'
import os, subprocess, sys
from pathlib import Path
p, fixture, captures, timer = map(Path, sys.argv[1:])
starts = sorted(int(f.stem.removeprefix("window-")) for f in captures.glob("*.ixqp"))
assert len(starts) == 341
for shard, at in enumerate(range(0, len(starts), 64)):
    name = f"wide-validation-{shard}"
    env = dict(os.environ, IXBY_FUSION_FIXTURE=str(fixture),
               IXBY_FUSION_WINDOWS=str(captures), IXBY_FUSION_SCALES="2752",
               IXBY_FUSION_STARTS=",".join(map(str, starts[at:at + 64])),
               RAYON_NUM_THREADS="1", MALLOC_ARENA_MAX="2")
    with (p / f"{name}.log").open("x") as log:
        subprocess.run([str(timer), "-v", "-o", str(p / f"{name}.time"),
                        str(p / "leaf-tests"),
                        "ixby::paged_exec::fusion_census::captured_fusion_quota_census",
                        "--exact", "--ignored", "--nocapture"],
                       env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
PY
```

`IXBY_FUSION_NAMED_ONLY=1` skips count-only shapes. `IXBY_FUSION_SCALES`
accepts comma-separated proportional sizes from 512 through 4096;
`IXBY_FUSION_SWEEP=1` additionally varies cell/parent capacities. Optional
`IXBY_FUSION_CANDIDATE` reads cells, parents, 31 ordinary quotas and eight
fused quotas from a whitespace-separated file. These options affect only the
ignored counter test, never the production verifier's approved classes.

For a short replay, decompress selected archived captures and set
`IXBY_FUSION_STARTS` to those clocks. The full report builder requires every
capture in its input native report, so a partial replay is a separate census.

## Matched leaf proofs and complete trees

Run large proof jobs sequentially. Each leaf output directory must be new.

```bash
for spec in baseline:cslib-2048 fused:cslib-fused; do
  name=${spec%%:*}
  class=${spec#*:}
  systemd-run --user --scope --quiet -p MemoryMax=84G -p MemorySwapMax=0 \
    env IXBY_PAGED_PROGRAM="$fixture/program.ixby" IXBY_PAGED_INPUT="$fixture/input.ixbi" \
    IXBY_PAGED_NATIVE_CLASS="$class" IXBY_PROOF_END_CLOCK=20000 IXBY_PROOF_BATCHES=32 \
    IXBY_PROOF_WORKERS=1 IXBY_PROOF_THREADS=2 IXBY_PROOF_OUT="$experiment/$name-proofs" \
    RAYON_NUM_THREADS=2 MALLOC_ARENA_MAX=2 \
    "$timer" -v -o "$experiment/$name-proof.time" "$experiment/leaf-tests" \
    ixby::paged_exec::benchmark_tests::original_execution_proof_throughput \
    --exact --ignored --nocapture > "$experiment/$name-proof.log" 2>&1
  mkdir "$experiment/$name-chain"
  systemd-run --user --scope --quiet -p MemoryMax=84G -p MemorySwapMax=0 \
    env IXBY_EXECUTION_CHAIN_CLASS="$class" IXBY_EXECUTION_CHAIN_LEAVES=3 \
    IXBY_LARGE_EXECUTION_PROOFS="$experiment/$name-proofs" \
    IXBY_LARGE_EXECUTION_CHAIN_OUT="$experiment/$name-chain" \
    RAYON_NUM_THREADS=2 MALLOC_ARENA_MAX=2 \
    "$timer" -v -o "$experiment/$name-chain.time" "$experiment/tree-tests" \
    execution_tree::tests::large_execution::execution_range_chain_proves_fresh \
    --exact --ignored --nocapture > "$experiment/$name-chain.log" 2>&1
done
```

The receivers rebuild the selected setup in a fresh process and reject all
114 public-word mutations, truncation and trailing bytes. To check an archived
root directly, concatenate its `.statement` and `.flock` on stdin to the same
tree test with `IXBY_LARGE_EXECUTION_CHAIN_RECEIVER=1`, the corresponding
`IXBY_EXECUTION_CHAIN_CLASS`, and `IXBY_EXECUTION_CHAIN_LEAVES=3`.

## Assemble the report

```bash
python3 -B flock-stage3/profile/fusion_tuning.py --root "$experiment" \
  --native-report flock-stage3/profile/cslib-runtime-v2-native.json --windows "$captures" \
  --census "$experiment/wide-validation-0.log" --census "$experiment/wide-validation-1.log" \
  --census "$experiment/wide-validation-2.log" --census "$experiment/wide-validation-3.log" \
  --census "$experiment/wide-validation-4.log" --census "$experiment/wide-validation-5.log" \
  --run baseline:cslib-2048 --run fused:cslib-fused --out "$experiment/fusion.json"
```

This validates measurements and receipts; the recorded Rust tests perform
proof verification. Reproduction can change timings and binary/proof bytes.
Preserve the source commitments, circuit identities, exact public boundaries
and counted capacities. No result here proves the complete CSLib execution.
