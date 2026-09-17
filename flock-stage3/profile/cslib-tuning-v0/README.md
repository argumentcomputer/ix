# Complete CSLib native profiling and quota tuning

See [the results](../../../docs/IxbyCslibTuning.md),
[native report](../cslib-runtime-v2-native.json), and
[proof/tuning report](../cslib-runtime-v2-tuning.json).

The sources are the unchanged [runtime-v2 artifacts](../../../flock-stage4/fixtures/cslib-runtime-v2/README.md).
The complete run uses direct native advice and checks the expected output and
360,337,913 fuel charges. `native_profile.py` independently compares all 5,816
block counts and the three charged control phases with the compiler observer.
It does not verify a Flock proof.

## Retained evidence

- `full.log/.time`: complete native execution and resource use.
- `pilot`, `timed-pilot`, `fast-pilot`: matched million-row timing samples.
  Chip nanoseconds measure the native producer, not constraint/proof costs.
- `compare-pilot.log`: 100,000 original CSLib steps with native/Boolean
  comparison enabled. `numeric-differential.log` and `exact-boundaries.log`
  record the targeted arithmetic and boundary checks.
- `early-census`, `max-census`, `bulk-census`: average-ratio exploration,
  maximum-ratio tuning, then explicit builder/hash/equality capacity.
- `validation-0` through `validation-5`: exact replays of all 341 captures,
  in groups of at most 64 windows, for eight named classes.
- `baseline-proof`, `cslib-proof`, `baseline-chain`, `cslib-chain`: actual
  leaf and recursive proofs for physical clocks 0–20,000, including separate
  root receivers and mutation/truncation rejection.
- `*-tests-final.log` and `*-clippy-final.log`: regression and lint checks.
- `windows/*.ixqp.gz`: 13 selected captures, compressed losslessly with a
  fixed gzip timestamp. The complete manifest is in the native report.
- `measurement.json`: producer versions, source pins, selection windows,
  and the distinction between native execution and proof claims.
- `roots/*.flock/.statement`: both final recursive proofs and their identical
  public statement, for verification without rerunning the leaf producers.

Trailing blank lines are removed from archived logs. `original-log-pins.json`
records their original bytes before that normalization. Measurements and
test output are otherwise unchanged. Leaf proofs, intermediate proofs and the
remaining raw captures stay in the experiment directory; the reports record
their sizes and SHA256 digests. Both final roots are archived here.

The full native profile used the first accelerated test binary. The baseline
proof binary subsequently added exact range stopping. The final binary adds
quota-census options, tests and the new class. The native calculations are
the same across these versions; older classes retain their setup identities.
Rebuilding the final source can reproduce all experiments.

## Build once

Commands below are Bash, run from the repository root. The measurements used
Rust/Cargo 1.98.1 and the locked dependencies. Offline builds require the
dependencies to be available locally.

```bash
experiment=$(mktemp -d /tmp/ixby-cslib.XXXXXX)
fixture="$PWD/flock-stage4/fixtures/cslib-runtime-v2"
timer=$(type -P time)
cargo test --offline --locked --release --manifest-path flock-stage3/Cargo.toml \
  -p ixby-flock --lib --no-run --message-format=json > "$experiment/leaf-build.jsonl"
cargo test --offline --locked --release --manifest-path flock-stage4/Cargo.toml \
  -p ix-flock-recursion --lib --no-run --message-format=json > "$experiment/tree-build.jsonl"
python3 - "$experiment" <<'PY'
import json, shutil, sys
from pathlib import Path
p = Path(sys.argv[1])
for stem, target in [("leaf", "ixby_flock"), ("tree", "ix_flock_recursion")]:
    entries = [json.loads(s) for s in (p / f"{stem}-build.jsonl").read_text().splitlines()]
    binaries = [e["executable"] for e in entries
                if e.get("executable") and e["target"]["name"] == target]
    assert len(binaries) == 1
    shutil.copy2(binaries[0], p / f"{stem}-tests")
PY
```

## Native profile and all capture replays

Use a fresh output directory. The profiler enforces fixed capture bounds and
checks the original output when it halts. `IXBY_PROFILE_COMPARE=1` enables the
expensive Boolean differential path; it was used only for the bounded check.

```bash
systemd-run --user --scope --quiet -p MemoryMax=32G -p MemorySwapMax=0 \
  env IXBY_PROFILE_FIXTURE="$fixture" IXBY_PROFILE_OUT="$experiment/full" \
  IXBY_PROFILE_EXPECTED_STEPS=360337913 IXBY_PROFILE_WINDOW_STRIDE=5000000 \
  IXBY_PROFILE_WINDOW_ROWS=100000 IXBY_PROFILE_PROGRESS=5000000 \
  "$timer" -v -o "$experiment/full.time" "$experiment/leaf-tests" \
  ixby::paged_exec::profile_tests::streaming_native_execution_profile \
  --exact --ignored --nocapture > "$experiment/full.log" 2>&1

python3 - "$experiment" "$fixture" "$timer" <<'PY'
import os, subprocess, sys
from pathlib import Path
p, fixture, timer = Path(sys.argv[1]), sys.argv[2], sys.argv[3]
starts = sorted(int(f.stem.removeprefix("window-")) for f in (p / "full").glob("*.ixqp"))
for shard, at in enumerate(range(0, len(starts), 64)):
    env = dict(os.environ, IXBY_PROFILE_FIXTURE=fixture, IXBY_PROFILE_OUT=str(p / "full"),
               IXBY_PROFILE_WINDOW_STARTS=",".join(map(str, starts[at:at + 64])),
               IXBY_QUOTA_NAMED_ONLY="1")
    with (p / f"validation-{shard}.log").open("w") as log:
        subprocess.run([timer, "-v", "-o", str(p / f"validation-{shard}.time"),
                        str(p / "leaf-tests"),
                        "ixby::paged_exec::profile_tests::captured_window_quota_census",
                        "--exact", "--ignored", "--nocapture"],
                       env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
PY
```

For a short replay without rerunning native execution, decompress the selected
`windows/*.ixqp.gz` into a new directory and set `IXBY_PROFILE_OUT` to it.
Set `IXBY_PROFILE_WINDOW_STARTS` to those file clocks. The Rust reader checks
the original program/input hashes, clock, fuel, chip/access widths, address
bounds and exact end of file.

To reproduce the adaptive sweep, select clocks
`0,55000000,115000000,195000000,380000000,390000000,520000000,670000000,710000000`,
set `IXBY_QUOTA_TRAINING_STARTS=0,55000000,115000000,195000000,380000000`,
set `IXBY_QUOTA_BULK=1`, and omit `IXBY_QUOTA_NAMED_ONLY`. The original average
experiment predates the maximum-ratio change and remains archived for context.

## Equal-work proofs and all recursive joins

Each benchmark creates its output directory and fails if it already exists.
The 32-batch bound is a hard limit; the benchmark must reach physical clock
20,000 exactly. Run the two large proof jobs sequentially.

```bash
for spec in baseline:shared-linked-1024 cslib:cslib-2048; do
  name=${spec%%:*}
  class=${spec#*:}
  systemd-run --user --scope --quiet -p MemoryMax=84G -p MemorySwapMax=0 \
    env IXBY_PAGED_PROGRAM="$fixture/program.ixby" IXBY_PAGED_INPUT="$fixture/input.ixbi" \
    IXBY_PAGED_NATIVE_CLASS="$class" IXBY_PROOF_END_CLOCK=20000 IXBY_PROOF_BATCHES=32 \
    IXBY_PROOF_WORKERS=1 IXBY_PROOF_THREADS=2 IXBY_PROOF_OUT="$experiment/$name-proofs" \
    MALLOC_ARENA_MAX=2 "$timer" -v -o "$experiment/$name-proof.time" \
    "$experiment/leaf-tests" ixby::paged_exec::benchmark_tests::original_execution_proof_throughput \
    --exact --ignored --nocapture > "$experiment/$name-proof.log" 2>&1
  leaves=$(python3 -c 'import pathlib,sys; print(len(list(pathlib.Path(sys.argv[1]).glob("*.statement"))))' \
    "$experiment/$name-proofs")
  mkdir "$experiment/$name-chain"
  systemd-run --user --scope --quiet -p MemoryMax=84G -p MemorySwapMax=0 \
    env IXBY_EXECUTION_CHAIN_CLASS="$class" IXBY_EXECUTION_CHAIN_LEAVES="$leaves" \
    IXBY_LARGE_EXECUTION_PROOFS="$experiment/$name-proofs" \
    IXBY_LARGE_EXECUTION_CHAIN_OUT="$experiment/$name-chain" \
    RAYON_NUM_THREADS=2 MALLOC_ARENA_MAX=2 \
    "$timer" -v -o "$experiment/$name-chain.time" "$experiment/tree-tests" \
    execution_tree::tests::large_execution::execution_range_chain_proves_fresh \
    --exact --ignored --nocapture > "$experiment/$name-chain.log" 2>&1
done
```

## Assemble the reports

The native report requires a completed run, the exact compiler counters,
and every recorded capture. The proof report requires successful producer
and receiver logs, proof/statement files with matching receipts, all joins,
and byte-identical root statements across classes.

```bash
python3 -B flock-stage3/profile/native_profile.py \
  --log "$experiment/full.log" --time "$experiment/full.time" \
  --binary "$experiment/leaf-tests" --fixture "$fixture" \
  --observer flock-stage3/profile/cslib-runtime-v2/observer.json.gz \
  --inventory flock-stage3/profile/cslib-runtime-v2/inventory.json \
  --windows "$experiment/full" --out "$experiment/native.json"
python3 -B flock-stage3/profile/cslib_tuning.py --root "$experiment" \
  --native-report "$experiment/native.json" \
  --census "$experiment/validation-0.log" --census "$experiment/validation-1.log" \
  --census "$experiment/validation-2.log" --census "$experiment/validation-3.log" \
  --census "$experiment/validation-4.log" --census "$experiment/validation-5.log" \
  --run baseline:shared-linked-1024 --run cslib:cslib-2048 \
  --out "$experiment/tuning.json"
```

Timings, proof bytes and executable hashes may differ on reproduction.
Counter agreement, circuit identities, class capacities and the public
execution boundaries are the checks to preserve.

To verify an archived root directly, concatenate its `.statement` and `.flock`
files on stdin to the same tree test, with `IXBY_LARGE_EXECUTION_CHAIN_RECEIVER=1`,
the selected `IXBY_EXECUTION_CHAIN_CLASS`, and `IXBY_EXECUTION_CHAIN_LEAVES=7`
for the baseline or `3` for `cslib-2048`. The receiver compiles the selected
setup, checks the proof, and runs the public-word and framing rejection checks.
