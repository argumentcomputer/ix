# Runtime-v2 CSLib evidence

This directory preserves the compiler handoff and two new local native count
runs. The [executable artifacts](../../../flock-stage4/fixtures/cslib-runtime-v2/README.md)
are copied unchanged. The [performance report](../../../docs/IxbyPerformance.md)
uses these records to rank optimization opportunities.

## Imported complete observation

- [compiler-integration.json](compiler-integration.json): unchanged upstream
  record, including artifact/observer hashes, commitments, and all function counts.
- [import.json](import.json): source location, compiler checkout revision, and
  hash of the imported integration record.
- [inventory.json](inventory.json): names and block spans for 672 functions.
- [observer.json.gz](observer.json.gz): losslessly compressed complete report;
  its decompressed bytes match the upstream observer hash.
- [ExecutionProfile.lean](ExecutionProfile.lean) and [observer.time](observer.time):
  the compiler's observer source and process timing. The source uses its
  kernel-proved chunked simulation of the reference step and compares exact
  output at halt. It is retained for provenance and builds in Compilatrix.
- [groups.json](groups.json): explicit, disjoint function groups for this image.

The [reference summary](../cslib-runtime-v2-reference.json) checks the completed
360,337,913-transition run against the compiler record. Its 303,848,647 Eval
visits cover all block counts; 55,345,920 Return and 1,143,346 Apply control
transitions complete the total. Maxima are observations, not global bounds.

The [function cost record](../cslib-runtime-v2-costs.json) joins all block counts
to checked function spans. Reproduce it from the repository root, choosing a
new output filename:

```sh
python3 flock-stage3/profile/function_costs.py \
  --report flock-stage3/profile/cslib-runtime-v2/observer.json.gz \
  --inventory flock-stage3/profile/cslib-runtime-v2/inventory.json \
  --reference flock-stage3/profile/cslib-runtime-v2-reference.json \
  --program flock-stage4/fixtures/cslib-runtime-v2/program.ixby \
  --groups flock-stage3/profile/cslib-runtime-v2/groups.json \
  --output /tmp/cslib-v2-costs-recomputed.json
cmp /tmp/cslib-v2-costs-recomputed.json \
  flock-stage3/profile/cslib-runtime-v2-costs.json
```

The previous complete reference run was imported, not rerun locally. The
compiler comparison's revision-1 baseline is 2,033,412,182 transitions. Older
IxBy records for 2,268,502,805 transitions refer to a different earlier image.

## Local original-artifact checks

The native CLI reproduced the profile and statement; the reference summary
pins the binary used. To reproduce using a current release build:

```sh
cargo build --locked --release --manifest-path flock-stage4/Cargo.toml \
  -p ix-flock-recursion --bin paged-execution
cslib_fixture="$PWD/flock-stage4/fixtures/cslib-runtime-v2"
cslib_checks="$(mktemp -d)"
flock-stage4/target/release/paged-execution profile \
  --program "$cslib_fixture/program.ixby" --out "$cslib_checks/profile.ixfp"
cmp "$cslib_checks/profile.ixfp" "$cslib_fixture/profile.ixfp"
flock-stage4/target/release/paged-execution statement \
  --profile "$cslib_fixture/profile.ixfp" \
  --program "$cslib_fixture/program.ixby" --input "$cslib_fixture/input.ixbi" \
  --output "$cslib_fixture/output.ixbo" --out "$cslib_checks/expected.statement"
cmp "$cslib_checks/expected.statement" "$cslib_fixture/expected.statement"
```

These commands check artifact decoding and commitments; they do not prove or
execute the complete program.

## Local physical windows

[prefix.log](prefix.log) and [holdout.log](holdout.log) are two successful native
count-only harness runs, with process measurements in the corresponding
`.time` files. One trailing empty line is omitted; the physical summary also
pins each original process log. The harness calls the new workload `retained`; its printed
program/input BLAKE3 values identify these copied runtime-v2 artifacts.
Other logged workloads are the independent arithmetic, array, and builder
fixtures required by the existing harness.

The [physical summary](../cslib-runtime-v2-physical.json) contains only the new
CSLib windows, seven named class geometries, all 31 family counts, batch-stop
causes, and average complete-leaf occupancy. It also pins the existing measured
arithmetic model used for the explicitly labeled 193-day scale illustration.

The binary matches `leaf-tests-final` from the
[batch tuning record](../execution-batch-tuning-v0.json), and every source-file
pin in that record matched before collection. Native advice uses the existing
fast path, with per-row Boolean differential checking disabled as in that
benchmark. These count passes do not generate proofs or compare final output.

From the repository root:

```sh
python3 flock-stage4/fixtures/paged-execution-batch-sweep.py \
  --out /tmp/cslib-v2-count-fixtures
IXBY_QUOTA_FIXTURES=/tmp/cslib-v2-count-fixtures \
IXBY_QUOTA_RETAINED="$PWD/flock-stage4/fixtures/cslib-runtime-v2" \
IXBY_QUOTA_NAMED_ONLY=1 IXBY_QUOTA_MICROSTEPS=100000 \
cargo test --locked --release --manifest-path flock-stage3/Cargo.toml \
  -p ixby-flock --lib \
  ixby::paged_exec::quota_tests::physical_batch_quota_sweep \
  -- --exact --ignored --nocapture
```

Repeat with `IXBY_QUOTA_SKIP_MICROSTEPS=100000` for the adjacent second window.
The reusable `batch_tuning.census` parser checks success and extracts these
logs. Together the windows cover the first 48,599 logical transitions; they
are early occupancy samples, not a full-run proving forecast.
