# Formal Aiur in Ix

The new implementation is imported from `aiur` commit
`7584bf5` on `bench/ixvm-audit`. Its compiler correctness proofs are retained;
the Lean sources are adapted to Ix's Lean/Mathlib 4.34.1 toolchain. In particular,
the Aiur package selects Lean's legacy `do` elaborator to preserve the verified
monadic definitions from 4.29. Proof adaptations do not add axioms or `sorry`.

## Package boundaries

| Component | Lean package/library | Rust crate |
| --- | --- | --- |
| Generic language, compiler, proofs, libraries | `Aiur/` / `Aiur` | `crates/aiur` |
| IxVM claim verifier and host | `IxVM/` / `IxVM` | `crates/ixvm` |
| Recursive verifier and aggregation program | `MultiStark/` / `MultiStark` | `crates/stark-verifier` |
| Shared verifying-key and range-advice codecs | — | `crates/stark-key` |
| Existing language and prover | `LegacyAiur` | `crates/aiur-legacy` |
| Existing IxVM and recursive verifier | `LegacyIxVM`, `LegacyMultiStark` | `crates/ixvm-legacy` |
| Existing generated execution kernels | generator in `LegacyAiur` | `crates/ixvm-legacy-native` (optional) |

The generic Aiur crate does not depend on IxVM, the legacy interpreter, or a
Lean installation. The IxVM crate registers its hint channels and table
accelerators using Aiur's generic APIs. Its Rust binary accepts an exported
execution package. Lean's `IxVM.parse` loads the application and its shared
Goldilocks word/hash library; callers select entrypoints with
`Aiur.Modules.prepare`.

Aiur owns the FFI: `Aiur/c/execution.c` adapts Lean objects to the JSON C ABI
exported by the Rust `aiur` static library. Lake's `aiur/execution_o` and
`aiur/aiur_rs` targets are linked only by executables that use it. The IxVM
export driver builds without Rust and invokes the separate `ixvm` host for
execution with its application hint providers. Pure Lean library/proof builds
do not run Cargo. Cargo builds do not invoke Lake. Serialization remains the
current bridge; this migration does not replace it with a direct object ABI.
The old experimental IxVM
`ffi` replay command is removed: the data-only ABI cannot supply the word
library's closure hints. Generic Aiur FFI execution and tracing remain covered
by their own test executables.

## Build and run

From the repository root:

```sh
lake -d Aiur build
lake -d Aiur test
cargo test --locked -p aiur -p ixvm --features parallel --all-targets

lake -d IxVM build ixvm
lake -d IxVM exe ixvm export /tmp/ixvm-execution.json
cargo run --release --locked -p ixvm -- /tmp/ixvm-execution.json all

lake -d IxVM exe ixvm export-trace /tmp/ixvm-trace.json
cargo run --release --locked -p ixvm --features parallel --example ixvm_bench -- \
  /tmp/ixvm-trace.json IxVM/IxVM/fixtures/nat-add-comm.json witness 1
```

The last command executes bytecode, generates traces, and proves and verifies
the fixed fixture. `stats` exports per-function stage-one widths. These drivers
also work from the root Lake workspace as `lake exe ixvm/ixvm ...`.

## Current port and CLI integration

The application port now follows Ix revision
`827550579ea660a4749c520968ad6f58be63acf4`, including the current claim dispatcher,
evaluation, environment checking, reveal and membership claims. It contains
809 application source functions; the claim execution export contains 831
bytecode functions including shared libraries. The generic Aiur proofs have
not changed in this update.

The ordinary commands now select new Aiur. Pass `--legacy` to use the retained
implementation. `--formal` remains a compatibility alias and conflicts with
`--legacy`:

```sh
ix check Nat.add_comm
ix prove Nat.add_comm
ix verify <proof-address>

ix prove --ixe env.ixe --ixes env.ixes --shard-rows 65536
ix verify --ixe env.ixe --ixes env.ixes <shard-proof-address>...
ix aggregate --ixe env.ixe --ixes env.ixes \
  --shard-rows 1048576 --direct-joins --structural-above 0 <shard-proof-address>...
ix verify --aggregate --ixe env.ixe --ixes env.ixes \
  --structural-above 0 <aggregate-address>
```

The CLI builds the separate exporter and caches its artifact by source and
exporter contents. `--aiur-artifact` / `IX_AIUR_ARTIFACT` and
`--aggr-artifact` / `IX_AGGR_ARTIFACT` select already exported **trusted** compiler
artifacts. These are verifier configuration, never advice supplied by the
prover. `IX_AIUR_HOST` and `IX_STARK_HOST` can select prebuilt host executables.
Rebuild the Rust binaries after changing their sources.

Proofs retain Ix's claim wrapper and content-addressed store. Formal stage-one
and aggregate proof payloads have distinct `IXAIUR2` and `IXAGGR2` markers;
legacy proofs cannot be mistaken for them. Verification reconstructs keys from
the trusted artifacts, binds the exact public claims, and rejects trailing
proof bytes. Manifest verification checks disjoint coverage, binds every
nonempty shard, and rejects duplicate or missing proofs. Aggregate verification
also reconstructs the requested flat/structural root and checks that all
environment constants occur exactly once with no undischarged assumptions.

The formal shard index and aggregate cache use separate namespaces from the
legacy caches. Cache hits are verified before reuse. `--skip-proven`,
`--no-index`, `--no-cache`, and `--no-write` apply to their corresponding formal
paths. Aggregation supports wrap-first and direct joins, flat and structural
folds, manifest plan inspection, subtree selection, and targeted reproving from
verified cached children. Ready slots run in bounded waves. `--jobs` defaults to
one; zero uses the available CPU count. The total RAM budget and CPU threads
are divided among the jobs in each wave, so a single remaining job can use
the full reservation. Every worker in a wave is joined before a failure is
reported or the next wave starts. A verified cache hit cuts off its dependency
subtree, including when no original shard proofs were supplied. Explicitly
supplied aggregate proofs may also cover intermediate statements; their kind,
key, public claim and position in the manifest plan are checked before reuse.

`--range N` wraps large IxVM proofs through range leaves of at most N source
trace shards, range joins, and a range root. The host only slices advice; Aiur
shapes 10–12 verify the child proofs, preamble binding, contiguous coverage,
residual sum, and original public claim. Range intermediates have a separate
verified cache. `--wrap-root` forces fresh self-wraps until one trace shard
remains, and stops with an error if the shard count stops decreasing.

Batch proving partitions function and width-specific ROM rows. Channel 16
closes memory intervals across shards, while the function channel is 1 and
the ROM channel is 2. The verifier checks activation, fixed-table heights,
Goldilocks domain/lookup bounds, exact claims, and ordered nonoverlapping memory
intervals before calling multi-stark. `--retention auto` selects retain when
the estimated batch fits its RAM budget and regenerate otherwise; both can
also be requested explicitly. Both policies produce identical proof bytes in
the partition regression test. Stage-one-only population avoids allocating the
whole-trace lookup buffers that batch proving recomputes per shard. The
execution record stays resident through trace generation, then is dropped
before proving. The complete stage-one matrices remain in host memory.

Both hosts share the same allocation-phase planner. It accounts for fixed
tables, source matrices, lookup buffers, commitment data, and retained shard
state, with a 25% allowance. It conservatively includes the observed RSS even
after the execution record is dropped. This is an estimate, not a hard allocator
limit or a calibrated peak-RSS bound. The execution itself happens before the
record can be measured. An earlier artifact/fixed-table estimate rejects
budgets that splitting cannot satisfy. Generated matrix sizes are checked
against the plan before proving. `--max-ram` is the total new-backend budget in GiB;
without it, the controller reserves 85% of available host memory, respecting a
root-mounted cgroup v2 limit. Shard rows are capped at 65536 by default;
`--shard-rows 0` lets the planner choose the cap.

Manifest proving supports `--shards`, `--jobs`, `--skip-proven`, `--exec-only`,
`--out-ixes`, and `--report`. An oversized claim is cut into whole blocks and
its parts are executed and planned again. `--trace-shards` requires the original
claim to fit through trace sharding and rejects it if source-record or trace
residency prevents that. `ix check --ram-budget` runs the same planning and
refinement loop without proving. Reports use `ix-formal-run/1` and contain
per-part plans, timings, failures and proof addresses. A failed run does not
publish a refined manifest. Ordinary `ix check` only executes.

`MultiStark/MultiStark/Program.aiur` is the ordinary Aiur recursive verifier;
`Aggregate.aiur` adds all thirteen current aggregation shapes, including range
leaves, joins and closure. They share the existing opaque word and Blake3
libraries. Hint closures provide raw advice, and ordinary program assertions
check it. Digest and duplicate-row equality use full structural comparisons;
there are no pointer identities or unconstrained calls. Application address
sets also compare complete address contents, and 64-bit equality compares both
limbs instead of reducing modulo Goldilocks.

The standalone recursive host supports `execute`, `plan`, `prove`, `verify`,
key export, and range-advice export. A proof invocation supplies the key digest and claims digest publicly,
and proof/key/claims streams privately. The output directory contains
`proof.bin`, `key.bin`, `claims.bin`, `public.json` for independent verification,
and `input.json` for feeding the proof into another recursive-verifier run.

## Legacy support and native builds

`--legacy` retains the old execution, proving and verification paths, including
old proof formats and caches. Distributed cross-record execution, the shared
execution-ahead pool, multi-GPU lane orchestration, and texray remain behind
that boundary; requesting their flags on the new backend fails explicitly.
These are not silently replaced by independent claim proofs.

The new hosts select multi-stark's CUDA prover with `--gpu-device N` or
`IX_CUDA=1` (device from `MULTI_STARK_CUDA_DEVICE`, otherwise zero). CPU binaries
live in `target/release`; CUDA binaries live in `target/formal-cuda/release` and
are built with `--features parallel,cuda`. Override them independently with
`IX_AIUR_HOST_CUDA` / `IX_STARK_HOST_CUDA`. Verification and key export use the
CPU hosts. Device choice does not enter the verifying key or proof protocol.
An explicit device request to a CPU-only Rust host fails.

The current trace writer populates stage-one matrices on the CPU. CUDA
accelerates multi-stark's prover phases; this does not add GPU trace codegen.
The CUDA CI job checks and links both separate hosts. On a GPU machine, run
`IX_TEST_CUDA=1 bash tools/ixvm/check-formal.sh` to prove an IxVM claim and a
recursive proof on CUDA, then verify both with the CPU hosts. Both hosts also
compile and link locally in the CUDA 13.3.1 development container. This host
has no NVIDIA device or driver, so GPU execution remains hardware-unvalidated.

`AIUR_TRACE_ONLY_LOOKUPS=1` lets CUDA derive lookup messages from the committed
stage-one rows using multi-stark's graph evaluator. It avoids host lookup
buffers and selects regeneration at the batch barrier. Full host buffers remain
the default because they support multi-stark's memory-pressure CPU fallback;
shape-only buffers fail explicitly if a CPU fallback tries to consume them.
The hardware integration gate exercises both modes and CPU-verifies the proofs.

`tools/ixvm/adapt.py --check` checks reproducibility against the pinned source
revision. `tools/ixvm/recursion.py --check` and `--aggregate --check` do the same
for recursive programs. `tools/ixvm/audit.py --out DIR` inventories lexical and
semantic adaptations; the audit is not a proof of equivalence to legacy IxVM.
The compiler correctness proofs remain intact. Neither those proofs nor the
port tests constitute a new formal proof of the cryptographic backend or
discharge the existing memo-acyclicity hypothesis of the semantic model.

Normal builds leave generated native execution out of the dependency graph.
The retained legacy path uses bytecode by default. To select its existing
native kernels:

```sh
IX_NATIVE=1 lake build ix
cargo build -p ix-ffi --features legacy-native,parallel
```

The three native kernels share one optional crate. `cargo --workspace` explicitly
includes that crate; ordinary workspace default members exclude it. Legacy
GPU flags (`IX_CUDA`, `IX_CUDA_TRACE_CODEGEN`) are retained independently.
`ix codegen` and `trace-fixtures` still regenerate legacy artifacts at their
new paths.

Function grouping is now enabled in the IxVM and recursive-verifier exports.
The application policies translate legacy's measured groups; missing, inlined,
or already deduplicated members are skipped, and entrypoints stay singleton.
`--ungrouped` disables the policy when exporting either application. The generic
Aiur library accepts an explicit policy and otherwise leaves functions separate.

The Lean transformation shares data columns and reserves private columns to
silence inactive members. It checks polynomial silence, gates the remaining
constraints and lookup arguments, and preserves degree three, logical call
identities, and all-zero padding. Selector exclusion is valid in arbitrary
fields. The compiler now returns a proof-bearing `Grouping.Checked` layout and
the exporter checks a `Grouping.Plan` covering the entire source system.
`Checked.localRule_iff` proves equivalence of finite grouped rows and original
function rows. It derives selector properties and source memory validity from
the emitted equations and shared lookup words. The raw packet theorems cover
both projection and extension, including tags, widths, enables, unused slots,
and zero padding. `Plan.derives_iff` proves whole-program equivalence, and
`Physical.Prepared.grouped_native_heap_sound` composes grouping with source
evaluation and heap representation. These proofs use no `sorry` or added
axioms. Certification runs only during export. Rust scatters each
function's prepared row directly into the shared layout, including lifted
lookup arguments. Shard planning and auxiliary placement use the grouped shapes.
The Rust lowering and cryptographic backend retain their existing trust boundary.

The port now preserves legacy's nonrecursive `@`-only helper boundaries through
the existing proved inliner. Byte AND/OR share XOR's fixed table and less-than
uses subtraction's borrow. Fixed-arity word hint closures accelerate legacy
primitive counterparts without adding language primitives. Controlled bytecode
comparisons, including each circuit's columns and FFT cost, are recorded in
[the grouping comparison](formal-aiur-grouping-comparison.md).

The final codegen phase will use Rust procedural macros, not a generation
script. The macros should live in an optional `aiur-macros` crate,
with their IxVM expansion compiled in a separate optional `ixvm-native` crate.
Neither belongs in the ordinary `aiur` or `ixvm` dependency graph. This change
does not implement the future macro backend or create empty placeholder crates.

## Migration validation

Default-backend/controller checks on 2026-10-26:

- New CLI modules build with `--wfail`; Rust tests and Clippy pass. The compiler
  theorem sources are unchanged. The integration gate checks default selection,
  the explicit legacy bytecode path, real claims, recursive proofs, all thirteen
  aggregation shapes, and wrong-claim/proof/identity/range rejection.
- Two concurrent `Nat.add_comm` environment claims reproduce the prior proof
  addresses and sizes, with four trace shards each. Independent partition
  verification and `--skip-proven --shards 1` reuse pass. The controller emits
  its measured-plan report and a valid refined manifest.
- A 1 GiB total budget with two jobs is rejected before execution: each
  512 MiB reservation is below the estimated artifact/fixed-table floor.
  The failure report is written and no refined manifest is emitted. A separate
  one-job, 1 GiB execution audit successfully refines the full environment
  from one leaf into four fitting parts; the emitted manifest passes coverage
  and aggregation-plan checks. No STARK is requested in that audit.
- Real range leaves, joins, and roots were proved for both IxVM proofs using
  `--range 2`. Their persisted intermediates were then independently verified
  and supplied to `--reprove-slot 2`. The final structural join produced
  20,583,260 proof bytes in sixteen trace shards. Independent aggregate
  verification, root-cache replay with no input proofs, and supplied-proof
  subtree replay pass; all 342 constants are covered without assumptions.
  The root address is
  `7cf439d1369a2523d435282d9c6b7496168157c8926fb444bc23841f01b4cf19`.
- The targeted final join took 4m41s and `/usr/bin/time` reported 77.95 GiB peak
  RSS for its largest process. This is a controller validation, not a new
  performance comparison: the range hierarchy does more recursive work than
  the earlier direct join. Its first run exposed a reservation bug at the
  final single-job wave; the corrected scheduler gives that wave the full
  128 GiB budget instead of half.
- CUDA linking is covered by the updated CI job; hardware validation remains
  pending. `IX_TEST_CUDA=1` enables CPU verification of GPU-produced proofs in
  the integration gate.

Current-port checks on 2026-10-22:

- The complete Aiur proof graph builds (2,050 root-workspace build jobs), with
  its theorem sources unchanged. The imported proofs still have pre-existing
  linter warnings under `--wfail`; the ordinary proof build succeeds.
- All 84 new Rust tests pass; the shared codec refactor also passes 101 legacy
  runtime tests (3 ignored) and 6 legacy host tests. New Rust targets pass
  Clippy with warnings denied.
- Ten current claim cases pass, including normal-form evaluation and rejection
  of an unreduced claimed result. The `.ixe` input path accepts `Nat.add_comm`.
- The recursive verifier accepts a real multi-stark proof and rejects wrong
  public digests, truncated proof/key/claim streams, and a corrupted opening.
  Its execution is itself proved and independently verified.
- Thirty-two aggregation cases cover all thirteen shapes, including rejected
  dropped assumptions, wrong identities/kinds, incorrect range residuals,
  incomplete ranges, and malformed child proofs. An aggregate wrap is itself
  proved and independently verified (6,263,653 bytes, one trace shard).
- A real two-shard partition of the `Nat.add_comm` environment proves and
  independently verifies all 342 constants. Its stage-one proofs contain
  12,207,268 and 14,306,442 bytes, each with four trace shards. A structural
  direct join verifies both proofs in Aiur bytecode (23.126 s in this run,
  34,189,789 recorded queries) and produces a verified aggregate of 11,975,716
  bytes across eight trace shards. Its stored address is
  `8e261edbcef1fcb3e64505ea68ce7399ba0a98fd1b251ba9676bf87f0a5211d0`.

`bash tools/ixvm/check-formal.sh` runs the reproducible integration gate: current
claims, CLI persistence/verification, recursive proof round trips and all
aggregation shapes. The full-size aggregation above is a separate local check;
CI uses small real child proofs to keep its memory requirements reasonable.

For the current `Nat.add_comm` claim, the first CLI proof run measured 28.2 ms
execution, 9.5 ms trace generation and 1.33 s proving, producing an 11,657,213-byte
proof. These are single-run observations, not a controlled comparison with the
legacy backend. The stage-one-only batch population optimization was added
after those measurements.

### Initial import regression results

Validated on 2026-10-22 with Lean 4.34.1 and Rust 1.98.1:

- All 365 Aiur modules build, including compiler soundness/completeness,
  provenance, optimization, physical deduplication, and word-library proofs.
  The existing theorem statements are retained, with no added axioms or
  `sorry`. The package's default target explicitly includes every submodule.
- The full Aiur regression suite, execution/FFI checks, trace checks, U32 tests,
  and shared-library tests pass. Trace tests include 202 executions under each
  of three compiler configurations and 54 executions over F₂, accepted by
  Lean's `checkMemo`.
- `cargo test -p aiur -p ixvm --all-targets --features parallel` passes all
  82 tests. Workspace Clippy with the new parallel and legacy native features
  passes with warnings denied.
- `Tests.AiurBoundaries` imports both implementations and elaborates both
  surface languages together. Legacy parser categories use a `legacy_aiur_`
  prefix because Lean syntax-category names are global.
- The new IxVM accepts all five validation entrypoints and all 342 fixture
  serialization cases. Corrupted serialization, a wrong address, missing
  advice, and a correctly hashed invalid proof are rejected.
- The fixed `Nat.add_comm` fixture executes, generates a witness, proves, and
  verifies through multi-stark. Its exported package SHA-256 matches the
  recorded pre-migration digest exactly:
  `14cc72161dd26070d290ffd949b10b9225b0792da0a98633827340ca49da1e48`.

| New IxVM fixture result | Value |
| --- | ---: |
| Function queries | 75,988 |
| Fixed-table queries | 140,137 |
| ROM queries | 21,981 |
| Stage-one columns | 18,222 |
| Stage-one cells | 4,082,430 |
| Execution-record fingerprint | 17083028404579245216 |
| Trace fingerprint | 18300081860579238156 |

Both fingerprints match the pre-migration results. These checks concern
migration fidelity; they do not establish equivalence to today's legacy IxVM.

The legacy Rust tests pass (102 tests, 3 ignored), as do six legacy host tests
including the bytecode fallback. The rebuilt legacy Lean execution, cost,
trace-plan, and generated-Rust checks pass. The retained native and bytecode
`Nat.add_comm` runs report matching circuit widths, FFT cost, and cache-hit
counts. Generated execution kernels, Rust trace writers, CUDA units, and
manifests pass their regeneration checks. GPU execution and proving were not
run locally.
