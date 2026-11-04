# Formal Aiur in Ix

Formal Aiur is Ix's only Aiur backend. Legacy Aiur, legacy IxVM and
the legacy recursive verifier were retired by
[PR 678](https://github.com/argumentcomputer/ix/pull/678).

The implementation is imported from `aiur` commit `7584bf5` on
`bench/ixvm-audit`. Its compiler correctness proofs are retained; the Lean
sources are adapted to Ix's Lean/Mathlib 4.34.1 toolchain. In particular,
the Aiur package selects Lean's legacy `do` elaborator to preserve the
verified monadic definitions from 4.29. Proof adaptations do not add axioms
or `sorry`.

## Package boundaries

| Component | Lean package/library | Rust crate |
| --- | --- | --- |
| Generic language, compiler, proofs, libraries | `Aiur/` / `Aiur` | `crates/aiur` |
| IxVM claim verifier and host | `IxVM/` / `IxVM` | `crates/ixvm` |
| Recursive verifier and aggregation program | `MultiStark/` / `MultiStark` | `crates/stark-verifier` |
| Shared verifying-key and range-advice codecs | — | `crates/stark-key` |
| Generated native executors | — | `crates/aiur-macros`, `crates/ixvm-native`, `crates/stark-verifier-native` |
| Prover library linked into `ix` | `Ix/FormalProver.lean` | `crates/ix-prover` |
| Proving scheduler | — | `crates/aggregate-controller`, `crates/record-pool` |

The generic Aiur crate does not depend on IxVM or a Lean installation. The
IxVM crate registers its hint channels and table accelerators using Aiur's
generic APIs. Its Rust binary accepts an exported execution package. Lean's
`IxVM.parse` loads the application and its shared Goldilocks word/hash
library; callers select entrypoints with `Aiur.Modules.prepare`.

Aiur owns its FFI: `Aiur/c/execution.c` adapts Lean objects to the JSON C ABI
exported by the Rust `aiur` static library. Lake's `aiur/execution_o` and
`aiur/aiur_rs` targets are linked only by executables that use it. The IxVM
export driver builds without Rust and invokes the separate `ixvm` host for
execution with its application hint providers. Pure Lean library/proof builds
do not run Cargo. Cargo builds do not invoke Lake. Serialization is the
bridge; there is no direct object ABI. IxVM has no `ffi` replay command: the
data-only ABI cannot supply the word library's closure hints. Generic Aiur
FFI execution and tracing are covered by their own test executables.

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

## Application port and CLI

`tools/ixvm/adapt.py` reproduces the IxVM application port from pinned Ix
revisions (`05cc396fc` for the application, `827550579` for the shared
libraries). The application covers the claim dispatcher, evaluation,
environment checking, reveal, membership and role-binding claims. Every
claim is relative to the environment's role binding, read from input
channel 6; see [role binding](formal-aiur-orchestration.md#role-binding).

The ordinary commands use formal Aiur. `--formal` is accepted as an alias for
the default:

```sh
ix prepare          # once per source revision: certified artifacts
ix check Nat.add_comm
ix prove Nat.add_comm
ix verify <proof-address>

ix prove --ixe env.ixe --ixes env.ixes
ix verify --ixe env.ixe --ixes env.ixes <shard-proof-address>...
ix prove --aggregate --ixe env.ixe --ixes env.ixes --trace-shards
ix aggregate --ixe env.ixe --ixes env.ixes <shard-proof-address>...
ix verify --aggregate --ixe env.ixe --ixes env.ixes <aggregate-address>
```

The CLI compiles a certified program with the compiler linked into `ix`,
hands the result to the prover in memory and caches it as a binary artifact
keyed by the compiler's identity and the sources, in the `.lake/aiur` of the
checkout `ix` was built in (or `IX_ROOT`), so commands work from any
directory. `ix prepare` does this ahead of time and selects the artifacts
for the native executors that the next `lake build ix` links; otherwise the
first command that needs a program compiles it, which takes several minutes
for IxVM. `--aiur-artifact` / `IX_AIUR_ARTIFACT` and `--aggr-artifact` /
`IX_AGGR_ARTIFACT` select **trusted** binary artifacts (`aiur-artifact
convert` turns a legacy JSON export into one); see
[direct FFI](formal-aiur-direct-ffi.md). These are verifier configuration,
never advice supplied by the prover. The prover runs inside `ix` as a linked
library, so `lake build ix` rebuilds it with its sources; see the
[orchestration guide](formal-aiur-orchestration.md#in-process-prover).

Proofs retain Ix's claim wrapper and content-addressed store. Stage-one and
aggregate proof payloads carry distinct `IXAIUR2` and `IXAGGR2` markers.
Verification reconstructs keys from the trusted artifacts, binds the exact
public claims, and rejects trailing proof bytes. Manifest verification checks
disjoint coverage, binds every nonempty shard, and rejects duplicate or
missing proofs. Aggregate verification also reconstructs the requested root
and checks that all environment constants occur exactly once with no
undischarged assumptions.

## Aggregation

The aggregate controller is the only proving scheduler. `ix prove --ixe
--ixes` proves manifest claims on it; `--aggregate` (CPU lanes) and `--lanes`
(GPUs) also join them and wrap the root; `ix aggregate` folds supplied claim
proofs. Claims join directly: the fold never wraps a single claim, and
`--range` and wrap-first are rejected. Every join is structural by default
(`--structural-above 0`). The root is wrapped until it is one trace shard.
Lean recomputes the expected root from the environment and manifest and
accepts the controller's root only if it proves exactly that claim. See the
[orchestration guide](formal-aiur-orchestration.md) and the
[controller design](formal-aiur-unified-controller.md).

Claim proofs are indexed under `~/.ix/cache/shard-proofs` and joins under
`~/.ix/cache/aggregate`; every hit is verified before reuse. `--no-index`,
`--no-cache` and `--no-write` apply to their corresponding paths. Manifest
plan inspection (`--plan-only`), subtree selection (`--subtree`) and
targeted reproving from verified cached children (`--reprove-slot`) are
available on `ix aggregate`.

`MultiStark/MultiStark/Program.sources` composes the Aiur recursive verifier
modules; `Aggregate.sources` reuses them and adds the aggregation shapes:
wraps (0–1), flat joins (2–5), structural joins (6–9), range-sum shapes
(10–12, which the controller does not schedule), binding discharge (13–14),
cross-binding joins (15) and catalog joins (16). Both reuse the checked
byte/word, list, address, Blake3 and Goldilocks libraries. See
[the module layout](formal-aiur-modules.md) for interfaces and compatibility
checks. Hint closures provide raw advice, and ordinary program assertions
check it. Digest and duplicate-row equality use full structural comparisons;
there are no pointer identities or unconstrained calls. Application address
sets also compare complete address contents, and 64-bit equality compares
both limbs instead of reducing modulo Goldilocks.

The standalone recursive host (`stark-verifier`) supports `execute`, `plan`,
`prove`, `verify`, key export and range-advice export. A proof invocation
supplies the key digest and claims digest publicly, and proof/key/claims
streams privately. The output directory contains `proof.bin`, `key.bin`,
`claims.bin`, `public.json` for independent verification, and `input.json`
for feeding the proof into another recursive-verifier run. Proving no
longer goes through this host: catalog aggregation and binding discharge run
on the controller.

## Batch proving and planning

Batch proving partitions function and width-specific ROM rows. Channel 16
closes memory intervals across shards, while the function channel is 1 and
the ROM channel is 2. The verifier checks activation, fixed-table heights,
Goldilocks domain/lookup bounds, exact claims, and ordered nonoverlapping
memory intervals before calling multi-stark. `--retention auto` selects
retain when the estimated batch fits its RAM budget and regenerate otherwise;
both can also be requested explicitly, and both produce identical proof
bytes. Population retains the execution record and generates packed trace
pieces as needed, so the complete stage-one matrices are never allocated. See
[incremental generation](formal-aiur-orchestration.md#incremental-trace-generation)
and the [streaming design](formal-aiur-streaming-traces.md).

Proving uses the production STARK parameters (`Parameters::default` in
`crates/aiur/src/trace/stark.rs`): `log_blowup` 2 (blowup factor 4), 100
queries and 20 query proof-of-work bits. The aggregate identity and cache key
include `fri_parameter_bytes`, so caches follow the parameters actually used.

All provers share one allocation-phase planner. It accounts for fixed tables,
source matrices, lookup buffers, commitment data and retained shard state,
with a 25% allowance. CUDA plans charge host RAM only for witnesses and
upload staging, since commitment, stage two and openings stay on the device.
It conservatively includes the observed RSS even after the execution record
is dropped. This is an estimate, not a hard allocator limit or a calibrated
peak-RSS bound. The execution itself happens before the record can be
measured. An earlier artifact/fixed-table estimate rejects budgets that
splitting cannot satisfy. Generated matrix sizes are checked against the plan
before proving. `--max-ram` is the RAM budget in GiB (per GPU with
`--lanes`); without it, 85% of available host memory is used, respecting a
root-mounted cgroup v2 limit. Shard rows default to `0`: the planner chooses
the largest shards that fit the budget. CUDA runs also bound each shard's
committed cells by `AIUR_TRACE_SHARD_MAX_CELLS` (1.5 billion, sized for a
96 GB device). An explicit `--shard-rows` caps rows; small caps multiply
recursive verification work (at 65536 rows the complete pipeline failed on
both CPU and CUDA; see [GPU validation](formal-aiur-gpu-validation.md)).

Manifest proving supports `--shard`, `--shards`, `--jobs`, `--exec-jobs`,
`--out-ixes` and `--report`. A claim whose execution record exceeds the
record ceiling is bisected into whole blocks, the refined partition is
checkpointed, and a rerun resumes from it. `ix check --ram-budget` and
`ix prove --exec-only` execute and plan each selected shard without proving,
cutting an over-budget shard into whole blocks. Their reports use
`ix-formal-run/1` and contain per-part plans, timings and failures. A failed
run does not publish a refined manifest. Ordinary `ix check` only executes.

## CUDA and native execution

The prover selects multi-stark's CUDA prover with `--gpu-device N`,
`--lanes`, or `IX_CUDA=1` (device from `MULTI_STARK_CUDA_DEVICE`, otherwise
zero), provided `ix` was built with `IX_CUDA=1`. Verification and key export
run on the CPU. Device choice does not enter the verifying key or proof
protocol. An explicit device request to a CPU-only build fails.

The trace writer populates stage-one matrices on the CPU by default; CUDA
accelerates multi-stark's prover phases. With `AIUR_GPU_TRACE=generated`
(which needs the default device lookups), function circuits whose population
plans read only recorded calls, byte tables and word hints are filled on the
device instead (`crates/aiur/cuda/population.cu` interprets the same
compiled plans and group placements) and reach multi-stark as generated
traces; the record tables they read are uploaded once per proof. Circuits
with memory stores, loads or stream hints, ROMs and fixed tables keep host
rows. Proofs are byte-identical either way. This halves host RAM in the
pipeline but does not make it faster
([GPU validation](formal-aiur-gpu-validation.md)).
The CUDA CI job checks and links the reference drivers and the `ix-prover`
binary. On a machine with an NVIDIA driver and CUDA toolkit, run this from
the repository root:

```sh
IX_TEST_CUDA=1 IX_TEST_OUTPUT_DIR=.lake/cuda-validation \
  bash tools/ixvm/check-formal.sh
```

Set `MULTI_STARK_CUDA_DEVICE` to select a device (zero by default). The gate
builds CPU and CUDA hosts separately, then compares complete proof and key
bytes for three grouped applications: the `Nat.add_comm` frontier claim,
recursive verification, and aggregation wrapping. Each application must use
multiple trace shards. It checks CPU retain/regenerate, CUDA
retain/regenerate with host lookup buffers, and CUDA regeneration with
graph-derived lookups. It also checks single-shard CUDA proofs with
graph-derived lookups under both retention policies against an independent
CPU proof, including that the requested retention policy was actually
honored. Every proof is independently verified by the CPU host. Wrong public
inputs and explicit GPU requests to CPU-only hosts must fail.

Logs, proofs, artifact/binary hashes, and a JSON report are saved under
`.lake/cuda-validation/cuda-check-*/`, including on failure. Without
`IX_TEST_OUTPUT_DIR`, GPU runs retain a directory under
`.lake/formal-cuda-check.*`. Ordinary CPU CI runs the same gate's CPU
controls; its report explicitly sets `hardware_validated: false`. Successful
CUDA builds alone do not validate GPU execution. Hardware results are in
[GPU validation](formal-aiur-gpu-validation.md).

CUDA proving derives lookup messages from the committed stage-one rows using
multi-stark's graph evaluator by default, without host lookup buffers.
Multi-shard batches select regeneration to bound device residency;
single-shard batches can retain their commitment across the barrier,
avoiding a second upload, LDE and Merkle commitment at the same peak memory.
When device memory pressure forces multi-stark onto a path that reads lookup
values on the host, it rebuilds them from the committed trace (coset
interpolation of the committed LDE, then its own lookup evaluator), so the
fallback is slower but produces the same proof bytes.
`AIUR_TRACE_ONLY_LOOKUPS=0` builds host lookup buffers instead; CPU builds
always do and reject `AIUR_TRACE_ONLY_LOOKUPS=1`. CPU verification and key
export ignore this prover-only setting, so leaving it exported after GPU
proving does not break those commands. CPU proving still rejects a request
for graph-derived device lookups. The
[batch preparation follow-up](formal-aiur-gpu-preparation.md) records the
hardware review and fixes for serial host lookup reconstruction, redundant
trace copying and unnecessary single-shard commitment regeneration.

Native execution is generated by the `aiur-macros` procedural macros into
`crates/ixvm-native` and `crates/stark-verifier-native`, outside the ordinary
`aiur` and `ixvm` dependency graph. `ix-ffi`'s `formal-native` feature links
them once `ix prepare` has exported the artifacts; the interpreter produces
identical records and proofs. See
[native execution](formal-aiur-native-execution.md) and the
[build order](formal-aiur-orchestration.md#native-executors-and-build-order).

`tools/ixvm/adapt.py --check` checks reproducibility against the pinned
source revision. `tools/ixvm/recursion.py --check` and `--aggregate --check`
do the same for recursive programs. `tools/ixvm/audit.py --out DIR`
inventories lexical and semantic adaptations. The compiler correctness proofs
remain intact. Neither those proofs nor the port tests constitute a new
formal proof of the cryptographic backend or discharge the existing
memo-acyclicity hypothesis of the semantic model.

## Function grouping

Function grouping is enabled in the IxVM and recursive-verifier exports. The
application policies list measured groups; missing, inlined or already
deduplicated members are skipped, and entrypoints stay singleton.
`--ungrouped` disables the policy when exporting either application. The
generic Aiur library accepts an explicit policy and otherwise leaves
functions separate.

The Lean transformation shares data columns and reserves private columns to
silence inactive members. It checks polynomial silence, gates the remaining
constraints and lookup arguments, and preserves degree three, logical call
identities, and all-zero padding. Selector exclusion is valid in arbitrary
fields. The compiler returns a proof-bearing `Grouping.Checked` layout and
the exporter checks a `Grouping.Plan` covering the entire source system.
`Checked.localRule_iff` proves equivalence of finite grouped rows and
original function rows. It derives selector properties and source memory
validity from the emitted equations and shared lookup words. The raw packet
theorems cover both projection and extension, including tags, widths,
enables, unused slots, and zero padding. `Plan.derives_iff` proves
whole-program equivalence, and `Physical.Prepared.grouped_native_heap_sound`
composes grouping with source evaluation and heap representation. These
proofs use no `sorry` or added axioms. Certification runs only during
export. Rust scatters each function's prepared row directly into the shared
layout, including lifted lookup arguments. Shard planning and auxiliary
placement use the grouped shapes. The Rust lowering and cryptographic
backend retain their existing trust boundary.

The port keeps nonrecursive `@`-only helper boundaries through the existing
proved inliner. Byte AND/OR share XOR's fixed table and less-than uses
subtraction's borrow. Fixed-arity word hint closures accelerate word
primitives without adding language primitives.

## Init benchmark

Full Init on one RTX PRO 6000 proved in **7:30.2** wall time with
**131.8 GiB** peak RSS, root `cf5b813b…`. This was measured on
`formal-aiur-perf` at `b8e708a35`, before PR 678 and role binding, with the
production STARK parameters: `ix prove --lanes 1` on `Init-230.ixes` (a
3-shard partition from `ix shard --max-ram 230 --exec-jobs 3`),
`--exec-jobs 3 --max-ram 230`, direct joins and structural threshold 0. On
the same setup with the former parameters (`log_blowup` 1, 64 queries, no
proof of work) it took 5:56.9 and 128.5 GiB.

The figure is historical. IxVM has since gained role binding, so the
current code proves a different root, and the benchmark has not been
re-measured since.

## Validation history

These results were measured before the production STARK parameters and
before role binding; current proof sizes and addresses differ.

Controller checks on 2026-10-26:

- New CLI modules build with `--wfail`; Rust tests and Clippy pass. The
  compiler theorem sources are unchanged. The integration gate checks real
  claims, recursive proofs, all aggregation shapes, and
  wrong-claim/proof/identity rejection.
- Two concurrent `Nat.add_comm` environment claims reproduce the prior proof
  addresses and sizes, with four trace shards each. Independent partition
  verification and `--skip-proven --shards 1` reuse pass. The controller
  emits its measured-plan report and a valid refined manifest.
- A 1 GiB total budget with two jobs is rejected before execution: each
  512 MiB reservation is below the estimated artifact/fixed-table floor.
  The failure report is written and no refined manifest is emitted. A
  separate one-job, 1 GiB execution audit successfully refines the full
  environment from one leaf into four fitting parts; the emitted manifest
  passes coverage and aggregation-plan checks. No STARK is requested in that
  audit.

Port checks on 2026-10-22:

- The complete Aiur proof graph builds (2,050 root-workspace build jobs),
  with its theorem sources unchanged. The imported proofs still have
  pre-existing linter warnings under `--wfail`; the ordinary proof build
  succeeds.
- All 84 new Rust tests pass. New Rust targets pass Clippy with warnings
  denied.
- Ten claim cases pass, including normal-form evaluation and rejection of an
  unreduced claimed result. The `.ixe` input path accepts `Nat.add_comm`.
- The recursive verifier accepts a real multi-stark proof and rejects wrong
  public digests, truncated proof/key/claim streams, and a corrupted opening.
  Its execution is itself proved and independently verified.
- Thirty-two aggregation cases cover the thirteen shapes of that time,
  including rejected dropped assumptions, wrong identities/kinds, incorrect
  range residuals, incomplete ranges, and malformed child proofs. An
  aggregate wrap is itself proved and independently verified (6,263,653
  bytes, one trace shard).
- A real two-shard partition of the `Nat.add_comm` environment proves and
  independently verifies all 342 constants. Its stage-one proofs contain
  12,207,268 and 14,306,442 bytes, each with four trace shards. A structural
  direct join verifies both proofs in Aiur bytecode (23.126 s in this run,
  34,189,789 recorded queries) and produces a verified aggregate of
  11,975,716 bytes across eight trace shards. Its stored address is
  `8e261edbcef1fcb3e64505ea68ce7399ba0a98fd1b251ba9676bf87f0a5211d0`.
- For the `Nat.add_comm` claim, the first CLI proof run measured 28.2 ms
  execution, 9.5 ms trace generation and 1.33 s proving, producing an
  11,657,213-byte proof (single-run observations).

`bash tools/ixvm/check-formal.sh` runs the reproducible integration gate:
current claims, CLI persistence/verification, recursive proof round trips,
all aggregation shapes and the [controller gate](formal-aiur-orchestration.md#validation).
CI uses small real child proofs to keep its memory requirements reasonable.

### Initial import regression results

Validated on 2026-10-22 with Lean 4.34.1 and Rust 1.98.1:

- All 365 Aiur modules build, including compiler soundness/completeness,
  provenance, optimization, physical deduplication, and word-library proofs.
  The existing theorem statements are retained, with no added axioms or
  `sorry`. The package's default target explicitly includes every submodule.
- The full Aiur regression suite, execution/FFI checks, trace checks, U32
  tests, and shared-library tests pass. Trace tests include 202 executions
  under each of three compiler configurations and 54 executions over F₂,
  accepted by Lean's `checkMemo`.
- `cargo test -p aiur -p ixvm --all-targets --features parallel` passes all
  82 tests.
- The IxVM accepts all five validation entrypoints and all 342 fixture
  serialization cases. Corrupted serialization, a wrong address, missing
  advice, and a correctly hashed invalid proof are rejected.
- The fixed `Nat.add_comm` fixture executes, generates a witness, proves, and
  verifies through multi-stark. Its exported package SHA-256 matches the
  recorded pre-migration digest exactly:
  `14cc72161dd26070d290ffd949b10b9225b0792da0a98633827340ca49da1e48`.

| IxVM fixture result | Value |
| --- | ---: |
| Function queries | 75,988 |
| Fixed-table queries | 140,137 |
| ROM queries | 21,981 |
| Stage-one columns | 18,222 |
| Stage-one cells | 4,082,430 |
| Execution-record fingerprint | 17083028404579245216 |
| Trace fingerprint | 18300081860579238156 |

Both fingerprints matched the pre-migration results.

## Open work

### GPU trace population

GPU population uploads the leaf's query tables and indexes once and shares
them across every circuit (`crates/aiur/src/trace/stark/gpu.rs`). Under
device pressure, with `AIUR_GPU_TRACE_RELEASE=1`, it downloads every table,
frees the record and later re-uploads the whole record; release is off by
default. The record occupies 3–5.6 GB of device memory on an Init leaf.

Measured on `formal-aiur-perf` (before PR 678) on Init leaf 0 at a fixed
10-shard layout:

| Population | Trace s | Proving s | Total |
|---|---:|---:|---:|
| CPU | 11.59 | 19.03 | 30.6 |
| Interpreter | 10.25 | 24.67 | 34.9 |
| Compiled | 9.71 | 24.27 | 34.0 |

The compiled writer fills `Blake3::compress` 100× faster than the CPU
(0.050 s against 4.98 s). Even so, GPU population makes proving about 5 s
slower, so CPU population is the default. The suspected cause, not yet
measured, is that the resident record puts multi-stark's commitments under
device-memory pressure. With release on, 24 releases and 23 re-uploads cost
about 13 s on that leaf.

The open question is whether to keep the shared device record or replace it
with compact per-circuit, per-shard seeds held on the host and cached on the
device under a fixed bound, which evict without a download. Decide by a
matched benchmark: the same Init leaves (then a Mathlib sample), the same
trace-shard layout and parameters, one GPU, cold and warm runs, comparing CPU
population, the shared record with release off and on, and bounded seeds.
Measure trace fill, proving and wall time; the prover's stall waiting for
witnesses; device and host peaks; bytes uploaded and downloaded; releases
and re-uploads; and commitment-time memory pressure. Check that proof bytes
are identical across arms. Adopt the arm with the lowest leaf wall time
within the planned budgets, prefer the bounded design when two arms are
within noise, and delete the other implementation.
