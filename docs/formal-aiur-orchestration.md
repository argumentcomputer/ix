# Formal Aiur orchestration

Formal Aiur proves on one scheduler: the aggregate controller
(`crates/aggregate-controller`). The controller is generic over a `Backend`
trait. Its formal backend, `crates/ix-prover/src/aggregate.rs`, executes,
proves, verifies and encodes one unit of work; the controller decides what
runs when. Both are Rust libraries linked into `ix`. Lean keeps only the
trusted acceptance check. None of this adds an Aiur primitive, constraint,
axiom or `sorry`. The [controller design](formal-aiur-unified-controller.md)
describes the trust split and the backend trait in detail.

## Commands

```sh
# Manifest claims only: two CPU prover lanes, four executions ahead of them.
# Prints one `shard-id address` line per claim.
ix prove --ixe env.ixe --ixes env.ixes --jobs 2 --exec-jobs 4 \
  --max-ram 64 --out-ixes proven.ixes --report claims.json
ix verify --ixe env.ixe --ixes proven.ixes CLAIM_PROOF...

# Claims, joins and the root on CPU lanes; prints the accepted root.
ix prove --aggregate --ixe env.ixe --ixes env.ixes --jobs 2 --exec-jobs 4 \
  --trace-shards --max-ram 192 --out-ixes completed.ixes
ix verify --aggregate --ixe env.ixe --ixes completed.ixes ROOT_ADDRESS

# The same pipeline on four CUDA lanes, starting at device zero.
# Here --max-ram and --exec-jobs are per GPU.
ix prove --lanes 4 --gpu-device 0 --ixe env.ixe --ixes env.ixes \
  --trace-shards --max-ram 96 --exec-jobs 3 --out-ixes completed.ixes

# Fold already proven claims (or one subtree of the plan) into a root.
ix aggregate --ixe env.ixe --ixes env.ixes --trace-shards CLAIM_PROOF...
```

Claims join directly: the fold never wraps a single claim. `--direct-joins`
is accepted and has no effect; `--range` and wrap-first are rejected. Every
join is structural by default (`Aggr.defaultStructuralAbove = 0`,
`Ix/Aggr/Parameters.lean`). `--structural-above N` makes joins of at most N
subject leaves flat; verify with the same value. A root proved with
`--structural-above 4096` verifies only with `--structural-above 4096`.

`ix prove --lanes`/`--aggregate` always wraps the root until it is one trace
shard. `ix aggregate` does so with `--wrap-root`. A wrap that does not reduce
the shard count is discarded and the previous proof kept. A very small
`--shard-rows`, or a lane workspace too small for a single-shard verifier
proof, can make recursive proofs grow instead of shrink.

`ix aggregate` also takes `--plan-only` (print the slot plan), `--subtree N`
(prove one plan subtree and publish it through the aggregate cache),
`--reprove-slot N` (recompute one slot from verified cached children),
`--no-write`, `--jobs` (slots proving at once) and `--exec-ahead` (slots
executing ahead of the provers, default 1).

`--lanes` selects CUDA, while `--aggregate --jobs N` runs the pipeline on
CPU. `--texray` prints timings and RSS for execution, trace population and
proving. Exporters, sources and the artifact cache (`.lake/aiur`) are resolved
against the checkout `ix` was built in (or `IX_ROOT`), so `ix` runs from any
directory. `ix prepare` exports the IxVM, recursive verifier and aggregation
artifacts ahead of time; otherwise the first command that needs an artifact
exports it (several minutes, once per source revision).

## In-process prover

`ix` reaches the prover through Lean FFI (`Ix/FormalProver.lean`, adapter
`crates/ffi/src/formal.rs`):

| Call | Rust | Used by |
|---|---|---|
| `proveLanes` | `ix_prover::aggregate`, lane controller | `ix prove --ixe --ixes`, `--aggregate`, `--lanes` |
| `aggregate` | `ix_prover::aggregate`, slot scheduler | `ix aggregate` |
| `prove` | `tools::prove` | single claims, `ix prove-binding` |
| `check` | `tools::check` | `ix check`, `--exec-only`, `--ram-budget` |
| `verify`, `identity` | `tools::verify`, `tools::identity` | every verification, key identity |

Single claims prove through `tools::prove` without the controller: execute,
plan within the device and RAM budget, prove, and write the proof next to the
requested output. Verification always runs on the CPU, independently of CUDA
settings.

The controller returns a root address; it does not decide acceptance.
Before `ix prove` or `ix aggregate` prints a root, Lean's `accept`
(`Ix/Cli/FormalAggregate.lean`) recomputes the expected root statement from
the environment and the final manifest (`Reference.expectedFromManifest`),
audits that every constant occurs exactly once with no undischarged
assumptions, checks that the proof states exactly that claim, and verifies it
against the certified artifacts. `ix verify --aggregate` runs the same check.

Rust errors become Lean `IO` errors. The workspace builds with
`panic = "abort"`, so a Rust panic never unwinds into Lean; it ends the `ix`
process.

CUDA is a build-time selection: `IX_CUDA=1 lake build ix` links the CUDA
prover, and `--gpu-device N`, `--lanes` or a runtime `IX_CUDA=1` requests it.
A CPU build rejects a device request.

### Requests and advice

Rust builds the advice; Lean selects claims and checks results.

- **Leaves.** The controller opens the bound `.ixe` (see
  [Role binding](#role-binding)), rebuilds each shard's statement, and builds
  its witness with `ixon::witness` and `crates/ix-prover/src/request.rs`. The
  witness must reproduce the controller's statement. For single claims, Lean
  submits a request handle (`Request.check`, `Request.shard`) with the claim
  it computed; Rust rebuilds the witness and rejects the job if the
  recomputed claim differs. The claim proved is always the expected one; the
  advice is untrusted input that the circuits check.
- **Joins and root wraps.** `aggregate_controller::streams` encodes the
  aggregation advice: child proofs, verifying keys, claims, trees and paths.
  `streams_parity` (`crates/aggregate-controller/examples`) checks it byte
  for byte against the Lean reference builder in `Tests/FormalAdvice.lean`.
- **Other claim forms** (binding, evaluation, reveal, membership) submit a
  Lean-built witness as flat buffers (`Request.buffers`): little-endian
  stream metadata, one byte buffer and one numeric buffer. Rust validates
  every buffer: lengths must match, every buffer must be consumed exactly,
  keys must be unique per channel, channels must be below 256 and numeric
  words canonical.

Leaf streams follow the order `ixon::witness` specifies: channels ascend
(0, 1, 2, 3, 4, 6); channel 1 holds the subject tree, then the assumption
tree; channels 2 to 4 ascend by address. The order depends only on the
environment and the request, so building twice yields identical records.

Advice is held as compact byte arenas (`aiur::library::advice`), widened to
field words only for numeric channels, and charged to the job's record
reservation. Single-claim reports give `advice_payload_bytes`,
`advice_metadata_bytes`, the charged `advice_reserved_bytes` and the
`claim_digest` the leaf checked.

### Role binding

Every IxVM claim is relative to the environment's role binding, which the
kernel reads from input channel 6. An `.ixe` without a binding is normalized
by Lean (`loadBoundIxe`, `Ix/Check.lean`): `withDefaultRoleBinding` adds the
default binding and the constants, blobs and hints it needs, and the
normalized environment is serialized in memory and handed to Rust as an
`Aiur.EnvHandle`. Lean and the Rust prover check the same bytes, and nothing is
written to disk. Leaf advice carries the role arena, `seedBinding` and
`bindingRoots`, `assumeBinding` and the binding claims.

By default each shard proof validates the binding itself. To check it once
instead:

```sh
ix prove --ixe env.ixe --ixes env.ixes --assume-binding --out-ixes proven.ixes
ix prove-binding env.ixe --out binding.proof
ix verify --ixe env.ixe --ixes proven.ixes --binding-proof binding.proof CLAIM_PROOF...
```

With `--binding-proof`, the controller discharges the role binding once at
the root, before the root wrap, for `--lanes`, `--aggregate` and
`ix aggregate` (shapes 13 and 14). The binding proof must state the
environment's own binding and verify natively. `--assume-binding` without
`--binding-proof` is rejected on those paths, because the root would stay
conditional. With `--subtree` or `--reprove-slot`, `ix aggregate` proves the
selected slot under the assumed binding and discharges nothing: the printed
proof still assumes the binding (stderr says so), and a later full run
discharges it at the root.

Catalog aggregation (`ix aggregate --ixc`) runs on the controller as well.
Lean computes the members and the catalog plan, the controller binds one
supplied root to each member, checks the planned root against Lean's, and
proves the cross-binding and catalog joins (shapes 15 and 16). Lean accepts
the result with `CatalogAggregate.acceptCatalog`. No operation runs a
separate prover executable.

### Native executors and build order

The generated native executors (`crates/ixvm-native`,
`crates/stark-verifier-native`) are compiled from the exported artifacts
(`AIUR_IXVM_ARTIFACT`, `AIUR_VERIFIER_ARTIFACT`, `AIUR_AGGREGATION_ARTIFACT`),
but exporting them needs a built `ix`, and `ix` links the Rust archive. The
kernels are therefore the optional `formal-native` feature of `ix-ffi`:

1. `lake build ix` without artifacts links the interpreter only.
2. `ix prepare` exports the artifacts and records their absolute paths in
   `.lake/aiur/native-kernels.env`.
3. The next `lake build ix` reads that file, enables `formal-native`, passes
   the three variables to Cargo and adds the artifacts' contents to the
   archive's Lake trace, so a re-exported artifact rebuilds its kernel.

Setting all three `AIUR_*_ARTIFACT` variables overrides the file;
`IX_FORMAL_NATIVE=0` builds without kernels and `IX_FORMAL_NATIVE=1` fails if
they are unavailable. Kernels are only an optimization: a kernel runs a job
only for an artifact whose program has exactly its fingerprint, and the
interpreter produces identical records and proofs. `ix prepare` prints which
executors are linked, and check and prove reports name the `executor`. See
[native execution](formal-aiur-native-execution.md).

`ixvm-proof` and `stark-verifier` remain as reference drivers for the check
tools: fixture generation, acceptance cases, and independent single-proof
plans, proofs, verification and key export. The `ix-prover` binary writes
range advice (`ix-prover ranges`).

```sh
cargo build --release --locked -p ix-prover --features parallel
cargo build --release --locked --target-dir target/formal-cuda \
  -p ix-prover --features parallel,cuda
```

## Incremental trace generation

Lanes and single-claim proofs populate traces incrementally, with independent
circuit-piece packing. The execution record stays alive while its trace
pieces are generated as needed; the complete source trace is never
allocated. Packing respects both the host workspace and the device cell
budget (`AIUR_TRACE_SHARD_MAX_CELLS`). An explicit `--shard-rows` caps each
piece. Planner options can select `"packing": false` for the uniform layout,
whose proofs are byte-identical to those of the complete trace; the check
tools use it as their reference.

`AIUR_GPU_TRACE=generated` fills eligible circuits on the device. Planning
accounts for their avoided host matrices and their persistent device record
tables and indexes. CUDA planning applies both the committed-cell bound and a
device-byte estimate, which still needs calibration; it can change the
selected layout or reject a plan.

`trace_seconds` includes host preparation and population in both proving
rounds; `proving_seconds` excludes it. The
[streaming design](formal-aiur-streaming-traces.md) describes the layout,
lifecycle and resource invariants.

## Scheduling and memory

The controller loads and checks each artifact once and keeps one prover
backend per application on each lane. Claims and ready joins execute through
one bounded queue shared by all lanes; prepared records go to the next free
lane, joins first. Lanes refill as individual jobs finish, without a wave
barrier.

The host budget is `--max-ram` (per GPU with `--lanes`, total with
`--jobs`), or 85% of available memory when omitted, capped by a visible
cgroup v2 limit. From it the controller reserves:

- one fixed prover workspace per lane, sized from the committed-cell limit
  as `ceil((16 × cells + 256 MiB) × 43 / 40)` bytes
  (`AIUR_HOST_WORKSPACE_BYTES` overrides it);
- the resident artifacts and backends, with a 25% margin;
- 10% headroom.

The rest is a shared `record-pool` for execution records. Records charge
arena, ROM, index, fixed-table and frame growth, and advice, to their
reservations; reservations follow record storage and are released when it
drops. When executions mutually block on growth, the pool cancels the
youngest and retries it after capacity is released. Each proof is planned
within its lane's workspace before traces are allocated. CUDA plans charge
host witnesses and upload staging; the commitment phases stay on the device.

One execution record may not exceed 128 GiB of counted storage
(`AIUR_RECORD_MAX_BYTES` overrides it). A claim over the ceiling is bisected
into whole blocks. Counted storage plus the workspace estimate is **not a
hard RSS limit**: allocator retention and transient runtime allocations also
use memory.

Progress goes to the controller's `[lanes]` log, including the host budget
split and a record-pool summary (peak granted bytes, growth waits,
contention retries). With `--aggregate`/`--lanes`, `--report` writes only the
verified root.

## Refinement and resume

When a claim must be split, the controller bisects it, writes the refined
partition immediately by atomic rename to
`<cache>/refined-manifests/<manifest hash>.ixes`, and continues with the
proofs it already has. `<cache>` is `$AIUR_LANES_CACHE_DIR`, or
`~/.ix/cache`. A rerun over the same manifest resumes from that partition. A
checkpoint records the partition, not a claim that all parts have proofs.
An atomic block over the ceiling stops the run ("cannot be split further");
it is never silently omitted.

Claim proofs are reused from the shard-proof index (`<cache>/shard-proofs`)
and joins from the aggregate cache (`<cache>/aggregate`), each verified
before reuse. The aggregate cache key includes the STARK parameters
(`fri_parameter_bytes`), so proofs made under other parameters are not
reused. `--no-cache` bypasses the aggregate cache and `--no-index` the
index. Before returning a root, the controller verifies every claim proof of
the run natively (the composed verdict). `--out-ixes` is written only after a
run completes.

## Validation

`tools/ixvm/check-controller.py` is the repeatable gate, also called by
`tools/ixvm/check-formal.sh`. On a three-constant environment with
dependencies, split into two leaves, it checks that:

- a record ceiling no claim fits stops the run on an atomic part and
  publishes no manifest;
- the pipeline with every join structural proves, passes the acceptance
  check, verifies independently, and resumes with no claim executed again
  and the aggregate cache hit;
- claims-only proving prints one verified proof per claim;
- with `--pipeline`, the complete aggregation proves, verifies and resumes.

`--devices 0,1` runs the gate on GPU lanes with independent CPU
verification. On a single GPU, `--devices 0,0` runs two lanes on one device
(the test opt-in `IX_PROVER_SHARED_DEVICES=1`, which `ix prove --lanes N`
also honors by placing every lane on the starting device). `IX_TEST_CUDA=1`
enables the one-device controller gate in `check-formal.sh`. Hardware results
are recorded in [GPU validation](formal-aiur-gpu-validation.md).
