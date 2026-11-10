# Formal Aiur on the aggregate controller

## Summary

Formal Aiur proves on one Rust scheduler, `crates/aggregate-controller`. The
controller is generic over a `Backend` trait. Its only backend is the formal
one, `Formal` in `crates/ix-prover/src/aggregate.rs`.

The controller owns every scheduling rule:

- admission, priority, retry and cancellation;
- bisection of oversized claims;
- resume from the shard-proof index, the aggregate cache and the
  refined-manifest checkpoint;
- root wrapping and progress.

The backend reports memory estimates, and it executes, proves, verifies and
encodes one unit of work.

Lean keeps two things:

- the trusted acceptance check (`ix verify --aggregate`, and the same check
  that `ix prove` runs before it prints a root);
- artifact provenance: exporting and caching the certified artifacts.

The entry points are:

- `ix prove --ixe E --ixes M --trace-shards --lanes N`: N GPU lanes;
- `ix prove --ixe E --ixes M --trace-shards --aggregate --jobs N`: N CPU
  lanes;
- `ix prove --ixe E --ixes M` without aggregation: claims only (§2);
- `ix aggregate --ixe E --ixes M PROOF…`: fold supplied claim proofs
  (`Ix/Cli/FormalAggregate.lean` `run`).

Single claims prove through the stateless `tools::prove`
(`crates/ix-prover/src/tools.rs`), not the controller. There is no
distributed proving: formal `--distributed`/`--cells` proving and the
partitioned execution behind it do not exist.

## 1. Trusted and untrusted code

### What a formal root means

`ix verify --aggregate --ixe E --ixes M ROOT` (`FormalAggregate.verify`,
`Ix/Cli/FormalAggregate.lean`) accepts when all of the following hold:

1. `manifest`: `Ix.Shard.shardsCover` (`Ix/Shard/Environment.lean`) gives
   every constant exactly one owner, then `pruneEmpty` drops empty shards.
   The environment is the role-bound one (`Ix.Check.loadBoundIxe`, §3).
2. `Reference.expectedFromManifest env view above`
   (`Ix/Aggr/Reference.lean`) recomputes the expected root statement. It
   runs `schedulePlan` at the structural threshold, then folds through
   `CheckEnvTrees.join` and `joinStructural` (`Ix/Aggr/Host.lean`).
3. `auditAggregateConstants` (`Ix/Aggr/Verification.lean`): the root carries
   no assumptions, and its subject leaves are exactly the environment's
   constants, each once.
4. The wrapper's claim equals the expected claim.
5. `verifyWrapper ctx .aggr` runs the STARK verifier in process, through the
   library FFI (`FormalProver.verify`). It checks the proof against
   `Aggr.pubInput ctx.allowed (claim bytes)`. `ctx.allowed` (`Aggr.allowedBlob`,
   `Ix/Aggr/Protocol.lean`) binds both verifying keys and entry indices. They
   are taken from the artifacts that `compiledArtifact`
   (`Ix/Cli/FormalAiur.lean`) exports from certified sources.

With `--ixe` alone, step 2 is replaced by `envCanonicalTree`, which accepts
only flat roots.

The circuits (`ix_aggr`) check every fold relation, Merkle path, preimage and
child proof against those public inputs. A wrong witness therefore produces
either no proof or a proof of a different claim, and step 4 rejects that
claim.

### The trusted step in `ix prove`

`runController` passes a JSON configuration to `FormalProver.proveLanes`
(`rs_formal_prove_lanes`, `crates/ffi/src/formal.rs`). The controller
returns the root's store address and always writes the final partition, to
`--out-ixes` or to a temporary file. `accept` then runs steps 1–5 on that
partition, with the same definitions `verify` uses. The root is printed only
if `accept` passes. `ix aggregate` applies `accept` to a full root and
`acceptSlot` to a `--subtree` or `--reprove-slot` result. Under `--no-write`
the controller returns the proof's wrapper bytes with its address, and the
same check runs on those bytes.

### Untrusted Rust

Every Rust step either builds a witness that the circuits check again, or
picks what to prove next:

| Rust | Why untrusted |
|---|---|
| Leaf advice (`ixon::witness`, `request::leaf_advice`, `request::bind_advice`) | A witness. A wrong one fails execution or proves a claim that verify rejects. |
| Aggregation streams (`aggregate_controller::streams`, `advice`) | Channel 0–6 advice. `ix_aggr` re-hashes every tree and path. |
| The statement fold (`prepare`, `plan`, `statement`) | Used to name outputs and to build witnesses. Verify refolds independently. |
| Scheduling, caching, bisection, resume | Cached proofs are checked again by their parent circuit and by verify. |
| Native verification of resumed, cached and leaf proofs | A liveness check that fails early instead of in the parent. |

## 2. Controller crate

`crates/aggregate-controller` depends on `ixon`, `ix-common`, `record-pool`,
`rayon`, `rustc-hash` and `blake3`. No prover is in its dependency graph.
Shard types (`ShardManifest`, `static_block_profile`, `bisect_leaves`,
`RAM_USABLE_FRAC`) come from `ixon::shard` (`crates/ixon/src/shard.rs`).

| Module (`crates/aggregate-controller/src/`) | Contents |
|---|---|
| `lib.rs` | `expected_from_manifest` (the Rust fold with its audit) and `claim_context`. |
| `backend.rs` | `Identity`, `Backend`, `Slot`, `Run`, `ProvenClaim`, `PrepareFailure`. |
| `statement.rs` | Host statements: cached roots, sorted leaves, structural subject trees with shard-membership bitsets. |
| `prepare.rs` | `PreparedRun`, `prepare_run`, `validate_root_statement`. |
| `plan.rs` | `PlanOp`, `SlotSpec`, `FoldPolicy`, `build_statement_specs`, `build_specs`, `subtree_plan`, `plan_replay`, `shape_ram_bytes`. |
| `advice.rs` | `tree_advice`, `structural_path_advice`, `path_payload`, `advice_trees`. |
| `streams.rs` | The ordered `ix_aggr` advice streams, with in-place replacement. |
| `protocol.rs` | Shape codes, `serialize_claims`, `allowed_blob`, `WordIdentity`, `CACHE_VERSION`. |
| `store.rs` | The content-addressed store, the shard-proof index and the aggregate cache. |
| `lanes.rs`, `lanes/{limits,checkpoint,queue}.rs` | The proving run: `Config`, `plan_pass`, `resume_pass`, the prepare and prove loops, `composed_verdict`, `HostBudget`. |
| `scheduler.rs`, `aggregate.rs` | `ix aggregate`: the slot scheduler (`SlotWorker`, `run_scheduler_with`) and its run. |

### Backend trait

`Identity` is a supertrait with an associated `Claim` type, so plans
(`SlotSpec<C>`) and slots (`Slot<C, P>`) carry the backend's own field
words. It supplies `outer_claim`, `claims_bytes` and `cache_key`, which are
pure functions of the claim bytes, so a plan can be built without a prover.

`Backend` adds:

- `lanes(count)`: resident provers with equal verifying keys;
- `resident_bytes` and `lane_workspace_bytes`: the only per-backend resource
  inputs (§4);
- `bind(reservation)`: the guard that routes the current thread's records to
  a reservation;
- `execute_claim` and `execute_aggregate`, on an executor thread. They take
  the controller's expected claim or plan slot and the bound
  `RecordReservation`. `execute_aggregate` returns a staged record or a cache
  hit;
- `prove_claim` (returns a `ProvenClaim`, which the controller persists and
  indexes), `prove_aggregate` and `wrap_root`, on the lane's prover thread;
- `verify` and `verify_on(lane, ..)`, `trace_shards`, `encode_proof` and
  `decode_proof`.

`Run` gives the backend read access to the plan: specs, prepared shards,
owners, the store and cache directories, the slot budget, and
`reprove_slot`. It also carries `range_width`, which both formal entry points
leave `None`.

### Run configuration and fold

`lanes::Config` carries:

- `lanes`, `max_ram_bytes` and `exec_jobs`;
- `fold: FoldPolicy { structural_above, direct_joins }`;
- `use_cache` and `use_index` (`--no-cache`, `--no-index`);
- `out_manifest`, `store_dir` (default `~/.ix/store`) and `cache_root`
  (default `AIUR_LANES_CACHE_DIR`, else `~/.ix/cache`);
- `claims_only`, `select` and `assume_binding`.

The fold is fixed:

- **Direct joins.** Claims join directly: shapes 2 and 6 over raw IxVM
  proofs, then shapes 5 and 9 over aggregates. `plan_pass` rejects
  `direct_joins == false`. The fold never wraps a single claim, so
  wrap-first leaves and range wrapping do not exist. `--range` is rejected by
  `ix prove` and `ix aggregate`. `--direct-joins` is accepted and has no
  effect.
- **Structural threshold 0.** `Aggr.defaultStructuralAbove = 0`
  (`Ix/Aggr/Parameters.lean`), so every join is structural, and `ix prove`,
  `ix aggregate` and `ix verify --aggregate` agree without a flag. A root
  proved at a different `--structural-above` verifies only with the same
  value.
- **Root wrapping.** `ix prove` wraps the root (`wrap_root`) until it is one
  trace shard or stops shrinking. `ix aggregate` does so with `--wrap-root`.

Persistent state lives under the cache root:

- the shard-proof index, `shard-proofs/`;
- the aggregate cache, `aggregate/<key>`. The key is
  `blake3(CACHE_VERSION ‖ blake3(aggr vk) ‖ FRI parameter bytes ‖ outer
  claim)` (`WordIdentity::cache_key`);
- the refined-manifest checkpoint, `refined-manifests/<hash(manifest)>.ixes`.

The checkpoint is always kept. Without the cache, the aggregate cache is
neither read nor written. Without the index, the shard-proof index is
neither read nor written.

Before a root is accepted, `composed_verdict` re-verifies every leaf proof
the run holds, natively and in parallel.

### Claims only

With `claims_only`, the plan has no joins and no root. Selection by shard id
carries over to the parts of a bisected claim. The run ends when the claim
queue drains, after a composed verdict over the selected claims, and returns
one `id address` line per claim. `ix prove --ixe --ixes` without
`--lanes`/`--aggregate` proves this way:

- `--keep-going` is rejected: the controller stops at its first failure and
  resumes on rerun;
- the index is read unless `--no-index`;
- `--trace-shards` is implied.

`--exec-only` and plans still run per shard in Lean on the stateless
`check`.

### `ix aggregate`

`aggregate_controller::aggregate::run` folds supplied claim proofs on the
slot scheduler, with the same fold as `ix prove`. Each supplied proof is
bound to its claim by digest and verified before it is joined. The run
supports:

- `--subtree`, which publishes its root through the aggregate cache;
- `--reprove-slot`, which needs cache reads;
- `--plan-only`;
- `--wrap-root`;
- `--exec-ahead` (default 1): slots that execute ahead of the provers.

Supplied aggregate (`IXAGGR2`) proofs are not inputs; the aggregate cache
plays that role. Lanes are checked out by one proving thread at a time.

## 3. Formal backend

`Formal` (`crates/ix-prover/src/aggregate.rs`) holds the IxVM and `ix_aggr`
programs, their executors, verifiers and verifying keys, and a
`WordIdentity`. Its `Identity` is `WordIdentity`:

- an IxVM outer claim is `[1, ixvm index] ++ digest words`;
- an aggregate outer claim is `[1, aggr index] ++ pubInput`;
- the cache key includes `fri_parameter_bytes(Parameters::default())`, so
  cached proofs follow the parameters actually in use.

The production parameters are `Parameters::default`
(`crates/aiur/src/trace/stark.rs`): `log_blowup` 2 (blowup 4), 100 queries
and 20-bit query proof of work.

- **Lanes.** A `Lane` holds both provers on its device, a prover thread pool
  of `cores / lanes` threads, and a `ShardFeed` population pool of the same
  width. A pipelined proof runs its shard producer on a scoped OS thread
  inside that pool, so the producer always starts. The producer stops on its
  first error, and the consumer returns it.
- **Environment.** Lean loads the `.ixe` with `Ix.Check.loadBoundIxe`. A file
  with a role binding is passed to Rust as is (`Aiur.EnvHandle.fromIxe`). A
  file without one is normalized in memory with `withDefaultRoleBinding` and
  serialized, and Rust decodes exactly those bytes (`Aiur.EnvHandle.fromBytes`).
  The controller receives that handle; nothing is written to disk, and Rust
  never reopens the file.
- **Claim execution.** `execute_claim` rebuilds the leaf witness with
  `request::leaf_advice` (`WitnessRequest::ShardCheckEnv`) against the
  controller's expected claim, so every leaf rechecks the Rust fold. Leaf
  advice follows the role-binding recipe in `crates/ixon/src/witness.rs`:
  - the role binding on channel 6;
  - its bound roles and proof evidence (`binding_roots`) as extra roots of
    the byte scope;
  - `assume_binding` taken from the expected claim's context.

  `request::bind_advice` charges the advice and hint maps to the execution's
  reservation before allocation.
- **Aggregate execution.** Joins and root wraps use
  `aggregate_controller::streams`. A cache hit is returned staged, without
  execution.
- **Proving.** Records are planned at proving time within the lane workspace
  (`cell_workspace`, or `AIUR_HOST_WORKSPACE_BYTES`). A plan that does not
  fit is fatal with a `--max-ram` diagnostic. Each proof logs its population
  stall.
- **Persistence.** Leaf wrappers are `IXAIUR2\0 ++ raw` and aggregates
  `IXAGGR2\0 ++ raw`, in the shared store. `decode_proof` rejects a proof
  with any other magic, and the slot is proved again.
- **Failures.** `BudgetError::Exceeded` maps to
  `PrepareFailure::OverRecordCap`, which bisects the claim.
  `BudgetError::Cancelled` maps to `MemoryContention`, which requeues it.
  Anything else fails the pass.

`ffi` exposes `rs_formal_prove_lanes` (a JSON `LaneConfig`) and
`rs_formal_aggregate` (a JSON `AggregateConfig`). Single claims and the
`--exec-only`/plan checks still pass a Lean-selected claim to Rust through
`rs_formal_request_check`, `rs_formal_request_shard` and
`rs_formal_request_buffers`.

### Role binding

`ix prove --ixe --ixes --assume-binding` proves claims-only shard claims that
assume the environment's binding meets the specifications. `ix prove-binding`
proves the binding claim once, and `ix verify --binding-proof` checks the two
together.

The controller does not discharge a binding. `--binding-proof` and
`--assume-binding` are rejected with `--lanes`/`--aggregate` and by
`ix aggregate --ixe`, so no command discharges a binding into an aggregate;
`FormalAggregate.dischargeBindingNode` is defined but has no caller. Catalog
aggregation (`ix aggregate --ixc`, `Ix/Cli/CatalogAggregate.lean`) proves on
the one-shot `stark-verifier` host (`FormalAggregate.proveAdvice`), with
advice built in Lean.

## 4. Record pool and estimates

`HostBudget` (`lanes/limits.rs`) sets the backend's resident bytes aside
before any record is admitted. It admits with
`initial = records / (2·lanes + executions)`, so admission bounds
concurrency by memory. A preferred waiter keeps first claim on pool growth
until its execution finishes. A single long preferred execution can
therefore serialize a run.

| Input | Formal value |
|---|---|
| `resident_bytes` | `planning::resident_memory() · 5/4`, measured after the lanes are built |
| Lane workspace | `cell_workspace(cells)`, or `AIUR_HOST_WORKSPACE_BYTES` |
| Per-record ceiling | 128 GiB (`DEFAULT_RECORD_MAX_BYTES`), overridden by `AIUR_RECORD_MAX_BYTES` |
| Advice charge | Advice and hint maps, charged before allocation |

`--max-ram` is per GPU with `--lanes` and the total with `--jobs`. When it is
omitted, the controller detects the host's allowance. `--exec-jobs` is per
lane, and 0 divides the cores among the lanes. Each lane plans within its
fixed workspace share, with no borrowing between lanes.

## 5. Advice streams and parity

`aggregate_controller::streams` builds the `ix_aggr` streams in the order
that Lean's reference builder in `Tests/FormalAdvice.lean` produces:

1. identity: `ch3[0] = allowed`, `ch6[0] = [shape]`;
2. each child: `ch1[kind] = vk`, `ch0[slot] = raw proof`,
   `ch2[slot] = serialized outer claim`;
3. pairs only:
   - `ch2[2] = output claim`;
   - `ch4[digest]` preimages for the left claim, then the right claim;
   - `ch5[root]` for each tree in `advice_trees` order;
   - structural pairs: `ch6[candidate] = path payload` for each assumption
     candidate, in sorted order.

A repeated `(channel, key)` replaces the earlier payload in place. Range
shapes 10–12 are not encoded.

`check-formal.sh` (`tools/ixvm/check-formal.sh`) runs `formal-aggregate-tests`,
which writes `aggregation.json.streams.json`. The file covers both wraps,
every pair shape (flat and structural), and a pair whose children and output
share one assumption tree, each built by Lean. The script then runs the
`streams_parity` example (`crates/aggregate-controller/examples/streams_parity.rs`)
on that file. The example compares the Rust streams byte for byte, and
checks that the Rust fold reaches Lean's output claim for every pair. The
same script runs `formal-checks controller`
(`Tests/FormalChecks/Controller.lean`), which covers a controller prove, an
independent verify, a resume, and claims-only manifest proving.

## 6. Migration stages

All stages are done.

| # | Stage | Status |
|---|---|---|
| S0 | Record-pool growth priority held until the preferred execution finishes. | Done |
| S1 | `aggregate-controller` crate and `Backend` trait; `static_block_profile` in `ixon::shard`. | Done |
| S2 | `FoldPolicy` as run configuration, `use_cache`/`use_index`, `resident_bytes`. Wrap-first leaves dropped. | Done |
| S3 | Rust advice encoder (`streams`) and the `streams_parity` test. | Done |
| S4 | Formal backend, `rs_formal_prove_lanes`, the trusted `accept` after the controller. | Done |
| S5 | `ShardFeed` population pools. | Done |
| S6 | The controller is the only path for `ix prove --lanes/--aggregate`. Lean scheduling, `ix prove --exec-ahead`, and the session's workspace borrowing are removed. | Done |
| S7 | `ix aggregate` on the slot scheduler, with `--subtree`, `--reprove-slot`, `--plan-only` and `--wrap-root`. `--range` rejected. | Done |
| S8 | Claims-only plans for `ix prove --ixe --ixes`. Single claims through `tools::prove`. | Done |

The prover session and its spool, the Lean scheduler (`runCore`,
`proveNode`, the range nodes, `wrapRanges`, `neededSlots`), and formal
distributed proving no longer exist. The `ix-prover` binary keeps only the
`ranges` tool.

## 7. Decisions

- **One cache and store layout.** The aggregate cache key covers the cache
  version, the aggregate verifying key, the FRI parameter bytes and the outer
  claim. Proofs made under other STARK parameters are not reused.
- **Composed verdict.** The controller re-verifies every leaf proof natively
  before it accepts a root. This is a rule, not a flag.
- **Fold.** Direct joins, structural threshold 0, and the root wrapped to one
  trace shard.
- **Report.** With `--report`, `ix prove --lanes/--aggregate` writes only the
  verified root (`ix-formal-pipeline/1`). Progress is the `[lanes]` log, which
  `formal-checks controller` reads.

## 8. Init benchmark

Measured on `formal-aiur-perf` at `b8e708a35`, before PR 678: 7:30.2 wall,
131.8 GiB peak RSS, root `cf5b813b…`. The run used one CUDA GPU,
`Init-230.ixes`, `--exec-jobs 3 --max-ram 230`, direct joins, structural
threshold 0 and the production parameters. IxVM has since gained role
binding, so the current root differs, and the figure has not been re-measured
since.

## 9. Open questions

1. **Mathlib under the pool policy.** One long preferred execution can
   serialize a run. Before the definitional-equality identity precheck,
   formal Mathlib leaves reached 137–142 GB on `Char.all.eq_1`; with it,
   measured leaves are 27–40 GB, in legacy's range. A full formal Mathlib
   run has not been made since, so whether to pre-bisect leaves whose
   measured peak is over the ceiling remains open.
2. **Population pool width.** Each lane's `ShardFeed` is as wide as its
   prover pool. A narrower pool has not been measured.
