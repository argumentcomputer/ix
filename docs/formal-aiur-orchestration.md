# Formal Aiur orchestration

The formal Aiur backend uses `crates/ix-prover` for resident proving. This
governs runtime scheduling and witness construction; it adds no Aiur primitive,
constraint, axiom, or `sorry`.

## Commands

```sh
# Independent manifest claims, two CPU prover lanes and four executions ahead.
ix prove --ixe env.ixe --ixes env.ixes --jobs 2 --exec-jobs 4 \
  --trace-shards --max-ram 64 --report claims.json

# Prove leaves, schedule recursive joins, verify the root, then publish it.
ix prove --aggregate --ixe env.ixe --ixes env.ixes --jobs 2 --exec-jobs 4 \
  --trace-shards --max-ram 192 \
  --out-ixes completed.ixes --report aggregate.json
ix verify --aggregate --ixe env.ixe --ixes completed.ixes ROOT_ADDRESS

# The same controller with four resident CUDA lanes, starting at device zero.
# Here RAM and positive execution counts are per GPU.
ix prove --lanes 4 --gpu-device 0 --ixe env.ixe --ixes env.ixes \
  --trace-shards --max-ram 96 --exec-jobs 3 --out-ixes completed.ixes

# One whole-environment claim across several execution records.
ix prove --distributed --ixe env.ixe --ixes env.ixes --exec-jobs 4 \
  --max-ram 64 --retention regenerate --report distributed.json
ix verify --distributed --ixe env.ixe --ixes env.ixes PROOF_ADDRESS
```

`--texray` prints timings/RSS for execution, trace population and proving.
`--direct-joins`, `--structural-above` and `--range` select the same recursive
strategies available to `ix aggregate`. Direct joins can save wrappers but need
more RAM. A very small `--shard-rows`, or a lane budget too small for a
single-shard verifier proof, can make recursive proofs grow rather than
shrink; root wrapping detects this and fails with a diagnostic.

`--lanes` selects CUDA, while `--aggregate --jobs N` runs the complete pipeline
on CPU. Explicit CUDA requests never select a CPU host silently. Hosts live in
`target/release` and `target/formal-cuda/release` of the checkout `ix` was
built in, with independent overrides `IX_PROVER_HOST` and `IX_PROVER_HOST_CUDA`.
Exporters, sources and the artifact cache (`.lake/aiur`) are also resolved
against that checkout (or `IX_ROOT`), so `ix` runs from any directory; outside
a checkout it fails unless the artifacts and hosts are supplied (see
[Formal Aiur in Ix](formal-aiur-migration.md#current-port-and-cli-integration)).
`ix prepare [--cuda]` builds the hosts and exports the IxVM and aggregation
artifacts ahead of time; otherwise the first command that needs an artifact
exports it (several minutes, once per source revision). Building by hand:

```sh
cargo build --release --locked -p ix-prover --features parallel
cargo build --release --locked --target-dir target/formal-cuda \
  -p ix-prover --features parallel,cuda
```

## Scheduling and memory

One Rust process checks each artifact once and keeps one prover backend for
each application on each lane. Lean submits dependency-ready jobs through
atomic control files. Execution records stay in Rust memory; they are never
serialized to those files. Ready recursive jobs have queue priority over new
leaves. Workers refill as individual jobs finish, without a wave barrier.

The `record-pool` crate manages bounded execution-record memory across workers.
Aiur charges record arena, ROM, index, fixed-table count,
frame, and distributed dependency storage growth to reservations. Advice is
charged conservatively before parsing. Reservations follow record storage and
are released when it drops. When executions mutually block on growth, the pool
cancels the youngest and retries it after capacity is released. Completed
records wait in a bounded priority queue.

After accounting for resident Rust artifacts/backends with a margin, half the
remaining budget goes to record storage and half to a prover workspace shared
by the lanes. Each job reserves its planned peak, normally within its lane's
equal share. Trace generation and proving are planned before allocating traces;
the execution record is dropped before STARK proving. CUDA plans charge host
witnesses and upload staging rather than the commitment phases, which stay on
the device.

A recursive job that its lane's share would split into more shards may plan
within the whole workspace instead and waits until that much is free
(reservations are granted in request order, so it is not overtaken). On CPU it
also runs on a thread pool spanning every lane, since the others wait. Without
this, each further level of the tree verifies every shard of the level below:
on the 342-constant environment, `--jobs 2 --max-ram 192` used to split wraps
into 8 shards and failed at the root, while it now proves single-shard wraps
and the same root as one lane ([GPU validation](formal-aiur-gpu-validation.md)).
Plans depend only on the budgets, not on timing. Job reports record
`borrowed_workspace` and `workspace_wait_seconds`. The default record ceiling
is 128 GiB, capped by pool capacity; `AIUR_RECORD_MAX_BYTES` overrides it. This is
counted record storage plus a conservative workspace estimate, **not a hard RSS
limit**. Lean's environment/witness buffers, allocator retention and transient
runtime allocations also consume memory. The controller does not clone records.

With `--report PATH`, resident runs preserve `PATH.events.jsonl`,
`PATH.ready.json` and `PATH.summary.json` alongside the result. They show queue
order, execution/proving phases, lane assignment, effective plans, record peak,
waits and retries. A failed job is drained with its admitted peers before the
controller and temporary advice files are destroyed.

## Refinement and resume

The combined pipeline bisects oversized environment leaves down to atomic
blocks. It checkpoints a valid refined partition immediately when a split is
chosen, even if proving its parts or joining them later fails. Checkpoints are
written by atomic rename and identified by the original environment/manifest
contents. They live under `~/.ix/cache/formal-lanes`, or
`$AIUR_LANES_CACHE_DIR/formal`.

Rerunning loads that partition and independently verifies cached leaf/aggregate
proofs before reuse. A checkpoint records the partition, not a claim that all
parts have proofs. `--out-ixes` is published only after the completed root is
verified. An atomic block or recursive record that cannot fit fails explicitly;
it is never silently omitted. `--no-cache` bypasses aggregate caches and
`--no-index` bypasses the leaf-proof index.

## Distributed records

`--distributed` proves one canonical `CheckEnv` claim with no assumptions. Each
nonempty manifest leaf owns its `IxVM::check_owned` calls. Calls owned elsewhere
are deferred only because their result is unit; their circuit lookup demands
remain. The host merges incoming multiplicities into the owning rows. Ordinary
function calls, hints and byte-table accelerators use the existing interpreter.

Each record allocates ROM addresses in a disjoint interval for every width.
Numeric addresses may still be reused across different widths. The existing
batch verifier checks interval ordering/disjointness and balances memory and
function lookups across all shards. Proof format and verifying keys are unchanged.
`WidthROM.append_valid` proves that valid ROMs with disjoint addresses within
each width compose into a valid ROM. The compiler correctness theorems remain
unchanged; Rust lowering and the cryptographic adapter keep their existing trust
boundary and this is not a new proof of the cryptographic backend.

A metadata pass executes workers in parallel and keeps their shapes, call
counts and dependency edges. Cached helper calls propagate owned-call
dependencies too, so a cycle cannot hide behind a memoization hit. Missing or
duplicate owners, cycles, overflow and changing replay shapes are rejected.
Proving replays one worker at a time. `regenerate` replays again in round two;
`retain` keeps commitments across all workers if the global estimate fits.
`auto` chooses from that combined estimate. This bounded-storage approach can
execute a worker three times, unlike legacy's caller-ordered commit pipeline;
it is a deliberate implementation tradeoff, not a performance parity claim.

## Validation (2026-10-29)

`tools/ixvm/check-controller.py` is the repeatable gate, also called by
`tools/ixvm/check-formal.sh`. It tests two resident CPU lanes with six jobs
(IxVM, recursive verification, aggregation), compares every proof/key byte to
standalone hosts, independently verifies the proofs, checks quota rejection and
reservation release, and compares distributed retain/regenerate proofs. The
distributed fixture has three well-typed constants with dependencies, two
workers, two cross-record calls and one public claim.

The complete pipeline gate (`--pipeline`) also ran on CPU with two lanes and a
192 GiB budget: direct joins produced a verified single-shard aggregate, and a
second invocation reused the verified root with **no execution events**. These
are integration tests, not a new performance comparison with legacy.

Initial complete-pipeline gate report:
`.lake/cuda-controls/controller-check-pfh7yywn/report.json`.
The final standard gate is saved under `.lake/orchestration-final`, including
`controller-check-euv1j7t4/report.json`. The forced 25,000,000-byte record test
split a three-block leaf into one and two blocks before failing on an atomic
part; its checkpoint remained valid and no completed manifest was published.
Removing the limit resumed from that partition and reused the independently
verified aggregate root (`.lake/orchestration-check/refinement-resume.json`).
The distributed proof was
`2677e65a118c21bb80cccfa9cb24fa6b814ed755505f1a198f6af51bd9218ae3`;
the aggregate root was
`a42a4374a76943c235938ec698578efcb2a9caced1dc77bf87b5ed3f65bc9691`.

Rust tests cover pool contention/cancellation, queue priority, reservation
lifetime, cross-record proofs, wrong claims, overlapping ROM intervals,
unresolved calls, cached-helper dependencies, retention planning and replay
failure. Lean tests cover failure draining in the scheduler. The ROM composition
lemma checks in Lean without new axioms or placeholders.
When this was validated, the targeted Rust suite passed 194 tests, with three
legacy tests ignored, and the standard gate also checked explicit legacy
bytecode execution; both legacy parts have since been removed.

The controller and both application hosts compile/link with CUDA 13.3.1 for
SM 80. The one-device gate passed on hardware on 2026-10-31
([GPU validation](formal-aiur-gpu-validation.md)); `check-controller.py --devices 0,1`
tests multiple GPU lanes and distributed proving, with independent CPU
verification; add `--pipeline` for complete aggregation. On a single GPU,
`--devices 0,0` runs two lanes on the same device (the test opt-in
`IX_PROVER_SHARED_DEVICES=1`, which `ix prove --lanes N` also honors by placing
every lane on the starting device). `IX_TEST_CUDA=1`
enables the one-device controller gate in `check-formal.sh` as well.
