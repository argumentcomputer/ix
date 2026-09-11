# Stage 2 CPU execution lookahead

> **Status (2026-09-11, end of day):** historical. The one-node lookahead it recommends was implemented for the range tree (`prove_range_level`) and measured as described below. Stage 2 has since moved to direct structural joins over env-shard claims with the same idea generalized into the DAG scheduler (`ix aggregate --exec-ahead`, commit a2faf5e3): Mathlib's 127 joins in 1:06:06. See `docs/aiur-gpu-plan-status.md`.

**Status update after ix `3a673630`: implemented and measured.** The committed
preparation/proving split and one-node lookahead reduced the same range-28 tree
from 4:32 to 3:46 (223.4 seconds tree time). The verified stored root is
9,500,004 bytes including its wrapper. THP was `always`; later verified runs
also resolved the original queue script's verification gap. The detailed
recommendation below records the earlier design and baseline, not outstanding
implementation work. See the updated [multi-GPU design](aiur-multi-gpu-design.md)
for the current worker boundary and first-leaf overlap opportunity.

The new default width `ceil(shards / (2 * max(jobs, 1)))` is a useful initial
heuristic; multi-GPU optimality has not been measured. Current lookahead is
only in `prove_range_level`'s `jobs <= 1` branch. Multiple GPU workers each need
that pipeline; the existing `jobs > 1` path does not provide it.

2026-09-11. Recommendation based on ix `5e94bdca` and the completed v12
range-12 GPU run. This review did not run or modify any prover workload.

**Recommendation:** keep the range/join/root protocol and add one CPU node
preparation ahead of one GPU node proof. The measured execution rate already
appears sufficient to feed the prover; the present scheduler serializes the
two phases. Use the existing within-node witness lookahead unchanged.

**Baseline.** `~/benchdata/trace-shards-gpu/queue15.sh`, launched by queue16,
aggregated the 56-shard Init batch with `--range 12 --jobs 1 --max-ram 100`,
trace sharding and a 1.5e9 committed-cell budget. There were five leaves,
four joins and one root.

| Measurement | Result |
| --- | ---: |
| Complete aggregate command | 376.06 s (6:16.06), exit 0 |
| Range tree | 372.1 s |
| Sum of node execution spans | 144.56 s |
| Sum of both proving-round spans over all nodes | 225.19 s |
| Host peak reported by time | About 30.9 GiB |
| Five leaf nodes | 221.0 s combined |
| Leaf execution / proving phases | 15.4–19.4 s / 23.8–29.6 s per node |
| Leaf retained-record estimate | 8.5–10.4 GB, before IO/other allocations |

Proving spans include witness preparation; they are not a measurement of
continuous GPU busy time. The log's node-level `query-record peak` labels
report a projected heaviest-shard prover peak, not actual record RSS.

The shell verification step was skipped: the script searches for a bare hash,
but the command printed `[aggregate] root proof: ...`. The queue log consequently
has an empty `root` value. Fix extraction and verify the persisted aggregate
before accepting the complete baseline. Successful proving is established;
that script did not establish final native verification.

**Expected benefit, conditional on unchanged phase times.**

With one CPU producer and one proof consumer, the five leaves would take
about 150 seconds instead of 221 seconds. Applying lookahead within each
existing tree level gives an estimated 291 seconds (4:51) for the command,
including its unchanged non-node overhead. That saves about 85 seconds.
Allowing the first join to prepare while the last leaf proves gives roughly
278 seconds (4:38), saving another 13 seconds. These are calculations from the
serial spans, not measured parallel runs. CPU/memory-bandwidth contention and
available host memory can reduce the benefit.

The simple within-level implementation is the first task. The final joins and
root depend on newly produced child proofs; lookahead cannot remove those
true dependency waits. A full ready-node scheduler is not necessary to obtain
most of the measured opportunity on this tree.

**Implementation handoff.** The production CLI calls the Rust controller in
`crates/ffi/src/aiur/aggregate.rs`. The retained Lean DAG scheduler is a
reference implementation, not the active range-tree path.

1. Split node preparation from node proving around `prove_aggr_io` and
   `AiurSystem::prove_ixvm_within_budget`. Preparation builds advice, runs
   `execute_ix_aggr`, and retains the execution's record, IO, input/output,
   node metadata and any CPU-only planning result in an owned prepared value.
   The consumer proves that exact execution. Extract/reuse the existing
   budget/trace-plan logic and `prove_from_execution_planned`; do not duplicate
   the planner or execute the node again when consuming the prepared value.
2. Adapt `prove_range_level` to a preparation iterator and a single proof
   consumer. The zero-capacity rendezvous-channel pattern already used by
   multi-stark's `consume_ahead` is sufficient. It permits the producer to
   prepare the next node while the consumer proves the current one, then
   blocks the producer from advancing further until handoff.
3. Permit at most one extra node **executing or prepared**, in addition to the
   node being proved. A channel with one queued item can accidentally allow
   another large record to execute before the producer blocks on send. Count
   both in-flight and completed preparation. Shared host admission must cover
   the active record, prepared record/IO, witness buffers, shared state and
   other live proof data. A one-item limit by itself is not a hard RSS bound.
4. Use one GPU-proof permit for the selected device across nodes in this
   process. Acquire it for the proving phase, after CPU execution; holding it
   across preparation would defeat the overlap. Do not obtain lookahead by
   simply increasing the existing `--jobs`, which currently runs complete
   nodes concurrently and changes their per-node RAM allowance.
5. Move records between Rust threads rather than serializing or cloning them.
   Keep the existing tree order, transcript, claims, node cache checks and
   final root semantics. Drain/join the producer on failures and release its
   memory. A failed preparation must prevent consumption of incomplete work.

No new preflight requirement, execution-size fit, or family of prefetch flags
is needed for the initial one-node pipeline. Keep the overall host budget and
its enforcement limitations explicit. Measure the combined live footprint in
the new run rather than adding unrelated per-node historical RSS peaks.

**Validation.** After the serial root is verified, compare the same batch,
range width, cell cap and host budget with lookahead enabled. Verify the root
and intermediate proof semantics; compare deterministic commitments where
applicable. Record execution/proving overlap, GPU starvation, actual peak
host/device memory and total elapsed time. Confirm there is one active GPU
proof and no duplicate node execution. Include an injected preparation failure
so shutdown cannot deadlock while holding records or channel endpoints.

**Next performance work.** One producer is enough when execution of a ready
node takes less time than proving a node, as it does in these leaf measurements.
Only add more CPU preparation workers if fresh timings show a throughput
shortfall and memory permits them. This parallelizes independent node records,
not concurrent mutation of one Aiur record.

After validating lookahead, compare fewer, larger ranges on the same input.
For example, two balanced leaves of 28 shards would require one join and one
root, four nodes instead of ten. Measure actual host memory, total trace cells,
intermediate proof bytes, final proof size and elapsed time; larger leaves can
increase both records and the child-proof cost of joins. There is no guarantee
that a node's prover workspace fits merely because trace sharding is enabled.

Use the CPU profile to identify repeated proof decoding, transcript/hash work,
field operations and record insertion costs before adding executor fast paths.
The generated native executor is already in use. Reducing full-preamble work
inside the circuit requires authenticated context reuse; a host-only cache
cannot replace checks the proof must constrain.

A single distributed recursive claim is a later design option. Its deferred
ownership entry must fit Aiur's void-return boundary; the current recursive
`aggr_verify_range` returns a residual and byte offset, so it cannot simply be
marked deferred. The new claim must bind all workers to the same batch and
challenges, cover every range exactly once, and constrain residual closure.
Its output is still a batch of trace-shard proofs. Measure that intermediate
shard count and the cost of verifying it at the next recursion layer before
assuming one batch plus one root replaces the whole tree at Mathlib scale.

Source files: `crates/ffi/src/aiur/aggregate.rs` (`prove_aggr_io`,
`prove_range_level`, `prove_range_tree`), `crates/aiur/src/synthesis.rs`
(`prove_ixvm_within_budget`, `prove_from_execution_planned`),
`Ix/Aggr/Circuit.lean` (`aggr_verify_range`, range leaf/join/root), and
`multi-stark/src/batch.rs` (`prove_batch_with`, `consume_ahead`).
Raw results: `~/benchdata/trace-shards-gpu/init-gpu-v12-stage2-range12.log`
and `queue16.log`.
