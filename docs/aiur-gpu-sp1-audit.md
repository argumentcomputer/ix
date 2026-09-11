# SP1 GPU and Cluster adoption audit

> **Status (2026-09-11, end of day):** still applicable. Reviewed at ix `3a673630` / multi-stark `ac144be2`; the pipeline has since moved to env-shard claims (`docs/aiur-gpu-plan-status.md`), which changes the scheduling around each proof but not the proof itself. The per-proof findings here (allocation and pinned-buffer reuse, cached device metadata, transfer overlap) target the ~40 % of each proof the GPU sits idle, the next Stage 1 lever.

2026-09-11. Source review revisiting SP1 after the
[Zisk/proofman audit](aiur-gpu-zisk-proofman-audit.md). No builds, tests,
benchmarks, or GPU jobs were run. Upstream source was read in existing
checkouts or isolated temporary snapshots; no upstream code was changed.
The performance opportunities below have not been measured on our workload.

| Source | Reviewed revision and scope |
| --- | --- |
| ix | `3a67363049ceddfe797958e9f2fb2467e5ca79a4`, `sb/aiur-trace-sharding-gpu` |
| multi-stark | [`ac144be2eb670aa081ec3800614454f3c036b7b5`][ms], pinned by ix |
| SP1 GPU | [`5517b0a04d893e4278be09e7077a785830468e76`][sp1], current `main`; workspace version 6.8.0 |
| SP1 Cluster | [`316b524c9f394b810badd23e99ac79b0de13ac02`][cluster], current `main`; release 2.8.2 |
| Cluster's SP1 runtime | [`f5a5bbf6a1cf6007315b410d88678d96fb399fb5`][runtime], tag `v6.6.0` |

Cluster [pins SP1 to 6.6.0][cluster-deps] and delegates substantive task work
to `sp1-prover`, so that matching runtime was read separately. GPU `main`
and Cluster are not assumed to form one tested build. Earlier local docs
reviewed GPU revision `a3f98a36` and the same Cluster revision listed above.

**The strongest additional ideas are cached, partitioned constraint programs
and recomputation of the lower Merkle paths.** SP1 also provides concrete
references for streaming completed proofs into recursion and separating CPU
preparation, GPU admission, and output publication. Zisk remains the more
direct Goldilocks/BLAKE3 kernel reference.

This supplements the [earlier upstream review](aiur-gpu-upstream-review.md),
[performance recommendations](aiur-gpu-performance-recommendations.md), and
[multi-GPU design](aiur-multi-gpu-design.md). Our current baseline already
includes batch witness lookahead, Stage 2 node lookahead, pinned upload
staging, resident proving, and liveness-based temporary-slot reuse.

1. **Cache GPU constraint programs, then partition by shared inputs and live storage.**

   SP1 compiles and uploads machine-stable bytecode at prover construction
   and reuses it across shards. Its chunker groups constraints by overlapping
   input columns under resource budgets. General expressions use an
   interpreter with reused temporary slots; suitable linear sums use a
   column/term-parallel kernel. Runtime values and challenge offsets remain
   separate from the cached program. [Construction][program-cache],
   [chunking][chunker], [dispatch][constraint-dispatch]

   This is an intermediate option before proofman's per-AIR CUDA source
   generation. Our quotient and lookup encoders already reuse slots, and our
   graph shares common expressions. The remaining opportunities are program
   lifetime, partitioning, and specialized execution. The resident quotient
   path still encodes graph metadata and uploads it for each call.
   [Local encoder][ms-encoder], [resident upload][ms-quotient]

   First cache immutable instructions, roots, and lookup descriptors per
   graph/device, keeping public values, challenges, selectors, and pointers
   dynamic. Then compare bounded chunks and linear-sum specialization with
   our fused evaluator. Preserve every assertion and canonical challenge
   index when changing evaluation order. Chunking can duplicate loads or
   add launches; SP1's 32-bit field resource thresholds need retuning for
   our 64-bit Goldilocks arithmetic.

   **Assessment:** a useful new experiment if quotient/lookup work is
   material. Caching is the smaller step; full CUDA generation remains an
   option. Liveness allocation alone is already implemented here.

2. **Keep upper Merkle levels and reconstruct queried lower paths.**

   SP1 drops eight bottom levels from retained trees of height at least 15.
   At opening time it rehashes the corresponding 256-leaf subtree per query
   and combines those siblings with the stored upper path. This keeps roughly
   1/256 of the full tree's digest storage, not 1/256 of all prover memory.
   [Storage policy][merkle-tree], [commit/open implementation][merkle-open]

   Our CUDA implementations retain full digest trees, including the
   [mixed-height tree][ms-merkle]. An independently implemented variant could
   preserve commitments and proof bytes while reducing retained VRAM. It
   complements Zisk's commitment-only first pass by retaining enough
   information to open proofs later.

   SP1 constructs the full tree before copying the upper levels, so it does
   **not** remove the initial full-tree allocation. Original committed leaf
   values must also remain available or reproducible. Measure extra BLAKE3
   work and leaf reads, especially for wide rows and spilled LDEs. Begin
   with a single-height tree; mixed-height reconstruction must reproduce
   every lower-height matrix injection. A memory-bounded tree builder is a
   separate change.

   **Assessment:** the clearest additional memory experiment. Measure
   retained memory and construction peak separately; the benefit depends
   on digest storage's share of our working set.

3. **Combine SP1's shared GPU admission with Zisk's completion events.**

   SP1 starts CPU trace generation into pooled pinned storage before
   acquiring its GPU permit. Completed chip traces can upload while the
   remaining CPU traces are generated. One permit is shared by core,
   recursion, shrink, and wrap provers. Upload and device trace generation
   occur after acquisition; CPU lookahead does not imply unrestricted
   cross-proof GPU overlap. [Trace pipeline][trace-pipeline], [permit][permit]

   Its ordinary shard path holds the pinned buffer until proving returns.
   Proofman's release after the last upload event suggests separating
   host-buffer lifetime from device-workspace lifetime. Our next step would
   be direct pinned witness production with one common device admission
   mechanism across Stage 1 and Stage 2. Account for all pools together and
   keep buffers alive through both CPU writers and DMA completion.
   [SP1 buffer lifetime][buffer-lifetime]

   **Assessment:** reinforces the existing direction and makes its resource
   boundaries concrete. Further overlap needs evidence that it improves the
   critical path; Zisk explicitly quiesces competing work during its
   latency-sensitive GPU planning phase.

4. **Feed completed shard proofs into ready recursive ranges.**

   Cluster's SP1 runtime receives proof-completion events, joins adjacent
   ranges, and submits reductions as groups become ready. It tracks the
   final range separately and filters duplicate delivery. The core prover
   releases its GPU permit before later normalization or output publication;
   recursive preparation, execution, and proving have separate worker/queue
   capacities. [Range controller][ranges], [release][release],
   [recursion stages][recursion-stages]

   Our [aggregation code](../crates/ffi/src/aiur/aggregate.rs) already overlaps
   preparation of one node with proving another. The next interface is an
   indexed stream of completed Stage 1 round-two proofs, with the frozen
   batch context, into ready range leaves. Start by overlapping the first
   leaf's CPU execution with remaining Stage 1 GPU work. Later, ready leaf
   proofs can share device admission or run on another GPU.

   Preserve Aiur's all-header transcript barrier and predetermined ranges;
   completion order must not redefine proof order or tree shape. Budget
   queued proof bytes and prepared records. Several SP1 controller channels
   are unbounded, so task separation alone does not establish a memory bound.
   Keep large Aiur execution records local rather than routing them through
   a service artifact store.

   **Assessment:** strengthens an existing proposal. It may matter more to
   total latency than kernel work when CPU preparation is exposed.

5. **Generate selected trace columns from compact events on-device.**

   SP1 supports recursive ALU, Poseidon, selection, conversion, and
   prefix-check trace generation from events/instructions. Its ordinary
   RISC-V main-trace GPU dispatcher currently enables only the Global chip.
   [Recursive dispatch][recursion-traces], [event expansion][event-expansion],
   [RISC-V dispatch][riscv-traces]

   This agrees with proofman's compact witness plus GPU expansion. Aiur
   candidates are repeated hash/byte gadgets and regular derived columns,
   selected from measured witness-generation costs. Preserve padding and
   lookup multiplicities. Neither upstream establishes that all our
   execution or witness construction should move to the GPU.

   **Assessment:** a targeted follow-on project, distinct from speeding up
   irregular CPU execution.

6. **Consider LDE recomputation as an alternative to full host spill.**

   SP1 can discard a main-trace codeword after commitment and reconstruct it
   before opening; Merkle data remains available. This uses optional
   codeword storage and a later transform. [Retention][lde-retain],
   [reconstruction][lde-recompute]

   We already support resident and host-spilled matrices. The additional
   choice is rematerialization from retained compact inputs when an extra
   transform is cheaper than retaining/transferring the full LDE. This is
   distinct from both batch `Retention::Regenerate` and Zisk's commitment-only
   streaming. Every lookup, quotient, and opening consumer still needs the
   correct values, and recomputation needs workspace of its own.

   **Assessment:** conditional on memory/PCIe pressure; it can slow workloads
   that already fit comfortably.

7. **For multiple workers, budget artifact bytes and publish outputs atomically.**

   Cluster's limiter accounts for cgroup-aware RAM and, where relevant,
   shared-memory capacity. Its Redis client reserves in-flight bytes through
   upload completion, uses unique staging keys, and publishes only complete
   artifacts. Task weights remain estimates, and client admission is not a
   global hard memory limit. [Worker budget][worker-budget],
   [reservations][artifact-budget], [publication][artifact-publish]

   Apply the concepts to local workers/files: budget RAM, VRAM, pinned
   buffers, and pending artifacts; identify attempts; and drain users before
   reusing storage. Much is already proposed in our multi-GPU design.
   Cluster's balanced policy allocates capacity across proofs and chooses
   workers by predicted availability/weight; it is not proofman's
   resident-key affinity policy. Our single-claim workload needs its own
   dependency, locality, and memory decisions. [Assignment][assignment]

   **Assessment:** useful for multi-worker implementation. The service stack
   and multi-tenant scheduling add no immediate single-GPU speedup.

**Adoption boundaries.** SP1's reviewed GPU path uses KoalaBear, Poseidon,
and Hypercube/jagged multilinear machinery. Its optional cuPQC adapter
explicitly uses 32-bit KoalaBear; sppark remains the default. Neither is a
demonstrated replacement for our Goldilocks LDE. Keep the bounded Goldilocks
NTT experiment and proofman's fusion ideas as the direct comparisons.
[NTT configuration][ntt-readme], [cuPQC adapter][nvidia]

Jagged layout includes authenticated row/column metadata and specialized
proving logic. Compact storage and delayed padding are useful where our
existing commitments permit them; adopting SP1's jagged commitment itself
requires protocol work. Its Poseidon kernels provide no new BLAKE3
implementation for this branch. [Jagged commitment][jagged]

**Recommended sequence and validation.** Keep short-row BLAKE3 and fused LDE
loads as the first kernel experiments from the Zisk audit. Add cached
constraint programs as the smaller SP1-derived change, and test truncated
Merkle retention when digest memory is material. Develop the proof-completion
interface for exposed Stage 2 preparation and multiple GPUs.

Compare complete cold proofs, Stage 2/root verification, host/VRAM peaks,
and output bytes. Constraint changes must preserve every assertion and
challenge weight. Merkle changes need exact roots and full/pruned openings,
including boundary indices, mixed heights, and spilled leaves. Pipeline
changes need cancellation, duplicate/stale completion, slow-consumer, and
buffer-lifetime checks. Include packing, transfers, recomputation, and
layout conversion in timing. None of those runtime checks was performed
for this source-only audit.

[sp1]: https://github.com/succinctlabs/sp1/tree/5517b0a04d893e4278be09e7077a785830468e76/sp1-gpu
[cluster]: https://github.com/succinctlabs/sp1-cluster/tree/316b524c9f394b810badd23e99ac79b0de13ac02
[runtime]: https://github.com/succinctlabs/sp1/tree/f5a5bbf6a1cf6007315b410d88678d96fb399fb5
[ms]: https://github.com/argumentcomputer/multi-stark/tree/ac144be2eb670aa081ec3800614454f3c036b7b5
[cluster-deps]: https://github.com/succinctlabs/sp1-cluster/blob/316b524c9f394b810badd23e99ac79b0de13ac02/Cargo.toml#L52
[program-cache]: https://github.com/succinctlabs/sp1/blob/5517b0a04d893e4278be09e7077a785830468e76/sp1-gpu/crates/shard_prover/src/prover.rs#L85
[chunker]: https://github.com/succinctlabs/sp1/blob/5517b0a04d893e4278be09e7077a785830468e76/sp1-gpu/crates/air/src/ir/chunker.rs#L1
[constraint-dispatch]: https://github.com/succinctlabs/sp1/blob/5517b0a04d893e4278be09e7077a785830468e76/sp1-gpu/crates/zerocheck/src/prover.rs#L92
[ms-encoder]: https://github.com/argumentcomputer/multi-stark/blob/ac144be2eb670aa081ec3800614454f3c036b7b5/src/cuda/mod.rs#L547
[ms-quotient]: https://github.com/argumentcomputer/multi-stark/blob/ac144be2eb670aa081ec3800614454f3c036b7b5/cuda/kernels.cu#L2741
[merkle-tree]: https://github.com/succinctlabs/sp1/blob/5517b0a04d893e4278be09e7077a785830468e76/sp1-gpu/crates/merkle_tree/src/tree.rs#L20
[merkle-open]: https://github.com/succinctlabs/sp1/blob/5517b0a04d893e4278be09e7077a785830468e76/sp1-gpu/crates/merkle_tree/src/single_layer.rs#L149
[ms-merkle]: https://github.com/argumentcomputer/multi-stark/blob/ac144be2eb670aa081ec3800614454f3c036b7b5/cuda/kernels.cu#L3998
[trace-pipeline]: https://github.com/succinctlabs/sp1/blob/5517b0a04d893e4278be09e7077a785830468e76/sp1-gpu/crates/jagged_tracegen/src/lib.rs#L719
[permit]: https://github.com/succinctlabs/sp1/blob/5517b0a04d893e4278be09e7077a785830468e76/sp1-gpu/crates/prover_components/src/builder.rs#L111
[buffer-lifetime]: https://github.com/succinctlabs/sp1/blob/5517b0a04d893e4278be09e7077a785830468e76/sp1-gpu/crates/shard_prover/src/prover.rs#L303
[ranges]: https://github.com/succinctlabs/sp1/blob/f5a5bbf6a1cf6007315b410d88678d96fb399fb5/crates/prover/src/worker/controller/compress.rs#L325
[release]: https://github.com/succinctlabs/sp1/blob/f5a5bbf6a1cf6007315b410d88678d96fb399fb5/crates/prover/src/worker/prover/core.rs#L612
[recursion-stages]: https://github.com/succinctlabs/sp1/blob/f5a5bbf6a1cf6007315b410d88678d96fb399fb5/crates/prover/src/worker/prover/recursion.rs#L55
[recursion-traces]: https://github.com/succinctlabs/sp1/blob/5517b0a04d893e4278be09e7077a785830468e76/sp1-gpu/crates/tracegen/src/recursion/mod.rs#L1
[event-expansion]: https://github.com/succinctlabs/sp1/blob/5517b0a04d893e4278be09e7077a785830468e76/sp1-gpu/crates/tracegen/src/recursion/poseidon2_wide.rs#L78
[riscv-traces]: https://github.com/succinctlabs/sp1/blob/5517b0a04d893e4278be09e7077a785830468e76/sp1-gpu/crates/tracegen/src/riscv/mod.rs#L9
[lde-retain]: https://github.com/succinctlabs/sp1/blob/5517b0a04d893e4278be09e7077a785830468e76/sp1-gpu/crates/basefold/src/fri.rs#L79
[lde-recompute]: https://github.com/succinctlabs/sp1/blob/5517b0a04d893e4278be09e7077a785830468e76/sp1-gpu/crates/basefold/src/fri.rs#L332
[worker-budget]: https://github.com/succinctlabs/sp1-cluster/blob/316b524c9f394b810badd23e99ac79b0de13ac02/crates/worker/src/limiter.rs#L3
[artifact-budget]: https://github.com/succinctlabs/sp1-cluster/blob/316b524c9f394b810badd23e99ac79b0de13ac02/crates/artifact/src/redis.rs#L146
[artifact-publish]: https://github.com/succinctlabs/sp1-cluster/blob/316b524c9f394b810badd23e99ac79b0de13ac02/crates/artifact/src/redis.rs#L624
[assignment]: https://github.com/succinctlabs/sp1-cluster/blob/316b524c9f394b810badd23e99ac79b0de13ac02/bin/coordinator/src/policy/balanced.rs#L89
[ntt-readme]: https://github.com/succinctlabs/sp1/blob/5517b0a04d893e4278be09e7077a785830468e76/sp1-gpu/README.md#L33
[nvidia]: https://github.com/succinctlabs/sp1/blob/5517b0a04d893e4278be09e7077a785830468e76/sp1-gpu/crates/sys/include/ntt/nvidia.cuh#L12
[jagged]: https://github.com/succinctlabs/sp1/blob/5517b0a04d893e4278be09e7077a785830468e76/sp1-gpu/crates/commit/src/commit.rs#L24
