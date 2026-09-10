# Shard proving with lookahead and split healing

Opt in with `ix prove --ixe ENV.ixe --ixes PLAN.ixes --lookahead
--max-ram PROOF_GIB`. The budget must be an explicit, positive GiB value.
`--heal-splits` enables the same claim-preserving split behavior with serial
execution. Commands without these flags retain the
existing partition-refinement behavior.

The native scheduler executes at most one next job while the current proof
runs, whenever that job's child proofs are ready. The existing prover consumes
the current record directly. A separate two-thread Rayon pool handles
preparation; at most one next execution or completed record waits for the prover.

`--max-ram` gates each completed query record's predicted proving peak, including
recursive healing proofs. Execution produces the record, then the existing
peak model determines whether it can be proved within the budget. The same
check applies to serial and lookahead preparation. This budget describes a
single proof's predicted peak; process RSS, free RAM and total machine RAM
do not control execution or overlap. Process placement and memory allocation
across concurrent provers remain the launcher's responsibility.

An oversized shard is dropped and re-executed in smaller parts, cut only at
block boundaries to preserve mutual recursion groups. Each part is gated again.
All local joins use canonical subject trees, including intermediates larger
than Stage 2's structural cutoff. A join discharges only assumptions in its
actual subject set. Before scheduling a split, the final folded claim bytes
must equal the original leaf's bytes. Recursive proofs are also verified before
publication. If a direct or mixed join does not fit, raw children are wrapped
and a self join is attempted. An indivisible block, wrap, or final flat join
that still cannot fit stops that shard with an error.

Only original shard proof addresses appear on stdout, each preceded by its
claim digest. Progress, predicted peaks and split decisions go to stderr.
`--shard` and `--shards` select original leaves; `--keep-going` continues to other originals
after a failure. `--out-ixes` copies the original manifest after a successful
run. Child peaks never overwrite original manifest peaks.

Every completed part and intermediate proof is stored and indexed by its claim
digest. `--skip-proven` verifies index hits under the current IxVM or recursion
backend before using them. Missing objects, wrong hashes, wrong claims and
invalid proofs are misses. Split plans live under `~/.ix/cache/shard-splits/`;
their versioned identity includes both verifier identities, the proving budget
and the original claim. Plans are validated as exact, disjoint block partitions
when restored. Store objects, native index entries and split journals are
published atomically. `--no-index` disables proof-index reads and writes;
proof objects and split plans are still persisted.

`ix verify`, shard-aware verification, the refinement proof guard, and native
Stage 2 accept healed leaves. Stage 2 authenticates each imported proof's
backend and selects the appropriate raw, mixed or self join while preserving
the existing manifest statement fold. `--plan-only` has no authenticated input
proofs and shows the plan for raw inputs. A replay of an imported healed leaf
has no Stage 2 execution to repeat; replay its consuming join instead, supplying
the shard proofs when an immediate child is an imported leaf.

No circuit, witness-generation rule, proving parameter, verifying-key encoding
or claim format changes. The only synthesis addition is an immutable bytecode
accessor; execution ownership stays private to the scheduler. Aggregate advice
construction and shard-proof verification reuse existing backends.

## Validation after benchmarks finish

The latest changes and new tests have not been built or run: implementation
was completed without Cargo or Lake commands after the request to protect
concurrent benchmark measurements. An earlier intermediate Rust check and CLI
module build passed; those do not validate the final revision.

Run the Rust aggregate tests and the existing aggregate/manifest suites first.
The additional `IxTests --ignored shard-pipeline` runner uses real IxVM and
recursive proofs with test-only FRI parameters. It exercises nested split
journals, exact original claims with an external frontier, lookahead, verified
resume and recovery from a corrupt child. All artifacts stay in a reported
temporary directory. This runner can use substantial RAM and should run
separately from benchmarks. Source unit tests also cover thread handoff,
canonical joins above the structural cutoff, invalid split partitions, and
authenticated mixed Stage 2 inputs.

Use `CFLAGS=-std=gnu17` with build commands on the current benchmark host, as
described in the committed handoff. Production shard-scale RSS calibration
and throughput measurements remain necessary before enabling lookahead for a
full proving campaign.

---

# Proving a whole environment: shard → refine → prove → aggregate

The recommended workflow for a full-environment proof (Mathlib-scale), as
measured on a 3-domain r8i.metal-48xl (2026-09-08/09), using the pipeline
above for Stage 1. The one rule this part exists to state: **run
`ix shard refine` before proving a whole environment.** Everything else
follows from it.

## 1. Compile and shard

```sh
ix compile Benchmarks/Compile/CompileMathlib.lean --out mathlib.ixe     # ~1 min
ix shard mathlib.ixe --max-ram 400 --out mathlib-400.ixes                # ~1 min
```

`--max-ram` in the static strategy is a *seed*, not a bound: it sets the
shard count (`233 × (400 / budget)^1.2` for Mathlib) and balances a block-shape
score across it. Real prover peaks are only known after execution, and the
static model's error tail runs to ~1.7x on a few leaves. Seed at 400 GiB for a
430 GiB prove budget: measured 236 → 246 leaves with 8 splits; seeding at 430
gave 217 → 237 leaves with 19 splits and leaves within 4 GiB of the gate.

## 2. Refine — always, before proving

```sh
ix shard refine mathlib.ixe --ixes mathlib-400.ixes --max-ram 400 \
  --out mathlib-refined.ixes --report mathlib-refined.json               # ~14 min
```

Refine executes every leaf in one parallel batch (admission gated on the
execute-peak estimates, ~11–23 GiB each, so all 236 leaves ran at once at
1.26 TB), records each leaf's measured projected prover peak in the manifest,
and cuts every leaf whose peak exceeds `--max-ram` into a balanced subtree of
parts (part 0 keeps the leaf's id; new parts get new ids at the end). The
output manifest is a refinement of the source: untouched leaves keep their
records and tree positions, and it is the manifest every later step binds to
(`ix prove --ixes`, `ix aggregate --ixes`, `ix verify --aggregate --ixes`).

Why refine rather than letting the prover split at run time:

| over-budget leaf handled by | extra cost |
|---|---:|
| refine (before proving) | one more leaf pair and one more Stage 2 join: ~215 s of one domain in the parallel phase ≈ 70 s of wall |
| prove-time split + heal (`ix prove --lookahead`, see `shard-pipeline.md`) | the parts are proved and joined back serially on that lane: measured 589 s vs 160 s for the unsplit leaf (≈ 300 s extra when the direct heal join fits the budget) |

Refine's fixed cost (~14 min for Mathlib, paid even if nothing splits) breaks
even at 2–3 split leaves per run; Mathlib had 8 (3.4 %). Refine also yields
the measured peaks the lane assignment needs (three lanes balanced to within
0.1 % of peak-sum stayed in lockstep for the whole run) and guarantees a
margin under the prove-time gate (refine at 400, prove at 430: every leaf
≥ 30 GiB under the gate, so no lane splits mid-run and the three lanes' output
manifests stay identical). Prove-time healing remains the right *insurance*
for the rare leaf the model still misses; it should not be the plan.

## 3. Stage 1: one process, one lane per NUMA domain, THP always

Set `transparent_hugepage/enabled` to `always` first (1.5–1.7x on the prover:
its per-phase buffers are fresh mappings, and 4K first-touch faults serialize on
the mm lock). Then a single `ix prove`:

```sh
systemd-run --user --scope --slice=ix-pipeline.slice -- \
  ix prove --ixe mathlib.ixe --ixes mathlib-refined.ixes \
    --lookahead --max-ram 430 --skip-proven --keep-going --texray \
    --out-ixes mathlib-proved.ixes
```

With `--lookahead`, the pipeline detects the NUMA topology and runs one lane
per domain inside the process (`IX_PROVE_LANES=N|off` overrides): the
environment and both systems are loaded once, the selected leaves are split
across lanes (longest-first by block count, manifest order within a lane), and
each lane runs the pipeline above on a thread pinned to its domain's cores and
memory node (`crate::numa`), so lanes never share a core or a memory channel.
Every lane keeps lookahead, split healing and publication unchanged, and there
is one `--out-ixes`. A single prove cannot use more than one domain (full-box
prove: 1.08–1.18x one lane); three isolated lanes scale 3.00x. `--lookahead`
hides the execute phase (~24 % of a leaf) under the previous proof: measured
116 s per ~300 GiB leaf per lane vs 132 s without.

Resume after any failure by rerunning the same command (`--skip-proven`).
Because the lanes share one process, a lane that outgrows its domain takes the
process down (its memory policy is `MPOL_BIND`); the restart loses at most one
in-flight leaf per lane. Expect `--out-ixes` to be byte-identical to the input:
prove-time splits are healed privately and never change the manifest.

### Memory bounding: one slice for the whole pipeline

Do not pass per-stage caps around. Size one cgroup slice from the machine and
run every stage as a child scope of it:

```sh
systemctl --user set-property ix-pipeline.slice MemoryMax=$((MemTotalGiB-24))G MemorySwapMax=0
systemd-run --user --scope --slice=ix-pipeline.slice -- ix prove …      # Stage 1
systemd-run --user --scope --slice=ix-pipeline.slice -- ix aggregate …  # Stage 2
```

The binaries adapt to whatever cgroup they run in: the prove pipeline reads the
tightest `memory.max` over its cgroup ancestors and caps its lane count at
`limit / (max_ram × 1.15)`; the aggregate scheduler clamps its admission budget
to 92 % of the limit. Within a process, per-lane bounding comes from the NUMA
memory policy, so the machine-wide cap is the only number that has to be right.
Section 5 below runs all of the above end to end and is safe to rerun.

## 4. Collect, verify, aggregate

Proof addresses come from the shard-proof index
(`~/.ix/cache/shard-proofs/<claim-digest>`; claims via `ix shard claims`).
Verify them with `ix verify --ixe --ixes <addresses>`: the composed verdict
runs through the native Stage 2 import (all shard claims reconstructed in
Rust, every proof bound to its shard and verified in parallel, exactly one
valid proof per shard), about a minute for Mathlib, almost all of it
environment load. It is a convenience gate: Stage 2 re-verifies every leaf
before building a join, and the final `ix verify --aggregate` covers the
environment. Then:

```sh
systemd-run --user --scope --slice=ix-pipeline.slice -- \
  ix aggregate --ixe mathlib.ixe --ixes mathlib-refined.ixes \
    --direct-joins --jobs 0 --max-ram 1300 <addresses>
ix verify --aggregate --ixe mathlib.ixe --ixes mathlib-refined.ixes <root>
```

The aggregate scheduler pins each slot to a NUMA domain (`crate::numa`;
`IX_NUMA=off` disables). Direct and mixed joins reserve 180 GiB: since the
IxVM function groups (main #619) halved what a leaf proof opens, a direct join
verifying two leaves peaks near 200 GiB resident (it was ≈ 400 GiB at the old
390 GiB reservation). A structural self-join reserves 195 GiB + 1.25 MiB per
subject, with a 390 GiB minimum above 65,536 subjects to cover trace-size
jumps; that subject term is the join's own claim work and did not shrink. Up to two joins can share a
node when their combined weights fit its budget (90% of node total, capped
by the process budget). This retains packing for small joins and separates
large upper joins; the old flat 195 GiB weight caused a Mathlib node OOM. See the
[calibration](numa-slot-pinning.md#12-subject-aware-structural-reservations-2026-09-09)
for measured peaks and the model's limits.

The solo dependency tail runs unpinned. A join whose weight exceeds every
node's budget also runs unpinned, with no other slots active until it finishes,
even when the process budget has spare room. `--jobs 0` derives the cap from
the topology. A join's identity depends only on its children's claims, so the
aggregate cache resumes any interrupted run and is shared between direct-join
and wrap-first modes.

The initial independent joins also overlap preparation of the next proof,
including on single-node hosts and with `IX_NUMA=off`. Each worker holds at
most one next execution record. With packing on, a NUMA lane runs up to two
such queues when both fit its budget (2 × (180 + 40) GiB ≤ 453 GiB): Mathlib's
105 direct joins then run six-wide at ≈ 155 s each instead of three-wide at
≈ 94 s, about 20 % more throughput, at the cost of the shared-pool
straggler tail (a few slots at 2–6x). `--max-ram` must hold all six queues
(1350 GiB on this box); `IX_NUMA_PACK=0` returns to one queue per lane. The batch obeys `--jobs`, the process RAM
budget (including its cgroup cap), and any NUMA node budgets. Proving capacity
is assigned first; a worker enables overlap only when its queue has another
job and there is room for the additional 40 GiB record allowance. Without
room for overlap, the ordinary scheduler handles the jobs. Dependent joins
continue to use dynamic admission and packing. `IX_NUMA_LOOKAHEAD=0` disables
overlap on both pinned and unpinned workers.

## 5. Reproduce end to end

Everything below was measured on an r8i.metal-48xl (Xeon 6975P-C, 96 cores /
192 threads, 1511 GiB, three sub-NUMA domains of ~504 GiB, Ubuntu 26.04). No
helper scripts are needed; each step is one command, and every step can be
rerun after a failure.

### Build

```sh
sudo apt install clang            # bindgen needs libclang's headers
export CFLAGS=-std=gnu17           # gcc ≥ 14 defaults to C23; Lean's sysroot lacks __isoc23_strtol
lake build ix
```

### Box setup, once per boot

```sh
echo always        | sudo tee /sys/kernel/mm/transparent_hugepage/enabled
echo defer+madvise | sudo tee /sys/kernel/mm/transparent_hugepage/defrag
sudo sysctl -w kernel.numa_balancing=0
numactl --hardware                 # expect the domains the lanes will use
```

THP `always` is the largest single lever (prover 1.5–1.7x: 87 M → 0.66 M
first-touch faults per leaf). `numa_balancing=0` keeps the kernel from
migrating pages the lanes have deliberately bound. No CPU governor or clock
changes are needed. Then one cgroup slice for the whole pipeline, sized from
the machine (24 GiB left to the OS), swap off:

```sh
systemctl --user set-property ix-pipeline.slice \
  MemoryMax=$(( $(awk '/MemTotal/{print $2}' /proc/meminfo) / 1048576 - 24 ))G MemorySwapMax=0
```

Every `ix` invocation below runs as `systemd-run --user --scope
--slice=ix-pipeline.slice -- ix …`; the binaries read that limit (lane count,
admission budget). A lane that outgrows its NUMA node is killed by the kernel
under `MPOL_BIND`, not by the slice; the slice bounds the process as a whole.

### Environment, shards, refine (sections 1–2)

```sh
ix compile Benchmarks/Compile/CompileMathlib.lean --out mathlib.ixe
ix shard mathlib.ixe --max-ram 400 --out mathlib-400.ixes
ix shard refine mathlib.ixe --ixes mathlib-400.ixes --max-ram 400 \
  --out mathlib-refined.ixes --report mathlib-refined.json
```

The manifest to use from here on is `mathlib-refined.ixes` (246 leaves for
Mathlib as of 2026-09-09). A manifest's `measured_peak_bytes` come from the
prover peak model; a manifest measured with a binary that mis-projected (see
the note under the budget table) should be re-run through `refine`.

### Stage 1

```sh
systemd-run --user --scope --slice=ix-pipeline.slice -- \
  ix prove --ixe mathlib.ixe --ixes mathlib-refined.ixes \
    --lookahead --max-ram 430 --skip-proven --keep-going \
    --out-ixes mathlib-proved.ixes
```

What to look for in the first minutes:

- `[shard-pipeline] numa: 3 lanes: node 0 (82 shards), … balanced by measured peak`
  — one lane per domain. `IX_PROVE_LANES=1` forces a single lane.
- `[shard-pipeline] shard K claim …: projected prove P GiB, budget 430.0 GiB`
  — Mathlib leaves project 250–400 GiB; a projection above 430 means a
  prove-time split (`splitting into N parts`), which is healed privately and
  costs ~5 min of that lane.
- ~118 s per leaf per lane once the overlap is running; 246 leaves ⇒
  ≈ 2 h 40 min. Node usage stays under ~420 GiB.

Rerun the same command to resume: `--skip-proven` finds each leaf's proof in
`~/.ix/cache/shard-proofs/<claim digest>` and re-verifies it under the current
verifying key before skipping. Proofs made by a binary with a different
verifying key (any change to the IxVM circuits, e.g. the function groupings)
are not reused; start such a run on fresh `~/.ix/cache/{shard-proofs,aggregate}`
directories (move the old ones aside).

### Collect and verify the leaf proofs

```sh
ix shard claims mathlib.ixe --ixes mathlib-refined.ixes > claims.txt   # "id digest blocks consts" per leaf
while read -r id digest rest; do
  [[ "$id" =~ ^[0-9]+$ ]] && cat ~/.ix/cache/shard-proofs/$digest && echo
done < claims.txt | sed '/^$/d' > proofs.txt
wc -l proofs.txt                                                          # must equal the leaf count
ix verify --ixe mathlib.ixe --ixes mathlib-refined.ixes $(cat proofs.txt)
```

The composed verdict (`[verify] OK: composed verdict — all 246 shards proven +
disjoint cover`) runs through the native Stage 2 import: about a minute,
almost all of it environment load. Stage 2 repeats the same check on import.

### Stage 2

```sh
systemd-run --user --scope --slice=ix-pipeline.slice -- \
  ix aggregate --ixe mathlib.ixe --ixes mathlib-refined.ixes \
    --direct-joins --jobs 0 --max-ram 1350 $(cat proofs.txt)
```

`--max-ram 1350` is what lets two prepare-ahead queues run on every node
(6 × (180 + 40) GiB); the scheduler clamps it to 92 % of the slice anyway.
First lines to check:

- `[aggregate] plan: 0 wraps, 0 imported healed leaves, 246 direct IxVM leaves + 245 binary joins`
- `[aggregate] numa: 3 lanes … policy=Bind pack=true`
- `[aggregate] pipelines: 105 independent slots over 6 workers (node 0: 18 slots, 220.0 GiB reserved, …); prepare-next overlap on 6/6 workers`
- direct joins complete at ≈ 155 s each packed two per node (≈ 94 s alone);
  the direct phase takes ≈ 50 min; upper joins 45–150 s; the last three
  levels run nearly serially (~12 min). Root after ≈ 1 h 50 min:
  `[aggregate] root proof: <address>`.

Rerun the same command to resume: every finished join is in
`~/.ix/cache/aggregate`, keyed by its children's claims, so a restart replays
the cache and continues. `IX_NUMA_PACK=0` returns to one queue per lane
(three-wide, ≈ 300 GiB headroom per node instead of ≈ 95 GiB);
`IX_NUMA_LOOKAHEAD=0` disables prepare-ahead; `IX_NUMA=off` disables pinning.

### Root

```sh
ix verify --aggregate --ixe mathlib.ixe --ixes mathlib-refined.ixes <root address>
```

Expected: `[verify] all 679499 included constants certified well-typed; 0
undischarged assumptions`, in a few seconds. The root wrapper is
`~/.ix/store/<a>/<b>/<c>/<rest>` for address `abc…rest` (≈ 4.9 MB).

### Reproducing a measurement on a subtree

Stage 2 experiments do not need the full tree. With a completed Stage 1,
`IX_AGGREGATE_SHARDS=0-31 ix aggregate … $(cat proofs.txt)` aggregates only
that subtree of the manifest (the leaf claims do not depend on the manifest
size; the root then keeps assumptions on the other shards). Use a fresh
`~/.ix/cache/aggregate` per configuration (move the previous one aside) so
nothing is shared between the A and B runs; join times, per-slot peaks and
`lane peaks` are on stderr, and `memory.current` of the slice's cgroup is the
process peak. Shards 0–31 of the Mathlib manifest (32 leaves, 31 joins) run
in 16–36 minutes depending on the configuration and were the basis for the
direct-vs-wrap-first, function-groups and two-queues comparisons in the
budget table.

## Measured budget (Mathlib, 679,499 constants, 246 leaves)

| step | wall |
|---|---:|
| compile + static shard | ~2 min |
| refine | ~14 min |
| claims + lane split | ~3 min |
| Stage 1 (3 lanes, lookahead) | 2 h 44 min measured (2 h 38 min the run before) |
| collect + verify | ~1 min (native composed verdict) |
| Stage 2 (pinned direct joins, two queues per lane) | 1 h 52 min measured (3 h 25 min before main's function groups) |
| root verification | seconds |

Total proving on the rebased binary: **4 h 36 min** (run `mathlib2`, 2026-09-10;
root 4.9 MB, leaf proofs 11 MB each). The previous run on this box took
6 h 20 min; production on one 64-vCPU box (PR #598) took 28 h for the two
proving stages.

The prover peak model (`AiurSystem::peak_prove_bytes`) gates each leaf against
`--max-ram`; after function groups it must sum a circuit's member rows (fixed
on this branch) — a manifest measured with the broken projection carries
inflated `measured_peak_bytes` and should be re-measured with `ix shard
refine`.
