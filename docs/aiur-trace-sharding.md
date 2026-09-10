# Prover-level trace sharding for Aiur

Design for splitting one Aiur execution into K independently provable
trace shards whose proofs form a vector of STARKs, so that each shard's
STARK phases fit in GPU memory, then aggregating that vector with the
existing `ix_aggr` recursion. Written against `main` at `ba9522a3`,
multi-stark `9a906122`, with PR #619 (function grouping) taken as
landing. Terminal compression of the final root (e.g. PR #602) is a
downstream consumer of this design's verifier contract, not part of it.

## 1. Summary

- **What is sharded.** The rows of every circuit's trace, not the
  execution. One execution produces one `QueryRecord`; the K shards are K
  row-partitions of the traces derived from it. Nothing about execution,
  the record, the bytecode, or the kernel changes.
- **Why rows are relocatable.** Aiur's soundness is one LogUp multiset
  identity over all rows of all circuits (each function row pulls its own
  return message and pushes its calls, stores, loads and byte ops); the
  only cross-row constraint in the system is the memory table's
  `ptr_next = ptr + 1`. So any row can live in any shard provided (a) all
  shards evaluate the lookup argument under the same challenges and (b)
  the sum of the shards' lookup residuals is zero.
- **Shared challenge, one barrier.** Every shard commits its stage-1
  (main) traces. A *batch transcript* — the parameter seed, the system
  shape, and one digest `D` over every shard's header (activation bitmap,
  stage-1 commitment, heights, claims) and over the batch's memory totals
  — samples the lookup challenges β, γ once; every shard's transcript
  forks from that common state. Shard proofs are therefore dependent — as
  the colleague's notes anticipate — but the dependency is a single
  exchange of K ~100-byte headers, after which all shards finish
  independently and in parallel. This is Zisk's two-round
  global-challenge protocol; SP1's challenge-free elliptic-curve digest
  is rejected in §4.2 because Aiur's cross-shard message volume makes it
  ruinous.
- **Residuals, not zero.** multi-stark's verifier already materializes the
  per-proof lookup residual (`intermediate_accumulators.last()`) as a
  transcript-bound public field and merely asserts it is zero. The shard
  verifier returns it; the vector verifier requires the K residuals plus
  the batch's boundary terms to sum to zero.
- **Memory.** No change to memory semantics. A shard's memory table is a
  contiguous pointer range; two `sel`-gated lookups on every memory row
  (push `ptr`, pull `ptr + 1`) telescope to one push of the first pointer
  and one pull of one past the last, and two terms contributed by the
  vector verifier force the K ranges to tile `[0, N_w)` exactly — Zisk's
  continuation-record idiom, with a flow-conservation proof over the
  finite field in §5.
- **One verifier contract.** Because the boundary lookups are part of the
  memory AIR and the transcript prefix changes, a single unsharded proof
  is the `K = 1` vector and `verify_vector` is the verification routine
  for every Aiur proof. Anything that embeds an Aiur verifier — native
  Rust, the Lean in-circuit verifier, `ix verify`, and any downstream
  consumer of the root such as a terminal compressor — adopts it.
  Terminal compression itself is out of scope: it consumes a valid root
  proof and is unchanged by how that root was aggregated.
- **Byte tables** are present in every shard; one shard's copy carries
  the record's multiplicities and the others' carry zeros (deactivating
  them awaits an in-circuit PCS extension, §3.1).
- **Proof vector.** `VectorProof = { preamble, shard_proofs[K] }`. Size is
  `Σ_k 9 B · q · active_width_k`; with PR #619's grouping a 10-way split
  of a Mathlib shard lands near 25–30 MB against ~9.4 MB monolithic.
- **Recursion.** `ix_aggr` gains a vector-child verifier; recursion proofs
  are themselves trace-sharded by the same machinery (natural boundary:
  one child verification per shard); direct joins become the default
  because RAM no longer bounds recursion. Using SP1's recursion for the
  tree is rejected on measured cost (§8.4).
- **Sizing.** Shards are cut to a VRAM budget with the existing peak
  model, in committed-cell units: fully-resident CUDA proving needs about
  `8·(1 + 2^log_blowup)` bytes per committed cell plus 25 % headroom,
  i.e. ~1.8·10⁹ committed cells on a 96 GB card, roughly 0.7–1.2·10⁹
  main-trace cells depending on the circuit's committed-to-main width
  ratio (§7.1).

## 2. Facts the design rests on (verified in source)

### 2.1 Aiur

- A function circuit row is one memoized query `(fn, inputs) →
  (output, m)`. Slot 0 pulls the row's own return message with
  multiplicity `sel · m`, where `sel` is the row's branch selector (the
  gate matters: a branchless function sends its return arguments raw, so
  an ungated `m` would let a padding row — every constraint off — pull an
  arbitrary `f(x) = y`); every constrained `Call`, `Store`, `Load` and
  byte op pushes one message with the branch selector as multiplicity
  (`crates/aiur/src/constraints.rs:170-190, 400-490`;
  `crates/aiur/src/trace.rs:96-160`). Function circuits have no
  cross-row constraints.
- The claim `[chan 0, fun_idx, input…, output…]` is the verifier's push
  balancing the entry row's pull (`crates/aiur/src/synthesis.rs:447-452`).
- Memory is content-addressed and write-once: `Store(values)` dedups by
  value and assigns `ptr = insertion index`; `Load(ptr)` bumps the
  multiplicity (`crates/aiur/src/execute.rs:365-407`). The memory circuit
  for width `w` has rows `[mult, sel, ptr, values…]`, one pull of
  `(chan 1, w, ptr, values)` with multiplicity `sel · mult`, and
  constraints: `sel` boolean, real-next ⇒ real-current,
  `ptr_next = ptr + 1` on real transitions. There is no
  first-row anchor (`crates/aiur/src/memory.rs:34-67`). An unqueried
  memory width yields an empty trace and is deactivated.
- Bytes1 (256 rows) and Bytes2 (65 536 rows) carry preprocessed operand
  columns and always emit the full table
  (`crates/aiur/src/gadgets/bytes2.rs:284-`). They are the per-proof
  fixed floor of the RAM model.
- Prover peak model (`crates/aiur/src/synthesis.rs:287-367`):
  `max(phase_witness, phase_stage2, phase_open) + preprocessed`, where
  `phase_open` ∝ committed LDE bytes `8·b·n·(main + stage2 + q·d)` per
  circuit plus FRI buffers ∝ `b · tallest`. `suggested_split_parts`
  already projects this model over rows divided evenly into parts — it is
  the trace-shard sizing model, minus the byte tables.
- Proof size ≈ `9 B × num_queries × active committed width` (20 MB at
  ~22k columns and q=100; 9.4 MB at ~10k columns after PR #619).
- The Lagrange selectors are unnormalized polynomials, not 0/1
  indicators: at ζ, `is_first_row = Z_H(ζ)/(ζ − 1)`, `is_last_row =
  Z_H(ζ)/(ζ − g⁻¹)`, `is_transition = ζ − g⁻¹`
  (`Ix/MultiStark/Verifier.lean:413-440`, mirroring p3's
  `selectors_at_point`); on the trace rows `is_first_row` takes the value
  `n` on row 0. They are safe as constraint gates (anything times zero is
  zero) but must not be used as lookup multiplicities.

### 2.2 multi-stark (rev `9a906122`; protocol identical to `a8aab731`)

- Transcript: parameter seed → system shape → activation bitmap →
  preprocessed and stage-1 commitments → `log_degrees` → length-prefixed
  claims → **sample β (lookup), γ (fingerprint)**, observe them back →
  stage-2 commitment → `intermediate_accumulators` → α → quotient
  commitment → ζ → FRI (`src/prover.rs:317-688`; mirrored in
  `Ix/MultiStark/Verifier.lean`).
- Per circuit the lookup publics are `[β, γ, acc_initial, acc_final]` and
  the constraint forces `acc_final − acc_initial = Σ mult / (β +
  fingerprint(γ, args))`. The chain across active circuits starts from
  the claims-derived accumulator (each claim contributes `+1/m`) and the
  verifier asserts the last accumulator is literally zero
  (`src/verifier.rs:242-246`; `Ix/MultiStark/Verifier.lean:466`).
- `prove_multiple_claims` is monolithic; β, γ are sampled inside it with
  no seam (`src/prover.rs:396-399`).
- Inactive circuits are omitted from every round except preprocessed,
  where inactive circuits are opened at zero points — so a circuit with
  preprocessed columns can be inactive in a proof
  (`src/prover.rs:666-679`).
- Every column of every active matrix is opened at every FRI query
  (`p3 fri/src/proof.rs:66-71`); query values dominate proof size.
- CUDA backend is first-party (PRs #75, #76, #79). Requires
  `cap_height = 0`, `max_log_arity ≤ 1`. Fully resident commit needs
  `source + (source << log_blowup) + minimum_free ≤ free` with
  `minimum_free` defaulting to a quarter of device memory
  (`src/cuda/pcs.rs:553-565`); larger proofs spill height groups to
  pinned host memory (#79). Measured on an RTX PRO 6000 (96 GB): Init
  split 16 ways at q=64 gives 1.99× end to end and 2.23× on recursion
  while spilling; 8.13× when fully resident (`docs/cuda-benchmarks.md`;
  #79 commit message). This gap is the motivation: today's env shards do
  not fit VRAM.
- `Expr` has `IsFirstRow`, `IsLastRow`, `IsTransition`, `Public(u32)`
  (`src/expr.rs:39-51`).
- PR #55 (open) makes claims part of the proof with multiplicities and
  adds `partially_prove/verify` whose final accumulator must equal the
  accumulator of `remaining_claims`. It chains shards at message
  granularity; §4.2 explains why that is not usable for Aiur's cross-shard
  volume, but the claim-multiplicity machinery is reusable.

### 2.3 Precedents

- **SP1 (Hypercube 6.6.0).** Shards are cut by trace area
  (`ELEMENT_THRESHOLD = 1.5·2^28 ≈ 4.0·10^8` main-trace cells;
  ~2.85·10^8 on ≤30 GB GPUs) and per-chip height (2^22), with worst-case
  headroom reserved. Each shard's LogUp is balanced *internally*, with
  the public values acting as a virtual chip (state send/receive, memory
  init/finalize controls). Cross-shard facts (memory, syscalls) go
  through the `Global` chip: hash-to-curve on a septic extension plus
  elliptic-curve point addition, no verifier challenge; the recursion
  checks the total is the identity. Cost: 241 cells per global
  interaction plus a Poseidon2 permutation, two rows per newly touched
  address per shard. Each shard gets a fresh challenger seeded only by
  the vk — shards are embarrassingly parallel. One shard is proven per
  GPU at a time; multi-GPU is independent shard tasks plus an arity-4
  compress tree.
- **Zisk / pil2-proofman.** Instances have PIL-fixed heights (Main 2^22,
  Mem 2^22, precompiles 2^17–2^20) and are planned deterministically on
  every worker from replayed minimal traces. Cross-instance lookups use
  one global stage-2 challenge derived in two rounds: every instance
  commits stage 1 and emits a contribution digest; digests are combined
  homomorphically (EC point add or lattice add, so worker order is
  irrelevant), all-gathered over MPI, and the challenge is a transcript
  over publics ‖ stage-1 proof values ‖ aggregate. The final recursive
  circuit re-derives the challenge and evaluates the global
  sum-to-zero. Memory is split by address range and row budget; segment
  `i` "proves" a continuation record keyed by `(region, i+1, tail_state)`
  and segment `i+1` "assumes" `(region, i+1, head_state)`; they cancel in
  the global sum iff equal, so boundary state is recomputed locally and
  never transmitted. Instance size is bounded by one GPU stream buffer.
- **Plonky3 (rev `3152b14a`).** `p3-lookup` distinguishes `Kind::Local`
  and `Kind::Global` buses; `batch-stark` exposes per-AIR
  `lookup_terminals` as a proof field and `verify_terminal_sum` sums an
  arbitrary slice; the duplex challenger observes arbitrary digests and
  has `CanFinalizeDigest`. No GPU code.

## 3. Trace shards

### 3.1 Definition

A *batch* is one execution (today: one env shard's `CheckEnv` claim; the
manifest's leaf). A *trace shard* `S_k`, `k ∈ [0, K)`, is a choice of
row subsets for every circuit such that every real row of every circuit
belongs to exactly one shard. Shards are planned deterministically from
the record by `plan_shards(record, budget)`; the plan is a pure
function of the record, so any prover reproduces the same shards, the
same stage-1 commitments, and the same preamble — a failed shard is
re-proven alone without disturbing the batch.

Per-circuit rules:

- **Function circuits** (including PR #619's grouped circuits, whose
  rows are the concatenation of member rows): any row partition.
  Heuristic below.
- **Memory circuits** (one per width): the rows of width `w` in
  insertion order are cut into K contiguous ranges `[P_{k,w},
  P_{k+1,w})`; range `k` goes to shard `k`. Contiguity is what makes the
  `ptr + 1` transition hold inside a shard, and insertion order is
  execution order, so this also places a value's table row in the shard
  whose function rows first stored it.
- **Byte tables**: present in every shard. Shard 0's copy carries the
  record's multiplicities; every other shard's copy has zero
  multiplicities and contributes nothing to the lookup sum. Leaving the
  tables *inactive* in those shards would save their small, fixed
  commitment (~2.6 M committed cells) per shard, but the in-circuit PCS
  verifier handles only the preprocessed matrices of active circuits, so
  that optimization waits for a `Pcs.lean` extension; multi-stark itself
  now supports inactive preprocessed circuits (opened at one point).
- **Entry row**: the entry function's query row goes to shard 0 with the
  execution's claim. Other shards carry no function claim.

### 3.2 Sizing and balancing

The objective is to fit each shard fully resident in VRAM (so the CUDA
backend runs at its 8× rather than its spilling 2×), minimize the total
active width across shards (proof size and recursion cost), and keep
shard costs balanced.

Cost model per shard `S`, in *committed* cells (`W_c = main + stage2 +
q·d` is circuit `c`'s committed width, `n_c` its padded height in `S`,
`b = 2^log_blowup`):

- device residency: `R(S) = 8·(1 + b)·Σ_{c active in S} n_c·W_c` (source
  plus LDE for every committed round held to the opening) plus FRI
  buffers ∝ `b · tallest(S)` plus the backend's headroom. This is
  `peak_prove_bytes_by` with per-shard row counts and without the record
  term; only the calibration constant changes (device allocator instead
  of process RSS). Main-trace cells convert to committed cells by the
  circuit's `W_c / main_c` ratio, which for Aiur circuits is typically
  1.5–2.5 (one stage-2 extension column per lookup group plus `q·d`
  quotient columns).
- proof size: `9 B · q · Σ_{c active in S} W_c` — a fixed price per
  *activation*, independent of rows.

Planner (`plan_rows` in `crates/aiur/src/shard.rs`): every shard commits
the byte tables, so their cells are charged to every shard and the room a
shard has for rows is what remains after them. Each circuit is cut into
the fewest pieces that each fit that room — a circuit that fits whole is
one piece, a larger one is cut into equal pieces of at most the largest
power-of-two row count whose padded cells fit — and the pieces are packed
first-fit in decreasing size, a new shard opening only when no shard has
room; two pieces of one circuit never share a shard. A circuit's width is
charged to proof size and verification once per shard it appears in, so
the fewest pieces and the fewest shards are what the packing minimizes,
and padding costs at most one doubling per piece. K is an output of the
packing, not a global constant, and can be re-sized freely — the protocol
does not depend on K.

Expected shape for a Mathlib env shard after PR #619: shard 0 carries the
~150 cold grouped circuits (most of the ~10k active columns) plus byte
tables, memory tables' first range and the entry row; shards 1..K−1
carry only the kernel's hot circuits (the `whnf`/`defeq`/hashing inner
loops — a few thousand columns). The measured `[texray]`/statistics
output already ranks circuits by FFT cost, which is the input this
heuristic needs.

### 3.3 Witness generation

`prove_from_execution` today builds every circuit's full trace in
parallel and hands one `SystemWitness` to multi-stark. Sharded: for each
`S_k`, build only the rows in `S_k` (the row builders are already
per-row parallel and take an index range), producing a per-shard
`SystemWitness`. The record must stay resident until the last shard's
witness is built. Host residency is governed by the round-1 retention
policy of §7.3.

## 4. Shared lookup challenge

### 4.1 Protocol

Two rounds per batch.

**Round 1 — commit.** For each shard `k`, on some GPU: build stage-1
traces, LDE, Merkle-commit; produce the *shard header*

```
header_k = (k, active_k, stage1_cap_k, log_degrees_k, claims_k)
```

**Preamble.** The orchestrator collects the K headers in shard order,
computes the batch's memory totals (§5), and forms

```
preamble  = (K, header_0, …, header_{K−1}, memory_totals)
D         = blake3(serialize(preamble))
```

Everything that introduces a lookup message anywhere in the batch —
every shard's committed traces (through its stage-1 commitment), every
claim, and every boundary term the verifier will add — is bound by `D`
before any challenge is sampled.

**Batch transcript.** One challenger, identical for every shard:

```
seed(parameters) → observe(system shape) → observe(D)
→ sample β, observe β → sample γ, observe γ
```

**Round 2 — finish.** Shard `k`'s transcript *forks* from the batch
transcript state after γ: it then observes its own header
(`active_k`, preprocessed and stage-1 commitments, `log_degrees_k`,
`claims_k`), and continues exactly as today — stage-2 commitment,
`intermediate_accumulators`, α, quotient commitment, ζ, FRI. The shard's
own data are bound twice: through `D` (the vector verifier checks
`header_k` against the proof) and by observation before α and ζ.

This ordering is the point the earlier draft got wrong: appending a
common digest *after* per-shard observations leaves the K challenger
states different, so β, γ differ and honest cross-shard messages do not
cancel. The common prefix must end at the sample.

Zisk's homomorphic contribution aggregation buys order-independence for
workers that do not share a plan; Aiur's plan is deterministic and
ordered, so a plain ordered digest is simpler and cheaper to re-derive
in circuit.

### 4.2 Why not challenge-free cross-shard messages (SP1)

SP1 keeps shards fully independent by routing cross-shard facts through
a hash-to-curve accumulator: no challenge, but roughly 250 cells plus a
Poseidon2 permutation per crossing message, and SP1 keeps crossings rare
(memory boundaries, syscalls). In Aiur every function-call message,
every memory push and every byte-op push is a potential crossing: the
callee's memoized row lives in exactly one shard while callers of that
query are wherever execution put them, memory rows live in one shard
while loads come from all, and byte tables live in one shard while byte
ops come from all. Crossings are the common case, not the exception;
paying ~5× a function row's width per crossing would multiply the trace
several times over. PR #55's message-level chaining has the same
problem: it exposes each unmatched message as a claim. The shared
challenge makes crossings free; its cost is one exchange of K ~100-byte
headers per batch.

### 4.3 Residuals

`verify_shard(batch, k, proof)` performs today's verification with the
transcript of §4.1 and, instead of asserting
`intermediate_accumulators.last() == 0`, returns it as `r_k ∈ EF`. The
vector verifier computes

```
Σ_k r_k + boundary_terms(β, γ, memory_totals) == 0
```

where `boundary_terms` are the memory tiling terms of §5 (the verifier
knows β, γ: it re-derives them from the batch transcript). The
claims-derived initial accumulators are already inside each `r_k`, so
exactly one shard carrying the entry claim and the rest carrying none is
enforced by the same sum: a duplicated or missing claim unbalances it
with overwhelming probability, exactly as a bad multiplicity does
today. The vector verifier additionally checks the claim *policy* (shard
0's claim is the expected `verify_claim` claim; no other function
claims), which `ix_aggr` does today for a single proof
(`Ix/Aggr/Circuit.lean:636-657`).

### 4.4 Vector proof

```
VectorProof {
  preamble: {
    K,
    headers: [Header; K],            -- ~100 B per shard
    memory_totals: [(w, N_w)],       -- §5: canonical, one per active width
  },
  shards: [Proof; K],                -- multi-stark proofs, unchanged format
}
```

`verify_vector(system, vector)`:

1. `1 ≤ K ≤ K_MAX`; each `headers[k]` matches `shards[k]` (activation
   bitmap, stage-1 cap, `log_degrees`, claims).
2. The messages are exactly consecutive pairs `pull (MEMSEG, w, a)`,
   `push (MEMSEG, w, b)` with `a ≤ b`, sorted by width and, within a
   width, into disjoint intervals (`b` of one pair at most `a` of the
   next), compared as integers — no other shape, no other channel. Each
   pair closes one memory interval `[a, b)`; a record's width-`w` table
   is one such interval, starting at the record's pointer base, so a
   batch of several records closes several per width. The verifier need
   not know which intervals the records use: a missing pair leaves an
   interval's end points unmatched (unbalanced), and a pair no shard
   fills balances only at `a = b`, the zero contribution. What must be
   excluded is two overlapping intervals (two paths through the same
   pointers).
3. `Σ_{k, active c} 2^{log_degree_{k,c}} < p` over every shard and
   circuit (the finite-field bound of §5, coarsened to the whole batch so
   it needs no circuit-to-width mapping; trivially true for honest
   batches, required as a check).
4. `D = blake3(preamble)`; derive β, γ from the batch transcript.
5. `r_k = verify_shard(batch, k, shards[k])` for all k.
6. `Σ_k r_k + Σ_w (1/m(β,γ,(MEMSEG, w, N_w)) − 1/m(β,γ,(MEMSEG, w, 0))) == 0`
   (signs per §5).
7. Claim policy as above.

A single unsharded Aiur proof is the `K = 1` case of this routine; there
is no separate "plain" verification once the memory AIR carries the
boundary lookups (§8.3).

## 5. Memory across shards

Aiur memory has no timestamps and no address-ordering argument. The only
things sharding must preserve are (a) every table row is pulled exactly
once somewhere and (b) no two rows anywhere share `(w, ptr)`. (a) is the
lookup balance. (b) needs the K per-width pointer ranges to be disjoint;
contiguity inside a shard is already enforced by `ptr_next = ptr + 1`.

### 5.1 Boundary lookups by telescoping

Add two lookups to the memory circuit on a new channel `MEMSEG`, both
gated by the existing real-row selector `sel` and present on *every*
row:

- **push** `(MEMSEG, w, ptr)` with multiplicity `sel`;
- **pull** `(MEMSEG, w, ptr + 1)` with multiplicity `sel`.

Within a shard the real rows are a prefix with `ptr_next = ptr + 1`, so
they carry consecutive pointers `a, a+1, …, b−1`, and the circuit's
contribution on the channel telescopes exactly:

```
Σ_{p=a}^{b−1} ( 1/m(p) − 1/m(p+1) )  =  1/m(a) − 1/m(b),     b = last_ptr + 1
```

Padding rows have `sel = 0` and contribute nothing — on this channel and
on the memory channel, whose pull is gated the same way (`sel · mult`);
an ungated multiplicity column would let padding rows inject messages of
their own. The result is
precisely one unit push of `first_ptr` and one unit pull of
`last_ptr + 1` — the boundary residual §5.2 needs — with no new columns
and no new constraints; only two lookup slots, which any per-row
boundary scheme needs anyway (LogUp cost is per slot, not per nonzero
multiplicity).

Two designs were rejected on the way here. Gating the boundary lookups
with the Lagrange selectors does not work because they are not
indicators (§2.1): `IsFirstRow · sel` evaluates to `n · sel` on row 0,
so the push would carry multiplicity `n`. Constrained boolean flag
columns (`first`, `last`) do work but cost two columns and two pinning
constraints per memory circuit, and the telescoping form makes them
unnecessary.

### 5.2 Verifier terms and the tiling argument

The vector verifier contributes, per memory interval `[A, B)` of width
`w` in `memory_totals`, one pull of `(MEMSEG, w, A)` and one push of
`(MEMSEG, w, B)`; a single record's table is the one interval
`[0, N_w)`, and records proven together hold intervals a fixed pointer
stride apart. The end points are committed in the preamble before β, γ
are sampled (§4.1) and the list is canonical (§4.4 step 2); both
conditions are load-bearing:

- if an end point could be chosen after the challenges, an adversary
  with two free base-field values (two intervals' ends) can solve the
  two extension-field coordinates of any target imbalance — the audit's
  `adaptive_memory_totals` counterexample does exactly this to cancel a
  wrong memory read;
- if overlapping intervals were allowed, two entries `[0, 1)` supply two
  boot and two terminal terms, so two shards can each claim pointer 0
  with different values and all `MEMSEG` terms cancel — the audit's
  `duplicate_widths` counterexample. Sorted, disjoint intervals is the
  whole of what canonicity must enforce; the verifier need not know the
  records' widths or intervals (§4.4 step 2).

With both conditions, balance on the `MEMSEG` channel states, as
multisets over `F_p` (written for the single interval `[0, N_w)`; each
further interval adds its own source and sink):

```
{ first_{k,w} : k } ∪ { N_w }  ==  { last_{k,w} + 1 : k } ∪ { 0 }
```

**Claim.** Given `Σ_k n_{k,w} < p` (verified from the public heights), this
holds iff the K ranges exactly tile `[0, N_w)` with no overlap.

*Proof.* Each shard's real rows form a run `first, first+1, …, last` of
`ℓ_k ≥ 1` consecutive residues mod `p` with `ℓ_k ≤ n_{k,w}`; view the
shard as a directed edge `first → last + 1` of length `ℓ_k` on the
cycle `Z_p`. The multiset identity says every residue has equal in- and
out-degree except `0` (one more out) and `N_w` (one more in), i.e. unit
net flow from `0` to `N_w`. Decompose the edge multiset into a
source-to-sink path plus directed cycles. A directed cycle of edges on
`Z_p` traverses a positive multiple of `p` residues, so its edges have
total length `≥ p`; but `Σ_k ℓ_k ≤ Σ_k n_{k,w} < p`, so there are no
cycles. Unit flow means exactly one path, and it uses every edge.
Consecutive edges on that path abut, so the runs are disjoint and cover
exactly the residues from `0` to `N_w − 1` without wrapping (wrapping
would again need length `≥ p`). Hence the ranges tile `[0, N_w)`. ∎

The height bound is the reason step 3 of `verify_vector` exists: the
"pointers strictly increase" intuition is a statement about integers,
and `ptr + 1` is a field operation. The bound turns the physical
observation "no batch has 2⁶⁴ rows" into a verifier guarantee at the cost
of summing K public heights.

Consequences: no per-shard public boundaries, no sorting in the
verifier, no change to how execution assigns pointers, and an inactive
memory width in some shard contributes nothing (both flags are zero on
an empty trace, and an inactive circuit is omitted). The alternative —
exposing `(first, last)` per shard as claims and checking tiling
arithmetically in the verifier — is equivalent and slightly more code;
it is the fallback if adding a channel is undesirable.

## 6. Soundness argument

Under β, γ sampled from the batch transcript after `D` binds all K
stage-1 commitments, claims and memory totals:

1. Each shard proof establishes that its committed traces satisfy every
   circuit's constraints (including the boundary flags and lookups) and
   that its lookup residual is `r_k` — unchanged from today's per-proof
   soundness, with the batch prefix replacing the per-proof prefix.
2. `Σ r_k + boundary = 0` establishes the global multiset identity over
   all rows of all shards plus the verifier's public messages (the entry
   claim, the `MEMSEG` boundary terms), with the usual LogUp soundness
   error over the extension field. All of those messages were fixed
   before the challenges.
3. The `MEMSEG` identity with a canonical total per width and the height
   bound forces the memory ranges to tile `[0, N_w)` (§5.2), so `(w, ptr)`
   is unique across the batch; with the memory circuit's pull
   multiplicities, the memory channel identity then has the same meaning
   as in one proof.
4. The function, memory and byte channels' identity over all shards is
   exactly the identity today's single proof establishes; the entry
   claim's pull is matched exactly once. Hence the batch proves the same
   statement a single proof of the same record proves.

Two bounds are verifier checks, not assumptions: the per-width height
sum `Σ_k n_{k,w} < p` (§5.2), and `K ≤ K_MAX` (say 2¹⁶) so preamble
parsing in circuit is a fixed-shape loop. The total number of terms in
the global sum (rows across shards) must also stay far below `p` for the
LogUp argument itself; the same height sums bound it.

## 7. GPU execution model

### 7.1 Sizing rule

Cut shards so the CUDA backend never spills: per shard, all committed
LDEs (stage 1, stage 2, quotient) plus FRI workspace resident. In
committed cells (§3.2), at `log_blowup = 2`:

```
resident bytes ≈ 8 · (1 + 4) · Σ_c n_c·W_c  +  FRI workspace
budget         ≈ 0.75 · device memory        (25 % default headroom)
```

so a 96 GB card admits about `72 GB / 40 B ≈ 1.8·10⁹` committed cells
before FRI workspace; a 24 GB card about 4.5·10⁸. In main-trace cells
(the unit SP1's `ELEMENT_THRESHOLD` counts) that is roughly 0.7–1.2·10⁹
on 96 GB and 2–3·10⁸ on 24 GB, given the 1.5–2.5 committed-to-main
ratio — the same order as SP1's 4.0·10⁸ (2.85·10⁸ on ≤30 GB cards). The
planner reads the budget from device memory and
`MULTI_STARK_CUDA_MIN_FREE_BYTES` and the circuit shapes; the
calibration constant is measured once per GPU model, the way
`PROVER_RSS_CALIBRATION` was for CPU, and every shard-count and
proof-size forecast in this document should be re-derived from it.

### 7.2 Pipeline per batch

1. **Execute** (CPU, serial, latency-bound): produce the record. Unchanged.
2. **Plan** (CPU, ms): `plan_shards(record, budget) → K, row ranges,
   memory_totals`.
3. **Round 1** (GPUs, parallel over shards): build shard `k`'s stage-1
   traces from the record (CPU, per-row parallel), upload, LDE, commit.
   Emit `header_k`. Then apply the retention policy of §7.3.
4. **Barrier** (µs): the orchestrator forms the preamble, `D`, and the
   batch transcript state. Within a box this is shared memory; across
   boxes it is K headers over the network — the only inter-node traffic
   the protocol needs.
5. **Round 2** (GPUs, parallel): rebuild or restore stage-1 state
   (§7.3), then stage 2, quotient, FRI per shard; persist `Proof` bytes.
6. **Assemble** the `VectorProof`; content-address it by the claim
   digest exactly as shard proofs are indexed today.

Shards of one batch are scheduled together so the barrier wait is short;
with G GPUs and K ≤ G every shard runs in one cycle. Batches from
different env shards are independent and can interleave to fill GPUs.
Because shard proving is deterministic, a lost or failed shard is
re-proven alone.

### 7.3 Round-1 retention policy and host memory

Round 2 needs, per shard, the stage-1 traces, the lookup witness, and
the stage-1 LDE and Merkle tree (or the means to recompute them). What
is held across the barrier determines the host peak. `Retention` in
`multi_stark::batch` names the policy; `prove_batch_with` takes it with
a witness factory. Two policies are implemented:

- **Retain.** Build every shard's witness, release the record, and hold
  every shard's committed stage 1 across the barrier. Nothing is
  recomputed; the host peak is the whole batch's stage-1 state. This is
  what the unsharded entry point — and so today's CLI — uses, and what
  `prove_from_execution_sharded` uses when the plan has one shard.
- **Regenerate (default for K > 1).** After emitting `header_k`, drop
  everything but the header. In round 2 rebuild the shard's traces and
  lookup witness from the record (deterministic, per-row parallel, CPU),
  and recompute the stage-1 LDE and Merkle tree on the GPU; the
  recommitted header must equal the one in the preamble, which the driver
  asserts.
  Cost: one extra witness build and stage-1 commit per shard. On the
  2026-09-09/10 Init measurements (64-core Xeon 6975P-C) the commit is
  ~20 % of STARK time and the rebuild ~5 %, under 1 s per shard: the
  witness builder is per-row parallel and beats a copy of the witness, so
  holding witnesses across the barrier instead (measured on a quarter of
  Init in 21 shards: 4.5 s per clone against 0.9 s per rebuild, and the
  held witnesses at 10× the record's bytes) does not pay on either axis.
  Host peak: the record plus the traces and lookup witnesses of the
  shards being built *concurrently* (one per active lane), not of all K
  shards. This is the only policy whose peak does not grow with K, and so
  the one whole-environment batches use.

Under Regenerate the 400 GiB-class STARK-phase host peaks of today
disappear, because no full-execution LDE is ever resident on the host;
the peak is the record plus one shard per lane. The recommit is the LDE
itself, which no policy short of Retain avoids.

## 8. Recursion and aggregation

### 8.1 Vector wrap in `ix_aggr`

`aggr_verify_child` today reads one proof and one claim list and calls
the in-Aiur multi-stark verifier. It becomes `aggr_verify_vector(kind,
key)`: read the preamble; run the canonicity and height-bound checks;
compute `D` and the batch transcript; for each shard, fork the
transcript, run `verify` + `ood_verify`, collecting `r_k` (the Lean
verifier already computes the accumulator chain; `last_acc_is_zero`
becomes "return last"); then check the residual sum with the `MEMSEG`
terms and the claim policy. The output statement is unchanged
(`CheckEnv` digest), so every shape above the leaf, the cache keys, and
`ix verify --aggregate` are untouched.

Verification cost is ∝ total shard proof bytes, so a K-way vector costs
about `(Σ_k active_width_k) / active_width_monolithic` times a monolithic
wrap — the same ratio as proof size (§10), roughly 2.5–3× with grouping.

### 8.2 Recursion proofs are vectors too

`ix_aggr` is an Aiur program, so §3–§7 apply to it verbatim: its
execution record is trace-sharded to the same VRAM budget and proven as
a vector on GPUs. The verifier program's rows are dominated by Blake3
gadget rows and FRI arithmetic per child proof, so the natural cold/hot
split places each child's verification in its own shard(s). A parent
`ix_aggr` node therefore verifies child *vectors*; `aggr_verify_vector`
is the only child-verification primitive at every level.

### 8.3 Direct joins and the root

The wrap-first policy exists because a direct join (two raw IxVM
children) needs ~390 GiB of prover RAM. With recursion proofs
trace-sharded, RAM no longer bounds a join; total verification work does,
and direct joins do strictly less of it (each IxVM proof is verified once,
at its first join, and the N wraps disappear). Direct joins become the
default plan.

The root is whatever the final join produces: a `K = 1` vector if proven
unsharded on the CPU box (one proof, one `Ixon.Proof` wrapper, the
uniform 18-word claim), or a `K > 1` vector if proven on GPUs. Either way
it is verified by `verify_vector` like every other Aiur proof (§4.4);
there is no separate root arrangement. Once the memory AIR carries the
`MEMSEG` lookups, *every* Aiur proof has the residual
`1/m(w, 0) − 1/m(w, N_w)` per active width, and only a verifier that adds
the boundary terms accepts it; a verifier that still asserts a zero
final accumulator rejects every honest proof. (A second, `MEMSEG`-free
key arrangement for root proofs would put two verifying keys into the
allowed blob and is not worth the identity complexity.)

What happens to the root afterwards — native verification, or a terminal
compressor that re-verifies it inside another proof system to shrink it
— is outside this design and independent of how the root was
aggregated. The only requirement this design places on such a consumer
is that its embedded Aiur verifier implement the §4.4 contract: the
batch-transcript prefix and the boundary terms.

### 8.4 Why not SP1's recursion for the tree

PR #602's synthetic smoke measured 4.27 M RISC-V instructions and 891
Blake3 syscalls to verify a 28 KB Aiur proof in the SP1 guest. Production
shard proofs are 2–20 MB and verification cost is dominated by hashing
opened rows and FRI folding, so a shard proof costs on the order of 10⁹
guest cycles. Published SP1 GPU throughput is ~1–3 MHz per GPU including
recursion, i.e. several hundred GPU-seconds per Aiur shard proof, versus
seconds to tens of seconds for the same verification as an Aiur circuit
on the CUDA backend (PR #597 measured 8.2× over CPU on recursive
workloads). Across thousands of shard proofs that is two orders of
magnitude; SP1 stays where PR #602 puts it — the terminal compression of
one root.

## 9. Interaction with env sharding and PR #619

- **Env shards can grow.** Today N ≈ 239 Mathlib env shards is forced by
  the STARK-phase RAM peak per shard. With trace sharding that peak is
  chunked, and the env-shard size is bounded by the record, by serial
  execution time, and by the round-1 retention policy's host budget.
  Fewer, larger env shards mean proportionally fewer aggregation nodes.
  The existing `--max-ram` gate becomes a host-record/execution budget
  rather than a prover-peak budget.
- **PR #619 grouping stays orthogonal but should be re-tuned.** Grouping
  merges cold functions into shared circuits; its partitioner prices
  active width per proof. Under trace sharding a hot circuit's width is
  paid in every shard and a cold circuit's once, so the benefit model
  should weight widths by expected shard multiplicity. Re-running the
  partitioner with that weighting is the only change; the mechanism
  (concatenated member rows) is exactly what §3.1 partitions.
- **Manifests and caches.** A leaf's identity stays its claim digest; the
  vector proof is one store object indexed under that digest. `--skip-
  proven`, `ix verify --record`, the aggregate cache and the refinement
  flow are unchanged.

## 10. Proof size

Per shard: `≈ 9 B · q · Σ_{active} W_c`. The colleague's ungrouped
estimate (17 MB first shard + smaller hot-only shards ≈ 73 MB for 10
shards) is the right shape; with PR #619 the first shard's active width
is ~10k columns (~9 MB at q=100) and hot-only shards a few thousand
columns (~2–3 MB), so a 10-way vector lands near 25–30 MB. Two
refinements: Merkle authentication shrinks slightly per shard (pruned
paths over smaller trees), and the per-proof fixed overhead
(commitments, PoW, final polynomial, the two flag columns per memory
circuit) is negligible at these sizes. K itself follows from the §7.1
budget and must be re-derived once the device calibration exists. The
FRI parameter bench in `HANDOFF-recursion-fri-params.md` (q=50-class
recursion parameters) halves all of these numbers if adopted.

## 11. Implementation plan and status

Status as of the `sb/aiur-trace-sharding-design` branch (ix) and
`sb/trace-sharding` (multi-stark, pinned by commit):

| Step | State |
|---|---|
| 1. multi-stark batch protocol (`src/batch.rs`; `prove_stage_1` / `prove_after_challenges`; `verify_after_challenges`; inactive preprocessed matrices opened at ζ) | landed; single-proof pins unchanged; 46 tests |
| 2. Aiur `memseg` lookups, selector-gated pull multiplicities, row-range witnesses, planner, `AiurProof = BatchProof`, batch policy | landed; 21 tests incl. the audits' counterexamples as rejections |
| 3. Lean verifier: `read_batch`, batch/shard Fiat–Shamir, header agreement, residual sum, policy, `verify_batch_at` | landed; `multi-stark`, `recursive-verifier` suites |
| 4. `ix_aggr` and legacy join circuits verify children as batches | landed; `aggregate-first`, `ix-aggr` suites; codegen regenerated |
| 5. Downstream verifiers adopt the contract | open (no in-tree compressor consumes the root yet) |
| 6. CLI / pipeline (`ix prove --trace-shards`, budget-to-plan search, per-shard spans; sharded aggregate wraps on GPU) | leaf path landed: `plan_shards_within` sizes the batch from `--max-ram` and `ix prove --trace-shards` proves it under Regenerate (§14); the aggregate wrap still proves unsharded |
| 7. Tests | landed for 1–4 as listed |
| 8. Benchmarks (`--trace-shards K`, VRAM calibration, recompute overhead) | open |

Two deliberate deviations from the design as first written: byte tables
stay active in every shard (zero multiplicities outside shard 0) because
the in-circuit PCS handles only preprocessed matrices of active circuits
(§3.1); and the verifier's message policy checks pairs and width
distinctness rather than a computed set of active widths, which is
sufficient (§4.4) and needs no circuit-to-width table in circuit.

Ordered so each step is testable alone; file references are the current
seams.

1. **multi-stark: batch transcript, two-round prover, residual verifier**
   (`src/prover.rs`, `src/verifier.rs`, `src/system.rs`, `src/config.rs`).
   - `BatchTranscript::new(params, shape, D)` samples β, γ once and is
     cloneable into per-shard transcripts.
   - `Stage1 { commitment, log_degrees, active, claims }
     = prove_stage1(key, claims, witness)` plus the retained or
     regenerable witness per §7.3.
   - `prove_finish(key, stage1, &batch) → Proof`: forks the batch
     transcript, observes the shard header, continues as today.
   - `verify_shard(&batch, k, proof) → Result<EF>` returning the
     residual.
   - `prove_multiple_claims`/`verify` become the `K = 1` compositions; the
     byte-level proof pins change because the transcript prefix changes,
     so this is a protocol bump.
   - CUDA: the Regenerate policy needs nothing new.
2. **Aiur: memory boundary flags and lookups, shard planner**
   (`crates/aiur/src/memory.rs`, `synthesis.rs`, `trace.rs`, new
   `shard.rs`).
   - The `MEMSEG` channel and the two `sel`-gated telescoping lookups on
     every memory row; the witness builder pushes `(MEMSEG, w, ptr)` and
     pulls `(MEMSEG, w, ptr + 1)` on real rows.
   - `plan_shards(record, budget) → ShardPlan` per §3.2, including
     `memory_totals`; row-range witness builders; per-shard
     `SystemWitness`.
   - `prove_from_execution_planned(...) → BatchProof` orchestrating
     round 1 / preamble / round 2 with the retention policy as a
     parameter (in-process over one or more devices first; the cross-box
     variant is a header exchange).
   - `verify_vector(...)` per §4.4 including canonicity and height-bound
     checks. Bincode format for `VectorProof`.
   - Extend `peak_prove_bytes_by` with a device-residency variant in
     committed cells and calibrate it on the target GPU.
3. **Lean verifier** (`Ix/MultiStark/Verifier.lean`, `Deserialize.lean`):
   batch-transcript prefix and per-shard fork in the Fiat-Shamir replay;
   return the last accumulator; `MEMSEG` terms, canonicity, height bound
   and residual sum in `verify_vector`; `read_vector` deserializer.
4. **`ix_aggr`** (`Ix/Aggr/Circuit.lean`, `Ix/Aggr/Host.lean`):
   `aggr_verify_vector` replaces `aggr_verify_child`; child kind 0 (IxVM)
   and kind 1 (self) both become vectors; plan direct joins by default.
5. **Downstream verifiers**: any embedded Aiur verifier outside this
   repository's native/Lean pair (e.g. a terminal compressor's) adopts
   the §4.4 contract — preamble parsing, canonicity, the boundary terms,
   and the transcript prefix.
6. **CLI and pipeline** (`Ix/Cli/ProveCmd.lean`, `crates/ffi`): `ix
   prove --vram <GiB>` (or auto) selects the vector prover; the shard-proof
   index stores vector proofs under the same claim digests; `ix
   aggregate` and `ix verify` consume vectors transparently.
7. **Tests**: `K = 1` vector round-trips through the native and Lean
   verifiers; K-way vectors verify and reject: a tampered residual, a
   duplicated memory range, adaptively chosen totals (the audit's two
   counterexamples as fixtures), a duplicate or missing width, a
   height-sum overflow, a duplicated entry claim, a mismatched header, a
   shard proven under a different `D`; Lean verifier pins; `ix codegen
   --check`.
8. **Benchmarks**: the `bench-typecheck` harness gains `--trace-shards K`;
   measure per-shard VRAM, prove time, proof bytes, and vector-wrap cost
   on InitStd, then on one Mathlib env shard on the 96 GB card; measure
   the Regenerate policy's round-1 recompute overhead.

## 12. Open questions

- **In-circuit cost of the batch transcript.** The preamble is larger
  than "~100·K bytes": under the current fixed-width transport (u64
  counts, one byte per activation flag, one byte per active log degree,
  one 32-byte cap per shard, raw u64 claim words) it is
  `B = 32 + 8L + 16M + K·(72 + C) + Σ_k A_k` bytes for a canonical circuit
  count `C`, active counts `A_k`, `M` memory widths and one `L`-word
  claim — the activation bitmap dominates. The in-circuit Blake3 makes
  `T(B) = ⌈B/64⌉ + ⌈B/1024⌉ − 1` compressions, each ~7,400 unpadded
  compressor cells (925 committed columns × 8 rows) plus byte-walker and
  assembly rows. Illustratively, `C = 200, A_0 = 200, A_k = 50, M = 20,
  L = 10` gives ~3.8 KB / 63 compressions / ~0.47 M cells at `K = 10` and
  ~7 KB / 116 / ~0.86 M at `K = 20` — small next to verifying the shard
  proofs themselves, but not free. Bit-packing the activation bitmap
  (`C/8` bytes) and nibble-packing log degrees cut `B` by roughly `K·C`
  bytes; the encoding must be fixed before the cost is exact. The batch
  prefix is computed once per vector; each shard's fork replays only its
  own suffix.
- **Byte-table multiplicities on the GPU.** The designated shard's
  Bytes2 table needs global counts; today they come from the record, so
  nothing changes, but if execution is ever distributed the counts need
  the same gather Zisk does for shared tables.
- **Piece padding.** A circuit cut into the fewest fitting pieces pads
  each piece to a power of two, up to one doubling; cutting into one more
  piece can pad less at the price of one more activation. Whether the
  trade is worth taking depends on the ratio of prover cost per cell to
  recursion cost per column, and is worth measuring once both are
  calibrated.
- **Root on GPU.** If the CPU `K = 1` root becomes the bottleneck, the
  root is a `K > 1` vector; the verifier routine is the same, and only a
  downstream consumer with a per-proof cost budget would notice.
- **Cross-box batches.** The protocol needs only header exchange, but the
  orchestration (which box proves which shards of which batch) is the
  same scheduling problem the env-shard fleet plan solves; the natural
  unit of placement is a batch.

## 13. Beyond env shards: one execution, one batch, one claim

Env shards exist for one reason — the prover's RAM peak — and they cost a
whole layer: `CheckEnv` claims with frontier assumptions, the manifest and
its bisection tree, refinement and healing on splits, and an `ix_aggr`
tree whose joins do set unions, assumption discharge and Merkle-path
checks in circuit. Trace shards remove the reason. This section plans the
end state in which the environment is proven as a single execution: its
rows dealt out to one batch of trace shards, its recursion reduced to
summing residuals, and its claim the final statement directly.

### 13.1 What disappears and what replaces it

| Today | End state |
|---|---|
| N env shards, each `CheckEnv(owned, frontier)` | one execution of `verify_claim(CheckEnv(envRoot, none))` |
| `.ixes` manifest, bisection tree, refinement, healing | a shard plan: a pure function of the record and the budget |
| `ix_aggr` wrap/join shapes folding subjects and assumptions | a range-sum recursion: each node verifies shards `[i, j)` of one batch and outputs `(D, Σ residual, i, j)` |
| root = folded `CheckEnv` after ~2N slots | root = one node covering `[0, K)` that checks `Σ residual + messages = 0` and reads the claim from the headers |
| per-shard proof index, aggregate cache keyed by folded claims | shard proofs and recursion nodes cached by `(D, i, j)` |

The lookup argument already makes this sound: the batch verifier
(§4.4) proves the multiset identity over every row of every shard, and
the only per-execution facts — the entry claim and the memory closure — are
public in the preamble. Nothing about statement folding survives because
there is exactly one statement.

### 13.2 The range-sum recursion

A batch of K shards is too large for one recursion node (Mathlib is on
the order of a thousand shards, §13.5), so recursion verifies *ranges*:

- **Leaf node** `vec_verify(D, i, j)`: for each `k ∈ [i, j)`, verify
  shard `k` under the batch challenges (β, γ from `D`), check its header
  against its proof, and accumulate `r_k`. Public output: `(D, Σ r_k, i,
  j)` plus the claims found in headers `i..j` (or their digest).
- **Internal node**: verify two children, require the same `D`, contiguous
  ranges `[a, b)`, `[b, c)`, output `(D, r_L + r_R, a, c)` and the union of
  claims.
- **Root**: range `[0, K)` with `K` the header count under `D`, plus
  `Σ r + messages_acc(β, γ, messages) = 0`, the message policy of §4.4,
  and exactly one claim equal to the expected `verify_claim` claim.

Every node is an Aiur program and is itself proven as a batch of trace
shards; the natural shard boundary is one child verification, so nodes
fit the same VRAM budget as leaves. The whole `Ix/Aggr` set-folding
circuit, its host advice (preimages, trees, paths), and the manifest-bound
verifier become unnecessary on this path.

**Preamble commitment.** With thousands of headers, every leaf cannot
absorb the whole preamble to derive β, γ. The batch transcript should
therefore observe a *commitment* `D` to the preamble — a Merkle root over
the headers and messages — and a shard verifier takes `header_k` with its
authentication path to `D`. That is a small revision of the multi-stark
batch transcript (observe one digest instead of the header list) and the
one protocol change this section needs; make it before anything ships,
since it changes every batch proof's challenges. K = 1 pays a couple of
hashes.

### 13.3 The two hard problems: record size and serial execution

Proving one execution requires *producing* one execution, and here env
shards were doing real work: today the record of one 450 GiB shard is tens
of GB (§7.3), so a whole-Mathlib record is several TB, and execution is
serial — roughly a quarter of Stage 1's 12.7 box-hours, i.e. ~3.5 h of
single-thread time. Two routes, both of which trace sharding makes
available:

**Bounded memoization (cheap, partial).** Execute in windows with a
bounded memo table; a query evicted from the table is recomputed when it
recurs, producing a second row with its own multiplicity. LogUp does not
care — each row's pull matches its own callers' pushes — so this is sound
by construction and only costs rows. Whether it is affordable is a
measurement: `Ix/Aiur/Statistics.lean` already reports `cacheHits`
against unique rows per circuit (`totalUncachedFftCost` vs
`totalFftCost`), so the duplication a given window size would cause can be
read off existing runs before anything is built. It addresses record RAM
but not serial time.

**Distributed execution through the lookup argument (the real answer).**
An Aiur call is a lookup message; the callee's row may live anywhere in
the batch. So one logical execution can be split across W workers without
splitting the *statement*:

- The kernel names a constant across records by its 32 address bytes, not
  by its interned pointer, which is per record: the whole-environment
  `CheckEnv` walks every constant through `check_owned(bytes)`, an entry
  whose body interns the bytes and runs the unsharded walk from there
  (`Ix/IxVM/Kernel/Claim.lean`). Nothing else in the kernel changes.
- A record carries an *ownership*: the set of address bytes it answers
  `check_owned` for (`QueryRecord::ownership`). A constrained call to
  `check_owned` outside it is *deferred*, in the interpreter and in every
  generated call site: the caller's row pushes the call's message, no row
  is emitted, and the record counts the push. The callee returns nothing,
  so a deferring caller needs no hint. Ownership is a prover choice, never
  constrained: a call no record answers leaves the batch unbalanced, and a
  constant two records both check is two balanced rows.
- Worker 0 runs `verify_claim` over the environment's claim and defers
  every foreign constant; worker `r` runs `check_owned` as an entry over
  the leaves it owns, in the same process or on another host, with no
  ordering between workers: ownership is static, so nobody waits. After
  execution each record's deferred counts are added to the multiplicities
  of the rows that answer them (`QueryRecord::absorb_deferred`); a worker's
  own entry registrations, which no claim pulls, are taken off.
- Memory pointers are namespaced: record `r` stores its tables at pointer
  base `r · 2^32 / W` (the kernel's memoization compares pointers as
  `u32`, so every pointer stays below `2^32`), and the closure messages
  become one `pull a_j, push b_j` pair per interval, which both verifiers
  require sorted and disjoint (§5.2). A worker's tables must fit its
  stride; the driver checks this before proving.
- Memoization does not cross workers; shared subcomputations are
  duplicated, as they are across env shards today (Init in 4 workers:
  90 GiB of records against 75 GiB for one execution, 2026-09-10).

`ix prove --ixe E --ixes M --distributed [--cells N]` runs this with one
worker per manifest leaf, verifies nothing by itself, and persists one
proof of `CheckEnv(root, none)` — the claim `ix verify --ixes` checks
against a one-leaf manifest of the same environment. Measured on Init
(64 cores, 2026-09-10, 4 workers at 1.8 G cells): execution 107 s for all
four workers in parallel against 6.0 min for one execution; 71 shards;
27:22 wall; 170 GiB peak with all four records resident; a 100 MiB batch
that verifies natively in 14 s. What is not built: the range-sum
recursion of §13.2 (today the batch is wrapped whole).

**Record residency.** A worker's record is needed from its execution to
the second round of its last shard, and every worker's record exists at
the batch barrier if every worker executes first: the footprint is then
the sum of the workers (Init: 84 GB of records for four, within a
170 GiB process peak). Two facts bound it instead. A worker can commit as soon as every worker that may call into
it has executed — its rows' multiplicities count those calls — and
"may call into" is static: worker `c` reaches only the byte scope of
its owned constants, so the callers of `r` are the workers whose scope
holds a constant `r` owns (plus worker 0, whose walk reaches every
leaf). Records are therefore committed in an order with callers first
(Tarjan's components over that graph, mutually calling workers
grouped), each worker executed when its turn comes with the callers it
still lacks, `--exec-jobs` at a time, and dropped once its shards are
committed. And a record is a deterministic function of the program,
the worker's inputs and the calls absorbed, so round two re-executes
the worker instead of retaining anything: the batch prover takes round
one from a stream of shards (`batch_round_one`, no shard count up front,
the closure messages asked for when every memory total exists) and
`batch_round_two` asks for each record again, when it is regenerated and dropped after
its shards. Resident memory is the size of the current caller group in
records plus one shard's proving state in round one (Init's four
workers all call into each other, so they are one group and all four
records exist until the first is committed), and one record plus one
shard in round two, plus the next worker's record when its execution
runs ahead: by default the driver executes the next worker in commit
order while the prover works on the current record, so the re-execution
is hidden behind proving. Measured on Init with four workers: 28:16
wall and 159 GiB peak against 27:04 and 170 GiB with every record
resident (33:21 when the prover waits for each re-execution instead);
the peak barely moves because Init's four workers are one caller group
and all four records exist until the first commits, while round two
holds one record and the one being executed ahead.

### 13.4 What the planner and prover look like

- **Plan**: rows from all W records dealt out to K shards by the §3.2
  heuristic, with one refinement — each worker's memory intervals must stay
  contiguous within shards, which the row-range scheme already provides.
- **Round 1** commits every shard's stage 1 (any GPU, any box); the
  coordinator collects headers, builds the preamble Merkle tree, and
  publishes `D`. **Round 2** finishes every shard. Both rounds are
  embarrassingly parallel; the barrier is one digest.
- **Recursion** runs as a work queue over ranges: leaves as shard proofs
  land, internal nodes as children land, all keyed `(D, i, j)` in the
  cache. No manifest, no per-leaf claim reconstruction.
- **Verification** of the final artifact: one recursion root proof (or, for
  a native verifier, `verify_batch` over the whole vector).

### 13.5 Sizing for Mathlib

Total committed cells are what today's 239 env shards commit in total, so
the batch has about `Σ_shards committed / budget` trace shards: with
~250 GiB average CPU peaks (≈ 40 B per committed cell) against a 1.8·10⁹-cell
GPU budget, on the order of **~1,000 shards**, roughly 2–5 GB of shard
proofs in total. Recursion work is proportional to the bytes of child
proof verified (hashing opened rows per query dominates; statement folding
on `main` is already small, since most joins are structural). Against
`main`'s direct-join mode with grouped proofs:

| | `main`, direct joins | single execution |
|---|---|---|
| base proofs verified once | 239 × ~9 MB ≈ 2.2 GB | ~1,000 × 2–5 MB ≈ 2–5 GB |
| internal nodes | ~238 × 2 × ~9 MB ≈ 4.3 GB | `K/L − 1` × 2 × 1–3 MB: 2–6 GB at one shard per leaf, 0.5–1.5 GB at four |

The leaf layer costs *more*, not less: trace sharding replicates the hot
circuits' width in every shard, so shard proofs total ~2–3× the bytes of
the monolithic proofs they replace (§10). Internal nodes are cheaper each
— a range-sum program is tiny next to `ix_aggr`, so its proofs are ~1–3 MB
rather than ~9 MB — but more numerous unless leaves verify several shards.
Net in-circuit work is comparable to `main`'s, plausibly 1–1.5× its
verified bytes, tunable toward parity with 4–8 shards per leaf. The gains
are elsewhere: every node fits a GPU (today's 195–390 GiB wraps and joins
do not, which is the 4–8× that matters), Stage 1 stops re-executing
dependencies across env-shard cuts, and the statement-level machinery is
deleted rather than optimized. Execution is the schedule's critical path
until §13.3's distribution lands: ~3.5 h serial for Mathlib, then
`~3.5 h / W`.

### 13.6 Phasing

1. **Preamble commitment** in multi-stark (observe a Merkle root; header +
   path per shard). Protocol bump; small.
2. **Range-sum recursion program** `vec_verify` (leaf/internal/root as one
   entrypoint with a shape hint, like `ix_aggr`), its host driver, cache
   keys `(D, i, j)`, and tests on a K = 4 InitStd batch. Retire nothing yet.
3. **Bounded-memo execution** behind a flag, with the duplication
   measurement from `Statistics.lean` deciding the window size — enough to
   prove InitStd or a mid-size library as one execution end to end on one
   GPU box.
4. **Distributed execution**: deferred calls, worker memory namespaces,
   generalized closure policy (sorted disjoint intervals), coordinator.
   Built (§13.3, `ix prove --distributed`) and measured on Init with four
   workers in one process, records committed in caller order and
   re-executed for round two; what remains is the fleet driver that
   places workers on hosts.
5. **Switch-over**: `ix prove` defaults to the single-execution batch;
   `ix aggregate`'s set-folding path and the manifest machinery become the
   legacy mode for composing independently proven libraries (the one thing
   `CheckEnv` with assumptions still does that a single execution cannot:
   combine proofs made at different times from different environments).

### 13.7 Risks to measure first

- **Duplication from lost memoization** across windows or workers — read
  off `cacheHits` today; if the kernel's shared subcomputation is a large
  multiple, distribution must follow the dependency structure closely.
- **Executor surgery**: deferred calls change the invariant that a row's
  output is computed, not hinted; the hinted output is bound only through
  the lookup, which is exactly the trust model the design already relies
  on, but the implementation must not let a hinted call leak into a
  constrained value without the push.
- **Range-sum node cost** per verified shard byte on the CUDA backend — the
  §8 wrap measurements are the prior; measure on the K = 4 batch.
- **Preamble Merkle path cost** per shard in circuit (log K hashes) — small,
  but it sits in every leaf.

## 14. Whole-env measurement on a large box

The first measurement of the design is one environment proven as one
claim under a fixed host budget: no env shards, no joins, the prover
bounded by trace shards alone. Init is the target (65,994 constants;
a single execution needs more than the ~38 GiB a development box can
spare just to execute, so this runs on a 512 GiB machine). Everything
below exists on the branch; the box only runs it.

### 14.1 Setup

1. Pin the kernel and set up the box as in the metal-48xl handoff
   (`apt-mark hold`, cgroup caps).
2. Check out `sb/aiur-trace-sharding-design` (ix). Its `Cargo.toml`
   pins the multi-stark branch `sb/trace-sharding` and the texray branch
   `sb/per-span-peak` by commit, so nothing else needs to be checked out.
3. `lake build ix`.
4. Compile the env and a one-shard manifest (the whole env as one
   claim; `--shards 1` overrides the static planner's budget sizing):

   ```console
   lake exe ix compile Benchmarks/Compile/CompileInit.lean --out init.ixe
   lake exe ix shard --shards 1 --out init-1.ixes init.ixe
   ```

### 14.2 Step 1: the floor (exec-only)

```console
systemd-run --scope -p MemoryMax=200G -- \
  /usr/bin/time -v lake exe ix prove --ixe init.ixe --ixes init-1.ixes \
    --shard 0 --exec-only --max-ram 100 --trace-shards --texray
```

What to read off:

- `[texray] aiur/execute_ixvm` peak RSS: what execution alone needs.
- `[trace-shards] K shards for a … budget: record R B, whole-execution
  peak P B, heaviest shard peak S B`: the planner's answer for the
  budget. `R` is the floor under Regenerate; the natural cap is `R`
  plus one shard's phases plus headroom, so if `R` alone is a large
  fraction of the budget, lower the budget in later steps only as far
  as `R + 20 GiB`.
- If instead the run reports `peak … over budget — cutting … into N
  parts`, no shard count fits the budget: the floor is above it.
  Raise `--max-ram` until a `[trace-shards]` line appears; that budget
  is the natural cap.

With `--trace-shards`, an infeasible budget stops the run at that
report instead of cutting the shard into env-shard parts, so each run is
exactly one execution. Repeat with `--max-ram` at 400, 200, 100 and the
natural cap to see how K grows.

### 14.3 Step 2: the proof

```console
systemd-run --scope -p MemoryMax=100G -p MemoryHigh=95G -- \
  /usr/bin/time -v lake exe ix prove --ixe init.ixe --ixes init-1.ixes \
    --shard 0 --max-ram 100 --trace-shards --texray --no-index \
    2> init-trace-shards.log
lake exe ix verify --ixe init.ixe --ixes init-1.ixes <proof address>
```

Record, from `init-trace-shards.log` and `time -v`:

| Quantity | Where |
|---|---|
| K, record bytes, projected heaviest shard | `[trace-shards]` line |
| per-shard round-1 and round-2 wall, RAM Δ and peak | `[texray] stark/batch_round_1`, `stark/batch_round_2` (in emission order: every shard's round 1, then every shard's round 2). Both the Δ and the `peak` are the span's own: the peak is the tree-RSS sampler's maximum while the span was open (texray fork `sb/per-span-peak`; the pinned release reported the process high-water mark there) |
| witness builds per shard (two under Regenerate) | `[texray] aiur/witness` count |
| whole-run wall and peak RSS | `time -v` (`Maximum resident set size`) |
| proof bytes | the stored wrapper's size |

Two comparisons make the numbers meaningful, both on the same box:

- **Env-shard baseline at the same cap.** `ix shard --max-ram 100
  init.ixe`, then `ix prove --ixe init.ixe --ixes init.ixes --max-ram 100
  --texray` (no `--trace-shards`) and the aggregate root. Compare total wall,
  the sum of shard peaks, total committed rows (env shards re-execute
  shared dependencies; trace shards do not), and total proof bytes.
- **The same plan under both policies.** Run the K-shard plan twice,
  `--retention regenerate` and `--retention retain`, at the same
  `--max-ram` (the retain run needs the box to hold the whole retained
  batch, so raise the cgroup cap for it, not the budget, which fixes
  the plan). Same FFT sizes, tables and padding; the wall-time
  difference is the regeneration overhead alone. The default
  `--retention auto` retains when the model projects the retained batch
  fits the budget and regenerates otherwise; compare its choice with
  the measured retain peak.

### 14.4 Step 3: calibration

`shard_peak_bytes` (`crates/aiur/src/shard.rs`) projects a shard's
peak as the phase model over its rows with the record resident in every
phase, scaled by the calibration constant the single-proof model uses.
Compare the projected heaviest shard with the measured `MemoryMax`-bound
peak from step 2. If the ratio is outside 0.9–1.1, adjust
`PROVER_RSS_CALIBRATION_*` in `crates/aiur/src/synthesis.rs` before
relying on the budget, and note the multi-stark revision the constant
was calibrated against.

### 14.5 Step 4: the wrap (second phase)

`ix aggregate --trace-shards --max-ram 100 --jobs 1` on the single leaf
wraps the K-shard batch through `ix_aggr`, measuring in-circuit
verification of a batch, with the wrap's own execution proven through
the same trace-shard path under a per-slot budget of `--max-ram`
divided by `--jobs`. Init-scale wraps measured 187–196 GiB before this
branch, so expect the wrap to shard at a 100 GiB cap. The scheduler's
per-slot admission weights are unchanged by the flag, so keep `--jobs`
explicit. VRAM is not sampled anywhere on this branch; a CUDA run needs
its own device-memory reading alongside these lines.
