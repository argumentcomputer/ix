# Incremental trace generation and packing for formal Aiur

Formal Aiur proves a record without materializing its complete trace. The
prover keeps the completed execution record, plans an explicit layout of
trace shards from record metadata, and populates one shard at a time from the
immutable record. Circuits are cut independently and their pieces are packed
into shards by committed cells. The implementation is
`crates/aiur/src/trace/stark/streaming.rs`, with planning in
`crates/aiur/src/trace/stark/planning.rs` and the two-round batch driver in
`crates/aiur/src/trace/stark/batch.rs`.

An **environment shard** selects constants for one claim. A **trace shard**
contains some circuit rows from the execution of that claim. Incremental
generation changes trace generation and partitioning within one claim; the
environment manifest remains the starting partition. Environment refinement
remains the fallback when an execution record or the smallest valid proving
workspace cannot fit.

## Why

A full-trace producer allocates every circuit's complete stage-one matrix
before slicing it into shards, and slices every circuit with one common row
cap. On `34619c5c`, before incremental generation, formal executed four
whole `Init` leaves and then rejected their plans because generation required
92–102 GiB against a 79.7 GiB workspace. Halving the leaves allowed proving,
but each resulting proof contained 128–256 trace shards and occupied 62–119
MB. The original leaves' single-shard plans contained 14.5–15.9 billion
committed cells against a 1.5-billion device limit, so host residency alone
was not the problem: the common row cap also produced many sparse shards,
which make recursive verification expensive.

Incremental generation removes the full-trace host floor. Packing removes
the sparse layout.

## Where it is used

Every formal proving path plans with `Backend::plan_record` (which calls
`plan_incremental`) and proves with the incremental producer:

- the aggregate controller's formal backend
  (`crates/ix-prover/src/aggregate.rs`, `prove_incremental_fed` on the lane's
  shard feed);
- single-claim proving (`crates/ix-prover/src/tools.rs`);
- the IxVM host (`crates/ixvm/src/proof.rs`) and the recursive host
  (`crates/stark-verifier/src/main.rs`);
- the native-executor comparison tools (`crates/ixvm-native`,
  `crates/stark-verifier-native`).

The full-trace producer in `crates/aiur/src/trace/stark/witness.rs`
(`Backend::generate`) remains for the FFI trace export, examples and tests,
where it serves as a differential reference.

## Explicit layouts

A layout names, for every shard, the slice of every circuit it holds:

```text
CircuitSlice = { first, rows, height }
ShardLayout  = { circuits: [CircuitSlice], fixed_counts }
BatchLayout  = { version, shards: [ShardLayout], memory_intervals }
```

`first` and `rows` select contiguous real rows in the circuit's original row
order; `height` is zero for an absent circuit and otherwise a power of two at
least `rows`. Fixed tables appear in every shard at their preprocessed
height. Exactly one shard, the first, has `fixed_counts`: it carries the
record's fixed-table multiplicities and the others carry zero. The memory
intervals are the record's ROM address intervals (`RecordShape`), which close
the batch's ROM boundary messages.

`Backend::validate_layout` rejects a layout before proving unless:

- every non-fixed circuit's real rows are covered exactly once across the
  shards, with no overlap or gap, and fixed slices are unchanged;
- each slice is within its circuit and its height is a power of two;
- there are between 1 and 65,536 shards, and only the first carries fixed
  counts;
- every shard passes the prover's shape check (`check_shape`);
- the batch-wide `Σ height · max(num_lookups, 1)` stays below the field
  order, the bound the native batch verifier enforces.

Only ROM needs contiguity, since its transition constraint is the one
constraint that spans rows. For function circuits, contiguity is a prover
simplification, not a protocol requirement.

`uniform_layout` reproduces the common-row-cap slicing, including slices
that hold only padding. It is used when packing is disabled
(`planning::Options::packing = false`) and in tests that compare incremental
population against the full-trace producer under the same layout.

## Preparing a record

`prepare_incremental` builds a `PreparedRecord` that borrows the immutable
`Execution` and owns only metadata needed across shards. It validates the
record and public root once, computes auxiliary table multiplicities once,
and records each circuit's real row count and, for each grouped function
circuit, the row span of every member function. Under CUDA with generated
population it also uploads the record tables the device circuits read (see
below). It does not clone the record or build a per-row descriptor array.

## Generating one shard

`incremental_witness` populates one `ShardLayout` into a `PreparedWitness`,
with circuits in parallel and rows of a function circuit in parallel batches:

- **Function circuits.** Each row index resolves through the member spans to a
  `(function, query)` pair; the circuit's compiled fill plan
  (`FillPlan::fill_into`) writes the row through the grouping placement with
  the query's full multiplicity. Only the slice's padded height is allocated;
  padding rows stay inactive. Population reads recorded calls, memory and
  hints without executing bytecode again or modifying the record.
- **ROM circuits.** The selected consecutive entries of the width bucket are
  written at their original width-local addresses: a slice beginning at
  address `a` still begins at `a`. ROM transition constraints apply within
  the piece, and the batch boundary messages close the original intervals.
- **Fixed tables.** The shard with `fixed_counts` gets the record's
  multiplicities; the others get zero multiplicities. Preprocessed contents
  are unchanged.

With host lookups, lookup buffers are built only for the current shard. With
device-derived lookups, the shard supplies only lookup shapes. Errors name
the function and query that failed.

## Batch lifecycle

`prove_incremental_fed` validates the layout against the record, prepares the
record, and drives `prove_streamed_scheduled`, which supplies witnesses on
demand for both proving rounds:

1. Round one generates and commits each shard and keeps its header.
2. The batch preamble is formed from all headers, the public claim and the
   original memory intervals.
3. Round two reuses a retained commitment or regenerates the same shard from
   the immutable record. A regenerated shard's complete header must match
   round one before it is proven.
4. The proof is returned; the record and its reservation are released by the
   caller.

Retention follows `RetentionPolicy`: device-derived lookups force
regeneration whenever there is more than one shard, `auto` retains when the
retained batch fits the RAM budget, and `retain`/`regenerate` are honoured
otherwise.

When the plan allows it (`BatchPlan::pipelined`), witnesses are built one
shard ahead of the prover on a `ShardFeed`, a thread pool separate from the
prover's threads. A rendezvous channel keeps at most one finished witness
ahead. Supplies happen in the same order either way, so pipelining changes no
proof byte. `planning::Options::pipeline = false` forces serial supply.

Each run returns a `PopulationReport`: preparation time, per-shard and
per-round wall time, allocation, fill and lookup thread-seconds, the time the
prover stalled waiting for a witness, and the slowest circuits.

## Packing

`packed_layout` cuts circuits into pieces and packs them into shards by
committed cells, charging each piece its padded height times the circuit's
main, stage-two and quotient widths:

1. Charge the fixed tables' cost to every shard and subtract it from the
   per-shard cell budget.
2. Cut each non-fixed circuit into pieces of the largest power-of-two row
   count that fits the remaining budget, the optional row cap and the trace
   domain (`2^(32 - log_blowup)` rows), plus a padded final remainder.
3. Sort pieces by decreasing cost, with circuit index and source offset as
   tie breakers, and place each in the first shard that has room and no
   piece of the same circuit yet.
4. Add fixed tables to every shard and validate the layout.

A row that cannot fit the cell budget is an error rather than an over-budget
piece. Shard order need not equal source address order: memory balance is a
commutative sum, and the shard index only forks the transcript.

The cell budget comes from `planning::Options::max_cells`; CUDA builds
default to `AIUR_TRACE_SHARD_MAX_CELLS`, then 1.5 billion
(`DEFAULT_DEVICE_CELLS`). CPU builds bound cells only when asked. The row cap
is `--shard-rows` (`max_rows`); zero lets the planner choose.

## Planning

`plan_incremental` returns a `BatchPlan` with its layout, chosen
deterministically from the record, circuit system and explicit budget:

1. A **floor check** charges a single shard holding only fixed tables plus the
   widest circuit row. If even that cannot fit the RAM, cell or device
   budget, the plan is rejected without packing.
2. Starting from a cell limit of the device budget (or the whole trace), it
   packs a layout and charges it with `plan_layout`. If the layout fits, it is
   returned. Otherwise, when the device-memory peak is the problem and a
   shorter piece height would fix it, the row cap is halved; else the cell
   limit is halved. Every candidate is recorded in `BatchPlan::candidates`.
3. A caller can fix the layout instead (`planning::Options::layout`, or
   `layout_file`, which may name a previous proof report). The plan then
   only charges it. Runs compared byte for byte must share a layout, because
   population placement changes the planner's estimates.

`plan_layout` models the maximum simultaneous allocations of each phase,
with a 25% margin:

- prepared-record metadata (slices, member spans, map input indexes);
- per-shard host stage-one cells, counting only circuits populated on the
  host;
- per-shard host lookup buffers when lookups are built on the host;
- the multi-stark proving allocation for the shard heights;
- retained commitments for the whole batch when retaining;
- one extra shard witness when pipelining, which is enabled only if it still
  fits;
- under CUDA, the device record bytes and per-shard device peak, checked
  against the device budget, plus a host copy of the device record when
  `AIUR_GPU_TRACE_RELEASE=1`.

`BatchPlan::population` lists, per circuit, real and padded rows, stage-one
cells, whether it is generated on the device, its provider, and why it stays
on the host.

## Memory in the aggregate controller

The controller (`crates/aggregate-controller/src/lanes.rs` and
`lanes/limits.rs`) splits the process host budget into a fixed workspace per
lane, 10% headroom, and a shared record pool (`crates/record-pool`) that
holds the rest. The per-lane workspace is `cell_workspace(cells)`, sized from
the device cell limit, or `AIUR_HOST_WORKSPACE_BYTES`. A lane proves one
record at a time and plans it against its workspace with zero resident
bytes, because the record is already charged to the pool; if no plan fits,
the proof fails with the generation and proving peaks.

Execution grows the record under its `RecordReservation`. The advice charge
is released when execution returns (`RecordReservation::release`); the
record's own charge stays until the record drops after its proof. All record
growth finishes before proving starts, so a lane never asks the record pool
for capacity while proving.

## GPU population

With `AIUR_GPU_TRACE=generated` (`crates/aiur/src/trace/stark/gpu.rs`),
function circuits whose population plans need no host-only state are filled
on the device by `crates/aiur/cuda/population.cu`, which interprets the same
compiled plans as the host writer. The record tables those rows read are
uploaded once per proof and shared by every shard. Each shard's device trace
is a view (`DeviceTrace`) of the slice's base row, padded height and real
rows; generated padding stops at the slice's real-row end. Device population
requires device-derived lookups.

A grouped function circuit is generated on the device only when every
member's plan can be encoded. Stores, loads, stream hints, maps the device
does not implement and unsupported hint channels keep it on the host, as do
ROMs and fixed tables. `AIUR_GPU_TRACE_CIRCUITS=a,b` restricts device
population to the listed circuits.

`AIUR_GPU_TRACE=compiled` replaces the interpreted device plans with
straight-line CUDA writers generated by `crates/aiur-tracegen` and compiled
for IxVM by `crates/ixvm-tracegen` (built with `IX_FORMAL_COMPILED_TRACE=1`).
A bundle binds by fingerprint to the backend's population description and is
rejected if stale. Circuits a bundle does not cover keep the CPU provider,
or the device interpreter with `AIUR_GPU_TRACE=compiled+generated`.

The planner charges host rows only for host-populated circuits; generated
circuits count against the device budget, together with the persistent
device record. Proof bytes are identical to host population.

Under device memory pressure multi-stark asks a generated source to release
its device state. With `AIUR_GPU_TRACE_RELEASE=1`, the uploaded record is
copied to host memory once, freed, and uploaded again on the next tile. It
stays resident by default, because the next generated source needs it again
at once.

## Soundness and compatibility

Allocation order is a prover implementation choice. Incremental population
and packing preserve the certified program, circuit constraints, grouping,
memory semantics, verifying keys and batch protocol, and use the existing
checks in batch verification (`crates/aiur/src/trace/stark/batch.rs`) and
the ROM boundary constraints (`crates/aiur/src/trace/stark/rom.rs`).

The verifier binds the exact public claim, authenticates shard headers before
sampling common challenges, checks memory intervals and field/domain bounds,
and enforces lookup balance over the complete batch. A replayed shard must
reproduce its first-round commitment.

Both verifiers accept packed layouts. The native batch verifier and the
recursive `StarkVerifier`/`Pcs` modules read each shard's activation and log
heights from its authenticated header; neither derives a height, a ROM
address or a query range from a row cap or the shard index, requires every
non-fixed circuit to be active, or requires shard 0 to be the largest. A ROM
piece starting at address `a` telescopes to a push of `a` and a pull of its
end, and the verifier only checks that the boundary intervals are well
formed, sorted and disjoint.

The two verifiers do not check the same things. As audited at `34619c5c`:

- The native verifier enforces the cumulative height/lookup budget below the
  field order, that fixed tables are active, and their exact heights.
- The recursive verifier bounds the largest domain (`log_gmax < 33`) and the
  shard count. It has no cumulative height/lookup budget and no explicit
  fixed-table activation or height check; for fixed tables it relies on the
  PCS opening against the preprocessed commitment.
- The no-wraparound argument for ROM intervals depends on the cumulative
  budget.

The prover's `validate_layout` checks the cumulative budget before proving,
but validation must not assume recursion enforces it; closing that gap
belongs to the recursive verifier.

The layout is not a trusted input to verification. It guides the prover;
verification derives its obligations from the trusted system and
authenticated proof data. Coverage checks in the producer catch
implementation errors but do not replace cryptographic verification.

Under an unchanged layout, incremental and full population produce identical
matrices, lookup data, keys and proof bytes. Packing changes activation,
heights and commitments, so proof bytes and content addresses may change
while keys and public claims stay the same.

The Lean compiler correctness results apply to unchanged circuits. They do
not constitute a formal proof of the Rust adapter or the cryptographic
backend; incremental generation preserves that trust boundary.

## Tests

`crates/aiur/src/trace/stark/tests/streaming.rs` covers:

- incremental slices against full grouped rows and proofs under the uniform
  layout, and fixed tables in both rounds;
- packed layouts that prove, layouts with missing or duplicate ranges that
  are rejected, and packing that reduces sparse shards while checking the
  protocol bounds;
- a changed second-round commitment, malformed records, the fixed-table
  floor, and errors that keep function and query context;
- GPU population (CUDA builds): padding that stops before the next piece,
  identical proofs, and placement reports;
- pipelined and serial supply producing identical proofs, a worker error
  stopping the pipeline, and a planner that charges the lookahead and
  accepts a fixed layout.

`crates/aiur/src/trace/stark/tests/gpu.rs` checks device tiles against host
rows, re-uploaded released records, and the circuit allowlist.
