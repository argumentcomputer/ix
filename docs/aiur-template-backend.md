# Aiur narrow template backend (prototype)

> **Historical (2026-11-15).** This document is the Rust prototype notes. The v1 layout and the Rust-only v2 layout path described here were removed; the soundness sections ("Soundness argument", "Soundness of sharing") are still the current arguments. The current backend is described in [aiur-compression-architecture.md](aiur-compression-architecture.md).

Status: Rust prototype for measurement and validation
(`crates/proof-compression/src/aiur_backend/template{.rs,/lower.rs,/v2.rs}`).
It is not the production path. The production tiling pass is planned in Lean,
with a refinement proof. Two layouts:

- **v1** (`template.rs`, `lower.rs`): §7.1 "L2 regions, T1, narrow ROM +
  stacked table" of `aiur-structural-gap.md`. Sections "Input" through
  "Soundness argument" below.
- **v2** (`template/v2.rs`): the §7.2 S4b layout — periodic shards sharing
  one fixed matrix, degree-3 spans, lane-slot messages, unrolled
  `Blake3::compress`. Section "v2 layout" below; it reuses every v1
  obligation not restated there.
- **v1 from the Lean pass** (`template/lean.rs`): the v1 layout as the
  verified Lean tiling pass exports it, the shape of
  `narrow_heap_sound_tables`. Section "v1 through the Lean pass" below. v2
  stays on the Rust prototype until the Lean v2 theorem exists.

## Input

The KZG adapter's per-function circuits (`kzg::Compiler::inputs`), compiled
to hash-consed constraint graphs, for an **ungrouped** artifact. Each
function circuit has these properties:

- It is one row with current-row main columns only (`[cols…, multiplicity]`).
- Lookup 0 is the receive `pull(mult, [CALL, f, payload])`.
- The other lookups are sends with constant `[tag, id]`.

The lowering rejects anything else: row selectors, next-row columns,
publics, or non-constant tags or ids. The original function circuits use no
first, last or transition selectors, and the template uses none.

## Physical layout (W cells, L = W/4 lanes)

- **Narrow circuit(s).** The main trace has `x_0..x_{W-1}`. The fixed columns are:
  - per lane: `qm, q0..q3, qc`;
  - `join` (when `L ≥ 2`);
  - `sel, tag, sub`;
  - W copy labels and W copy multiplicities.

  There are 32 fixed columns at `W = 8`.
  - Lane relation: `qm·a·b + q0·a + q1·b + q2·c + q3·d + qc`.
  - Constraints: `Σ lanes = 0` and `(1 − join)·lane_k = 0` for `k < L−1`. The degree is 4.
  - Lookups:
    - W copy lookups `push(cmult_j, [COPY=3, label_j, x_j])`;
    - one message lookup `push(sel·x_0, [tag, sub, x_1..x_{W−1}])`.

  No constraint reads the next row, so shards can split anywhere.
- **Regions.** Function `f` has a configured capacity `C_f`. Instance `i`
  has these fixed properties:
  - a row range;
  - invocation id `id_f + i`, which is globally unique;
  - copy labels `label_f + i·slots + s`, which are globally unique.

  The per-instance id is folded into the lane constant `qc`. Rows past the
  last region have all fixed columns zero.
- **Stacked table.** Fixed columns are `sub, a_1..a_{W−1}`, with one main
  count column, and the lookup is `pull(count, [CALL, sub, a…])`. Only maps
  that some template calls are included. Padding rows use a sentinel `sub`
  that no message uses.
- **Narrow ROM.** Fixed columns are `sub = width + j·2^32` and
  `addr = object index`. The main columns are a count and `W−2` values. The
  first chunk keeps the original `(ROM, width, addr, …)` tuple. Addresses
  are fixed and unique per width, which replaces the original ROM circuit's
  first-row and transition address chain.
- **Admission.** An execution with more invocations than `C_f`, or more
  objects per ROM width than configured, is rejected before witness
  generation.

## Lowering

Nodes become linear forms over atoms (wide columns and products). Each
value that is needed becomes a slot of one of these kinds:

- a column;
- `Sum(terms, k)`;
- `InvocationId`;
- `Key`, which is free.

Every slot of kind `Sum` is defined by one relation, which is a lane, a
joined row, or a chain of carries. Every constraint root is emitted as a
relation over slots. A product used once is fused into the relation that
uses it. A product with affine operands takes one lane, with its linear
parts absorbed into `q0` and `q1`. Message arguments are slots.

## Copy constraints: encoding

Every cell carries a fixed label and a **fixed multiplicity**, both in
preprocessed columns. If a slot has `o > 1` cells, its first cell has
multiplicity `o−1` and each other cell has `−1`; single cells have 0. So
there are W label columns and W multiplicity columns. The §7.1 planner
counted W+1.

For each label, LogUp balance means `Σ_c m_c·[(L, v_c)] = 0`. With these
multiplicities, any class of equal values that contains the first cell
balances only if it contains all `o` cells, because `o < p`. So all cells
share one value. The prover chooses neither labels nor multiplicities.

## Wide messages (T1, keyed chunks)

A payload wider than `W−1` is split into `W−2`-value chunks. Each chunk row
is `[tag, sub_j, key, chunk_j]` with multiplicity `sel·m`.

- **Calls:** `sub_j = f + (j+1)·2^32`.
  - Receive key: the instance's invocation id, pinned by a lane `x − id = 0`.
  - Send key: a free slot.
- **Maps:** the key is the table row index, which is fixed in the stacked table.
- **ROM:** the key is the address.

Within a template, the multiplicity and key are each one slot, wired across
all chunk rows.

**Booleanity.** Every chunked send adds `m² − m = 0`.

Bus separation: COPY uses tag 3, against `CALL = 1` and `ROM = 2`. Chunk
`sub` values are disjoint from narrow `sub` values. Fingerprints ignore
trailing zeros, so tags differ in the first coordinate.

## Soundness argument (obligations a Lean proof must discharge)

1. **Reconstruction.** By copy soundness, a valid trace gives one value per
   (instance, slot).
   - Every `Sum` slot equals its definition, by induction in creation order.
   - Each relation's expansion is the node's polynomial.
   - The wide row read off the column slots therefore satisfies every
     original constraint. This includes `(1 − act)·mult = 0`: an inactive
     instance can't receive.
   - Message rows carry exactly the original `(multiplicity, args)` of each
     lookup, because the multiplicity and arguments are wired slots.
   - Columns that no constraint or lookup reads are unconstrained, both here
     and in the original.
2. **Inactive physical rows.** Rows outside regions have `sel = qm = q = 0`
   and copy multiplicity 0, so they carry no message, gate or copy. Unused
   message cells are free. This is sound, because the balance of extended
   tuples implies the balance of their projections.
3. **Chunking.** Assume send multiplicities are boolean (enforced) and total
   counts are below `p` (the existing row bound).
   - For each `(sub_j, key)` there is exactly one receiver: the instance with
     that id, the table row or the ROM address. This gives uniqueness.
   - So every enabled sender with key `k` has chunk `j` equal to the
     endpoint's chunk `j`, for every `j`. All `J` rows are present by
     template, which gives completeness, and they share key and multiplicity.
     So there are no mixed tuples.
   - Hence the whole-tuple multiset relation of the original holds. The
     endpoint's free receive multiplicity `m_k` equals the number of senders,
     as in the original.
   - Without booleanity, mixed tuples are possible: `A + B − C` with
     cancelling multiplicities.
   - A chunked public claim is `J` claims with one prover-named key, by the
     same argument.
4. **Balance across regions.** Shards, table and ROM share one LogUp bus.
   The original bound applies (`MAX_TOTAL_ROWS`, count < `p`).
5. **Capacity.** It is fixed by configuration, so every proof shape is fixed.
   Every circuit has preprocessed columns and is always active.

Not covered:

- depth or acyclicity beyond what the original constraints and range maps
  already enforce (they are reproduced unchanged);
- the Lean refinement proof itself;
- grouped circuits.

## Measurements (2026-11-14)

**M1** (`tests/aiur_template.rs`, `bn254-trace.ixa`).
- Honest KZG proofs at `W = 8` and `W = 4` (chunked receives at `W = 4`)
  for three inputs, each with an exact native multiset check and a
  reconstruction check.
- The verifier rejects each of these: altered wired cell, receive chunk
  swapped between invocations, duplicate id, missing id, spare instance
  receiving a real tuple, changed output.

**M2** (`examples/aiur_template_count.rs`; chain_v1 ungrouped, Init stage-3
counts; `target/template-backend/m2-w8-h*.json`; W=8, shards of 2^24).

| | planner L2/T1/N/M0 h25 | actual h25 | planner h0 | actual h0 |
|---|---:|---:|---:|---:|
| evaluations | 423 | 374 | 337 | 324 |
| committed cells | 2.09B | 1.65B | 1.77B | 1.33B |
| fixed cells | 3.47B | 3.50B | 2.94B | 2.82B |
| main cells (padded) | 1.12B | 0.88B | 0.94B | 0.71B |
| template rows (unscaled) | 110.4M | 86.3M | | |
| gate rows | 75.5M | 51.5M | | |
| message / chunk rows | 34.86M / 7.86M | identical | | |
| copy constraints | 447M | 332M | | |
| narrow fixed columns per shard | 25 | 32 | | |
| narrow shards | 9 | 7 | | |

**M3** (`tests/aiur_template_kzg_source.rs`, ignored).
`KzgVerifier::verify_deferred` on the 3-circuit `nonconstant` source proof,
at exact capacities and W=8.
- Size: 1.52M narrow rows (2^21), compared with 1.15M wide main cells. That
  gives 74 evaluations, 33M committed cells and 71M fixed cells.
- Times: witness 0.4 s; fixed commitment 33 s (CPU, cacheable); prove
  32 s.
- Proof and verification: 3,448-byte proof, verified natively; a changed
  output is rejected.
- Peak RSS: 18.7 GB.

## v1 through the Lean pass (`template/lean.rs`)

The v1 layout is produced by the verified Lean pass, not by `lower.rs`.

**Pipeline.**

1. `LayoutInput` (Rust) writes the pass's input: the compiler's function
   graphs, their capacities, the table rows and the entry request.
2. `tiling_export` (`MultiStark/Examples/TilingExport.lean`, `lake build
   tiling_export` from the repository root) runs `Aiur.Tiling.lower` on every
   graph and on one `Bridge.tableCircuit` per table row. It rejects the layout
   unless `System.checkKeyed` and `Part.checkRequest` accept it. It writes the
   templates, the entry request `Part.request W t` padded to `W + 1`, and the
   fixed matrix.
3. `Layout::load` (Rust) parses and validates the export:
   - template shapes, slot order and message groups against each circuit's
     lookups;
   - every fixed row against the template row and instance that the witness
     writes there.
4. `Backend` (Rust) generates the witness and builds
   `Aiur.Tiling.narrowCircuit W` over the exported fixed matrix, split into
   power-of-two shards.

Nothing in Rust lowers a circuit or lays out a fixed column.

**Fixed matrix.** The exporter generates the rows in `System.places` order
with `Row.fixed`, the row function of `System.fixedAt`. Labels, copy
multiplicities and invocation ids use closed forms, because `System.fixedAt`
enumerates the places on every call. Every row is compared with
`System.fixedAt` itself when the system has at most 3,000 places (all
`bn254-trace` layouts). Larger systems get two sampled rows, or none above
4,000 circuits, since the definition is quadratic in the circuit count.

**Layout, as `narrow_heap_sound_tables` states it.** It differs from the
prototype in four ways:

- **Map tables.** Every row of every called map is its own single-instance
  circuit. A chunked row is keyed by its instance id. This replaces the
  stacked table.
- **ROM.** Every ROM entry is its own single-instance circuit receiving the
  constant `[ROM, width, address, words]`. A chunked entry is keyed by its
  address. This replaces the narrow ROM circuit.
- **One circuit.** Table and ROM rows live in the narrow trace, so the
  system has one narrow circuit (in shards) and no table or ROM circuit.
- **Entry request.** Chunked requests use key 0 (`Part.request`), so the
  entry function is circuit 0 and the witness moves the root invocation to
  its instance 0.

**Tests** (ignored; they need the exporter).

- `tests/aiur_template_lean.rs` (`bn254-trace`):
  - honest proofs for three inputs at `W = 8` and `W = 4`, each with an
    exact native multiset check and a reconstruction check;
  - the six forgeries of M1, plus a map row whose count is raised. The
    verifier rejects all seven.
- `tests/aiur_template_lean_kzg_source.rs` (the M3 execution, `W = 8`):
  - 161 functions and 401,306 table rows: 393,216 of them are six 2^16
    byte maps, and 6,542 are ROM entries;
  - 2,537,971 places in one `2^22` circuit: 50 evaluations, 32 fixed
    columns;
  - export 140 s (lowering 3.0 s, `checkKeyed` 10.4 s, fixed matrix 68 s
    and 434 MB), setup 63 s, prove 63 s;
  - 2,164-byte proof with a 4-tuple chunked request; a changed claim is
    rejected;
  - peak RSS 50.7 GB.

**The steady chain** (`examples/aiur_template_lean_chain.rs`).

- **Input.** `chain-ungrouped.ixa` under the 2-shard stage configuration
  (`target/narrow-terminal/stage3-s2-h0.08.config.json`), with `W = 8` and
  one v1 instance per round of `Blake3::compress`. There is no execution,
  so the system has no ROM rows and a zero request.
- **Size.** 156 functions and 395,020 map rows give 78,528,133 places,
  1,456,327 instances and 24.8M lookup parts.
- **Time.** The compiled exporter takes 47 s, with 2.7 GB peak RSS:
  lowering 2.9 s, `checkKeyed` 9.4 s, the rest JSON.
- **Fixed matrix.** It was not written. At the kzg-source rate it would
  take about 35 minutes and about 13 GB.
- **ROM.** The configuration's 422,221 ROM objects would add one circuit
  each.

No interpreted run was needed.

**What the theorem covers now.** With function circuits `C_f` and this
export, every layout hypothesis of `narrow_heap_sound_tables` is decided by
the exporter (`ok`, `req`) or is a closed-form size bound it reports
(`bound`, `instances`, `lookup_parts`). Three things are not covered:

- **`C_f = Bridge.lower idOf chip_f`.** The function circuits are the Rust
  KZG compiler's (`kzg::Compiler::inputs`), so this equality is the existing
  trusted Rust lowering of `Optimized/EndToEnd.lean`. The tiling of `C_f` is
  what is proved.
- **`fixedIn`.** The map rows are the program's tables and the ROM rows are
  this execution's ROM. Nothing checks them against
  `Bridge.fixedRows … (rawROM rom)` in Lean.
- **The ROM in the key.** ROM words are constants of the fixed matrix, so the
  verifying key depends on the execution's ROM. That is acceptable for these
  fixtures, but not for a fixed-key production stage. That stage needs a
  Lean variant with witness-valued ROM words under constant addresses.
  `checkKeyed` already accepts such ROM receivers; `narrow_heap_sound_tables`
  does not.

**The production narrow stage (v2).** `Periodic.narrow_heap_sound_stacked`
(plan §4, §5e) covers stage 3's layout: periodic shards, spans, lane
messages, merged lookups, virtual multiplicities (booleanity of chunked sends
included), the unrolled `Blake3::compress`, per-shard offsets, the fixed
matrix of one chip layout, and the stacked map and ROM tables with
witness-valued ROM words at fixed addresses. `tiling_export2` decides every
layout hypothesis (`Sharded.check`, `Unroll.check`, `Stacked.check`,
`checkMap`/`checkRom`, distinct channels, the request checks) and reports the
size bounds; its fixed matrix is `Sharded.fixedAt` by `Sharded.emit_eq`.
Still not covered:

- **`C_f = Bridge.lower idOf chip_f`**, as for v1: the trusted Rust lowering.
- **`mapsIn`**: the map rows against the program's map claims.
- **`enables`**: activated enables are 0 or 1 (`Optimized/EndToEnd.lean`).
- **The Rust tables.** `v2.rs`'s stacked table and `narrow_rom` must take
  `Periodic.Stacked`'s shape (count in main column 0; fixed `sel`,
  `key = keyBase + r`, data; `push(−sel·count, [code_c, key?, slice_c…, 0…])`)
  and its keys (map rows: global ids after the chip shards, map by map; ROM:
  the address). The export lists each table's descriptor; `lean.rs` does not
  read them yet.
- **The request**: the exporter checks the request's shape; the theorem's
  `req`, `req2` read only that shape, so they hold for every root of it.

## v2 layout (§7.2 S4b)

### Shared fixed matrix in multi-stark

Fork `~/repos/forks/multi-stark-shared-fixed`, branch
`formal-aiur/shared-fixed` (from the pinned `bcf3fc8`; used through a
command-line `[patch]`, the pin is unchanged).
`System::new_shared(config, inputs, shared, retain)` takes `shared[i] =
Some(j)`: circuit `i` reads the fixed matrix of circuit `j < i` and brings
none of its own. Changes:

- **Setup.** One fixed matrix per *slot*. `preprocessed_indices[i] =
  preprocessed_indices[j]`, and the reader's fixed width and height are the
  owner's.
- **Transcript.** `observe_shape` additionally observes every circuit's
  slot, only when some slot is shared. Systems without sharing keep their
  transcript byte for byte.
- **Prover.** Round 0 has one entry per slot, opened at the union of its
  active readers' points (`ζ`, and `ζω` if any reader reads the next row).
- **Verifier.**
  - It expects one opened matrix per slot.
  - It builds that slot's evaluation claim once.
  - Each reader's quotient identity reads the slot's values.
  - A slot is "inactive" only when every reader is inactive.

**Soundness of sharing.** Let `P` be the committed fixed polynomials of a
slot, with height `H`.

1. The verifier already checks that every active circuit with fixed columns
   has log degree `log H`. Every reader of the slot therefore has the trace
   domain of `P`.
2. multi-stark draws one global `ζ` after all trace commitments
   (`verifier.rs`). So every reader's "current row" and "next row" points
   are the same two points, `ζ` and `ζω_H`.
3. One KZG opening binds the claimed `P(ζ)`, `P(ζω_H)` to the committed
   `P`. Each reader `s` then checks its own identity
   `Q_s(ζ)·Z_H(ζ) = C_s(main_s(ζ), aux_s(ζ), P(ζ), …)`. Its main, lookup and
   quotient matrices are its own commitments.
4. This is exactly the check an unshared system makes against a private
   copy of `P` with the same values. The per-circuit Schwartz–Zippel bound
   and the union over circuits are unchanged, so each shard's row
   constraints hold over the shared fixed rows.

Sharing saves only repeated commitments and openings of the same
polynomial. It does not relate the readers' witnesses.

### Per-shard offsets and invocation placement

Shard `s` is its own circuit. Its constraint graph is the same as every
other shard's except two constants in its lookup expressions, which the key
fixes:

- **Copy tuple:** `[3 + 4·(label + s·Lₛ), x_j]`, where `label < Lₛ`
  (labels per shard).
- **Row-message key:** `x1 + rkey + kf·(s·Iₛ)`, where `rkey < Iₛ`
  (invocation ids per shard).

Global labels and ids are therefore disjoint across shards. This has two
consequences:

- **Copy classes.** A slot's copy class contains only cells of one shard.
- **Call keys.** A chunked call's key names one instance of one shard.

**No invocation straddles a shard.** Every shard holds `⌈cap_f/S⌉` instances
of each function at the same rows, and all of an instance's rows lie in
`[0, rows_per_shard) ⊆ [0, H)`. With per-shard labels, the copy argument
holds per shard. An instance split across two shards would put cells of one
slot under two different labels, so its copy constraints could not balance.
This is a completeness obligation on the tiling: `rows_per_shard ≤ H`, and
regions are contiguous within the period. It is not a verifier check.

**Forgery tests** (`tests/aiur_template_v2.rs`; each also run against a
test-only variant without offsets, which *accepts* the first two):

- **Straddling invocation:** the second half of an instance's rows is
  replaced by its twin's in the other shard. Every gate and message is
  unchanged.
- **Cross-shard wiring alias:** one message row is swapped with the twin's.

Both are rejected with offsets. Without them, labels alias across shards,
so both pass. Also rejected:

- a compression's chunked-receive row swapped across shards;
- an altered wired cell;
- an unrolled stage-4 state cell altered;
- a spare instance receiving;
- a changed output.

### Row and column layout (`W` cells, `L = W/4` lanes; 42 fixed columns at `W = 8`)

- **Gate lanes.** Lane `l` has `qm, q0..q3, qc`, so
  `lin_l = Σ q_c·x_{4l+c} + qc`.
- **Span flags.** There are `L(L+1)/2` flags `M_{l,l'}` for `l ≤ l'`.
- **Constraints.** There are `L` of them:
  `C_l = qm_l·x_{4l}·x_{4l+1} + Σ_{l' ≥ l} M_{l,l'}·lin_{l'}`. Each has
  degree 3, so the quotient degree is 2 and shards can be `2^25` rows.
  - A span starting at `l` has `M_{l,l'} = 1` for its lanes.
  - Continuation lanes have `qm = 0` and no flags, so their constraint is
    `0`.
  - Only a span's first lane holds a product.
  - Obligation on the fixed matrix: spans are disjoint, and no message lane
    is inside a span.
- **Lane messages.** Each lane `l` has `(ts, mk, mc)` and the lookup
  `push(mk + mc·x_{4l}, [ts, x_{4l+1}, x_{4l+2}, x_{4l+3}])`. It carries a
  payload of at most 3 values. A lane that is not a message has `ts = mk =
  mc = 0`, so its multiplicity is 0.
- **Row messages.** The columns are `(ts, mk, mc, rkey, kf)`, with the lookup
  `push(mk + mc·x0, [ts, x1 + rkey + kf·s·Iₛ, x2..x_{W−1}])`.
  - **Chunked receive rows:** `x1 = 0` is enforced by that row's own span
    (`M_{0,0} = 1`, `q1 = 1` on lane 0). The key is the instance's fixed
    global id.
  - **Other rows:** `rkey = kf = 0`.
- **Copy:** `W` labels and `W` multiplicities, as in v1.
- **Buses.** `ts = tag + 4·sub`, with `tag ∈ {CALL=1, ROM=2}` and copy `3`.
  - Every `sub`, label and id is below `2^62`.
  - So the first coordinates are distinct integers below `p`, and the three
    buses are disjoint.
  - Unkeyed tuples are `[ts, payload]`. Keyed chunk tuples are
    `[ts_j, key, values_j]`.
  - ROM's unkeyed tuple `[ROM + 4·width, addr, values]` is its chunk 0.
  - Unused message cells are free, which is sound by v1 obligation 2.
- **Multiplicity `M = mk + mc·x`.**
  - **Chunked sends:** each adds `M² − M = 0` as a relation:
    `mc²·x² + (2·mk·mc − mc)·x + mk² − mk`. A constant `M` is checked to be
    in `{0, 1}` when the template is built.
  - **Merging:** only unchunked lookups are merged, by adding
    multiplicities (LogUp additivity). Merging cannot break booleanity.

### Lowering

- **Products.** They are hash-consed on normalized operands, where
  `(a·g + b)(c·h + d)` becomes one product of `g`, `h`. A product used once
  linearly, and never as a cell, is fused into its relation.
- **Relations.** A relation with at most one product that fits `4L` cells is
  one span. Longer ones chain full-row spans with carry slots, at most one
  product per span.
- **Correctness.** All of this is exact algebra over coefficients fixed in the
  key, within one instance. The v1 reconstruction obligation applies
  unchanged:
  - each `Sum` slot equals its definition;
  - each relation expands to its constraint;
  - message rows carry the original `(multiplicity, args)`.

### Unrolled `Blake3::compress`

One template holds eight bodies of the compiled compress circuit:
- **Stage selector** (`sel`, the self-call's multiplicity column): fixed to
  1 in bodies 0–6 and 0 in body 7.
- **Activity column:** fixed to 1 in all bodies.
- **Stage argument:** fixed to 0 in body 0.
- **Receives:** body `s > 0` reads each receive column as the form of body
  `s − 1`'s self-call argument. Every self-call and every receive of bodies
  `1..7` is dropped.
- **Receive multiplicity** (column `main_width − 1`, read by the receive as
  `0 − x`): fixed to 1 in bodies `1..7`. The column holds no cell, so the
  template is unchanged. Fixing it makes each dropped receive of body `s`
  (multiplicity `−1`) cancel body `s − 1`'s dropped self-call (`+1`) on the
  same tuple, the pairing the Lean bridge for `Unroll.circuit` checks.
  Witness generation rejects a compression chain whose stage `s > 0` row
  has another multiplicity.

Obligations:

- **Soundness.**
  - Fixing a column to a constant restricts the original constraint set.
  - Wiring a receive to the previous self-call's payload replaces a
    self-call message pair whose tuples are equal by construction.
  - So any accepted instance yields eight original rows that satisfy the
    original constraints and whose dropped messages balance. The
    stage-constant arm conditions remain as constraints.
- **Entry.** Every external call to `Blake3::compress` must pass a
  constant stage 0. This is checked when the backend is built, and callers
  enter through `compress_init`. A caller with another stage would only lose
  completeness.
- **Padding.** With activity fixed to 1, an unused instance must still be a
  valid compression. The prover copies a real instance and sets its receive
  multiplicity to 0. Its byte-map lookups are added to the stacked table's
  counts, which the prover computes from all messages.

### Numbering of the verified layout (`aiur-template-lean-plan.md` §5e)

`v2.rs` uses the numbering of `Periodic.Sharded` (`PeriodicTemplate.lean`):

- **Slots.** A template's logical slots are the prototype's, then one
  invocation slot if its receive is chunked, then one virtual slot per
  message whose multiplicity is constant or has an offset (`mk ≠ 0` or no
  cell), in message order (`Template::logical_slots`). The extra slots hold
  no cell.
- **Labels.** Instance `i` of function `f` has labels
  `label_base_f + i·logical_slots_f + slot`, from 1; shard `s` adds
  `s·labels_per_shard` (`labelOffset`). Every occupied cell carries its
  label (`labelAt`); a single-occurrence slot's cell has multiplicity 0.
- **Regions and ids.** With `Config::entry` set, the entry function's
  region comes first and the root invocation is its instance 0, so the root
  has invocation id 0 and a chunked request is keyed by 0 (`Part.request`).
  Ids are `id_base_f + i` per shard plus `s·ids_per_shard` (`idOffset`).
- **Tables.** Map-claim rows are numbered after the chip shards' instances,
  map by map; a chunked map row is keyed by its id, not its row index.
  The tables are `Periodic.Stacked` circuits (`v2.rs` `Stacked`), one per
  called map and one per ROM width, after the shards.
  - Map table columns: fixed `sel`, `key`, payload; main count.
  - ROM table columns: fixed `sel`, `key`, where the key is the address
    `0..capacity`; main count and words.
  - Heights: at least `2^16`, so the tables share one packing class.
- **Buses and columns.** `ts = tag + 4·sub` with chunk subs
  `sub + (c+1)·2^32` (calls) and `sub + c·2^32` (ROM); the 42 fixed columns
  in `fixedRow` order, as before.

On Init stage 3 (2 shards, +8%) the numbering changes only the fixed
matrix: dimensions, evaluations (110), packed commitments (41) and proof
bytes are unchanged, and the narrow key's digest changes.

**Lean export path** (`template/v2/lean.rs`). It is the production layout
source: `aiur_template_v2_init --config` uses it by default, and `--lean`
turns it on for a derived configuration.

- **Input.** The function graphs in region order, with compress marked for
  unrolling; per-shard capacities, map rows, ROM widths and the request
  shape.
- **Export.** `Layout::export` runs `tiling_export2` (`--lean-exporter`,
  `IX_TILING_EXPORT2`) beside execution and witness generation. It decodes
  the fixed matrix from the exporter's stdout in parallel.
- **Checks.** `adopt_lean` checks the exported layout against this
  backend's lowering and numbering: templates (all logical slots), label
  and id strides, bus codes and lane flags, stacked-table descriptors and
  request shape. The exported fixed matrix is then committed as is.
- **Cross-check.** `--lean-reference` also compares every fixed row with
  `narrow_fixed`. It is a check between the two implementations, not a
  soundness step.
- **Tests.** `tests/aiur_template_v2.rs` round-trips `lean_reference` and
  rejects tampered copies. `v2_lean_exporter_on_fixture` runs the real
  exporter.

Init stage 3 under the exported layout, and what the theorem covers: plan
§5e "Production run" and §5f. The stacked key needs a `2^26` terminal
(42.7M constraints).

**Grouped artifacts:** not supported. The last stage uses the ungrouped
export of the steady chain artifact (`bn_grouping export … --chain` with an
empty policy, `target/template-backend/v2/chain-ungrouped.ixa`). Its program
is the same as the grouped `chain_v1` artifact's.

### Measurements (2026-11-14, `target/template-backend/v2/summary.json`)

**M4** (`tests/aiur_template_v2.rs`). Two runs, both with an exact native
multiset check:

- BN254 trace fixture: honest proofs for three inputs, with two shards sharing
  one fixed slot (`shared-fixed` feature). Default CI runs the same fixture at
  one shard on upstream multi-stark, the production L3 path: honest proofs,
  local forgeries, the Lean export round trip, and a checked-in one-shard
  `tiling_export2` layout whose fixed matrix matches the Rust one by BLAKE3.
- KZG source verifier with the unrolled compress (2,521 rows per
  compression, 2 shards): 1.26M rows, setup 20 s, prove + verify 28 s.

Forgeries are listed above.

**M5** (`examples/aiur_template_v2_init.rs`, `W = 8`, `2^25` shards). Init
stage-3 record of each chain:

| | planner2 S4b (gl-chain, h25) | v2, gl-chain h0 / h25 | v2, fold-transcript chain h0 / h25 |
|---|---:|---:|---:|
| template rows (unscaled) | 70.5M | 73.5M | 62.0M |
| shards | 3 | 3 / 3 | 2 / 3 |
| evaluations | 135 | 132 / 132 | 110 / 132 |
| main cells | 0.82B | 0.81B / 0.81B | 0.54B / 0.81B |
| committed cells | 1.62B | 1.62B / 1.62B | 1.08B / 1.62B |
| fixed cells | 1.11B | 1.41B / 1.42B | 1.41B / 1.41B |

The unrolled compression is 2,521 rows, against the planner's 2,987. On the
fold-transcript chain, `Blake3::compress` is 9,317 compressions and 23.5M
rows at h25 (30% of rows). Fixed cells are 42 columns at `2^25`.

**M6** (GPU, Ignition SRS; fold-transcript chain, h25). Init stage 3
verifies the stage-2 packed BN proof (`target/fold-transcript/chain/init`).
Both PCSs verify natively and reject a changed output. Proof shape for both:

- 5 circuits: 3 × `2^25` narrow shards, a `2^19` table and a `2^19` ROM;
- 3 fixed slots;
- 132 evaluations: 32 main, 40 lookup, 8 quotient, 52 fixed.

| | per-column KZG | packed SHPLONK (packing capacity `2^26`) |
|---|---:|---:|
| witness | 14.7 s | 14.7 s |
| fixed matrix build | 88 s, before per-row caching | 7.7 s |
| fixed commit (once, GPU) | 11.0 s | 14.2 s |
| prove | 43.3 s | 75.8 s |
| end to end | 2 min 45 s | 2 min 00 s |
| peak RSS | 165 GB, including a since-removed 45 GB clone | 121 GB |
| proof | 63 G1 points, 6,410 B compact | 49 packed commitments, 5,677 B wire |

**M7, terminal.** Run with `aiur_packed_terminal_cost` and
`aiur_column_verifier_cost` (gnark count, exact capacities, key as data).

*Input.* The key grammars have one fixed matrix per circuit and cannot
express a shared slot. So the counted proofs give each shard its own copy of
the fixed matrix (216 evaluations). They come from
`examples/aiur_template_v2_fixture.rs`: the v2 system of the KZG source
fixture, with Init's circuits and packing ratio.

*Shared-slot figure.* This subtracts the 42 duplicated fixed packs and the
84 duplicated fixed openings, at marginal costs measured as S3 − S2: 151–176K
constraints per G1 pack and 26.6K per BLAKE3 compression.

| Verifier on the narrow stage | Constraints (exact capacities) |
|---|---:|
| per-column KZG, unshared, 196 columns | 66.2M; G1 accounts for 38.7M |
| packed, unshared, 3 shards (95 packs, 216 evaluations) | **37.0M** (49.2M padded) |
| packed, unshared, 2 shards (66 packs, 152 evaluations) | 28.5M |
| packed, shared slot, 3 shards (53 packs, 132 evaluations), derived | 27.3–29.4M |
| the same with a fixed key (no key digest: −2.9M), derived | 24.4–26.6M |

Per-column KZG is out of range, because it pays about 190K constraints per
committed column. The packed figures exclude the complete-terminal contract:
statement binding, transcript fold and the gnark `PairingCheck`.

### M8: shared fixed slots in the Aiur verifier, and the narrow terminal (2026-11-14)

Summary: `target/narrow-terminal/summary.json`.

**Key grammar.** The packed key's fixed section (`IXAUSK02`, unchanged
magic) now has three forms:

- tag 0: no fixed matrices;
- tag 1: one committed matrix per circuit with fixed columns (byte-identical
  to before);
- tag 2: the commitment, then one u32 per system circuit, its slot plus one
  (0 without fixed columns).

`kzg_packed_advice::key_bytes_with_copies` writes tag 2 only when
`System::preprocessed_indices` names a slot twice.

**Verifier** (`KzgPackedDeserialize::fixed`, `KzgPackedShape::consume`,
`KzgPackedVerifier::observe_key`). It mirrors the fork:

- **Transcript.** After the circuit shapes, the slot list (slot + 1, as
  field elements) is absorbed only for tag 2, before the activation flags.
  This is `System::observe_shape` with `shares_preprocessed()`.
- **Slots.** Slots are numbered in order of first use. A circuit either opens
  the next slot, consuming its packed shape and opened rows, or reuses an
  earlier slot's rows.
- **Readers.** A reader must have the slot's height (its own log height),
  width and next-row class. Mixed next-row classes within one slot are
  rejected; native accepts them, so this costs completeness only.
- **Key checks.** A tag-2 key must share at least one slot, and its slot list
  must cover every circuit.
- **Opening reduction.** Round 3 lists each slot once, at its owner
  (`Frame`'s new last field), at `{ζ}` or `{ζ, ζω}`. This matches the
  prover's one entry per slot.

**Tests** (`tests/aiur_kzg_packed_shared_fixed.rs`, fork build). The system
is two circuits reading one fixed column at the current and next row, a
circuit with its own fixed column of another height, and a selector.

- An honest proof gives the native pair.
- The fold weight squeezed from the Aiur final transcript equals the native
  one, so the transcripts agree byte for byte, slot list included.
- Rejected:
  - a changed shared value (execution fails);
  - a forged shared opening that keeps every AIR identity, with both
    readers' main values and the shared rows shifted together (executes; the
    pairing fails);
  - a duplicated slot opening;
  - four altered slot lists;
  - the tag-1 form of the same key.

The 11 existing packed-source tests pass on the re-exported
`kzg-packed-shplonk.ixa`.

**Narrow stage under a fixed configuration.** `aiur_template_v2_init`:

- `--write-config` / `--config` fix the capacities, ROM capacities, width,
  shard height and count (`target/narrow-terminal/stage3-*.config.json`).
  Witness generation admits each execution against them.
- `--save` writes the wire key, claims, proof and `narrow.json`, which holds
  the claim chunk headers.

The predecessor is the normalized-wrap Init chain,
`target/wrap-normalized/pair-wrap`: wrap → GL → BN1 → BN2, with
`chain-fold.ixa`.

| Stage 3 (GPU, Ignition) | 2 shards, +8% | 3 shards, +25% |
|---|---:|---:|
| evaluations / packed commitments | 110 / 41 | 132 / 49 |
| prove / end to end / peak RSS | 56.0 s / 1:39 / 113 GB | 75.0 s / 2:00 / 121 GB |
| key / proof wire bytes | 3,873 / 4,637 | 5,057 / 5,677 |
| terminal, exact / padded (gnark) | **23,365,331** / 29,362,030 | 26,084,556 / 29,945,874 |

**Shard count: 2.**

- 8.2% is the largest headroom that still fits two `2^25` shards. At +8%
  `rows_per_shard` is 33,442,591, 99.7% of `2^25`.
- Under the +8% configuration, the stage-3 executions after the raw-root
  chains (`pair-raw`, `fold-transcript/chain/init`) are admitted. Their
  tightest function is `BN254G1::add`, at 94.5% of capacity.
- An execution that exceeds a capacity is rejected before witness
  generation. It needs the 3-shard configuration, which has its own key and
  terminal (26.1M, also `2^25`).

**Terminal** (`MultiStark/CompressFinalNarrow.lean`, export
`compress_final_narrow_export`).

- **Key and configuration.** The narrow key is in `KzgPackedTerminal`'s
  tables, and its digest is fixed at export. The configuration row (policy
  digest, anchors, stage interval `[4,4]`) and the claim chunk headers
  `[tag, instance, count]` come from `aiur_packed_final_config --narrow`.
- **Policy.** The entry authenticates the chain policy and binds its anchors
  to the key's and to the configured anchors.
- **Claim.** The four claim chunks are checked against the headers. The
  flattened `chain_v1` call must carry the configured policy, stage 3 and
  the public statement.
- **Verification and fold.** The entry verifies the narrow proof under the
  embedded key, folds the carried accumulator with the transcript weight,
  and returns 18 words for the gnark `PairingCheck`.
- **Tests.** `tests/aiur_narrow_terminal.rs` (ignored, env-driven) rejects a
  changed statement, a changed policy, a changed chunk tag, instance, policy
  word, stage, statement word or accumulator word, swapped, dropped or
  re-split chunks, and a configuration for another stage. A forged `W2`
  executes, and its pair fails the pairing check.

**Final PLONK proof** (`examples/aiur_narrow_terminal_prove.rs`, 2-shard
stage):

- **Schema.** The terminal schema has exact capacities and removes unused
  map receivers. It compiles to **23,365,331** constraints, which is exactly
  the cost model's figure, in a `2^25` domain with Ignition's first
  `2^25 + 3` powers.
- **Backend.** Proving uses the gnark CPU backend because the CUDA PLONK
  backend is limited to `N ≤ 2^24`.
- **Timings:**
  - compile: 33 s;
  - setup: 88 s, after a one-time Lagrange basis of 975 s that is cached;
  - load: 47 s;
  - prove: 131 s.
- **Memory.** Peak RSS is 55 GB.
- **Proof.** 584 bytes natively and 864 bytes in Solidity encoding.
- **Verification.** The proof verifies against the verifying key's digest
  and the Ignition anchors. A changed statement is refused by both the
  prover and the verifier.
- **Not measured:** gas, because this host has no Foundry or `solc`.
