# Verified narrow tiling in Lean: plan and status

> **Historical (2026-11-15).** This document is the plan and proof log of the verified tiling pass; its theorem statements and trust-gap status (§5f, §5g, §8) are still current, while references to the v1 Rust path and `chain_v1`/BN3 stages are historical. The current pipeline is described in [aiur-compression-architecture.md](aiur-compression-architecture.md).

Status (2026-11-15): the core is implemented and proved in
`Aiur/Aiur/Tiling/`. That covers gate lowering, copy wiring with fixed labels
and multiplicities, unchunked messages, fixed-capacity regions and the fixed
matrix. Three further pieces are also proved:

- **The `Chip` bridge** (`Bridge.lean`, `Compose.lean`). `narrow_heap_sound`
  composes the tiled layout with
  `Physical.Prepared.depth_grouped_activated_heap_sound` (§4).
- **The trailing-zero fingerprint question** (`Trim.lean`, §3.6). It is
  resolved by a proof, not an assumption.
- **The keyed-chunk soundness lemma** (`Chunks.lean`), and its system-level
  instantiation (`Assemble.lean`, `KeyedLedger.lean`, `ComposeKeyed.lean`,
  §5a).
- **Fixed tables and ROM inside the system** (`Tables.lean`, §5b). The only
  external lookup of `narrow_heap_sound_tables` is the entry request.
- **Periodic shards, v2 layout** (`Periodic*.lean`, §5e).
  `Periodic.narrow_heap_sound_v2` is `narrow_heap_sound_tables` for sharded
  v2 traces: spans, lane messages, packed `ts` codes, packed copy keys,
  per-shard offsets and one fixed matrix per layout. It covers the unrolled
  `Blake3::compress` (`PeriodicUnroll.lean`, `PeriodicUnits.lean`) and
  chunked sends with a virtual multiplicity.
- **Compact tables** (`PeriodicCompact.lean`, §5g).
  `Periodic.narrow_heap_sound_compact` replaces the 27 stacked tables by one
  map table and one ROM table, one narrow row tuple per physical row. On
  BN3 (`stage3-s2-h0.08`) the exporter builds and accepts them in 36 s
  (`tiling_export2 … tables.bin`): 395,276 map rows, 434,353 ROM rows.
- **Boolean enables, checked** (`Enables.lean`, §8). `enables` is no longer
  a hypothesis of any theorem.
- **The production narrow stage** (`PeriodicStacked.lean`, `PeriodicFixed.lean`).
  `Periodic.narrow_heap_sound_stacked` is `narrow_heap_sound_v2` with the map
  tables and the ROM as stacked tables beside the shards. ROM words are
  witness values at fixed addresses, so the key does not depend on the
  execution. The fixed matrix has a closed form proved equal to
  `Sharded.fixedAt` (`Sharded.emit_eq`), and `tiling_export2` exports the
  chain layout, fixed matrix included, in 65 s (§5e).

- **Lowering from the artifact** (`Ixa.lean`, §8). `tiling_export2` input
  format 2 reads the compiled `.ixa` and builds `Bridge.lower` circuits, map
  claims and request itself; `IChip.lower_ofChip` ties them to `Bridge.lower`.
- **Wide stages** (`WideStage.lean`): `WideStage.wide_heap_sound`, exporter
  `wide_export`; **Goldilocks corollaries** (`Goldilocks.lean`). Entry point
  table: §8 "Entry point".

There is no `sorry` anywhere. `Periodic.narrow_heap_sound_compact`, `narrow_heap_sound`,
`narrow_heap_sound_keyed`, `narrow_heap_sound_tables`,
`Periodic.narrow_heap_sound_v2`, `Periodic.narrow_heap_sound_stacked` and
`Periodic.Sharded.emit_eq` depend only on
`propext`, `Classical.choice` and `Quot.sound`. On every unchunked fixture of a
differential test, the Lean pass produces the same template as the Rust
v2 lowering (`template/v2.rs`; the v1 comparison with the deleted
`template/lower.rs` is retired, §8 round 6).

**Keyed chunks and in-system tables: done.**
`System.keyed_sound` is `System.sound` for layouts accepted by
`System.checkKeyed`, chunked templates included, and
`narrow_heap_sound_keyed` composes it with the end-to-end theorem (§5a),
with the external ledger given as explicit `Part`s. `narrow_heap_sound_tables`
(§5b) tiles the map tables and the ROM as circuits of the system
(`Bridge.tableCircuit`), so the external ledger is the entry request alone and
`tableSupport`, `extShape` and `extWide` are lemmas. On the 167-chip BN
snapshot plus 27 table rows, all 82 chunked channels have in-system
receivers: `external 0` (§5d).

**`Shaped` is checked, not assumed.** `Shaped.check` is executable, and
`Shaped.of_check` proves it sound. `narrow_heap_sound` takes
`Shaped.check … = true`.

**Production source (2026-11-15).** The Rust v2 backend builds its map
and ROM tables in `Periodic.Stacked`'s shape. The production narrow BN3
stage (`aiur_template_v2_init --config`) takes its layout from
`tiling_export2` by default; the fixed matrix is streamed through a pipe.
Init stage 3 proves and verifies under the exported layout (§5e,
"Production run"). §5f lists what the theorem covers in that pipeline.

Not done yet:

- **The terminal does not fit `2^25`.** With 27 stacked table circuits, the
  narrow proof opens 561 values, up from 110. The terminal compiles to
  42,739,164 constraints (domain `2^26`). That domain needs `2^26 + 3`
  powers, but the retained Ignition SRS has `2^26`, so the PLONK step, its
  gas and the end-to-end run were not redone on this key (§5e);
- `enables` is still assumed;
- the v1 theorem still has constant ROM rows (`narrow_heap_sound_tables`);
  only the v2 theorem has the witness-valued ROM.

Background: `aiur-template-backend.md` (prototype, soundness obligations)
and `aiur-structural-gap.md` §5, §6.2, §6.3, §6.7, §7.1–§7.2.

## 1. Requirements and the resulting shape

The requirements were:

- no new IR, no hand-written circuits, no source specialization;
- the column-minimizing layout is a maintained, formally verified compiler
  pass;
- the pass's output uses the constraint datatype that the proofs and
  backends use;
- a refinement theorem that composes with the existing end-to-end theorem.

The pass is a **checked transformation**:

```text
wide circuit (Graph → Circuit) ──lower (unverified)──▶ Template ──Template.check (verified)──▶
  System (templates, capacities) ──generated──▶ narrowCircuit W  +  fixed matrix
```

- `lower` ports the prototype's algorithm. It is untrusted. Optimizations
  (S1a fusion, S1b, S2 lane slots and so on in `aiur-structural-gap.md`
  §7.2) change only `lower`. They need no new proofs as long as the
  checker's certificate format covers them.
- `Template.check` is the only part the theorems trust. It is a small set of
  decidable conditions. Polynomial identities are decided by the sound
  normal form in `Poly.lean`.
- The narrow constraint system is `narrowCircuit W`, a single `Circuit` that
  depends only on `W`, plus the generated fixed matrix
  (`System.fixedAt`/`fixedMatrix`). Every program-specific value is a fixed
  column: lane coefficients, `join`, `sel/tag/sub`, copy labels and copy
  multiplicities.

A `Template` is a layout certificate: rows of four-cell lanes over numbered
slots, each relation labelled with its role. It is not an IR. Nothing
executes or compiles from it except the fixed-column generator.

## 2. Datatype: the minimal extension

The logical interface `Circuit.Chip` has no preprocessed columns, and its
lookups are not multiplicity expressions. A send fires on `enable = 1` with
weight one; a receive's weight is a property of the whole row. Copy
constraints with fixed labels and fixed signed multiplicities can't be
stated in it.

The STARK backends consume the level below `Chip`: one row of main columns,
preprocessed columns, current-row constraints, and `push(mult, args)`
lookups. Today that level exists only in Rust: `kzg::Compiler::inputs`
produces it, and `Optimized/EndToEnd.lean` lists it under "trusted Rust
lowering".

`Tiling/Basic.lean` adds that level as the smallest structure on top of the
existing types:

```lean
structure Lookup (F) where multiplicity : ArithExpr F; args : List (ArithExpr F)
structure Circuit (F) where
  width : Nat; fixedWidth : Nat := 0
  constraints : List (Constraint F)   -- Scalar.Circuit.Constraint, Satisfies
  lookups : List (Lookup F)
abbrev Ledger (F) := List F →₀ F       -- LogUp balance = ledger sum is 0
```

- **Reused:** `ArithExpr`, `Constraint` and `Satisfies` are the existing
  `Scalar.Circuit` definitions.
- **Same type on both sides:** a wide circuit is a `Circuit` with
  `fixedWidth = 0`, and the narrow circuit is a `Circuit` with fixed
  columns.
- **Lowering input:** `Graph` is the hash-consed input format of `lower`.
  `Graph.circuit` unfolds it to the `Circuit` that the theorems are about.

## 3. Pass structure

### 3.1 Gate lowering (`Shape.lean`, `Lower.lean`, `Sound.lean`)

**Slots.** A slot is either `column c` or `sum terms k`. A sum's terms are
`c·s` or `c·s·t` over earlier slots.

**Rows.**

- Gate rows hold `W/4` lanes, `qm·x0·x1 + q0·x0 + q1·x1 + q2·x2 + q3·x3 + qc`.
- An unjoined row asserts each lane is zero. A joined row asserts the sum
  of its lanes is zero.
- Each relation carries a `Role`: `defines s`, `root j` (wide constraint
  `j`), or `pad`.

**`Template.check` validates:**

- **Slots.**
  - Column slots are unique per column, which is what `Template.wide` reads.
  - Every sum term references an earlier slot.
  - Every sum slot has a `defines` relation.
  - Every cell references an existing slot.
- **`defines s` relations.** The relation, with every sum slot *above* `s`
  replaced by its definition (`expandAbove`), is identical to
  `Σ terms + k − s`. Carry chains need this: a long relation is split
  across rows linked by carry slots created after `s`. The fixtures caught
  the first, stricter version of this rule.
- **`root j` relations.** The relation, with every slot replaced by its
  meaning over wide columns, is identical to `ofExpr` of constraint `j`. A
  constraint whose polynomial normalizes to zero needs no relation.
- **Shape.** Lanes are well formed (an empty cell has coefficient 0), and
  rows have `W` cells.

**Theorem (`Template.Checked.constraints_hold`).** If `T.Checked C` holds
and every relation of `T` holds under a slot valuation `val`, then
`C.Holds (T.wide val)`.

The proof runs two inductions:

1. A descending induction shows that every sum slot equals its definition.
2. An ascending induction shows `meaning s` denotes `val s`.

The message part is `Template.Checked.messages_sound`. The message rows are,
in order, the wide lookups: each multiplicity is `sel·val(mult)`, and each
tuple is `tag :: sub :: payload.map val`.

### 3.2 Wiring: fixed labels and multiplicities (`Layout.lean`, `Copy.lean`, `Reconstruct.lean`)

**Numbering.** Labels and physical rows use the prototype's numbering:

- `label = 1 + index of (f, i, s)` in `keys`;
- the physical row of `(f, i, r)` is its index in `places`.

Labels are fixed and globally unique per (circuit, instance, slot).

**Multiplicities.** The anchor is the first occurrence in row-major order.
It gets `o − 1`, every other cell gets `−1`, and empty or padding cells get
0.

**Copy lemma.** `copy_class` is pure algebra. A class of `o` cells balanced
at the anchor's value forces `|agreeing| = o`. It needs `SmallCast F bound`,
meaning naturals below `bound` are nonzero in `F`. That holds for BN254 and
Goldilocks at any realistic size; for `ZMod p` it is a one-line lemma.

**`System.Valid.copy`** connects that lemma to the trace:

- It extracts the copy-bus coefficient at `[COPY, L, v]` from the narrow
  ledger.
- It identifies the cells with label `L` with the occurrences of one slot,
  using label injectivity and the `Nodup` of `places`/`keys`.
- It proves that the class size equals the generated occurrence count.

### 3.3 Messages without chunking

**Narrow tuple.** A message row emits `[tag, sub, x1, …, x(W−1)]`. The cells
after the payload are free, as in the prototype.

**Arity.** The theorem cuts tuples to arity: `System.proj` takes
`2 + arity(tag, sub)`, and `System.check` requires every `(tag, sub)` to
have one arity. The doc's "balance of extended tuples implies balance of
their projections" argument becomes `Finsupp.mapDomain` of a zero ledger.

**Separation.** Copy tuples have length 3 and message tuples have length
`W + 1 ≥ 5`. Tag separation is therefore not needed inside the narrow
system. The external ledger must have no `[COPY, L, v]` tuples.

### 3.4 Regions and capacities

- **Places.** `places` enumerates (circuit, instance, template row), with
  `cap f` instances per circuit. Rows past the last place have zero fixed
  columns and contribute nothing.
- **Admission.** The trace height `N ≥ |places|` is a parameter. Admission
  and choosing capacities stay outside the theorem, as in the prototype.

### 3.5 The refinement theorem (`Refinement.lean`)

```lean
theorem System.sound (ok : sys.check = true) (small : SmallCast F sys.bound)
    (tall : sys.places.length ≤ N)
    (rows : ∀ p < N, Satisfies (narrowCircuit sys.width).constraints (sys.assign main p))
    (extCopy : ∀ L v, ext [(COPY : F), L, v] = 0)
    (balanced : sys.narrowLedger N main + ext = 0) :
    (∀ f (hf : f < sys.circuits.length), ∀ i < sys.cap f,
        sys.circuits[f].Holds (sys.wideRow main f i)) ∧
      sys.wideLedger (sys.wideRow main) + Finsupp.mapDomain sys.proj ext = 0
```

`sys.assign main p` is main row `p` with the **generated** fixed columns.

The stronger form, `System.Trace.message_ledger`, states that the narrow
message ledger cut to arities *equals* the wide ledger of the reconstructed
rows. So the wide traces have exactly the narrow system's message multiset,
which is the "same lookup multiset" requirement.

Lemma decomposition, with sizes:

| Lemma | File | Lines |
|---|---|---:|
| sound polynomial normal form | `Poly.lean` | 227 |
| chunk groups: `ChunkSound`, `grouped`, `rowShaped` | `Groups.lean` | 220 |
| checker soundness (slots, constraints, messages) | `Sound.lean` | 375 |
| `copy_class`, `SmallCast` | `Copy.lean` | 56 |
| enumeration `Nodup` and indexing | `Enumerate.lean` | 73 |
| narrow constraint semantics per placed row | `Narrow.lean` | 176 |
| copy consistency (`Valid.copy`) | `Reconstruct.lean` | 334 |
| relations hold, message ledger, `System.sound` | `Refinement.lean` | 468 |
| parts, `Part.balance` | `Assemble.lean` | 323 |
| system parts, `System.keyed_sound` | `KeyedLedger.lean` | 541 |
| table circuits, request checker, `narrow_heap_sound_tables` | `Tables.lean` | 391 |
| v2 shard circuit, spans, packed copy keys | `Periodic.lean` | 224 |
| v2 templates, logical and shadow templates, checker, fixed rows | `PeriodicTemplate.lean` | 342 |
| fixed-row indexing, spans, key rows | `PeriodicRows.lean` | 341 |
| per-shard copy consistency | `PeriodicCopy.lean` | 169 |
| v2 ledger split, shapes, trimmed balance, copy balance per shard | `PeriodicLedger.lean` | 379 |
| logical system indexing, `locate`, `valV`, `mainV` | `PeriodicSystem.lean` | 203 |
| relations of the logical system (`Sharded.logical`) | `PeriodicLogical.lean` | 236 |
| v2 message entries: `unpack`, `lane_entry`, `row_entry`, `row_total` | `PeriodicMessages.lean` | 490 |
| message ledger total, `Sharded.sound` | `PeriodicSound.lean` | 252 |
| v2 request encoding, `narrow_heap_sound_v2` | `PeriodicCompose.lean` | 245 |
| merged lookups (`rowLedger_mergeBy`), unrolled circuits | `PeriodicMerge.lean` | 225 |
| v2 lowering, system assembly, JSON (unverified) | `Lower2.lean`, `Tile2.lean`, `Export2.lean` | 630 |

### 3.6 Trailing zeros in the fingerprint (`Trim.lean`)

multi-stark fingerprints a tuple as `Σ args[i]·γ^i` (`lookup.rs`). Two
tuples therefore meet on the bus exactly when they agree after dropping
trailing zeros, so the real LogUp balance is the ledger keyed by
`trimZeros`.

Every tuple on the narrow bus has one of two shapes:

- a message: `W + 1` entries, first entry a message tag;
- a copy tuple: 3 entries, first entry `COPY`.

`System.check` requires every message tag to differ from `COPY`, and the
external ledger must use the message shape. `trimZeros` is injective on
these two shapes, so trimmed balance implies exact balance
(`System.exact_of_trimmed`). The composed theorems take the multi-stark
balance, `mapDomain trimZeros (narrow + ext) = 0`, as their hypothesis.

## 4. Composition with the existing theorems (`Bridge.lean`, `Compose.lean`)

### The lowering

`Bridge.lower idOf c` is the Lean version of the lowering of an activated
chip `Activation.compile c` that is trusted today:

- the receive `push(−mult, [CALL, id f, inputs, output])`;
- the constraint `(1 − sel)·mult = 0`;
- each send `push(enable, [CALL, id g, args, result])`;
- each memory lookup `push(enable, [ROM, width, address, value])`.

`tileCircuits` tiles these circuits directly. Its lowering hint is
`Graph.ofCircuit` (unverified). The system's circuits *are* the lowered
chips, so no Rust lowering stands in between. On the fixtures, every graph
tiled through `Graph.circuit` and then re-hash-consed is accepted.

### `Bridge.Wide.checkMemo`

Rows of the lowered single chips whose ledger balances against the entry
request plus fixed tables and ROM give `WeightedRow`s that
`Grouping.Plan.checkMemo` accepts.

- **Providers.** Field balance at the encoding of a required claim
  produces an active providing row: the 0/1 requirement counts are below
  `p` (`Wide.provider`).
- **Weights.** The integer weights come from `Balance.weigh`.
- **Memory.** Enabled memory lookups land in the ROM by the same argument
  (`Wide.memory_valid`).

### `System.checkMemo_of_narrow` and `narrow_heap_sound`

```lean
theorem narrow_heap_sound
    (compiled : GenericArtifact specialized) (prepared : Physical.Prepared compiled.artifact)
    (certified : Depth.Certified cfg prepared.system)
    (plan : Grouping.Plan (Depth.system cfg prepared.system) id) (activated : plan.WellFormedActivation)
    (entry : name ∈ entries) (valid : rom.Valid) (signed …) (rooted …) (outside …)
    (arguments …) (decoded …)
    -- the tiled layout
    (ok : sys.check = true) (circuits : sys.circuits = plan.singles.map (Bridge.lower idOf))
    (capacity : capacityRows plan.singles sys ≤ 2 ^ 39)
    (small : SmallCast F bound) (sysBound : sys.bound ≤ bound) (tags : 3 < bound)
    (lookups : capacityLookups plan.singles sys < bound) (characteristic …)
    (shaped : Shaped (Depth.system cfg prepared.system) plan.singles idOf root bound)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM rom) root = .ok ())
    (tableSupport : ∀ t, tables t ≠ 0 → (∃ mc ∈ mapClaims, t = encode idOf mc) ∨
        ∃ e ∈ (Erasure.rawROM rom).entries, t = encodeRom e)
    (extShape : ∀ t, ext t ≠ 0 → t.length = sys.width + 1 ∧ t.head? ≠ some COPY)
    (extWide : Finsupp.mapDomain sys.proj ext = Finsupp.single (encode idOf root) 1 + tables)
    -- the narrow trace
    (tall : sys.places.length ≤ N)
    (rows : ∀ p < N, Satisfies (narrowCircuit sys.width).constraints (sys.assign main p))
    (balanced : Finsupp.mapDomain trimZeros (sys.narrowLedger N main + ext) = 0)
    (enables : ∀ f hf, ∀ i < sys.cap f, Bridge.Boolean plan.singles[f] (sys.wideRow main f i)) :
    ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
      Represents (…) heap value result
```

### `narrow_heap_sound_tables` (`Tables.lean`)

This is the same statement with the fixed tables and the ROM tiled in the
system (§5b). It has these hypotheses in place of `ok`, `circuits`,
`tableSupport`, `extShape`, `extWide` and `ext`:

```lean
    (ok : sys.checkKeyed = true)
    (circuits : sys.circuits = plan.singles.map (lower idOf) ++ fixed.map tableCircuit)
    (fixedIn : ∀ t ∈ fixed, t ∈ fixedRows (Depth.system cfg prepared.system) (Erasure.rawROM rom) idOf)
    (ids : sys.instances ≤ bound) (parts : (sys.enumerate sys.lookupCount).length + 1 < bound)
    (req : (Part.request sys.width (encode idOf root)).checkRequest sys (encode idOf root) = true)
    (balanced : Finsupp.mapDomain trimZeros
      (sys.narrowLedger N main + (Part.request sys.width (encode idOf root)).padded sys.width) = 0)
```

### `Periodic.narrow_heap_sound_v2` (`PeriodicCompose.lean`)

The same statement for a sharded v2 layout `S` (§5e). In place of the layout
and trace hypotheses of `narrow_heap_sound_tables`:

```lean
    (ok : S.check = true) (chipsIn : ∀ c ∈ chips, c ∈ plan.singles)
    (circuits : S.system.circuits = List.zipWith Circuit.mergeBy wide groups)
    (wideEq : wide = chips.map (lower idOf) ++ fixed.map tableCircuit)
    (lenG : groups.length = wide.length)
    (merged : ∀ j (hw : j < wide.length) (hg : j < groups.length), wide[j].checkMerge groups[j] = true)
    (codesBound : ∀ e ∈ S.buses, e.2.1 < bound) (labels : copyKey S.labelTotal < bound)
    (shadowBound : ∀ k < S.shards.length, ((S.layout k).shadow S.width).bound ≤ bound)
    (req2 : S.checkRequest2 (Part.request S.width (encode idOf root)) = true)
    (tall : ∀ k < S.shards.length, ((S.layout k).shadow S.width).places.length ≤ H k)
    (rows : ∀ k < S.shards.length, ∀ p < H k, Satisfies (S.circuit k).constraints (S.assign k (main k) p))
    (balanced : Finsupp.mapDomain trimZeros (S.ledger H main + S.padded2 (Part.request …)) = 0)
```

`fixedIn`, `ids`, `parts`, `shaped`, `context` and `req` are as in
`_tables`, over `S.system`. `sysBound` is replaced by `shadowBound`. The
circuits are *units* `(chip, unrolling?)`: `wideEq : wide = units.map
(unitCircuit idOf) ++ fixed.map tableCircuit` with `unrolled : ∀ u ∈ units,
unitOk idOf u = true` (`Unroll.check` of the unrolling). An unrolled instance
stands for one chip row per body, so `capacity` and `lookups` are
`capacityRowsU`, `capacityLookupsU` (instances times bodies) and `enables` is
stated for every body row (`unitRows`). `units` may repeat plan chips (the
chips layout on every shard).

### `Periodic.narrow_heap_sound_stacked` (`PeriodicStacked.lean`)

The production statement. The layout is `narrow_heap_sound_v2`'s without
table rows (`wideEq : wide = units.map (unitCircuit idOf)`), plus stacked
tables `tables : List (Stacked F)`, each its own circuit beside the shards:

```lean
    (tablesOk : ∀ T ∈ tables, T.check S = true)
    (kinds : ∀ T ∈ tables, T.checkMap = true ∨ T.checkRom = true)
    (channels : (tables.map fun T => (T.tag, T.sub)).Nodup)
    (mapsIn : ∀ T ∈ tables, T.checkMap = true → ∀ r < T.rows,
      T.tag :: T.sub :: T.data.getD r [] ∈ (Depth.system cfg prepared.system).mapClaims.map (encode idOf))
    (keysSmall : ∀ T ∈ tables, T.keyBase + T.rows ≤ bound)
    (parts : (S.system.enumerate S.system.lookupCount).length + 1 + (tables.map (·.rows)).sum < bound)
    (context : (Depth.system cfg prepared.system).checkContext (Erasure.rawROM ⟨[]⟩) root = .ok ())
    (tallT : ∀ t T, tables[t]? = some T → T.rows ≤ HT t)
    (balanced : Finsupp.mapDomain trimZeros (S.ledger H main + tableLedger S tables HT mainT +
      S.padded2 (Part.request S.width (encode idOf root))) = 0) :
    ∃ rom : WidthROM F, rom.entries = romEntries tables mainT ∧ rom.Valid ∧
      ∃ value heap, EvalFn source.world name args [] value heap ∧ Represents (… rom …) heap value result
```

`rom`, `valid` and `fixedIn`'s ROM half are gone: the ROM is the one the ROM
tables' trace holds, which matches how Aiur binds it. Aiur's ROM is prover
data (the Rust ROM circuit has no preprocessed columns; the claim carries no
ROM digest), and the end-to-end theorem takes any `rom` with `rom.Valid` and
reads the result relative to it. Here the addresses are fixed
(`keyBase + r`, `0..capacity` per width), so `Valid` is a lemma: equal
lengths give the same width, hence the same table, and equal addresses the
same row. `context` is checked on the empty ROM; its ROM part is `Valid`.

### Hypotheses beyond the existing theorem's

| Hypothesis | Status |
|---|---|
| `shaped : Shaped.check … = true` | Checked. Decided by `Shaped.check`, sound by `Shaped.of_check` |
| `enablesOk` (was `enables`) | Checked. `∀ c ∈ plan.singles, Bridge.checkEnables bound c = true`; `boolean_of_lower` derives `Boolean` from the lowered chip's constraints (§8). All 167 BN chips pass |
| `tableSupport` | `narrow_heap_sound`, `_keyed`: assumed. `_tables`: a lemma (`System.wideLedger_tables`); replaced by the static `fixedIn`: every table row is in `Bridge.fixedRows` (encoded map claims and ROM entries) |
| `extShape` | `narrow_heap_sound`, `_keyed`: assumed. `_tables`: a lemma (`Part.Request.padded_shape`); `ext` is defined as `request.padded sys.width` |
| `extWide` | `narrow_heap_sound`, `_keyed`: assumed. `_tables`: a lemma (`Part.Request.padded_proj`, `wideLedger_tables`) |
| `narrow_heap_sound_keyed` only: `X`, `extParts`, `extFormed`, `extRecv`, `extUnique` | Assumed. `ext` cut to arities is the narrow encoding of parts `X`, each formed and `RowsIn` the system's role and arity tables. Chunked external receivers use channels with no in-system receiver (`sys.receivers`), with distinct keys per channel. `_tables`: `X = [request]`, a send, so `extRecv` and `extUnique` are vacuous |
| `narrow_heap_sound_tables` only: `req` | Checked. `Part.request W t` builds the entry request part (one row, or `W − 2`-entry chunks under key 0, as `lower` splits a send). `Part.checkRequest` decides `Part.Request` and `Request.of_check` proves it sound: tuple, weight 1, send, `Formed`, chunks fit a row, row keys have the system's roles and arities. All 167 entry-request shapes of the BN proxy pass, 72 of them chunked |
| `narrow_heap_sound_tables` only: `ok`, `circuits`, `fixedIn` | Checked or static. `ok` is `checkKeyed`; `circuits` and `fixedIn` are equalities and memberships of computable lists |
| `narrow_heap_sound_keyed`, `_tables`: `ids`, `parts` | Size bounds: instances `≤ bound` (invocation ids are distinct field elements) and lookup slots plus `|X|` below `bound` |
| `context` | Static. `checkContext` of the root and ROM, decided by the existing checker |
| `capacity`, `lookups`, `bound`, `characteristic`, `small` | Size and characteristic bounds |
| `narrow_heap_sound_v2` only: `merged` | Checked. `Circuit.checkMerge` (groups disjoint, identical argument polynomials, every lookup outside the groups has zero multiplicity); `rowLedger_mergeBy` shows the merged circuit has the same row ledger |
| `narrow_heap_sound_v2` only: `ok`, `chipsIn`, `circuits`, `req2` | Checked or static. `ok` is `Sharded.check` (`checkKeyed` of the logical system, `checkPhysical` of every template, bus table distinct with codes `1`/`2` mod 4); `chipsIn` and `circuits` are list facts; `req2` decides the request's bus entries |
| `narrow_heap_sound_v2` only: `codesBound`, `labels`, `shadowBound` | Size bounds: bus codes, packed copy keys of all labels, and each layout's v1 copy bound below `bound` |
| `narrow_heap_sound_v2` only: `unrolled` | Checked. `Unroll.check`: body 0 drops only the self-call, later bodies drop it and the receive; each body's receive has the previous self-call's arguments (`argsIdentical`) and multiplicities summing to the zero polynomial; the last self-call's multiplicity is zero. `Unroll.rowLedger_circuit` (dropped lookups cancel along the chain) and `Unroll.holds` |
| `narrow_heap_sound_stacked` only: `tablesOk`, `kinds`, `channels`, `mapsIn` | Checked or static. `Stacked.check` (buses fit, the part is `Formed` and `RowsIn` the system's roles and arities, chunked channels have no in-system receiver), `checkMap` (slices read the data in order), `checkRom` (payload is address then words, `sub` is the word count), distinct channels. `mapsIn` is the map half of `fixedIn` |
| `narrow_heap_sound_stacked` only: `keysSmall` | Size bound: keys `keyBase + r` distinct as field elements |
| `narrow_heap_sound_v2`: shared preprocessed openings | Not a hypothesis. The theorem is per shard circuit with its layout's fixed values (`Sharded.fixedAt L` depends only on `L`); one opening for several readers is STARK trust (`aiur-template-backend.md`, "Soundness of sharing") |

**What `narrow_heap_sound_tables` still assumes.** Every layout and root
hypothesis is checked by code or is a static list fact: `ok`, `circuits`,
`fixedIn`, `shaped`, `context` and `req`. The rest are these:

- **`enables`, assumed.** Activated enables are 0 or 1 on the
  reconstructed rows. This is the trusted item of `Optimized/EndToEnd.lean`.
- **`small` and `characteristic`, field facts.** They are one-line lemmas
  for BN254 and Goldilocks at these sizes, not decided by code.
- **Size bounds, arithmetic on the layout.** These are `capacity`,
  `lookups`, `ids`, `parts`, `sysBound` and `tags`. Each is decidable once
  `bound` is fixed.
- **Trace hypotheses, the STARK's output.** `tall`, `rows` and `balanced`,
  with shared fixed columns and LogUp in the STARK trust base.

**`shaped` in detail.** `Shaped.check` decides these static facts about the
plan:
- every send to a chip uses that chip's signature;
- every send to a map, and the root, uses that map's claim shape;
- memory values are packed;
- channel ids are injective and below `bound`.

**Discharging `enables`.** This needs a certificate that activated enables
are boolean polynomials of boolean selectors.

## 5. Remaining work, in order

### a. Keyed chunks

**Done** (`Shape.lean`, `Sound.lean`, `Groups.lean`, `Chunks.lean`; standard
axioms only):

- **Invocation id.** `Lane.poly idv` carries `qid·X_idv`, with
  `idv = T.idVar = slots.length`. The layout generates `qc + qid·ID(f, i)`
  (`Lane.coef`, `Row.fixed … id`). `ID = System.instId f i` is the
  instance's global index, `Σ_{f'<f} cap f' + i`, as in the prototype's
  `id_base`. `slotValue` returns `ID` at `idVar`, and `Lane.value_poly` and
  `Placed.lane` include the term. `Lane.wellFormed` no longer requires
  `qid = 0`.
- **Slot kinds.**
  - `wideSlot` marks column and sum slots.
  - Root relations, sum terms, message multiplicities and payloads must use
    wide slots (`widePoly`, `wideTerm`). `meaning_val` holds for wide slots.
  - An `invocation` slot needs a `pin` relation, which must be `Identical`
    to `X_s − X_idv`. `Checked.invocation` proves `val s = val idVar`.
  - `key` slots are unconstrained.
- **Checker.** `Template.check` accepts `checkUnchunked ∨ checkGroups`.
  - `splitGroups` cuts the message rows into one group per lookup. A group
    has `groupSize W n rom` rows, which is the lowering's formula.
  - `checkChunked` checks:
    - a shared `sel`, `tag` and multiplicity cell;
    - one key cell;
    - `sub_c = chunkSub rom sub c`;
    - `cells = keyedCells W mult key chunk_c`;
    - that the chunks concatenate to the payload (after the address for a
      ROM read);
    - that a call receive is keyed by the invocation slot, and a ROM
      receive by its constant address (§5b);
    - for a send, a `boolean mult` relation `Identical` to `boolPoly sel mult`.
- **Template lemmas.**
  - `Checked.chunk_sound` gives `ChunkSound`: the group is
    `chunks.zipIdx.map (sel, tag, chunkSub rom sub c, keyedCells …)`, and
    the tuple is `tag :: sub :: ([val key] if rom) ++ flatten chunks`.
    Call receive keys equal `val idVar`; a ROM receive's address is a
    constant. Send weights `sel·val mult` are 0 or 1.
  - `Checked.grouped` gives the `flatten` decomposition and `GroupSound`
    per lookup.
  - `Checked.rowShaped` shows that every message row, chunked or not, is
    `messageCells W mult ps`, using `keyedCells_eq`.
- **System, linear part.** `Trace.row_message` and `Trace.message_rows` no
  longer assume an unchunked template. They show that the projected message
  ledger equals `Σ_{f,i} Σ_{m ∈ T_f.messages} msgEntry (slotValue f i) m`,
  where a chunk row contributes `[tag, sub_c, key, chunk_c]`.
  `Trace.message_ledger` is that plus `checkUnchunked`.
- **Abstract chunk lemmas** (`Chunks.lean`).
  - Chunk values now have any type `V`; the system uses `List F`.
  - `chunks_total` sums `chunks_sound` over keys.
  - `chunks_total_of_ledger` takes `Σ_S chunkLedger − Σ_R chunkLedger + rest = 0`
    and gives whole-payload balance, provided `rest` is zero at chunk tuples,
    the tuple encoding `u j k v` is injective, keys are unique on `R` and
    `S` weights are boolean.

**Keyed system check, done** (`Keyed.lean`).

- **`System.checkKeyed`.** It is `System.check` with the `checkUnchunked`
  gate replaced by two conditions:
  - every template passes `Template.checkGroups`;
  - the row-key role table `System.roles` is functional. A role is
    `(tag, sub_row) ↦ (sub, none)` for an unchunked row and
    `(sub, some (c, J, rom))` for chunk `c`.
- **`tileKeyed`.** It lowers and validates with `checkKeyed`.
- **`System.valid_of_checkKeyed`.** `System.Valid` no longer contains the
  unchunked fact, which moved to `System.Unchunked` /
  `unchunked_of_check`.
- **`System.keyed_holds`.** For chunked layouts, every reconstructed wide
  row satisfies its circuit. Only the lookup half of `System.sound` is
  still missing.
- **On the 167-chip BN proxy (§5d).** `tileKeyed` accepts the whole system
  (8,210 places, 3,857 roles) in 13.7 s, interpreted.

**Ledger half for `checkKeyed` systems, done** (about 960 lines).

- **`Part`** (`Assemble.lean`). One wide lookup on the narrow bus: tag, sub,
  payload, weight, receive flag, key, chunks (empty if unchunked). `narrow`
  is its row tuples (`chunkTuple c = [tag, chunkSub rom sub c, key, chunk_c]`),
  `wide` its whole tuple. `Formed W`: an unchunked payload fits a row
  (`≤ W − 1`); a chunked one does not (`≥ W`), its chunks concatenate to the
  payload after a ROM read's address key, and a chunked send has weight 0
  or 1. `RowsIn role arity`: every chunk row key has role
  `(sub, some (c, J, rom))` and arity `|chunk_c| + 1`; an unchunked key has no
  chunk role.
- **`Part.balance`.** Over any finite family, balanced narrow encodings give
  balanced wide tuples, if chunked receivers of a channel have distinct keys
  and the family is smaller than the `SmallCast` bound. Steps 1 and 3 of the
  old plan are inside it: functional roles separate channels and chunk
  indices and keep unchunked rows off chunk tuples (`same_role`,
  `unchunked_off`); functional arities make chunk lengths equal per channel,
  so whole-payload equality is chunk-wise equality (`flatten_eq_iff`). Short
  tuples balance as before; long ones by `chunks_total` (calls, maps) or
  `chunks_sound` at the address key (ROM).
- **System parts** (`KeyedLedger.lean`). `System.partAt main (f, i, l)` is
  lookup `l`'s group read at the instance's slot values (`groupPart`).
  `GroupSound.part` proves narrow, wide, `Formed`, `RowsIn` and the receive
  key from `GroupSound`; `W ≤ |payload|` for a chunk group comes from the
  group sizes of `splitGroups`. `ChunkSound` now also records
  `rom = (tag == 2)`. `Trace.sums` regroups `message_rows` and `wideLedger`
  over `(sys.enumerate sys.lookupCount).toFinset`. Receive keys are
  `instId`, distinct by `instId_inj` and `SmallCast` of `sys.instances`.
- **`System.keyed_sound`.** Constraints as in `keyed_holds`, and
  `wideLedger + Σ X.wide = 0` from the disjoint sum of system and external
  parts.
- **`System.checkMemo_of_keyed`, `narrow_heap_sound_keyed`**
  (`ComposeKeyed.lean`). The old theorems with `checkKeyed` and the `X`
  hypotheses of §4 in place of `extWide`. `extShape` stays: multi-stark
  trims trailing zeros of the unprojected tuples.

`checkKeyed` itself still accepts a chunked channel whose receivers are not
in the system. Soundness is not affected: `narrow_heap_sound_keyed` must then
be given those receivers as external parts satisfying `extRecv` and
`extUnique`. With `narrow_heap_sound_tables` there are no such parts.

### b. Stacked table and narrow ROM

**Done** (`Shape.lean`, `Groups.lean`, `Keyed.lean`, `KeyedLedger.lean`,
`Tables.lean`, about 450 lines; standard axioms only).

1. **Table rows as system circuits.** `Bridge.tableCircuit t` has width 1,
   no constraints and one lookup `⟨−X_0, t⟩` with constant `t`. It is tiled
   like any other circuit. A map-claim row is a call receive, keyed by its
   invocation id when chunked; a ROM row is a ROM receive.
   `Bridge.fixedRows source rom idOf` lists the candidate tuples (encoded
   map claims, then encoded ROM entries).
2. **ROM receivers keyed by address.**
   - `lower` no longer rejects a non-call receive. A ROM receive is keyed by
     its address slot, like a ROM read.
   - `Template.checkChunked` accepts `receive ∧ rom` when the address
     argument is a constant `.const k` and the key slot means it. There is
     no boolean relation, as for any receive.
   - `ChunkSound` splits the receive clause: a call receive's key is
     `val idVar`; a ROM receive's `lookup.args[2]?` is a constant. Through
     the tuple, the part's key is that constant (`GroupSound.part`).
   - `System.romReceivers` lists `(f, (tag, sub), address)` for every
     chunked ROM receive at lookup 0. `checkKeyed` adds two conditions:
     the `(channel, address)` pairs are `Nodup`, and each such circuit has
     `cap ≤ 1`.
   - `PartFacts` and the key-uniqueness case of `System.keyed_sound` split
     on `rom`. Call receivers use distinct instance ids as before. For ROM
     receivers, equal keys on one channel give the same `romReceivers` entry,
     so the same circuit, and `cap ≤ 1` gives the same instance.
3. **Theorem** (`Tables.lean`).
   - `circuits = plan.singles.map (lower idOf) ++ fixed.map tableCircuit`,
     with `fixedIn : ∀ t ∈ fixed, t ∈ fixedRows …`.
   - `System.wideLedger_tables` splits the wide ledger into the chips'
     instances plus a ledger supported on `fixed`. That ledger is `tables`,
     so `tableSupport` is a lemma.
   - The external ledger is `request.padded sys.width`: the narrow encoding
     of one send part, zero-padded to `W + 1`. `request.Request sys
     (encode idOf root)` collects its static facts. `narrow_heap_sound_tables`
     takes the built part `Part.request sys.width (encode idOf root)` and
     `checkRequest … = true` instead.
   - `Part.Request.padded_shape` gives `extShape`.
     `Part.Request.padded_proj` gives `extParts` for `X = [request]`, so
     `extWide` follows with `requestWide`. `extRecv` and `extUnique` are
     vacuous.
   - `ids` is now `sys.instances ≤ bound`, because the instances include
     table rows.
   - The results are `System.checkMemo_of_tables` and
     `narrow_heap_sound_tables`.

**Rust side: done** (`template/lean.rs`, `tiling_export`;
`aiur-template-backend.md`, "v1 through the Lean pass"). The v1 backend
loads the exported templates, fixed matrix and request. It validates them
and generates the witness. `bn254-trace` and kzg-source prove and verify
through it, and the M1 forgeries are rejected. The layout is the one
described below:

- **Map tables.** Each map-claim row is one instance of a `tableCircuit`
  (width 1, one receive `⟨−X_0, encode mc⟩`). A chunked row's key cell is
  its **global instance id** `instId f i`, pinned like any call receive.
  It is not the table row index.
- **ROM.** Each ROM entry is one `tableCircuit` instance receiving
  `[ROM, width, address, words]`, keyed by its **constant address** and laid
  out with `cap = 1`. Addresses must be distinct per width; the Lean
  `checkKeyed` rejects duplicates.
- **Fixed columns.** Both kinds must come from the Lean `System.fixedAt`
  export, like every other template row.
- **Entry request.** The verifier's external tuples are
  `Part.request W (encode root)`, zero-padded to `W + 1`. Chunked requests
  use `W − 2`-entry chunks under key 0.

### c. `Shaped` decider

Done (`Shaped.check`, `Shaped.of_check`).

### d. Checker scaling and timing on `chain_v1`

**Timed on the Rust function circuits** (`examples/aiur_template_lean_chain.rs`).
The input is `chain-ungrouped.ixa` at the 2-shard stage-3 capacities, with
156 functions and 395,020 map rows (78.5M places). The compiled
`tiling_export` lowers it in 2.9 s, decides `checkKeyed` and `checkRequest`
in 9.4 s, and finishes in 47 s. No ROM rows are included, since there is no
execution.

**`chain_v1` itself is not timed.** Its chips exist only inside
`MultiStark.BN.Packed.compilePackage`: the `bn_grouping export … --chain`
run takes about 36 CPU-minutes, and there is no snapshot of them. Timing
them needs a compiled driver that runs the packed pipeline up to
`plan.singles` and calls `tileCircuits`. That is a `lean_exe` in
`MultiStark/lakefile.lean`, which is not added yet.

**Proxy on a BN snapshot** (rerun 2026-11-14 after §5b).

- `tileKeyed` accepts the 167-chip system: 8,210 places, 3,857 roles,
  14.6 s interpreted. 82 channels are chunked; 72 have in-system receivers,
  and 10 are external, 9 of them ROM.
- With one `tableCircuit` row per channel that no chip receives (27 rows,
  13 of them ROM widths, with placeholder constants), `tileKeyed` accepts
  194 circuits: 8,419 places, 2,170 lookup slots, 9 chunked ROM receivers,
  14.0 s. All 82 chunked channels have in-system receivers: `external 0`.
- Scripts: `target/tiling-compare/probe/timing.lean` (snapshot timing) and
  `probe/table.lean` (table rows). The ROM probe accepts two chunked ROM rows
  of one width with distinct addresses. It rejects them with equal addresses,
  and it rejects `cap = 2`.
`target/column-min/snapshot.json` holds 167
depth chips of the BN program. For each chip,
`Bridge.lower → Graph.ofCircuit → lower → Template.check` ran at `W = 8`.
The run was interpreted (`lake env lean --run`); the script is
`target/tiling-compare/probe/timing.lean`, not in the repo.

- All 167 templates are accepted, and 97 of them are chunked.
- Total time is 11.0 s. The slowest chips are `Blake3::compress` (2.7 s;
  500 variables, 89 constraints, 226 lookups) and `KzgBlake3::rounds`
  (2.6 s). Every other chip takes under 0.9 s.
- `tileCircuits` over all 167 chips (`cap = 1`) takes 11.0 s and fails
  only on the `checkUnchunked` gate.

So the exponential blow-up feared in §6 does not appear on these chips.
Compiled code should be well under that. Memoizing `meaning`/`expandAbove`
and checking over the shared graph is still worth doing for larger fused
chips, but it is no longer on the critical path. §5a and §5b are done.

### e. Periodic shards (v2 layout, `aiur-template-backend.md`)

v2 changes the narrow circuit itself:

- **Span flags** `M_{l,l'}` and degree-3 constraints
  `C_l = qm_l·x_{4l}·x_{4l+1} + Σ_{l'≥l} M_{l,l'}·lin_{l'}`.
- **Lane messages** `push(mk + mc·x_{4l}, [ts, x_{4l+1..4l+3}])`.
- **Packed copy tuple** `[3 + 4·(label + s·Lₛ), x_j]`.
- **Per-shard key offsets** `x1 + rkey + kf·s·Iₛ`.
- **One fixed matrix** shared by all shards.

**Shard circuit** (`Periodic.lean`; standard axioms only).

- **Circuit.** `Periodic.narrowCircuit W labelOffset idOffset` is one
  shard's circuit. Its fixed layout has 6 gate coefficients per lane,
  `L(L+1)/2` span flags (`flagCol` indexes them by prefix sums), `(ts, mk, mc)`
  per lane, `(ts, mk, mc, rkey, kf)` for the row message, and `W` labels plus
  `W` multiplicities: 42 fixed columns at `W = 8` (`example`). The offsets are
  arbitrary naturals; a uniform layout uses `s·Lₛ` and `s·Iₛ`.
- **Constraints.** All shards have the same constraints
  (`constraints_shard`); `span_holds` gives a span's relation.
- **Messages.** `laneMessage_entry`, `rowMessage_entry` and `copyLookup_entry`
  give each lookup's ledger entry. Copy keys are `copyKey n = 3 + 4·n` for the
  global label `n`; `copyKey_inj` and `copyKey_ne_code` (codes `1`, `2` mod 4)
  separate them under `SmallCast`.

**Templates and checker: done** (`PeriodicTemplate.lean`); the lowering is not.

- **`Template2`.** Slots; the logical message rows `messages` (v1 format, in
  lookup order); physical rows. A gate row holds `LaneUse`s (gate lane, lane
  message `m`, empty) and `Span`s `(start, len, role)`. A row message is
  `.message m key`; `key` marks a chunked call receive's rows.
- **`logical`.** The v1 template with one joined gate row per span (the
  span's lanes padded with zero lanes), one pin row per invocation slot, and
  the message rows. The system of logical templates (`Sharded.system`) is
  checked by the existing `System.checkKeyed`, so relations, slots, message
  groups, roles, arities and ROM receivers are validated by the v1 checker.
- **`shadow`.** The physical cells as a v1 template; a key row's cell 1 is
  empty. Copy labels and multiplicities of a shard are the shadow system's.
- **`checkPhysical`.** Spans fit the row and have distinct starts;
  continuation lanes have `qm = 0`; gate lanes have `qid = 0` (v2 has no
  per-instance `qc`); physical cells are below the slot count and never an
  invocation slot; lane messages fit three cells; a key row's logical cell 1 is
  an invocation slot; every message is placed exactly once (`refs`); the bus
  table's lane flag matches the placement.
- **Bus table.** `buses : (tag, sub) ↦ (code, lane)`, with distinct keys,
  distinct codes, codes `1` or `2` mod 4 (`Sharded.check`). The fixed `ts`
  column is the code; `mk = 0`, `mc = sel`.
- **Fixed matrix.** `fixedRow` lists one row's columns in column order;
  `Sharded.fixedAt L p c` depends only on the layout `L`, so shards of one
  layout share it by definition. Rows past the layout's places are zero.
- **Systems.** `Sharded` is a list of shard layouts. Label and id offsets of
  shard `k` are the counts of all earlier shards, so global labels and ids are
  disjoint. A chips layout repeated `S` times plus one table layout is the
  Rust shape (the tables must not repeat: chunked ROM receivers are unique).

**Per-row semantics: done** (`PeriodicRows.lean`). `fixedRow_*` index the
fixed row. `Placed.span`: every span of a placed gate row enforces
`Σ_{l ∈ span} (laneAt ls l).value = 0`, the form that the logical span row
denotes. `Placed.key_cell`: a key row has `x1 = 0`.

**Step 2, per-shard copy: done** (`PeriodicCopy.lean`). The v1 copy lemma
now takes `System.CellsValid` (widths and cell bounds) and only label
balances (`CellsValid.copy`); `System.Valid.copy` is a wrapper.
`Sharded.copyLedger_key` identifies the coefficient of a shard's packed key
with the shadow system's copy coefficient, and `Sharded.consistent` gives
every physical cell its slot's anchor value.

**Step 3, trailing zeros: done** (`PeriodicLedger.lean`). `ledger_split`
splits every shard row into row, lane and copy lookups. `Sharded.Shape`: row
messages (length `W`, row-channel code), lane messages (length 4,
lane-channel code), copies (length 2, packed key). `exact_of_trimmed`:
trimmed balance is exact balance, given `Separated` (codes and labels below
the `SmallCast` bound, distinct codes) and an external ledger of message
shapes. `copy_balanced`: exact balance gives each shard's copy balance at its
own packed keys, because label ranges are disjoint.

**The v1 ledger argument now has a trace-free core.** `System.Logical sys
main` (validity plus relations under `slotValue main`) and `System.msgSum`
are what `System.keyed_core` reads; `System.keyed_sound` is now that core
plus the v1 physical trace. The v2 theorem instantiates the core at the
logical system with a synthetic `main`.

**Global indexing and the logical trace: done** (`PeriodicSystem.lean`,
`PeriodicLogical.lean`).

- `Sharded.base k` is shard `k`'s first logical circuit; `system_template`,
  `system_circuit`, `system_cap` and `system_instId` relate circuit `f'` of
  shard `k` to logical circuit `base k + f'`. `idOffset k` is defined as the
  logical system's id of that circuit's first instance, so
  `system_instId`: logical ids are the shard's local ids plus `idOffset k`.
  `decompose` and `locate_at` go the other way.
- `valV main f i s`: the instance's id for an invocation slot, else the
  shard's shadow `slotValue` (the physical anchor). `mainV main` is a trace
  of the logical system holding `valV` at every logical cell, so
  `slotValue_mainV`: the logical system reads `valV` at every cell slot.
- `Sharded.logical`: from `ShardTrace` (row constraints, heights, physical
  copy consistency), the logical system with `mainV` is a `System.Logical`.
  Span rows hold by `Placed.span` and `Lane.value_poly`; pin rows hold by
  the definition of `valV`.

**Messages and `Sharded.sound`: done** (`PeriodicMessages.lean`,
`PeriodicSound.lean`).

- `unpack` decodes `code :: rest` to `tag :: sub :: rest` through the bus
  table (`decode_code`: codes are distinct below the bound); `proj2` is
  `unpack` then the logical system's arity cut.
- `lane_entry`, `row_entry`: a placed lane or row message, through `proj2`,
  is its logical `msgEntry` at `slotValue mainV`. On a key row the key
  coordinate `x1 + rkey + kf·idOffset` is `0 + localId + idOffset`, the
  logical id (`Placed.key_cell`, `system_instId`).
- `row_total`, `instance_total`: a row carries its `refs`, and `refs` is a
  permutation of the message indices, so an instance carries each logical
  message once. `shard_total` and `msgLedger_total`: summed over places and
  shards (`sum_range_blocks`), this is `system.msgSum mainV`.
- **`Sharded.sound`.** Hypotheses: `S.check`; `SmallCast F bound` with codes,
  `copyKey labelTotal`, each shadow system's `bound`, the logical system's
  instances, and its lookup slots plus `|X|` below `bound`; shard heights;
  each shard row satisfying `S.circuit k` under `S.assign k`; an external
  ledger of message shapes whose `proj2` image is `Σ X.narrow`, with the v1
  `extFormed`, `extRecv`, `extUnique`; and trimmed balance
  `mapDomain trimZeros (S.ledger H main + ext) = 0`. Conclusion: every wide
  row of the logical system satisfies its circuit, and the wide ledger plus
  `Σ X.wide` is zero. The proof runs `exact_of_trimmed`, `copy_balanced`,
  `copyLedger_zero`, `consistent`, `logical` and `msgLedger_total` into
  `System.keyed_core`. No shared-opening fact appears: the theorem is per
  shard circuit with the layout's fixed values.

**Composition: done** (`PeriodicCompose.lean`). `Sharded.encode2` replaces
a narrow tuple's `(tag, sub)` by its code and pads it to 4 or `W`;
`padded2` is the request's encoding, `checkRequest2` decides that its row
keys have bus entries and fit, and `padded2_shape`, `padded2_proj` are the
analogues of `Request.padded_shape`, `padded_proj`.
`narrow_heap_sound_v2` runs `Sharded.sound` with `X = [request]` and then
the `checkMemo_of_tables` argument with `chips ⊆ plan.singles` (§4).

**Certificate extensions for what `v2.rs` emits: done.**

- **Merged lookups** (`PeriodicMerge.lean`). `Circuit.mergeBy C groups` has one
  lookup per group (arguments of the first member, sum of the members'
  multiplicities); a lookup in no group is dropped. `Circuit.checkMerge`
  decides the groups; `rowLedger_mergeBy` is LogUp additivity. Layout
  circuits are merged circuits, and `narrow_heap_sound_v2` takes `wide`,
  `groups`, `merged` (§4) and transports the ledger and constraints back to
  the lowered chips.
- **Constant and affine multiplicities** (`mk ≠ 0`, or no cell). A lookup
  whose multiplicity is `mk + mc·x` with `mk ≠ 0`, or a constant `mk`, gets a
  *virtual slot* `v := mk + mc·x` (or `mk`), listed in `Template2.virtual`.
  The logical message is `(1, tag, sub, v :: …)`, and the logical template
  has one defining row per virtual slot (`virtualRows`), checked by the v1
  checker. `physMult` gives the physical `(mk, mc, cell 0)`: the fixed `mk`
  and `mc` columns and the cell `x` (or none). `checkVirtual` (in
  `Sharded.check`): no physical cell holds a virtual slot, each is
  `k + c·x` for a physical `x` or a constant, and its messages have `sel = 1`.
  `valV` gives a virtual slot its definition over physical values;
  `mult_value` shows `mk + mc·x = sel·val(mult)` for lane and row messages.
- **Booleanity of virtual multiplicities** (`PeriodicTemplate.lean`,
  `PeriodicLogical.lean`). `Template2.booleans` lists virtual slots that get
  a logical-only row `X_v² − X_v` (`boolRow`, role `boolean v`), which
  `checkChunked` reads. `checkBool` (in `Sharded.check`) certifies each: for
  `v := k + c·x`, some span's relation is `Identical` to
  `(k + c·X_x)² − (k + c·X_x)` (`virtualBoolPoly`); for `v := k`, `k² = k`.
  In `Sharded.logical` the row holds from that span (`spanHolds`) and the
  virtual slot's definition. `lower2` fills `booleans` with every virtual
  slot that `boolOk` accepts.
- **Unrolled `Blake3::compress`** (`PeriodicUnroll.lean`,
  `PeriodicUnits.lean`). A row `w` of `Unroll.circuit U C` gives body rows
  `U.row C b w = fun c => (U.sigma C b c).denote w`. `Unroll.holds`: each
  satisfies `C`. `Unroll.check` decides the self-call chain (table in §4),
  and `Unroll.rowLedger_circuit` shows that the unrolled ledger is the sum of
  the body rows' ledgers (the dropped receive of body `b + 1` cancels the
  dropped self-call of body `b`; the last self-call has multiplicity 0).
  `narrow_heap_sound_v2` takes units `(chip, unrolling?)`;
  `System.wideLedger_units` and `instancesU` give one chip instance per body
  row. `compressUnroll` fixes the **receive multiplicity column `C.width − 1`
  (`numVars + 1`, read as `0 − X`) to 1 in bodies `1..7`**, which the
  multiplicity check needs; `v2.rs` does the same. The column holds no cell,
  so the template is unchanged (167/167 BN proxy templates still identical).
  `lowerCircuit` rejects an unrolling that `Unroll.check` rejects. Entry at
  stage 0 stays a completeness matter.
- **Stacked tables and witness-valued ROM** (`PeriodicStacked.lean`). A
  `Stacked` table is its own circuit beside the shards. Row `r`: main column
  0 is the count, the other main columns are witness values; fixed columns
  `sel` (1 on table rows, 0 on padding), `key = keyBase + r`, then the row's
  `data`. Narrow row `c` reads the columns `slices[c]`: one slice is an
  unchunked payload; with several, chunk `c` is `[code_c, key, slice_c…]`.
  Lookup `c` is `push(−sel·count, [code_c, key?, slice_c…, 0…])` at the
  channel's tuple length. `Stacked.rowLedger_part`: a table row's ledger is
  `padded2` of its receiver part; `ledger_eq`: padding rows contribute 0.
  A map table (`checkMap`) has fixed data; a ROM table (`checkRom`) has the
  address as key and witness words, so its row is the ROM entry
  `(keyBase + r, words)`. The table parts enter `Sharded.sound` as external
  parts: shapes and `proj2` from `padded2_shape`/`padded2_proj`, `Formed`,
  `RowsIn` and the receiver conditions from `Stacked.check`, key uniqueness
  from distinct channels and `keyBase + r < bound` (`pairwise_tableParts`).
- **Closed-form fixed matrix** (`PeriodicFixed.lean`).
  `System.places_closed` and `System.label_closed` give the place index
  `blockBase rowCount f + i·rowCount f + r` and label
  `blockBase slotCount f + i·slotCount f + s + 1`; `Template.anchor_eq`,
  `occurrences_eq` and `multFast_eq` compute copy multiplicities from one
  cell list per template (`multTable`). `Sharded.emit` builds a row from
  per-row parts (static columns, row-message columns at id 0, cells,
  multiplicities) plus the instance's label base and id, and
  `Sharded.emit_eq` proves it equal to `Sharded.fixedAt` at the closed-form
  index.

**Lowering and differential test: done** (`Lower2.lean`, `Tile2.lean`,
`Export2.lean`; harness `target/tiling-compare/harness/run2.sh`).

- `lower2` ports `v2.rs` `lower` (forms over body columns, normalized product
  interning, merging, fusion, spans and carries, first-fit placement, lane,
  row and keyed messages, booleanity relations). `lowerCircuit` returns the
  template and the merged (unrolled) circuit it is checked against;
  `compressUnroll` derives the bodies as `Backend::new` does; `tile2`
  assembles and checks a `Sharded` system.
- Rust side: `harness/rust2` extracts the lowering half of the live
  `template/v2.rs` at build time (`build.rs`) and reproduces `Backend::new`'s
  compress bodies. Both sides dump physical rows (`ts`, `mk`, `mc`, cells,
  spans, lanes) and the prototype's slots.
- Random graphs (300 per run, `gen.py`): every template that both lower is
  identical, 0 mismatches. With `checkBool`, `Sharded.check` accepts every
  one: 294/294 at `W = 8`, 293/293 at 12; chunk-heavy (`0.8`) 280/280 at 8
  and 286/286 at 12 (2026-11-15).
- **BN proxy** (`target/column-min/snapshot.json`, `W = 8`): all 167 templates
  identical to `v2.rs`, the unrolled `Blake3::compress` included (2,521 rows,
  8 bodies, 27 chunk rows); 10,145 template rows; 126 merged lookups; each
  template accepted by `Sharded.check`, and `tile2` accepts the whole system
  with two shards. Interpreted run: about 4 minutes (`bn2.lean`).

**Numbering Rust must adopt** (to read fixed columns from the Lean export):

- **Slots.** The prototype's slots, then the invocation slot (one, if the
  template has a chunked receive), then one virtual slot per lookup with a
  virtual multiplicity, in message order. Labels count all of them: the
  per-instance label stride is the Lean slot count, not `t.slots.len()`.
- **Labels.** `label = 1 + index of (f, i, s)` in `keys` of the shard's
  shadow system (`f` outer, then instance, then slot), i.e. Rust's
  `label_base + instance·slots + slot` with the Lean slot count. Every
  occupied cell carries its label (`labelAt`), including single-occurrence
  cells, which Rust currently leaves 0; multiplicities as Rust (`o − 1` at
  the row-major first cell, `−1` elsewhere, 0 for singletons).
- **Offsets.** `labelOffset k = Σ_{k' < k} (|keys_{k'}| + 1)` and
  `idOffset k` = the logical id of shard `k`'s first instance, i.e.
  `k·labels_per_shard` and `k·ids_per_shard` for `k` uniform chip shards
  (Rust's counters start at label 1 and id 0, which matches). Row keys
  `rkey` are the shard-local `instId f i = Σ_{f' < f} cap f' + i`.
- **Tables.** Stacked tables (`Periodic.Stacked`), not `tableCircuit`
  shards. One map table per called map in input order, keyed by global ids:
  `keyBase` of map `m` is `S.system.instances` plus the rows of the earlier
  maps. One ROM table per memory width with `capacity` rows, keyed by the
  address `r` (`keyBase = 0`). Columns as in "Stacked tables" above;
  `tiling_export2` writes each table's `tag`, `sub`, `rows`, `key_base`,
  `main_width` and `slices`.
- **Compress.** Receive multiplicity column `main_width − 1` fixed to 1 in
  bodies `1..7`.
- **Rows.** `places` order `(f, i, r)`: regions per function, instance-major,
  template rows in order (gate rows, then message rows), as Rust.
- **Buses.** `ts = tag + 4·sub` with chunk subs `sub + (c+1)·2^32` (calls)
  and `sub + c·2^32` (ROM); one lane flag per channel, from the placement.
  Fixed columns are Rust's order (42 at `W = 8`), `mk`, `mc` from
  `physMult`, key rows `rkey = local id`, `kf = 1`, lane 0 `q1 = 1`, flag
  `M_{0,0} = 1`.
- **Merging.** The merge groups are the lowering's (`lower2`'s second
  result); Rust's are the same by construction on every fixture.

**Exporter** (`MultiStark/Examples/TilingExport2.lean`, `lake build
tiling_export2`). Reads `ix-tiling-v2-input-1` (`template/v2/lean.rs`),
lowers every graph (`compressUnroll` on the marked graph), and rejects unless
`Sharded.check`, `Part.checkRequest`, `checkRequest2`, every table's
`Stacked.check` and `checkMap`/`checkRom` and distinct channels accept. It
writes `ix-tiling-v2-layout-1` (templates with all slots and `virtual`,
buses, request tuples, label and id strides, table descriptors, the
closed-form size bounds) and the chip layout's fixed matrix through
`Sharded.emit`. On the chain (`chain-ungrouped.ixa`, 2-shard config
`stage3-s2-h0.08`, `W = 8`): 156 graphs, 395,020 map rows in 14 map tables,
13 ROM tables (422,221 addresses); 33,442,591 places per shard, 42 fixed
columns. Parse 0.9 s, lowering 0.2 s, `Sharded.check` 23.7 s, tables and
request 5.5 s; fixed matrix 32.9 s (9.2 GB file); 65 s in all, 0.43 GB peak RSS (2026-11-15). Every template row's byte writer is compared with `Sharded.emit` on instance 0. The current exporter runs the checks beside the writer, in about 28 s ("Exporter speed" below), and production streams the matrix (`/dev/stdout`) instead of storing it.

**Rust stacked tables: done** (`template/v2.rs` `Stacked`, `stacked`,
`stacked_circuit`). Each stacked table is its own circuit, after the shards
in `circuit_inputs`:

- **Map table.** One per called map, in callable order.
  - Fixed columns: `sel`, `key = keyBase + r`, then the claim payload.
  - Main column: the count.
- **ROM table.** One per memory width, with `capacity` rows at the fixed
  addresses `0..capacity`.
  - Fixed columns: `sel` and `key`, the address.
  - Main columns: the count, then the words.
- **Lookups.** Lookup `c` is
  `push(−sel·count, [code_c, key?, slice_c…, 0…])`, padded to 4 on a lane
  bus and to `W` on a row bus.
- **Heights.** A table's height is a power of two, at least `2^16`. Packs
  are planned per height, so the small tables share one height class.
  Padding rows have `sel = 0`, which `tallT` allows.

`adopt_lean` checks that the exported `tables` equal `Backend::stacked`'s
descriptors. It also checks that the bus table, codes and lane flags,
equals the backend's. On the BN254 trace fixture, `tests/aiur_template_v2.rs`
covers:

- `v2_lean_exporter_on_fixture` runs the real exporter (ignored test; the
  exporter path is in `IX_TILING_EXPORT2`). Templates, buses, tables and
  every fixed row agree with Rust, and the honest witness proves.
- Rejected forgeries: a map count raised, a ROM word changed, a ROM read
  moved onto a padding row, and the earlier shard forgeries.

**Exporter speed.** `Sharded.check` and the table checks run as tasks beside
the fixed-matrix writer. The writer serializes blocks of about `2^16` rows
in parallel and writes them in order. The bytes are unchanged, and the
layout JSON is identical to the sequential exporter's. The exporter takes
27–30 s, bounded by `Sharded.check`, against 65 s before; the fixed matrix
takes 6 s standalone and 20 s beside a prover. Peak RSS is 1.8 GB.

**Production run** (Init stage 3, 2 shards, +8%,
`target/narrow-terminal/stage3-s2-h0.08-stacked`, GPU, packed SHPLONK).
`aiur_template_v2_init --config … --prove --packed --save` starts the
exporter on `lean-input.json` right after `Backend::new`. A reader thread
decodes the `IXTLFX01` stream from its stdout in parallel, into a matrix
reserved at the trace height. Execution and witness generation run
meanwhile. The 9.2 GB matrix never reaches the disk; only `lean-layout.json`
(4 MB) is kept. With `--lean-reference`, every fixed row is also compared
with `narrow_fixed`. It matched, in 8 s.

| | Rust layout, 2 tables | Lean layout, stacked |
|---|---:|---:|
| circuits / fixed slots | 4 / 3 | 29 / 28 |
| evaluations / packed commitments | 110 / 41 | 561 / 45 |
| key / proof wire bytes | 3,873 / 4,637 | 12,879 / 21,365 |
| witness / prove / fixed commit | 12.3 / 56.3 / 14.3 s | 13.7 / 59.9 / 15.0 s |
| wait for the layout after the witness | — | 12.5 s |
| wall / peak RSS | 1:40 / 113.1 GB | 1:50 / 113.6 GB |
| terminal (gnark, exact) | 23,322,728 | **42,739,164** (`2^26`) |

The proof verifies natively and a changed output is rejected. Padding the
tables to their own heights instead of `2^16` gives 85 packed commitments.
The terminal (`compress_final_narrow_export`, 3,661,454 bytes) was
re-exported from the new key. Its PLONK preparation stopped at the SRS: the
`2^26` domain needs `2^26 + 3` powers and the retained Ignition SRS has
`2^26`. So no PLONK proof, gas figure or end-to-end run exists for this key.
`target/narrow-terminal/plonk-lean` and `target/e2e-narrow/bin` still hold
the previous, Rust-layout pipeline, which `run.sh` runs unchanged.

Most of the growth is in openings: 27 table circuits, and ROM rows that
hold every word of an object (main width `1 + width`, up to 99 columns).
Ways to fit `2^25` again change the Lean statement in
`Aiur/Aiur/Tiling/PeriodicStacked.lean`:

- one stacked circuit for all maps, with a per-row fixed code column;
- ROM rows per `(address, chunk)`, as the earlier Rust `narrow_rom`.

That is two table circuits and about 110 evaluations, as before.

Next steps, in order:

1. ~~Restate `Periodic.Stacked` with a fixed per-row code and per-chunk ROM
   rows~~: done as `Periodic.narrow_heap_sound_compact` (§5g). Rust: adopt
   the §5g shape; then redo PLONK, gas and the end-to-end run.
2. ~~Discharge `enables`~~: done, `Bridge.checkEnables` (§8).
3. A v1 variant with witness ROM, if v1 stays in use.

Not soundness premises: shared preprocessed openings (STARK trust; the
theorem is per shard circuit with the layout's fixed values) and no
straddling (copy classes are per shard).

### f. What the theorem covers in the production narrow stage

With the Lean export as the layout source, these parts of BN3 are covered by
`Periodic.narrow_heap_sound_stacked`:

- **Layout.** The templates, the bus table, the label and id numbering, the
  per-shard offsets, the unrolled `Blake3::compress` and the merge groups.
  The exporter rejects the layout unless `Sharded.check`, `Unroll.check` and
  `checkMerge` (inside `lowerCircuit`) accept.
- **Fixed matrix.** The committed shard matrix is the exporter's bytes of
  `Sharded.emit`, proved equal to `Sharded.fixedAt` (`emit_eq`). Rust does
  not recompute it; `--lean-reference` is only a cross-check.
- **Tables.** The stacked map and ROM tables: `Stacked.check`,
  `checkMap`/`checkRom` and distinct channels. Map data equal to the encoded
  map claims is `mapsIn`, a static fact: the exporter's input holds the
  claim tuples. The ROM is the trace's, so no ROM is trusted.
- **Request.** The entry request's shape: `Part.checkRequest` and
  `checkRequest2`.

These remain trusted:

- **Rust lowering to the STARK.** `Bridge.lower` agrees with the compiler's
  activated chips (`Compiler::inputs`). The input graphs come from Rust's
  `compile_graph`, and `Graph.circuit` reads them.
- **Rust circuit construction.** The multi-stark circuits that
  `narrow_circuit` and `stacked_circuit` build equal `Periodic.narrowCircuit`
  with the shard offsets, and `Stacked.circuit`. These are expression
  shapes, not checked by Lean. The shard circuits read the Lean fixed matrix
  by column index.
- ~~**`enables`.**~~ Checked: `Bridge.checkEnables` (§8).
- **The STARK.**
  - The multi-stark/KZG argument and LogUp (`rows`, `tall`, `balanced` are
    the prover's output).
  - The shared fixed-slot openings (`aiur-template-backend.md`, "Soundness
    of sharing").
  - The packed SHPLONK PCS.
  - The terminal verifier's agreement with the native one.
- **Field and size facts.** `small`, `characteristic`, and the size bounds
  the exporter reports (`bound` = 566,935,683,439, below the field).
- **Map contents.** That the map tables in `lean_input` are the program's
  maps.

### g. Compact tables (`PeriodicCompact.lean`)

**Done; standard axioms only.** `Periodic.narrow_heap_sound_compact` is
`narrow_heap_sound_stacked` with the 27 stacked tables replaced by two
compact tables: one map table for every map claim and one ROM table for every
word count. A compact table holds many receiver parts of many channels, one
narrow row tuple per physical row; the code is a per-row fixed column.

**Proof changes.**

- `Part.cweights` (`Assemble.lean`): a chunked receiver may weigh its chunks
  separately, because each chunk is its own physical row with its own count.
  `Part.narrow` uses `cweight c = cweights.getD c weight`. `Formed` requires
  `cweights = []` or a receiver with `cweight 0 = weight`.
  `ChunkBalance` (`Chunks.lean`) takes per-chunk receiver weights `μ r j`;
  `chunks_sound` and `chunks_total` conclude with `μ r 0`. Chunk balance
  against boolean senders with unique receiver keys forces the chunk weights
  equal, so nothing else changes.
- Cells past a row key's arity are free. The v2 projection (`proj2`) cuts
  them (`Sharded.proj2_row`), so `Compact.proj_ledger` shows the projected
  table ledger is `Σ narrow` of the parts read from the trace.
- `CPart.trace_facts` gives `Formed`, `RowsIn`, `checkRequest2`, arity and
  the receiver condition from `CPart.check`. `map_part` makes a map part's
  tuple its static claim; `rom_part` makes a ROM part's tuple
  `encodeRom (address, words)` at its fixed address.
- `checkTables S ν tables` decides the table checks. Each table check runs
  once per distinct part shape. Distinct chunked receiver keys and distinct
  `(address, word count)` pairs are decided by sorting their images under
  `ν : F → Nat` (`fastNodup`, `O(n log n)`). `ν = ZMod.val` in practice; any
  function is sound.
- `compactRom_valid`: the ROM the trace holds is valid.

**The theorem's table hypotheses** replace `tablesOk`, `kinds`, `channels`,
`mapsIn`, `keysSmall` and `parts` of the stacked theorem:

```lean
    (tablesOk : checkTables S ν tables = true)
    (mapsIn : ∀ T ∈ tables, T.checkMap S = true → ∀ q ∈ T.parts,
      q.tag :: q.sub :: q.payload ∈ (Depth.system cfg prepared.system).mapClaims.map (encode idOf))
    (parts : (S.system.enumerate S.system.lookupCount).length + 1 + (tables.map (·.parts.length)).sum < bound)
    (tallT : ∀ t T, tables[t]? = some T → T.rows ≤ HT t)
    (balanced : Finsupp.mapDomain trimZeros (S.ledger H main + compactLedger S tables HT mainT +
      S.padded2 (Part.request S.width (encode idOf root))) = 0)
  : (compactRom S tables mainT).Valid ∧ ∃ value heap, EvalFn … ∧ Represents (… compactRom …) …
```

`mapsIn` holds by construction for `Compact.ofMaps W claims keyBase`
(`Compact.ofMaps_mem`) when `claims` are the encoded map claims.

**Exact shape, for Rust** (`template/v2.rs`, `template/v2/lean.rs`). Shard
width `W`, a table with `n = nFixed` fixed cells:

- Circuits, after the shards: the map table, then the ROM table. Both are
  built by the Lean exporter (`tiling_export2 … tables.bin`): map table
  `Compact.ofMaps W tables (shards · Σ caps)` over the input's `tables`
  tuples in input order; ROM table `Compact.ofRoms W rom` over the input's
  `(width, capacity)` pairs in input order. Layout JSON `"compact"` lists
  `n_fixed`, `main_width`, `fixed_width`, `rows`, `parts` per table; the
  `"tables"` array is then empty.
- **Main columns:** `count` (column 0), then cells `n … W − 2` as main
  columns `1 … W − 1 − n`. Map: `n = W − 1`, main width 1. ROM: `n = 1`,
  main width `W − 1`.
- **Fixed columns** (`3 + n`): `selL`, `selW`, `code`, cells `0 … n − 1`.
  Values: `tables.bin`, one `IXTLFX01` block per table (`rows × (3 + n)`,
  same field encoding as the chip matrix), rows in part order, a chunked
  part's rows in chunk order (`Compact.fixedRows`, equal to
  `Compact.fixedAt` by `fixedAt_offset`). Rows past `rows` are all-zero
  fixed (padding); the height is any power of two `≥ rows`.
- **Lookups**, in this order, no constraints:
  - `push(−selL·count, [code, cell₀, cell₁, cell₂])`;
  - `push(−selW·count, [code, cell₀, …, cell_{W−2}])`.
- **Rows.** A map claim `tag :: sub :: payload` with key `k = keyBase + i`
  is one row with cells `payload` (zero padded) if `|payload| + 1 ≤ W`, else
  `J` rows of chunks of `W − 2` (`Part.chunksOf`), row `c` with cells
  `[k, chunk_c …]` and code of `(tag, chunkSub false sub c)`. A ROM entry
  of width `w` at address `a` is one row `[a, words]` (code of `(ROM, w)`) if
  `w + 2 ≤ W`, else rows `c` with cells `[a, words chunk c]` (chunks of
  `W − 2`) and code of `(ROM, chunkSub true w c)`. `selL = 1` iff the code's
  bus is a lane bus, else `selW = 1`.
- **Witness.** `count` of each row is the number of reads of that entry or
  claim (every chunk row of an entry gets the same count; the theorem does
  not need it). Unused main cells may hold anything; the prover writes 0.

Shape cost at `W = 8`: map table 1 main + 10 fixed columns, ROM table 7 main
+ 4 fixed, two lookups each: two circuits beside the shards, against 27.

**Rust consumer (2026-11-15).** `aiur_template_v2_init --config` passes
`lean-tables.bin` and adopts the compact tables (`template/v2.rs`
`CompactTable`, `compact_circuit`, `compact_traces`; `v2/lean.rs`
`adopt_lean`); `--stacked-tables` keeps the stacked ones. The fixed values
are the exported blocks; Rust builds only the two lookups and the witness,
and checks each row's code and fixed cells against the export before writing
its count and words. On the fixed-key narrow stage (L3, 1 shard, +8%): map
table 447,230 rows, ROM table 281,262 rows (`log 19` each), 3 circuits, 96
evaluations, proof 3,853 bytes, exporter 28–30 s. In stacked mode (no `tables.bin`) the exporter no longer
builds or checks the compact tables, so it exits right after printing `total`
(L3 stacked: 15.8 s wall).

### Size

| | Lines |
|---|---:|
| So far | 12,300 |
| Remaining | `enables` certificate |

## 6. Risks

- **Checker performance on large templates.** Root relations are compared
  after expanding slot meanings to monomials over wide columns. That is
  exact, but it can blow up on deep product chains (`Blake3::compress`
  rounds). Fix: compare at the prototype's `Form` level, linear over product
  atoms, with each product atom validated once.
- **Unfolding.** `Graph.circuit` is exponential on shared DAGs. The theorems
  need the checker to run against a DAG-sharing semantics, or a proof that
  the graph checker and the tree checker agree.
- **Completeness is not proved.** The pass is proved sound, not complete:
  nothing yet shows an honest narrow witness exists. The `pad` role requires
  zero polynomials, and every relation is an exact identity, so the honest
  witness generator (the prototype's) satisfies the system. A completeness
  theorem would mirror `Template.Checked` in the other direction, at an
  estimated 300–500 lines.
- **Fingerprint semantics** (trailing zeros): resolved in §3.6. It relies on every external tuple being emitted at narrow width. That is `extShape`, a lemma for `narrow_heap_sound_tables` (`Part.padded`).
- **Rust and Lean divergence.** The prototype stays the prover-side witness
  generator and measurement tool. Production fixed columns must come from
  the Lean `System.fixedAt` (exported key), with the Rust side reading them,
  not recomputing them.

## 7. Executable check

The harness is in `target/tiling-compare/harness/` (untracked):

- **Generator.** `gen.py` generates random hash-consed graphs: products of
  sums, constant scaling, negation, CSE, receive and sends, ROM lookups,
  and consistent arities.
- **Rust side.** A scratch crate includes the prototype's
  `template/lower.rs` and `kzg/field.rs` unchanged through `#[path]` and
  dumps templates as JSON.
- **Lean side.** `Aiur.Tiling.Export.run` lowers, checks and dumps the same
  JSON.
- **Comparison.** `compare.py` compares templates field by field: slots,
  terms, lanes, coefficients, cells and message rows.
- **System check.** `sys.lean` additionally runs `tile` (full `System.check`
  and fixed-matrix generation).

Result with 300 graphs per width; "chunked" means out of scope: Rust
lowered with chunks and Lean rejected.

| `W` | Identical | Both rejected | Chunked | Mismatches |
|---:|---:|---:|---:|---:|
| 4 | 271 | 10 | 19 | 0 |
| 8 | 278 | 5 | 17 | 0 |
| 12 | 281 | 5 | 14 | 0 |
| 16 | 287 | 3 | 10 | 0 |

**Chunked graphs.** The comparison now covers chunked graphs.
`Export.run` compares `lower`'s output and records checker acceptance
separately, and the Rust dump includes `qid`, invocation and key slots.

| Run | Identical templates | Chunked among them | Mismatches |
|---|---:|---:|---:|
| Default generator, 300 graphs per `W` | 1,177 | 60 | 0 |
| `gen.py … 0.8`, chunk-heavy, `W = 4, 8` | 591 | 318 | 0 |

Every template is accepted by `Template.check`, chunked or not. Rerun on
2026-11-14 after §5a: 1,177 identical templates at the default setting, 60
of them chunked, 0 mismatches. `sys.lean` now also runs `tileKeyed`: all
1,177 pass `System.checkKeyed` (290/295/295/297 at `W` = 4/8/12/16);
`System.check` still rejects the 60 chunked ones by design.

Every unchunked graph passes `System.check`. The narrow circuit has the
prototype's 32 fixed columns at `W = 8`. Rerun with
`target/tiling-compare/harness/run.sh [count]`.

`run.sh` also tiles each fixture from its `Circuit` (`tileCircuits`).

Rerun 2026-11-15 after the `Ixa`/`WideStage`/`PeriodicMixed` work and the
`boolLinear` rule: `run.sh` 0 mismatches at every `W` (290/295/295/297
identical), `run2.sh` 0 mismatches in all six settings, BN proxy 167/167.
`crates/…/template/lower.rs` has been removed from the tree. Since round 6
(§8) `rust2` takes the bus constants from `template.rs` and builds again;
the v1 comparison (`rust/`) is retired and `run.sh` runs only `sys.lean`.

Build: `lake build Aiur.Tiling --wfail` from the repo root, with `target/terminal-complete/toolchain/lean-4.34.1-linux/bin` first on `PATH` (running lake inside `Aiur/` clones packages there; do not).

## 8. Trust gaps and generality: plan and status

Design rule: everything except the cryptography layer (multi-stark STARK,
LogUp, PCS) is Lean. Lean definitions are the implementation (run by the
exporters now, compiled by ixcc later); Lean exports the complete circuit
description and Rust only consumes it.

### Status

| Item | Status |
|---|---|
| 1b `enables` | **Done.** `Bridge.checkEnables bound c` (`Enables.lean`) certifies every activated send/memory enable boolean from the activated chip's own constraints: identically 0/1; a constraint identical to `±e(e−1)` (sound normal form); products and `1 − x` of certified terms; a selector split (a constraint `(1 − sel)·e` and `e[sel := 1]` certified); a partial sum of a one-hot family (variables of one constraint, each boolean, whose total is boolean, `|J| < bound`). `boolean_of_lower` derives `Boolean c w` from `(lower idOf c).Holds w`. `Bridge.Wide` carries `enablesOk` and derives `boolean`, so every composed theorem (`narrow_heap_sound`, `_keyed`, `_tables`, `Periodic._v2`, `_stacked`, `_compact`) takes `enablesOk : ∀ c ∈ plan.singles, checkEnables bound c = true` instead of `enables`. All 167 BN chips pass (`target/tiling-compare/probe/enables.lean`). This also discharges the boolean-enable item of `Optimized/EndToEnd.lean` for any stage whose rows are checked through `Bridge.Wide.checkMemo`: a wide stage proved with `Bridge.lower` circuits needs only `Holds` and balance, no enable assumption. |
| 1c `fixedIn`, `mapsIn` | ROM: no trust (the trace's ROM, `compactRom_valid`). Maps: `mapsIn` is a list membership, true by construction for `Compact.ofMaps` (`ofMaps_mem`) when its claims are `mapClaims.map (encode idOf)`. Open: the exporter still takes the claim tuples from the Rust input; see 1a. |
| Compact tables | **Done** (§5g), with `Part.cweights` (per-chunk receiver weights). |
| 2a Field | The theorems are parametric in `F`; the only field facts are `SmallCast F bound` and `characteristic` (`n ≤ 2^63 → (n : F) ≠ 0` at `cfg.bits ≤ 24`). `smallCast_zmod p (h : bound ≤ p)` proves the first for any prime field, BN254 and Goldilocks (`p = 2^64 − 2^32 + 1 ≈ 1.8·10^19`) alike; `2^63 < p` gives the second. BN3's exporter bound is 566,935,683,439 ≈ 2^39, so the same layout sizes hold on Goldilocks; every bound the theorem needs (rows `≤ 2^39`, labels, occurrences, parts, lookups) is below `p_GL` with room to `2^63`. LogUp over Goldilocks draws its challenges from an extension field; the ledgers are base-field multisets, and "balanced ledger" is exactly what extension-field LogUp establishes, so no model change is needed (STARK trust). Open: a Goldilocks corollary file instantiating `F := ZMod p_GL`. |
| 2b Grouping | Not needed for tiled functions: tiling reads `plan.singles`, and grouping only shares wide columns across chips, which the width-`W` narrow layout already does. A tiled stage uses a plan with `groups = []`. Grouped circuits matter only for the wide half of a mixed stage (2c). |
| 2c Mixed narrow/wide | Open. Route: wide units beside the shards, as the compact tables are — each wide row contributes its lookups as external `Part`s (receive keyed by a fixed id after the narrow ids, chunked sends with witness key cells and boolean weights from `checkEnables`), added to `S.sound`'s `X`; `Bridge.Wide`'s instances become narrow ++ wide rows. All the pieces exist (`Part.cweights`, `Compact.proj_ledger` pattern, `Wide.checkMemo` over any instance list). |
| 1a `Bridge.lower` | **Lean side done** (`Ixa.lean`, `tiling_export2` input format 2). The exporter decodes the compiled `.ixa` itself, lowers its chips with `IChip.lower` (`IChip.lower_ofChip`: equal to `Bridge.lower idOf c` for the chip `putChip` wrote), takes the map claims and callable numbering from the artifact, derives the request from the entry chip, runs `checkEnables` on every laid-out chip (`IChip.checkEnables_ofChip`), and exports the wide, narrow and compact circuits as graphs. Rust side: see "Export format 2" below. |
| 2c Mixed narrow/wide | **Done** (`PeriodicMixed.lean`). `Periodic.mixed_heap_sound`: `narrow_heap_sound_compact` plus wide units beside the shards and compact tables. A `WideUnit` `⟨chip c, keyBase, rows⟩` has main columns `0 … n+1` of `Bridge.lower` (`n = c.numVars` selector, `n+1` receive multiplicity), key cells `n+2+j` for send `j`, one fixed column (var `n+2+s`, `s` sends) holding `keyBase + r`, the constraints of `lower idOf c`, and its lookups in the narrow encoding (`WLook.narrowLookups`): receive (weight `−mult`, key = the fixed id), sends (weight = enable, key = key cell), memory (key = address); a payload with `|payload| + 1 ≤ W` is one `push(m, [code(tag,sub), payload…, 0…])`, else per chunk `c` of `W − 2` `push(m, [code(tag, chunkSub rom sub c), key, chunk…, 0…])`; tuples padded to 4 on a lane bus, `W` otherwise. Extra hypotheses: `wideIn`, `wideOk : checkMixed S idOf ν tables wideUnits = true`, `rowsW` (each row satisfies the unit circuit), capacity/lookups/parts extended by `mixedRows`/`mixedLookups`/`mixedPartCount`, and `mixedLedger` in `balanced`. Exporter: `tiling_export2` input 2 with `"wide"` (a channel used only between wide units gets a cap-0 carrier template; Round 3 item 3). |
| 2e Wide stages | **Done** (`WideStage.lean`). `WideStage.wide_heap_sound`: rows of `units.map (unitCircuit idOf)` (chips in `plan.singles`) plus Lean map tables (`mapAirs` of `mapClaims.map (encode idOf)`) and witness ROM tables (`romAirs`, ROM = `wideRom`, valid by construction), balanced with the request, give `EvalFn ∧ Represents` through `Wide.checkMemo` and `depth_grouped_activated_heap_sound`; `enablesOk` replaces the boolean-enable assumption. `wide_heap_sound_insts` takes any list of lowered single-chip rows. Grouped chips (`plan.groups ≠ []`) are not covered: a wide stage proved this way must run ungrouped circuits, or a group lowering must be added. |
| 2a Field (Goldilocks) | Corollaries in `Goldilocks.lean`: `small` from `bound ≤ p_GL` (`smallCast_zmod`), `characteristic` from `cfg.bits ≤ 24`. |
| 2d Entry point | See "Entry point" below. |

### `Bridge.lower`: what Rust should load

The theorem is about `units.map (unitCircuit idOf)` = `Bridge.lower idOf`
of the plan's singles. Today the exporter tiles the graphs in Rust's input
(`compile_graph`), so their equality with `Bridge.lower` is trusted. Next:

1. The exporter reads the artifact (`.ixa`) and builds the plan in Lean
   (as `bn2.lean` does from a snapshot), computes `Bridge.lower idOf c` for
   every single, tiles those (`Graph.ofCircuit`), and computes the map
   claims as `mapClaims.map (encode idOf)`; the Rust input then carries only
   the configuration (width, shards, caps, ROM capacities).
2. For wide stages, a Lean exporter writes each `Bridge.lower idOf c` (and
   `Compact` tables) as an expression DAG (`{width, nodes, zeros, lookups}`,
   the graph format of `Export.parseGraph`), and Rust builds the multi-stark
   AIR by interpreting it: constraints are `zeros` nodes, each lookup is
   `push(node m, [node a …])`. A `wide_heap_sound` theorem (rows satisfying
   the lowered circuits, balanced with the request and tables) follows from
   `Bridge.Wide.checkMemo` directly.
3. The narrow shard circuit and the compact circuits are exported the same
   way (`Periodic.narrowCircuit W`, `Compact.circuit W`), so Rust no longer
   builds `narrow_circuit`/`stacked_circuit` shapes itself.

### Export format 2 (for the Rust consumer)

`tiling_export2` reads `ix-tiling-v2-input-2` in place of
`ix-tiling-v2-input-1`. Rust stops supplying graphs, map claims and the
request; it supplies only the configuration and the artifact it proves with:

```json
{ "format": "ix-tiling-v2-input-2",
  "artifact": "path/to/stage.ixa",          // absolute, or relative to the input file's directory
  "width": 8, "shards": 1,
  "circuits": [ { "chip": "<chip name>", "cap": 1234, "unroll": true }, … ],
  "rom": [ [words, capacity], … ],
  "entry": "<entry chip name>" }
```

- `circuits` is the layout order (entry first, as today). A circuit names its
  chip by `"chip"` (the trace section's chip name, `compiler.names()`) or by
  `"chip_index"` (its index in the trace section's chip list, = the compiler
  circuit index of `order`). `"unroll": true` asks for the checked
  `compressUnroll` (today: `Blake3::compress`); absent means false.
- `rom`: one `[words, capacity]` per memory width used by the laid-out chips
  (the exporter fails if one is missing). `entry` defaults to the first
  circuit's chip.
- The exporter decodes the artifact (`Ixa.decodePackage`, versions 2 and 3),
  lowers each chip with `IChip.lower`, takes the map claim tuples
  `[CALL, callable, input row ++ output row]` of every map called by a
  laid-out chip (program order, table row order: Rust's `MapInfo` order) and
  the request `[CALL, id(entry), 0 × (|inputs| + |output|)]`, and runs
  `checkEnables bound` on every laid-out chip and a distinct-names check on the
  callables. Callable ids are the trace's numbering: functions, then maps.

The output is `ix-tiling-v2-layout-1` with every existing field unchanged,
plus:

- `circuits`: per laid-out circuit, in layout order, `{"wide": graph,
  "unroll": bool, "chip": name, "chip_index": i}`. `wide` is
  `Bridge.lower idOf c` (before unrolling and merging) as a graph in the
  format of `Export.parseGraph` plus `"fixed_width"` (variables
  `width … width + fixed_width − 1` are fixed columns; 0 here). **Rust must
  lower these graphs** (not its own `compile_graph`) when it validates the
  templates and places the witness: on L3, 74 of 153 templates differ from the
  ones lowered from Rust's graphs, because `compile_graph` drops duplicate
  constraints and reorders them (constraint sets and lookups are identical up
  to normal form on all 153; `places` 30,593,906 instead of 30,582,017).
- `narrow_circuits`: per shard `k`, `Periodic.narrowCircuit W (labelOffset k)
  (idOffset k)` (`S.circuit k`) as a graph with `fixed_width`. The multi-stark
  shard circuit is this graph read literally: constraints are the `zeros`
  nodes, lookup `l` is `push(node m, [node a…])`, variable `v < width` is main
  column `v`, `v ≥ width` is fixed column `v − width` of the exported matrix.
  Rust's `narrow_circuit` should be replaced by an interpreter of it (or
  checked equal to it).
- `compact_circuits`: map table then ROM table, `Compact.circuit W` as graphs,
  same reading; replaces `compact_circuit`.
- `map_claims`: the number of claim tuples (the map table's parts).

Measured on L3 (`narrow-fixed.ixa`, 153 chips, 446,807 claims): decode 1.3 s,
total 24.5 s; request, buses, compact tables (`tables.bin` byte-identical) and
the claim tuples equal the Rust input's.

`Shaped.check` and `checkContext` are now theorems of the compiled system
(round 5, Round 3 item 2 below: `Compiled.shaped_of_compiled`,
`context_of_compiled`), except the entry facts and the `idOf` name checks.

### Wide stages: Lean API `WideIxa.stageOf` and `wide_export`

For Lean consumers (the PLONK backend, `docs/aiur-plonk-lean-backend.md`):
`Aiur.Tiling.WideIxa.stageOf (pkg : Ixa.Package F) (cfg : WideIxa.Config) :
Except String (WideIxa.Stage F)` (`Aiur/Aiur/Tiling/WideIxa.lean`), with
`pkg ← Ixa.decodePackage modulus bytes` and `cfg = {circuits := [(chip name,
rows)…], rom := [(words, capacity)…], entry?, allMaps, pow2}`. The result's
`airs = units ++ maps ++ roms` is the table list of
`WideStage.wide_heap_sound`'s `balanced` in order (`stageLedger` of each
part); `units_ofChip` proves `units` equal `WideStage.unitAirs idOf` of the
source chips when the decoded chips are `IChip.ofChip` of them. `claims`,
`request` and `bound` are returned too; `stageOf` fails unless
`checkEnables bound` accepts every chip, callables and ROM widths are
distinct, every memory width has a ROM table and (with `pow2`) every row count
is a power of two. For the terminal at the PLONK capacities: `allMaps := true`
(every map receiver kept; map table rows are the next power of two of each
claim length's count, `WideIxa.mapRows`), `pow2 := true`, unit rows and ROM
capacities the PLONK capacities. Read the package with `Ixa.decodeChecked`
(trace section round-trip checked, round 3 item 1). `mapFixed` reads claims by list
index, so evaluating a map `Air`'s `fixed` row by row is quadratic; read the
values from `(claimsOf claims L).toArray` instead, as `wide_export` does
(compared with `fixed` on the first rows). L3 artifact, all 153 chips,
`all_maps`: 153 unit, 8 map, 13 ROM tables in 11 s.

**Requests from the PLONK backend (2026-11-15).**

- **Done (round 5):** `WideIxa.stageOf_spec` is proved as stated below
  (`WideIxa.lean`).
- `WideIxa.stageOf_spec : stageOf pkg cfg = .ok st → st.units = st.chips.map
  (unitAirI pkg.idOf) ∧ st.maps = mapAirs st.claims (mapRows st.claims) ∧
  st.roms = romAirs cfg.rom`. The PLONK checker replaces the map matrices by
  array-backed ones (`Plonk.mapAirsArr_eq`) and needs `st.maps` in that form.
- Interpreted (`lean --run`), `stageOf` on the L3 terminal
  (`compress-final-narrow-l3.ixa`, 157 chips) did not return within 10 min,
  while decoding takes 8 s and `pkg.claims` is immediate; the validation pass
  (probably `checkEnables`) dominates. A `stageOf` split into construction
  and a separate `Stage.validate` would let interpreted drivers build the
  tables and run the validation compiled.

The executable over the same API:


`wide_export input.json layout.json fixed.bin` writes the circuits of
`WideStage.wide_heap_sound` for an untiled stage, BN254 or Goldilocks:

```json
{ "format": "ix-wide-input-1", "field": "bn254" | "goldilocks",
  "artifact": "path.ixa",
  "circuits": [ { "chip": name | "chip_index": i, "cap": rows }, … ],
  "rom": [ [words, capacity], … ], "entry": name,
  "all_maps": false, "pow2": false }
```

Output `ix-wide-layout-1`: `tables`, in `stageLedger` order — units (`kind
"unit"`, `chip`, `chip_index`, `rows` = cap, `circuit` = `IChip.lower`, no
fixed columns), then map tables (`kind "map"`, one per claim length `length`,
`claims`, `rows` = next power of two of `claims`, circuit `mapCircuit L`:
main `mult` (var 0), fixed `sel` (var 1) and cells (vars `2 … L + 1`), lookup
`push(−sel·mult, cells)`), then ROM tables (`kind "rom"`, `words`, `rows` =
capacity, circuit `romCircuit w`: main `mult` and `w` words, fixed `addr` =
row index, lookup `push(−mult, [2, w, addr, words…])`); `request`; `bound`.
`fixed.bin` holds one `IXTLFX01` block per map and ROM table, in table order.
Every table's trace must have exactly `rows` rows: the theorem's ledger sums
rows `< rows` only. Grouped chips are not covered; a stage proved this way
runs its chips ungrouped.

### Entry point

One theorem per stage shape, all ending in `EvalFn ∧ Represents` with the
ROM the trace holds:

| Stage | Theorem | Exporter |
|---|---|---|
| Tiled narrow (BN3, L3) | `Periodic.narrow_heap_sound_compact` | `tiling_export2` (input 2, with `tables.bin`) |
| Mixed narrow/wide | `Periodic.mixed_heap_sound` (`PeriodicMixed.lean`); `IWideUnit`/`checkMixedI` (`MixedIxa.lean`) | `tiling_export2` (input 2 with `"wide"`, with `tables.bin`; Round 3 item 3) |
| Wide (any field) | `WideStage.wide_heap_sound`, `wide_heap_sound_insts` | `wide_export` |
| Goldilocks instances | `Goldilocks.narrow_heap_sound_compact_goldilocks`, `mixed_heap_sound_goldilocks`, `wide_heap_sound_goldilocks`, `wide_heap_sound_insts_goldilocks` (`small` ⇐ `bound ≤ 2^63`, `characteristic` ⇐ `cfg.bits ≤ 24`) | same exporters |
| Static facts discharged | `Compiled.*_compiled` of each theorem above (`shaped`/`context` ⇐ `entryPlain`, `chanIds`, `chanBound`; `Ids.lean`'s `ids_ofChip` for the last two) | same exporters (`Package.checkIds`) |

The exporters decide every checkable hypothesis (layout, tables, request,
enables) and report the size bounds; what remains per theorem is listed in
§4 and in `Goldilocks.lean`'s docstring: the static `shaped`/`context` facts,
the `.ixa` decoding (the trace section is round-trip checked by
`Ixa.decodeChecked`, round 3 item 1; the program section is not), and the STARK's `rows`/`tall`/`balanced`.

`checkEnables` gained `boolLinear` (an enable identical to a one-hot partial
sum or its complement `1 − Σ`, the default match arm): `KzgPackedShape::walk`
in L3 needed it; all 153 L3 chips now pass. `boolEnum` (`boolEnum_sound`) is a
case analysis: `V` = the variables near `e` (its own and those of constraints
sharing one with it) that `boolDirect` certifies, `|V| ≤ 12`, every variable
of `e` in `V`; on each of the `2^|V|` 0/1 assignments satisfying the
constraints over `V` alone, `e` is 0 or 1. It certifies the Goldilocks wrap's
(`compress-wrap-final.ixa`) `StarkVerifier::ood_loop` enables
`v26 + v27 − v22`: with `a = v21 + v22`, `s = v26 + v27`, the constraints
`v21·v22 = 0`, `v26·v27 = 0` and `a·(s − a) = 0` force `s = 1` when
`v22 = 1`. `wide_export` now accepts the wrap: 196 unit, 5 map and 12 ROM
tables, `bound` 1,583,106 (with 1024-row placeholder capacities). Profile
(per-chip timing): 515 of the 519 s were `checkEnables` on
`Blake3::compress` (88 constraints, 225 sends), because `boolDirect`
re-normalizes every constraint on every query (each enable, every variable
near it, every one-hot candidate). `EnablesFast.lean` adds `checkEnablesN`
(constraint normal forms computed once per chip, otherwise the same
definitions) with `@[csimp]` lemmas `Bridge.checkEnables_eq` and
`Ixa.IChip.checkEnables_eq`, so compiled code runs it and no statement
changes. `Graph.ofCircuit` now hash-conses on (operator, child indices)
instead of scanning a list of whole expressions. Wrap: 8.7 min → 3.2 s
(`Blake3::compress` 272 ms); L3 all 153 chips, `all_maps`: 11 s → 3.4 s;
both outputs and `fixed.bin` byte-identical to the previous exporter's.
`tiling_export2` on L3 (input 2): 24.7 s, layout and `tables.bin` identical.

**Round 3 results.**

1. *Decoder trust: round trip, done* (`IxaTrace.lean`). `decodePackage` now
   decodes the whole trace section (`getTrace`: plans with their operations,
   chip records, depth metadata, groups) into `Package.trace : ITrace F`, and
   `pkg.chips`/`pkg.groups` are read from it. `Ixa.decodeChecked modulus
   ZMod.val bytes` additionally re-encodes `pkg.trace` with the compiler's own
   pool primitives (`ITrace.write`: `withNodesWithEncoding`,
   `internPolynomial`, `listP`) and rejects unless the result equals the
   file's trace bytes. `putChip_eq` proves `Trace.putChip encode c` is, after
   its two checks, `putIChip encode (IChip.ofChip c)`. `wide_export` and
   `tiling_export2` read artifacts only through `decodeChecked`; the wrap,
   L3 (`narrow-fixed.ixa`) and the L3 input-2 run pass. Chosen over a proof
   of `getChip ∘ putChip = id` because that proof needs every earlier
   section's decoder proved too (the chips' offset depends on them); the round
   trip leaves no trusted decoding code for the trace section. What remains
   is a property, not code: `ITrace.write` is injective (every item is tag- or
   length-prefixed, TagN is bijective, the pool lists distinct nodes in
   first-completion order), and the plan/depth/group mirrors (`putIPlan`,
   `putIDepth`, `putIGroup`) write what `putFunctionOf`/`putDepth`/`putGroup`
   write (`putGroup_eq` and `putDepth_eq` prove the group and depth mirrors
   are the compiler's writers on `IGroup.ofLayout`/`IDepth.of`; the plan
   mirror is proved too, `IxaPlan.lean`: `putFunctionOf_eq` proves
   `putFunctionOf … = do planChecks …; putIPlan encode (IPlan.of …)` under
   `HintsResolve` (every hint step's site indexes `hintPCsOf bytecode`);
   `planChecks` are the compiler's four checks (logical chip, column
   allocation, final chip, hint count). The unresolved-hint throw stays a
   hypothesis because it happens mid-record (moving it changes which error
   wins); `putFunctionOf_fails`/`putFunctionOf_resolves` prove a run without
   it always fails, so `putFunctionOf_ok`: every successful run equals the
   checks-then-`putIPlan` run, bytes and pool. Injectivity of `ITrace.write`
   remains unproved: no Ixon decoder lemma exists (TagN `getNat ∘ nat`,
   UTF-8 strings, `getTy`, wide scalars, list loops over the cursor), the
   pool needs a `Std.HashMap` index invariant relating `internPolynomial`'s
   roots to `getNodes` of the pool bytes, `wide` is not written by the
   section, and the `F` side needs `encode` injective with
   `((encode x : ℕ) : F) = x` and `encode x < modulus`).
   *Program section, done (round 4).* `getPackage` now decodes the whole
   program section into `Package.program : Execution.Export F` (`getProgram`:
   functions with their instructions, enums, the row pool and tables, maps,
   entries with their IO interfaces), and the callables, map claims and
   entries are read from it. `decodeChecked` re-encodes the *whole file* with
   the compiler's own `Artifact.putPackageWithEncoding` (program section by
   `Export.putProgramWithEncoding` itself, no mirror) and the trace by
   `ITrace.write`, and rejects unless the bytes equal the file. Passes on the
   wrap and L3; exporter outputs unchanged. The injectivity of the encoding is
   not proved (a proof is a decoder-left-inverse argument over TagN, UTF-8
   strings, `getTy` and the pool; not attempted).
2. *`shaped`/`context`: done by the compiler route (round 5,
   `Compiled.lean`).* `Physical.Prepared` gained two compile-time
   certificates, checked by `Physical.prepare`: `faithful` (every
   deduplicated chip is the renamed erased chip of its name; the dedup
   certificate alone pins only the chips renaming reaches) and `mapShaped`
   (`MapShaped`: every map claim has the `mapShape` — declared parameter and
   result types with layout widths — of a map declared on its channel, and
   every call to a declared map has that shape; linear in claims). Both pass
   on the trace tests' programs (`target/tiling-compare/probe/prepare_check.lean`:
   three configurations and the `ZMod 2` program). Proved from them:
   `Compiled.shaped_of_compiled` (`Shaped` of `Depth.system cfg
   prepared.system` over `plan.singles`: `calls` via `prepared_call`
   (Compatible word counts through erasure, dedup and the depth word, with
   `slotOK`), `maps`/`rootMaps` via `depth_claim` (a depth map claim is a
   source claim or a range claim of shape `([field], ())`) and `mapShaped`,
   `rootChip`, `memory`), and `Compiled.context_of_compiled`
   (`compileChip_wellFormed`, `system_wellFormed`, packed root decoding).
   Remaining hypotheses: `entryPlain : cfg.recursive name = false` (read
   off the trace's depth flags) and `ids`/`idBound` (injectivity and bound of
   `idOf` on channel names); `entryChip` is proved (round 6). The `_compiled`
   corollaries of every entry-point theorem are in `Compiled.lean` (round 6).
   The version-4 chip record below is no longer needed.
   *Previous analysis:* `Shaped` compares
   `Erasure.shape w = (w.type, |w.words|)` of every send argument and result
   with the callee's `Erasure.signature`; the trace section stores only the
   words, and the program section's `Ty` signatures say what the callee
   declares, not what each send passes. Deriving `calls`/`maps` from them would
   need a compiler theorem (every depth chip's send wires have the callee's
   declared types), which does not exist; `checkContext` needs every source
   (pre-activation) chip `wellFormed`, and the file holds the activated chips.
   So option (b) is required: **chip record version 4**, for the Rust agent:
   trace plan version `4` (field after the magic of the trace section, today
   `3`); each chip record gains, after the depth metadata, a *type block*
   `source_num_vars : nat; inputs : list(ty); output : ty; sends : list
   (args : list(ty), result : ty); memory : list(ty)` in `putTy` encoding
   (`0` field, `1` tuple+list, `2` ptr, `3` enum+string), where each `ty` is
   the `WireValue.type` of the corresponding wire, in the record's order.
   **The Rust reader must accept plan version 4 and skip the type block**
   (read and discard: `nat`, then the four lists, recursing on `ty` tags); it
   carries no data Rust needs. Lean side then: the writer emits it under an
   opt-in flag, `getTrace` reads it into `IChip.types`, `IChip.ofChip` fills
   it, `Shaped.check` and the `wellFormed` half of `checkContext` get
   `IChip`-level versions proved equal on `ofChip`, and the exporters run
   them. Do not turn the flag on before the Rust reader skips the block.
   *Compiler-side route (round 4 investigation).* There is no theorem that
   the depth system's sends are well-typed against callee signatures, but
   most of `Shaped` is structural: `Physical.Prepared.compatible :
   Erasure.Compatible artifact.system` (call shapes equal callee signatures in
   the typed system), and the physical system is `Erasure.system` of it, in
   which every chip input, output, dynamic send and memory value is
   `Erasure.pack words` (type `tuple (replicate n field)`), and
   `Depth.compileChip` only appends `⟨.field, [v]⟩` depth words (recursive
   chips; the depth record's `column`). So `calls`, `rootChip` and `memory`
   are determined by the flattened word counts plus the depth flags, and are
   provable without a format change given lemmas that `Dedup` (the merge in
   `Prepared.merged`) and `Depth.system` preserve this packed form; `ids` and
   `idBound` are name checks. Not structural: `maps`/`rootMaps` (sends to
   *maps* keep their source types under `Erasure.send`, and `Compatible`
   covers only chip targets; needs a compiler lemma that a map call's argument
   types are the map's declared `params`, which the program section carries),
   and the `wellFormed` half of `checkContext` for the source chips (available
   in the compiler: `Artifact.wellFormed`, `Erasure.chip_wellFormed`,
   `Chip.rename_wellFormed`, `compileChip_*`; needs composing through `Dedup`
   and `Depth.system`). Recommendation: take this route (no format change);
   keep the version-4 record only as a fallback. If the fallback is used, the
   one Rust reader change is: accept trace plan version `4` and, after each
   chip record's depth metadata, read and discard the type block described
   above.
3. *Mixed exporter: done.* `MixedIxa.lean`: `IWideUnit`, `IWideUnit.circuit`,
   `check`, `mixedSigsI`, `checkMixedI`, with `circuit_ofUnit`,
   `looks_ofUnit`, `checkMixedI_ofUnit` (equal to `WideUnit.circuit`,
   `checkMixed` for `ofUnit`). `tiling_export2` input 2 takes an optional
   `"wide": [{"chip"|"chip_index", "cap"}…]` (compact mode only): the
   `circuits` are tiled as today; unit `t` gets `keyBase` = the narrow
   instance count plus the caps of units `< t`. Wide-only channels: **cap-0
   carrier templates**, not extended `Buses` — `WLook.check` needs
   `S.system.arityAt`/`roleOf` of every row key, which only template messages
   give, and `wideEq`/`chipsIn` need every template to be `unitCircuit` of a
   plan chip, so a carrier is an artifact chip (`chooseCarriers`: one with a
   lookup on the channel, not laid out wide preferred, never one whose receive
   is a chunked wide receive) lowered with capacity 0 and appended to
   `circuits`. Map claims, ROM widths and `checkEnables` cover carriers and
   units; `checkMixedI` must accept; `mixedLookups`/`mixedPartCount` are added
   to the `lookups`/`parts` bounds and `capacityRows + mixedRows ≤ 2^39` is
   checked. Output adds `wide_units` (`chip`, `chip_index`, `key_base`, `cap`,
   `circuit`: `IWideUnit.circuit` graph, fixed column 0 = row id
   `key_base + r`) and `mixed` (`rows`, `lookups`, `parts`, `carriers` =
   positions in `circuits`, cap 0). Without `"wide"` or with `[]`: L3 layout
   (minus `ms`) and `tables.bin` byte-identical to the previous exporter's
   (23.6 s). Tests on `narrow-fixed.ixa`: caps ≤ 2 with `UInt64::is_zero`
   wide (chunked receive, no carrier) and with `KzgPcsPacked::pow_u32` +
   `pow_byte` wide (carrier `pow_u32`), and full L3 caps with those three
   chips wide (112 rows, 520 lookups, 632 parts, carrier `pow_u32`): all
   accepted by `checkMixedI`, ~24.5 s each. Keeping `pow_byte` narrow while
   also wide (chunked receive with an in-system receiver) is rejected.
4. *Grouped chips: not needed.* No stage of `aiur-compression-stage-study.md` runs
   grouped circuits under the Lean theorems: L3 and the wrap export
   ungrouped (`wide_export`, `tiling_export2` read `plan.singles` only).

**Round 6 results.**

1. *`Physical.Prepared.faithful`/`mapShaped` validated on real programs.*
   The two compile-time checks round 5 added to `Physical.prepare` (the
   existing compiler) only add a `throw`; on success `prepare` returns the
   same `merged` system as before (the new fields are `Prop`s), so compiled
   output cannot change. `lake build Aiur Aiur.Optimized.EndToEnd
   Aiur.Optimized.Depth.EndToEnd` (official 4.34.1 toolchain) succeeds,
   `Audit.lean`'s pinned axiom messages included. Every program compiled
   through `prepare` passes both checks: the fixture gate
   (`tools/check-aiur-compression-fixtures.sh`, `--check`: every fixture
   byte-identical for every fixture the gate reached; the gate's cargo step
   stops on the worktree's out-of-date `Cargo.lock` under `--locked`, so the
   Lean checks after it were run by hand) and the four L3 stage compiles:
   `compress_narrow_fixed_export` (`narrow-fixed.ixa`),
   `compress_final_narrow_export` (`compress-final-narrow-l3.ixa`) and
   `compress_gl_export` (`target/compress-gl/compress-gl.ixa`) reproduce the
   pipeline's artifacts byte for byte; `stark-export export-trace
   --compress-wrap` compiles (the wrap policy packages under
   `target/wrap-normalized/policies/` come from another writer and were not
   compared).
2. *`_compiled` corollaries* (`Compiled.lean`). `static_of_compiled` gives
   `Shaped.check … = true ∧ checkContext … = .ok ()` from the compiled
   artifact, `entryPlain` and the two channel-id facts (`chanIds`,
   `chanBound`). With it: `Compiled.narrow_heap_sound_compact_compiled`,
   `mixed_heap_sound_compiled`, `wide_heap_sound_compiled`,
   `wide_heap_sound_insts_compiled` and the Goldilocks
   `narrow_heap_sound_compact_goldilocks_compiled`,
   `mixed_heap_sound_goldilocks_compiled`, `wide_heap_sound_goldilocks_compiled`,
   `wide_heap_sound_insts_goldilocks_compiled`: each is its theorem with
   `shaped`/`context` replaced by `entryPlain`, `chanIds`, `chanBound`
   (Compiled's file now imports `Goldilocks`). All depend only on `propext`,
   `Classical.choice`, `Quot.sound`
   (`target/tiling-compare/probe/compiled2_ax.lean`).
3. *`entryChip` proved.* `Compiled.compile_entry_function`: `compile`
   rejects an entry without a function (its entry loop, via
   `forIn_yield_ok`); `compile_entry_chip`: that function's chip is in
   `unmerged` (`compile_find_function`), and the deduplication certificate
   maps it to a chip of `artifact.system` under the entry's own name (entries
   are fixed by `rename`). `wide_heap_sound_compiled` lost its `entryChip`
   hypothesis.
4. *`IChip`-level channel ids* (`Ids.lean`). `Ixa.checkIds callables bound
   names` (every name a callable, `|callables| ≤ bound`) implies injectivity
   and the bound of `callables.idxOf` on `names` (`checkIds_sound`; no
   `Nodup` needed: `callables[idxOf x] = x`). `IChip.channels` lists the
   written chips' names and send channels, given claim channels and the
   root; `channels_ofChip`/`ids_ofChip` cover `Bridge.channels source chips
   root` for `chips ⊆ all`, checked on `all.map IChip.ofChip`, given
   `claimsIn : ∀ mc ∈ source.mapClaims, mc.channel ∈ claims`.
   `Package.checkIds` runs it on every chip of the package with the
   package's map names; `tiling_export2` (input 2) and `wide_export` reject
   unless it accepts. `claimsIn` (the depth system's map claim channels are
   the package's maps, range tables included) is a fact about the decoded
   program section, like the rest of the decoder trust. L3 narrow
   (`narrow-fixed.ixa`) and terminal (`compress-final-narrow-l3.ixa`) pass;
   layout, `fixed.bin` and `tables.bin` are byte-identical to the cached
   production exports.
5. *Mixed exporter: one layout per chip.* `tiling_export2` rejects a
   `"wide"` chip that is also in `circuits`, and a chip listed twice in
   `"wide"`. Carriers (capacity-0 templates chosen by `chooseCarriers`,
   possibly of a wide chip) have no rows and are not affected. Tested on
   `narrow-fixed.ixa`: `UInt64::is_zero` in both lists and twice in `wide`
   rejected; moved to `wide` (cap 6) accepted (`checkMixedI`).
6. *Differential harness off `lower.rs`.* `harness/rust2` (the v2 test,
   `run2.sh`) took `CALL`, `ROM`, `CHUNK_STRIDE` and `canonical` from the
   deleted `template/lower.rs`; its `build.rs` now extracts them from
   `template.rs` (the parent module `v2.rs` imports them from) into
   `OUT_DIR/base.rs`, so the harness compiles again against the live
   `template/v2.rs` lowering, which is the Rust code that consumes Lean
   output today (`Backend::from_lean` lowers the exported graphs with it and
   `adopt_lean` requires every template to equal Lean's). The v1 comparison
   (`run.sh` against `harness/rust`, the v1 prototype `lower.rs`) is retired:
   there is no v1 Rust consumer left. `run.sh` now runs only the Lean-side
   `sys.lean` checks; `run2.sh` replaces the Rust comparison. Rerun after
   the change: 0 mismatches in all six settings (294/280/293/286/296/291
   identical, all `Sharded.check`-accepted), BN proxy 167/167.

**Round 7 results.**

1. *`claimsIn` reduced to map names.* `Compiled.depth_claim_channel`: every
   map claim of `Depth.system cfg prepared.system` is on a map of the
   compiled program (`compiled.inlined.program.maps`, through the dedup
   certificate's `mapClaims` equality and `compile_stages`) or on
   `rangeName w` for a depth limb `w` (`claim_channel`, `Fresh`).
   `claimsIn_of_maps` turns that into `claimsIn` for any `claims` containing
   those names. The exporters now also run `Package.checkRanges` (every
   `rangeName w`, `w ∈ pkg.limbs`, is a package map; `checkRanges_spec`).
   What remains is that the package's map names and limbs are the compiler's
   (`program.maps` names ⊆ `pkg.mapNames`, `pkg.limbs = cfg.limbs`). This is
   the injectivity gap of the round trip, not something the round trip
   proves: `decodeChecked` shows `encode (decode bytes) = bytes`, and to
   conclude `decode bytes = exported` it needs the writer to be injective.
   That cannot be proved as the writer stands: `putTy`/`getTy` are `partial`
   (no equations to reason with), and the program section's maps come from
   the execution export (`exportExecution`, then `depthBytecode`), which no
   theorem relates to `inlined.program.maps`. Closing it needs (a) total
   `putTy`/`getTy` with a left-inverse lemma for the TagN, string and list
   primitives, and (b) a lemma, or a check in `exportPreparedPlanWithEncoding`,
   that `original.maps` names are `program.maps` names.
2. *`entryPlain` checked.* It is not a consequence of `compile`, since an entry
   may be a recursive function. `Package.checkEntryPlain` requires the entry's
   trace depth record to have no depth column. `Ixa.recursive_of_column`:
   `(IDepth.of cfg c).column = none → cfg.recursive c.name = false`, and
   `putDepth_eq` makes `IDepth.of` what the compiler writes (the trace
   section is round-trip checked, so the same injectivity gap applies). Both
   exporters run it; L3 narrow and terminal pass, and their outputs are
   still byte-identical to the cached exports.
3. *Carriers are never wide chips.* `chooseCarriers` only considers chips not
   laid out wide. Tests on `narrow-fixed.ixa`: `pow_u32` + `pow_byte` wide
   (formerly carried by `pow_u32` itself) and `pow_u32` alone wide are now
   rejected ("no chip can carry channel (1, 157)"), because only `pow_u32`'s
   own template carries its receive's row keys. `pow_byte` alone wide and
   `UInt64::is_zero` wide are accepted (no carrier needed).
4. *Wrap policy package.* `target/wrap-normalized/policies/m16384w64.ixa`
   is `compileCompressWrapPackage` with the groups of `m16384w64.policy.json`
   (`target/root-width/wx/WrapPolicy.lean`). Relinked against the current
   build (its C compiled with Lake's flags, linked with `stark-export`'s
   response file with `Main` replaced), the current compiler reproduces it
   byte for byte (3,104,590 bytes, 246 s). With round 6 this closes the L3
   compile check: wrap, GL, narrow and terminal all reproduce their
   artifacts.
5. *Fixture gate*: run in full, end to end, in `--check` mode after the
   `Cargo.lock` restore. It passes (exit 0), cargo examples and the
   `cmp` steps included.

**Round 8: the Rust consumer's requests.**

1. *Exporter time: not a regression of the current exporters.* The
   1,130 s / 559–735 s measurements come from the snapshot binaries in
   `target/e2e-l3/artifacts/bin/` (copied 20:41:46, before the
   `EnablesFast` build). On the same inputs, the current builds take: the
   terminal `wide_export` (157 chips, `all_maps`) 3 s, against more than
   150 s for the snapshot, which was killed at the 150 s timeout. The L3
   `tiling_export2` format 2 (153 chips, compact tables) takes 32 s. Both
   include `decodeChecked`, `checkEnablesN`, `checkIds`, `checkRanges` and
   `checkEntryPlain`. The outputs are byte-identical to the cached exports.
   Fix: refresh the snapshots (`cp MultiStark/.lake/build/bin/{tiling_export2,wide_export}
   target/e2e-l3/artifacts/bin/`); the caches are keyed by the exporter
   binary, so the next run re-exports once.
2. *Selector-free map tables: done* (`MapPad.lean`). `mapCircuitD L`: main
   `mult` (var 0), fixed cells (vars `1 … L`), lookup `push(−mult, cells)`,
   with no `sel`. Padding rows repeat the table's last claim (`padRow`,
   `mapFixedD`), so every row's tuple is a claim (`mapAirD_support`; every
   table of `mapAirsD` is non-empty, `claimsOf_ne_nil`).
   `WideStage.wide_heap_sound_dup` and `wide_heap_sound_insts_dup` are the
   wide theorems with `mapAirsD` in `balanced` (axioms: `propext`,
   `Classical.choice`, `Quot.sound`). The prover sets each padding row's
   `mult` to 0, or uses it to absorb lookups of that claim. `wide_export`
   gains `"map_padding": "repeat"`: the map tables are then `mapAirsD` with
   the same row counts (`"padding": "repeat"` in the layout), and the writer
   is compared with `mapFixedD` on the first rows and the first padding
   rows. On the L3 terminal: 9 map tables, all accepted. Without the flag the
   output is byte-identical to the cached export.
3. *Grouped circuits (CompressGL): not started.* Plan: `Bridge.lowerGroup`
   of a `Grouping.Packed` group (the checked group circuit: shared columns,
   per-member selector, member writes, `IGroup` in the trace) as a
   `Tiling.Circuit`, and a `Wide` variant whose instances are group rows,
   each of which decodes to one member's single-chip row. That is the step
   `grouped_activated_heap_sound` already proves for the trace checker, so
   the theorem should follow by composing `Wide.checkMemo` with that
   decoding, instead of `plan.singles` only. Then `IGroup.lower` with
   `lower_ofGroup` (as `IChip.lower_ofChip`), and `wide_export` accepting
   `"group"` entries.
4. *The wrap is not rejected by the current exporter.* The current
   `wide_export` accepts `target/wrap-normalized/policies/m16384w64.ixa`
   (all 196 chips, 1024-row placeholder caps, ROM widths 1–128): 196 unit,
   5 map and 128 ROM tables in 3 s, with every check of rounds 6–7. The
   rejection was reported from the snapshot binary, which is older than
   `EnablesFast` (item 1). Earlier exporters rejected the
   `StarkVerifier::ood_loop` enables until `boolEnum`. Refreshing the
   snapshots (item 1) should fix it.

Next: the group lowering (round 8 item 3); the injectivity work of round 7
item 1 (a)–(b).

**Round 9: grouped circuits and shared map tables.**

1. *Group lowering* (`Grouped.lean`). `Grouped.lowerGroup g` is the circuit
   `circuits.rs`/`grouping.rs` build for a trace group: main width
   `g.width + 1` (last column the receive multiplicity), `g.constraints ++
   [(1 − activation)·mult]`, lookups `push(−mult, receive)` then
   `push(enable, args)` per send slot. Group tuples are zero-padded to the
   longest member, so the theorems take the multi-stark balance
   `mapDomain trimZeros (…) = 0`. `group_row`: a group row with activation 0
   has a zero ledger; with activation 1 its trimmed ledger is that of the
   selected member's activated chip at the projected assignment
   (`packet_active`, `messages_ok`). `WideT` is `Bridge.Wide` over such virtual
   rows with the trimmed balance (`WideT.provider`, `WideT.memory_valid`,
   `WideT.checkMemo`); memo rows of members are the group rows, inspected by
   `Plan.inspectRow` through the layout (`group_inspect`).
2. *Theorems.* `grouped_heap_sound_insts` (rows), `grouped_heap_sound`
   (unit, group, map, ROM tables), `grouped_heap_sound_shared` (compiler map
   layout, item 4), `_compiled` versions of both (via
   `Compiled.shaped_of_compiled_on`, `Shaped` over `allChips plan` = singles
   ++ group members), `grouped_heap_sound_goldilocks_compiled`,
   `grouped_heap_sound_bn254_compiled`. Axioms: `propext`, `Classical.choice`,
   `Quot.sound` (`target/tiling-compare/probe/grouped_ax.lean`). New
   hypotheses beyond the wide theorem's: `idOk` (the plan's `id` agrees with
   `idOf`), `names` (circuit names distinct), `romWidths`/`memWidth` (widths
   `< bound`, needed to separate ROM tuples after trimming). With `groups = []`
   these are the wide theorems under the trimmed (multi-stark) balance.
3. *Exporter.* `Ixa.IGroup.lower` (`GroupedIxa.lean`: `lower_ofLayout`
   = `lowerGroup` on what `putGroup` writes); `WideIxa.Config.groups`;
   `stageOf` adds group tables (`gunits`), takes map claims, ROM widths,
   `checkEnables` and the lookup bound over group members too, and checks chip
   and group names distinct. `wide_export` input `"groups": [{"group" |
   "group_index", "cap"}]`; output tables units, groups (`kind "group"`,
   `members`), maps, ROMs. CompressGL (`target/compress-gl/compress-gl.ixa`,
   203 chips, 39 groups covering 174 chips, 29 singles, entry
   `CompressWrap::verify_root`): accepted in 2.8 s. **Compared with Rust**
   (`Compiler::new` of `compress_gl::Wrapper`, linked against the current
   `libix_proof_compression` rlib; scratch program, not in the tree): all 68
   function circuits agree in main width, constraint count and per-constraint
   degree (in order), lookup count, multiplicity degree, arity and per-argument
   degree (totals: width 3,749, constraints 4,986, lookups 1,179, arity
   12,253). No difference. Only the circuit order differs (Rust: layout
   order; Lean: singles then groups). Wrap
   (`m16384w64.ixa`, Goldilocks): accepted, 15 singles + 3 groups (`G_cold0`
   140 members, `G_cold1` 19, `G_mid` 22) = 18 function circuits, not 33;
   not compared with Rust (`grouping.rs` builds the same expressions).
4. *Shared map tables.* `SharedTable` (`fixedWidth`, `maps` = callable id
   and fixed cell columns per map, `rows`, `fixed`): main count column `k`
   per map, lookup `push(−count_k, [CALL, id_k, cells_k(i)])`, no constraints;
   `SharedTable.check claims` (every row's tuple of every map is a claim,
   padding rows repeat a genuine row) gives the support
   (`shared_support`). Not yet emitted by `wide_export` (needs a `HashSet`
   form of `check` with a `csimp`, and the Rust column-sharing layout).

Next: `wide_export` emitting `SharedTable`s in the compiler's layout; a Rust
run of the wrap comparison; then round 7 item 1 (a)–(b): total
`putTy`/`getTy` in `Execution/Encode.lean` (structural recursion on `Ty`;
`getTy` with fuel = remaining bytes, proved equal on success), a
left-inverse lemma for TagN/string/list primitives, and a check in
`exportPreparedPlanWithEncoding` that `original.maps` names are
`program.maps` names, which makes `claimsIn` a theorem. Not started: editing
`Encode.lean` rebuilds most of `Aiur`.

**Round 10.**

1. *Ungrouped exports unchanged.* After the `stageOf` changes, `wide_export`
   on the three cached L3 terminal inputs (`target/e2e-l3/artifacts/wide-cache/*`)
   and on the ungrouped wrap (196 chips) produces the same bytes as the
   pre-grouping snapshot binary (`target/e2e-l3/artifacts/bin/wide_export`,
   22:40). One cache (`e35774…`) also matches byte for byte. The other two
   differ only because their caches were written by older exporters: `b8622f…`
   lacks the round-8 `"padding"` key, and `650fa4…` (`map_padding: repeat`) holds
   selector tables. `bound` is unchanged in all of them.
2. *Shared map tables emitted.* `Grouped.sharedTablesOf pkg` builds the
   compiler's map layout from the decoded program section (`circuits.rs`
   `fixed_tables`): maps grouped by input-table height, height = next power of
   two, fixed column 0 = 1, then one column block per distinct input/output
   table in first-use order, padding rows = row 0, one main count column per
   map, lookup `push(−count_k, [CALL, id_k, cells])`. `wide_export` with
   `"map_layout": "shared"` (needs `all_maps`) writes them (`kind
   "map_shared"`, `maps` = callable and cell columns, `rows`, `real_rows`) and
   rejects unless `SharedTable.checkFast` accepts every table
   (`checkFast_eq`: equal to `check`, via `Std.HashSet.contains_ofList`).
   L3 terminal: 11 tables, 67,957 rows (`UInt8::pair_inputs` 65,536), 50 s.
   **Compared with Rust** (`Compiler::new` on the terminal plan, current
   `libix_proof_compression`; scratch program): all 11 tables agree in main
   width, fixed width, height, every lookup argument (callable constants and
   fixed column indices) and the whole fixed matrix, row for row and column
   for column. The multiplicity is `0 − m_k` in Lean and `−m_k` in Rust, which
   are equal. Neither side has constraints. Not covered: Rust's height-0
   table form (constraint `count = 0`, zero arguments); L3 has none.
3. *Wrap groups vs Rust.* `Backend::new` (Goldilocks, `grouping.rs`) on
   `m16384w64.ixa`: 33 circuits = 18 function circuits (15 singles, groups
   `G_cold0`, `G_cold1`, `G_mid`) + 3 map tables + 12 ROM widths. The 18
   function circuits agree with the `wide_export` groups/units in main width
   and lookup count (only `statistics()` is public there; per-constraint
   degrees were compared for CompressGL only). CompressGL was re-run against
   the freshly built rlib: still identical.
4. *`putTy`/`getTy` total; type codec round trip* (`Execution/Encode.lean`,
   `Execution/TyCodec.lean`). `putTy` uses well-founded recursion
   (`list items.attach`), and `getTy` is `getTyAux (remaining + 1)` (fuel;
   every level reads a tag byte). Same bytes as before. `getTy_putTy`: on a
   buffer `putTy t` wrote, `getTy` from the old end returns `t` and stops at the
   new end. `putTy_inj` follows. Both hold for `TyShort t` (every list length
   and name size `< 16,859,264`, the 1–4-byte TagN rungs). Pieces:
   `getNat_reads` (TagN), `getString_reads` (UTF-8 via `String.isValidUTF8`),
   `getArray_reads` (count check and `for` loop), and the writer lemmas
   `nat_writes`, `str_writes`, `list_writes`, `putTy_writes`. Axioms:
   `propext`, `Classical.choice`, `Quot.sound`. The 5- and 9-byte TagN rungs
   hit a kernel deep-recursion limit on the case proof and are not covered
   yet. `lake build Aiur Aiur.Optimized.EndToEnd Aiur.Optimized.Depth.EndToEnd`
   passes after the change, and so does the fixture gate
   (`tools/check-aiur-compression-fixtures.sh --check`, exit 0, every `cmp` step included).
   *`claimsIn` is still a hypothesis.* What remains is the left inverse of the
   whole program section, `getProgram (putProgram x) = x`: functions,
   instructions, enums, row pool, tables, maps, entries, with `putIOType`
   (still `partial`). The type codec is its first piece; maps also need
   `str`/`nat` (done). Then `decodeChecked` gives `pkg.program = exported`,
   and a check that `exported.maps` names are `program.maps` names (or a
   lemma about `depthBytecode`) closes `claimsIn`.

**Round 11.**

1. *`putIOType`/`getIOType` total.* `putIOType` (`Encode.lean`) uses
   well-founded recursion over `attach`ed lists. `Ixa.getIOType` is
   `getIOTypeAux (remaining + 1)`. No `partial` is left in `Encode.lean` or
   `Ixa.lean`. After the change:
   - `lake build Aiur Aiur.Optimized.EndToEnd Aiur.Optimized.Depth.EndToEnd
     wide_export tiling_export2` passes;
   - the L3 terminal export (`e35774…`) is byte-identical;
   - CompressGL (still 0 diffs vs Rust) and the wrap export unchanged.
2. *Wrap degrees, Lean side.* For all 18 wrap function circuits, Rust's
   `statistics().quotient_degree` equals `nextPow2(max(c, 2) − 1)` for the
   exported circuit's maximum constraint degree `c`, and the exported lookup
   degrees (≤ 2) do not raise it. Per-constraint degrees themselves are not
   public in the Goldilocks backend. `grouping.rs` builds the same
   expressions as `circuits.rs`, which matches per constraint on CompressGL.
3. *Not done:*
   - The program-section left inverse.
   - Lifting the TagN `< 16,859,264` bound: the 5- and 9-byte rung proofs
     hit kernel deep recursion; next try is a generic lemma over the rung's
     constants instead of literal case proofs.

   Plan for `claimsIn`, in order:
   - (a) `getIOType` reads `putIOType`, as `getTy_putTy`.
   - (b) Scalars: `putScalar`/`getScalar` for narrow and wide encodings.
     `getScalar` reads `encode x` and casts back to `x`; this needs
     `((encode x : ℕ) : F) = x` and `encode x < modulus`.
   - (c) `getInstruction` reads `putInstructionWith`: 14 tags, using `nats`,
     `getTests` and `str`.
   - (d) Functions, enums, `rowPool` (tables by row references: the pool
     lists distinct rows, `refs` index it) and maps.
   - (e) Entries, then `getProgram_putProgram`. With `decodeChecked` this
     gives `pkg.program = exported`.
   - (f) A check in `exportPreparedPlanWithEncoding` that `exported` map
     names cover `inlined.program.maps` names and range maps. This changes
     compiler output only by a `throw`; rerun the fixture gate after it.
   Then `claimsIn_of_maps` discharges `claimsIn`.

**Round 12.** `claimsIn` is a theorem.

1. *TagN without the size bound* (`Execution/TyCodec.lean`). `getNat_reads`
   covers every rung (`n < 2 ^ 64`, which `nat` itself checks). Each
   multi-byte rung is one instance of `rung_reads`, a lemma over the rung's
   head byte, base and width (`RungStep 192 16512 2` … `RungStep 195
   4311826560 8`), so no literal case proof unfolds `leB` or the reader; the
   kernel recursion limit is gone. `TyShort`, `getString_reads` and
   `getArray_reads` take `< 2 ^ 64`.
2. *Program-section left inverse* (`Tiling/IxaProgram.lean`). `RT p g x`: every
   successful run of the writer `p` appends bytes that `g` reads as `x`,
   whatever follows; success carries the TagN bounds, so there are no size
   hypotheses. In order:
   - (a) `rt1_ty`, `rt1_ioType` (fuel readers through `RTF`, `rtf_tagged`,
     `reads_remaining`);
   - (b) scalars: `rt1_narrow`, `rt1_putWideNat`/`rt1_wide` (limbs by
     `wideLimbs_spec`, loop by `wideLoop_reads`), `rt1_modulus`; the cast back
     needs `((encode x : ℕ) : F) = x` and `encode x < modulus`
     (`Claims.zmod_val_encodes` for `ZMod.val`);
   - (c) `rt1_instruction`, all 14 tags, over any `ScalarCodec`;
   - (d) functions, enums, maps; the row pool by `rowPool_spec` (the `j`-th
     reference list looks up the `j`-th table's rows; every pool row occurs in
     a table, so the decoder's `< modulus` check passes);
   - (e) entries, then `program_rt`: `getProgram (encoding == .wide) modulus`
     reads back `{ bytecode := exported.bytecode, interfaces := entries'
     interfaces }`. `program_of_decode`: bytes from
     `Artifact.putPackageWithEncoding` that `decodePackage` accepts carry
     `pkg.program.bytecode = exported.bytecode` (`decode_program` follows
     `getPackage` past magic and version).
3. *(f) Map-name check.* `Trace.exportPreparedPlanWithEncoding` is now
   `exportBytecode` (the old prefix checks, `depthConfig`, and a new `throw`
   unless every `program.maps` name is an `exported.bytecode.maps` name) then
   `exportTraceSection` (unchanged body); same throws in the same order, same
   bytes. `Package.mapNames` is the decoded program's map names (equal to the
   old callable lookup on every decoded package).
4. *`claimsIn` closed* (`Tiling/Claims.lean`). `exportPrepared_spec` and
   `depthBytecode_maps` give the program maps and every `rangeName w`,
   `w ∈ cfg.limbs`, among the package bytecode's maps; with
   `program_of_decode` and `Compiled.claimsIn_of_maps`,
   `claimsIn_of_export` holds for `claims = pkg.mapNames`. `ids_of_export`
   adds `ids_ofChip`. `ExportedIds compiled prepared cfg callables bound root`
   bundles the hypotheses (field encoding, `depthConfig = .ok cfg`, the export,
   the package bytes, `decodeChecked`, `checkIds` over
   `(Depth.system …).chips.map IChip.ofChip` with `pkg.mapNames`), and
   `narrow_heap_sound_compact_exported`, `mixed_heap_sound_exported`,
   `wide_heap_sound_insts_exported`, `wide_heap_sound_exported`,
   `grouped_heap_sound_exported`, `grouped_heap_sound_shared_exported` are the
   `_compiled` theorems with `chanIds`/`chanBound` replaced by
   `(hid : idOf = callables.idxOf) (ids : ExportedIds …)`. The `_compiled`
   theorems stay (`Plonk/WideSound.lean` uses them). Axioms: `propext`,
   `Classical.choice`, `Quot.sound`.

5. *Goldilocks/BN254 `_exported` forms* (`Claims.lean`):
   `narrow_heap_sound_compact_goldilocks_exported`,
   `mixed_heap_sound_goldilocks_exported`,
   `wide_heap_sound_insts_goldilocks_exported`,
   `wide_heap_sound_goldilocks_exported`,
   `grouped_heap_sound_goldilocks_exported`, `grouped_heap_sound_bn254_exported`.

**Round 13 (done): the trace-section left inverse.** Goal: make
`checkIds_of_package`'s equality `pkg.chips.toList = (Depth.system cfg
prepared.system).chips.map IChip.ofChip` (and `pkg.limbs = cfg.limbs`) a
theorem, so that the `_exported` theorems can take `pkg.checkIds bound
root.channel` directly. Plan:

- (a) *Done.* `NodesGood enc m E s` (pool `s` has `E.size` nodes, per-node
  `NodeBytes` that `getNodes` reads as `E`, every `index` key `k ↦ i` has
  `E[i] = nodeExpr E k` with operands before `i`). `node_run` computes
  `NodePool.node tag a b s buf` (UInt64 check, then index lookup, then
  `Ixon.run putNode 40`; proved by case-splitting first, `generalize Ixon.run _
  40 = r` in the miss case); `node_spec`: a successful node step leaves the
  buffer unchanged and extends `E` to a good pool whose node `i` is the key.
- (b) *Done.* `intern_spec` (by induction; `Holds E i p` survives `Ext`).
  `RTP ne enc m p G x` (pool writer `p` from a good `E` ends at a good
  `E' ⊒ E`, appends bytes, nonempty if `ne`, that `G Ef` reads as `x` for every
  `Ef ⊒ E'`) with `rtp_bind`/`rtp_cons`/`rtp_then`/`rtp_map`/`rtp_skip`/
  `rtp_lift`/`rtp_unless`/`rtp_listP`/`rtp_arrayP`; `rtp_poly` (putPolynomial
  vs `getPoly`). `RTE` is `RTP` with the value existential (fixed by the run),
  with the same combinators plus `rte_consp`/`rte_tagged` (exact value for a
  tag, then untracked), `rte_pure_bind` (a check-only writer step such as
  `ofExcept`), `rte_pure_seq`/`rte_throw_seq` (for `unless` after `dsimp only`
  inlines the join points: `iterate 4 (split; rotate_left; exact rte_throw_seq;
  refine rte_pure_seq ?_)`).
- (c) *Done.* `rtp_chip` (`putIChip` vs `getChipRecord`, given `width =
  activation + 1`), `rt1_depth` (`putIDepth` vs `getIDepth` for
  `IDepth.Valid`; `depth_valid` for `IDepth.of`), `rte_op` (all 8 tags),
  `rte_plan` (`putFunctionOf` vs `getIPlan`, section `Plans` over `[Field F]`
  to avoid the `NatCast` diamond), `rte_group` (`putIGroup` vs `getIGroup`).
- (d) *Done* (`IxaTraceCodec.lean`). `loop_idx_reads`/`loop_run`,
  `getNodes_reads` (`NodesGood` and `E.size < 2 ^ 64` give `Reads getNodes
  (tagBytes E.size ++ s.bytes) E`), `nodesGood_empty`, `rtp_putChip`,
  `rtp_chips` (the chip list reads back as `pairs.map fun (c, src) =>
  (IChip.ofChip c, IDepth.of cfg src)`). Then:
  3. the plan list: `rte_listP`, `split` on the inlined `unless`
     (`rte_pure_seq`/`rte_throw_seq`), `cases replays`, `rte_pure_bind
     (ofExcept_pool _)`, `rte_plan`; the group list: `rte_listP`, `putGroup_eq`,
     `rte_group`;
  4. `withNodes_ok` (a successful `withNodesWithEncoding` ran its body from
     the empty pool and buffer and wrote `tagBytes count ++ pool ++ body`),
     `body_reads` (the three lists over the final pool: RTE; RTP; RTE),
     `trace_reads` (`getTrace` over the whole section, chips and limbs exact);
  5. `section_reads`: a successful `exportTraceSection` (peeled with
     `except_bind_ok'`; `dsimp only` inlines the group loop's result match and
     the `WellFormedActivation` join point) reads back with `t.chips =
     (system.chips.zip physical.system.chips).map …`.
- (e) *Done.* `decode_chips` follows `getPackage` past the program section,
  the option byte (`reads_some_unit`), `get` and `getTrace` to `pkg.chips =
  (t.chips.map (·.1)).toArray`; `chips_of_decode` lays the bytes out as
  `program_of_decode` does. `Claims.chips_of_export` combines them with
  `exportBytecode_spec` and the zip length (`Depth.system` maps the chips):
  `pkg.chips.toList = (Depth.system cfg prepared.system).chips.map
  IChip.ofChip`. `checkIds_of_package` now takes the export, the package bytes
  and `decodeChecked` instead of that equality, and `ExportedIds`' last
  conjunct is `callables = pkg.callables.toList ∧ pkg.checkIds bound
  root.channel = true` (the `_exported` signatures are unchanged).
  `trace_reads`, `section_reads` and `decode_chips` also carry the limbs, and
  `Claims.limbs_of_export` gives `pkg.limbs = cfg.limbs`. Axioms: `propext`, `Classical.choice`, `Quot.sound`. No compiler code
  changed, so the export bytes are unchanged.

### `wide_export` options (stable interface)

Input `ix-wide-input-1`:

| Key | Values | Meaning |
|---|---|---|
| `field` | `bn254`, `goldilocks` | modulus |
| `artifact` | path | `.ixa`, read with `decodeChecked` |
| `circuits` | `[{chip | chip_index, cap}]` | single chips, `IChip.lower` |
| `groups` | `[{group | group_index, cap}]` (optional) | trace groups, `IGroup.lower` = `Grouped.lowerGroup` |
| `rom` | `[[words, cap]]` | ROM tables, `romCircuit` |
| `entry` | chip name | request `[CALL, id, 0…]`; default first circuit |
| `all_maps` | bool | keep claims of every map |
| `pow2` | bool | require power-of-two row counts |
| `map_padding` | `"repeat"` | selector-free `mapAirsD` (`wide_heap_sound_dup`) |
| `map_layout` | `"shared"` (needs `all_maps`) | compiler-layout `SharedTable`s (`grouped_heap_sound_shared`); overrides `map_padding` |

Output `ix-wide-layout-1`: `tables` in ledger order:
- units (`kind "unit"`);
- groups (`kind "group"`, `group`, `group_index`, `members`, `rows`, `circuit`:
  main width `width+1`, constraints then `(1 − activation)·mult`, lookups
  receive pull then sends);
- maps (`"map"`, or `"map_shared"` with `maps: [{callable, cells}]`,
  `rows`, `real_rows`, `padding "repeat-row-0"`);
- ROMs (`"rom"`).

Also written: `request`, `bound`. `fixed.bin` holds one `IXTLFX01` block per
map/shared and ROM table, in table order. The theorems take the multi-stark
balance (`mapDomain trimZeros`). Rust may order circuits differently: Lean
writes singles first, then groups.

### Remaining non-Lean pieces

- ~~The input graphs and map claim tuples from Rust~~ (input format 2);
  ~~the trace decoder~~ (round trip, `decodeChecked`); ~~the program
  section's decoder~~ (`program_of_decode`, round 12); left: the trace
  section writer's injectivity.
- Rust construction of the narrow, table and wide circuit expressions
  (removed by 1a steps 2–3; then Rust only interprets an exported DAG).
- The cryptography layer: STARK, LogUp, PCS, shared fixed-slot openings,
  and the terminal verifier's agreement with the native one.

### Rust consumer status and requests (2026-11-15)

Consumers (`crates/proof-compression`):

- **Narrow stage** (`template/v2/lean.rs`, `aiur_template_v2_init`): writes
  input format 2 (`lean::input2`; artifact path plus `artifact_blake3`, so
  the export cache is keyed by the artifact's contents), lowers the
  exported `circuits[k].wide` graphs (`Backend::from_lean`; Rust's
  `compile_graph` lowering is only a `--rust-cross-check`), and proves the
  exported `narrow_circuits` and `compact_circuits` read literally (Rust's
  `narrow_circuit`/`compact_circuit` are cross-checks only). The format-1
  writer (`lean_input`, `graph_json`) is deleted. On L3: 74 of 153 templates
  differ from the `compile_graph` lowering, `places` 30,593,906; the Rust
  and Lean shard and compact circuits agree at random points.
- **Terminal** (`plonk::sources`, `aiur_narrow_terminal_prove`): the schema's
  157 function circuits are the `wide_export` unit tables and its 13 ROM
  circuits the `romCircuit` tables (`all_maps`, `pow2`, PLONK capacities).
  The unit tables give the same schema nodes and constraints as the Rust
  circuits; the ROM tables remove 89,760 constraint rows.

Requests (Lean side), updated 22:50:

1. ~~Exporter time~~: the slow runs were stale exporter snapshots; current
   builds export the terminal in 3.6 s and the narrow layout in 32 s.
2. **Map tables for PLONK.** `map_padding: "repeat"` (`mapCircuitD`) removes
   the selector, but each table has one row per claim: on the L3 terminal
   the four large tables have 327,699, 131,596, 66,618 and 65,536 claims,
   983,040 rows at powers of two, against the compiler's 67,000 rows, where
   one row of an input table serves every map over it (one count column per
   map). The schema then exceeds the gnark bridge limit (16 MiB) and the
   rows would not fit `2^25`. The terminal therefore keeps the compiler's
   map tables (`aiur_narrow_terminal_prove --lean-maps` takes the Lean ones).
   Wanted: a map table per input table with one count column per map over it
   (`push(−mult_m, [CALL, id_m, in…, out_m…])` per map `m`), fixed cells
   shared, padding rows repeating a row.
3. **Grouped chips.** CompressGL (39 `verifier_group_*` circuits) and the
   Goldilocks wrap (`m16384w64` grouping: 196 chips in 33 circuits, the
   layout and key pinned by `WrapPolicy`) run grouped circuits; `wide_export`
   lays out single chips (196 units for the wrap), so both keep the Rust
   lowering until a group lowering exists. Running either ungrouped would
   change its pinned key and its cost.

