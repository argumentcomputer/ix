# The KZG stage: wrapping the recursive verifier over BLS12-381

Status: PHASE A COMPLETE (crates/aiur generic over `AiurField`,
Goldilocks the only instantiation, all pins byte-identical). Phases B–E
pending. Prerequisites landed earlier: multi-stark `pcs-traits` branch;
the `g_*`/`eg_*` inner-field interface and `GoldilocksForeign.lean` on
this branch.

## 1. Goal and architecture

A third proof stage that ends the recursion with a constant-size,
natively-verifiable proof:

- **Stage 1 (kernel)**: IxVM claims proven by Aiur over Goldilocks,
  FRI PCS. Many proofs, big.
- **Stage 2 (recursive verifier)**: the `multiStark` Aiur toplevel over
  Goldilocks/FRI verifies stage-1 proofs in-circuit. One proof,
  megabytes (query-dominated).
- **Stage 3 (KZG wrap, NEW)**: the same verifier *program*, compiled as
  an Aiur circuit whose **outer field is the BLS12-381 scalar field
  Fr**, proven under multi-stark's `KzgConfig`. It verifies one stage-2
  proof. Inner-field (Goldilocks) arithmetic is emulated via the
  byte-limb `GoldilocksForeign` module. Output: a kilobyte-scale KZG
  proof — one G1 point per column commitment round + a handful of
  witness points, no queries — verified natively in milliseconds
  (2 pairings). KZG is TERMINAL: it is never verified in-circuit
  (BLS12-381 has no efficient outer curve; that is a feature here, not
  a bug — see multi-stark `docs/pcs-abstraction.md`).

Field story: the stage-3 circuit's own arithmetic (constraints,
lookups, logUp) is Fr. The stage-2 proof's Goldilocks arithmetic is
emulated on bytes inside it. Fq (G1 coordinates, pairings) exists only
in the native prover/verifier — never arithmetized anywhere.

## 2. What is actually tied to Goldilocks today (survey)

**Rust (`crates/aiur`)** — one alias each, everything written against
them:

- `lib.rs`: `pub type G = multi_stark::p3_goldilocks::Goldilocks`;
  channel constants are `G::ZERO/ONE/TWO/…`.
- `synthesis.rs`: `pub type AiurConfig = GoldilocksBlake3Config`.
- Real field-specific content is small: `constraints.rs` builds
  `(2^32)⁻¹` (and similar) as Goldilocks constants — recompute
  generically; `vk_codec.rs` writes constants as 8-byte words —
  parametrize the width; the gadget tables (`gadgets/bytes1`,
  `bytes2`, `blake3`) are small-value lookup tables, field-agnostic.
- Bytecode constants are bytes/counters/u64 wire words — they embed
  canonically in any field ≥ 2^64.

**Lean (`Ix/Aiur/Goldilocks.lean`)**: `G = {u : UInt64 // u < gSize}`,
`G.extensionDegree = 2`. Used by the DSL elaborator, the bytecode
interpreter, and witness helpers. This is a REAL structural dependence,
not just hosting: source constants are capped at p_goldilocks (and
`G.ofNat` silently wraps larger literals), and the interpreter's
arithmetic wraps at p. DECIDED: this is the wrong factoring — fixed by
Phase A′ below (constants over ℚ, field chosen at execution), which
supersedes the earlier "out of scope" position.

**The keystone observation**: the foreign toplevel's semantics are
OUTER-FIELD-INDEPENDENT. Every `GoldilocksForeign` operation is
byte-level (u8 gadgets, carry chains, sums < 2^11 that wrap in no
large field), so it computes identical results over Fr and over
Goldilocks itself — that is why the `fg_*` self-tests pass under
today's Goldilocks interpreter. Consequently the ENTIRE foreign
verifier can be developed, executed, and validated on the existing
Goldilocks stack (no Lean interpreter changes); only PROVING needs Fr.

## 3. Phases (each lands green)

### Phase A — genericize `crates/aiur` over the field (behavioral no-op)

Make the config a parameter: `G = Val<SC>` for
`SC: StarkGenericConfig` (multi-stark's crate-owned traits, post
`pcs-traits`), Goldilocks/FRI remaining the only instantiation.
Mechanical for the bulk (`execute.rs`, `trace.rs`, `memory.rs`,
`querymap.rs`, `bytecode.rs` are field-generic in spirit); the known
field-specific spots:

- gadget-internal constants (`(2^32)⁻¹` etc.) — build from
  `G::from_u64(..).inverse()`;
- vk codec constant width (8 bytes → per-field width);
- challenger/transcript binding via the config (already abstract in
  multi-stark);
- `num_publics = 4·D` and stage-2 width derive from the config's
  extension degree (D = 2 today, D = 1 under `KzgConfig` — multi-stark
  already handles D = 1 first-class).

**Gate**: kernel FFT pins + shard pin byte-identical; `ix codegen
--check` clean. Same discipline as multi-stark's Phase 0 — the
refactor is provably a no-op before anything builds on it.

### Phase A′ — Lean constants over ℚ; interpreter parametrized by field

Constants belong to the program, fields to the instantiation:

- **Elaborator**: numeric literals become exact rationals in canonical
  form (reduced fraction, positive denominator; signed integers for
  free — `-1` instead of `0 - x`). Zero denominator is a TYPE ERROR at
  elaboration. `G.ofNat`'s silent mod-p wrap is gone.
- **Bytecode**: `Const ℚ`; match keys ℚ.
- **Interpreter**: generic over a Lean field class
  (`add/mul/inverse/eq/ofRat`), converting constants ON THE FLY
  (memoized per occurrence). Goldilocks is the instance today; an Fr
  instance (Nat-based) is a drop-in later if interpreter-level parity
  checks are ever wanted.
- **Per-field specialization checks**, eager at toplevel load: match
  keys must remain DISTINCT after reduction (two rationals can meet in
  a given field — hard error); denominators must be invertible in the
  target field (`p | b` is fine in ℚ, an error in that field); plain
  integers ≥ p reduce with a WARNING.
- **Rust boundary**: FFI ingestion and codegen run the same
  specialization and emit `Toplevel<F>` / baked `F` constants — the
  Phase-A Rust side is already exactly the post-specialization
  artifact, so nothing downstream of the boundary changes.
- Runtime VALUES in the Lean interpreter are still per-instance field
  elements; "bytecode is field-free" does not mean "execution is".

**Gate**: on all existing programs every constant is a small integer,
so specialization is the identity — codegen byte-identical, full pin
battery, all suites.

### Phase B — the foreign verifier toplevel, validated over Goldilocks

Swap the wire layer onto the inner-field interface and build
`multiStarkForeign`:

- `Deserialize.lean`: `type Ext = [G; 2]` → `[Goldilocks; 2]`; field
  lanes stay bytes (`[U8; 8]`) instead of reducing to native — under
  foreign, a wire limb already IS the representation, so ingest
  (`gl_val`) is one conditional subtraction of p;
- `limb_to_field` call sites (e.g. `ro_fold`) → `@gl_val`;
- challenger egress `gl_to_bytes` = identity (cheaper than native);
  rejection sampling (`gl_lt_p`) unchanged (byte logic);
- `SystemDeserialize` vk-constant ingest → interface-typed (already
  `@gl_val`);
- toplevel: `…merge goldilocksForeign…` in place of
  `goldilocksNative` (same names — exactly one merges, by design).

**Gate**: EXECUTE `multiStarkForeign` under the existing Goldilocks
interpreter against the same vectors the native verifier passes
(factorial stage-2 proof accepted; tampered advice and tampered claim
rejected). Full verifier correctness before any Fr machinery exists.

### Phase C — cost checkpoint + declaration-level inlining

The known risk. Foreign `g_mul` ≈ 64 `u8_mul` + ~150 carry gadgets;
an extension mul is 5 base muls. The verifier performs on the order of
tens of thousands of extension muls (FRI folds and reduced openings
per query per height, the OOD constraint sweep). Spliced at every
`@`-call site (today's call-site inline semantics), that is tens of
millions of gadget lookups in the calling circuits — likely
prohibitive width.

- **DSL change**: make inlining a property of the DECLARATION, not the
  call site (native marks its ops inline — they are trivial; foreign
  leaves `g_mul`/`eg_*` as memoized circuits — callers pay one call
  lookup each, the byte-gadget width lives once). Call sites in
  `Pcs.lean`/`Verifier.lean` stay textually identical — the interface
  survives.
- **Measure**: compile `multiStarkForeign`, run the existing
  stats/width loop (`bench-typecheck --interp`, circuit stats) at
  factorial scale and extrapolate to kernel scale.
- **Decide**: go/no-go numbers for stage-3 proving cost (rows ×
  columns → per-column MSM sizes over Fr). Mitigation knobs, in order:
  1. re-tune stage 2 for the wrap: stage-3 cost is LINEAR in stage-2
     query count — fewer queries + more PoW bits + higher blowup on
     stage 2 directly shrinks the wrap circuit;
  2. lookup grouping k = 4 for branchless circuits (the measured
     −582/−1844 column win, still unapplied);
  3. memoization hit rates on the byte gadgets (dedup across repeated
     byte pairs is high in carry chains).

### Phase D — KZG instantiation, end-to-end at toy scale

- Synthesis over `KzgConfig`: instantiate the Phase-A-generic
  `System<SC>` with Fr (D = 1: 4 publics, stage-2 width halves per
  slot), `Blake3Transcript`, `KzgPcs` with a dev SRS.
- Codegen: the foreign toplevel gets its own generated witness runner
  over Fr (`aiur_multi_stark_foreign.rs` or similar) — witness
  generation is native Rust Fr arithmetic, fast.
- **Gate**: prove the wrap of a small stage-2 proof (factorial),
  verify natively; tamper-reject; record proof size and prove/verify
  times. Target shape: proof ≈ (columns × ~48 B) + openings + a few
  G1 witness points; verification = 2 pairings + small MSMs.

### Phase E — scale and productionize

- Kernel-scale stage-2 proof wrapped end-to-end.
- Ceremony SRS loader (`Srs` is bring-your-own; monomial powers-of-tau
  only): Filecoin's 2^27 BLS12-381 setup is the likely fit — foreign
  traces are much taller than the native verifier's ~2^21; truncate to
  a power of two, `Srs::validate()` on load.
- Parallel MSM/FFT in the KZG prover (ark parallel features) after
  measuring.
- Final parameter tuning across the stage-2/stage-3 boundary.

## 4. Decision points and open questions

- **C is a real checkpoint**: if the foreign circuit is prohibitive
  even after the mitigations, the fallbacks are more aggressive
  stage-2 parameter shifts (PoW-heavy, query-light) or, much further
  out, a Plonkish frontend for the wrap (out of scope, noted in
  multi-stark's doc as Phase 3).
- **Declaration-level inlining** is the one Aiur-compiler change the
  plan needs; it should land independently (Phase C) with the native
  toplevel's codegen byte-identical as its gate.
- **Prune-after-splice** (nice-to-have): `@`-referenced functions
  currently survive pruning as empty deactivated circuits (217 vs 207
  fns today — zero column cost, a few vk bytes). Splice-then-prune
  would drop them; only worth doing if vk size ever matters.
- **Lean-side Fr interpreter**: NOT needed for the plan (the
  field-independence trick covers development; witness gen is Rust).
  Optional later for parity testing.
- **Stage-3 public input**: same existential statement shape as stage
  2 — the stage-2 vk digest + claims digest, as Fr elements packing
  digest bytes (`b3_pack`'s 4-bytes-per-element works in any field).

## 5. Prerequisites already landed

- multi-stark `pcs-traits`: crate-owned traits (Transcript, Domain,
  Pcs, field layer with D = 1 first-class), byte-identical FRI under
  the pin, `ark_adapter/` with `Scalar`(Fr)/`Radix2Coset`/
  `Blake3Transcript`/`Srs`(+validate)/`KzgPcs`/`KzgConfig`, end-to-end
  KZG prove/verify (1,781-byte two-circuit proof).
- ix `kzg` branch: multi-stark bump to `pcs-traits`; Aiur DSL modules
  de-imported (moduleless); the `g_*`/`eg_*` inner-field interface
  (`GoldilocksNative.lean`) adopted across `Pcs.lean`/`Verifier.lean`
  (zero raw inner-field arithmetic outside the interface); and
  `GoldilocksForeign.lean` (byte-limb, recovered from pre-nativization
  history), passing the `gl_ops_ref` vectors + boundary/root tests as
  its own toplevel.
