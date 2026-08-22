# The KZG stage: wrapping the recursive verifier over BLS12-381

Status: PHASES A–D COMPLETE, stage 3 in CI. The full pipeline runs on
`Nat.add_comm` at 40 queries: stage 1 (IxVM on FRI) 2 s / 5 GiB; stage 2
(FRI recursion on FRI) 48 s / 59 GiB, 3.4 MB proof; stage 3 (the foreign
verifier on KZG over BLS12-381) 15 min / 81 GiB, **765 KB** proof verified
natively in 0.13 s. The `aiur` CI benchmark carries all three stages plus
the pipeline ledger. Remaining: Phase E (ceremony SRS loader, codegen'd Fr
runner, per-circuit streamed witness, stage-2 tuning for the wrapped
pair).

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

### Phase A′ — Lean constants as exact naturals [COMPLETE]

Constants belong to the program, fields to the instantiation. Scoped to
`Nat` (rationals deferred: any other constant kind requires compound
operations anyway, and naturals keep specialization a single checked
embedding):

- **Elaborator**: numeric literals are exact `Nat`s — `G.ofNat`'s
  silent mod-p wrap is gone from the source path.
- **Source → bytecode**: `Term.field`/`Pattern.field`/`Op.const`/match
  keys carry `Nat` through every stage.
- **Specialization = checked embedding**, per consumer: a constant `≥ p`
  is a hard ERROR — "the field cannot represent this circuit" — never a
  wrap. Bonus: with the error in force, distinct keys stay distinct in
  every accepted field, so no match-collision check is needed.
  - Lean interpreters (`BytecodeEval`, `SourceEval`, `Interpret`):
    on-the-fly `G.ofNat?` per use; overflow raises `constantOverflow`
    (pattern keys: an unrepresentable constant matches no value).
  - FFI (`lean_nat_as_field`): decodes scalar AND GMP-boxed Nats
    (values in `[2^63, p)` are boxed), panics with the overflow message.
  - Codegen: `checkConstants gSize` guard at emission
    (`Bytecode.Toplevel.checkConstants`, off `Block.maxConstant`).
- Runtime VALUES in the Lean interpreters are still per-field elements
  (G today); "bytecode is field-free" does not mean "execution is". A
  field-class-parametrized interpreter lands with the second Lean field
  instance, if ever needed.

**Gate held**: codegen byte-identical, kernel FFT + shard pins exact,
all suites + Rust workspace tests green.

### Phase B — the foreign verifier toplevel, validated over Goldilocks [COMPLETE]

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

### Phase C — cost checkpoint + the emulation design [LANDED]

The risk, measured, then removed in three steps (all on `Nat.add_comm`'s
40-query stage-1 proof, same blobs through both verifiers):

1. **Call-site splicing** of the byte-limb ops put every `g_mul` body
   (~930 u8 lookups) into its caller: 386k columns, 43 MB wrap proof.
   → Inline wrappers over memoized `*_impl` circuits; byte primitives as
   their own circuits; pointer-threaded values. Width 386k → 8.5k, wrap
   proof 854 KB. But FFT cost stayed **6.5× native** (7.1e11 vs 1.1e11):
   the carry chains (`add16`/`add8`/`sub8`) were 54% of it, 43M rows.
2. **The large-field design** (outer field > p²): a Goldilocks value is
   ONE outer element `< p`; ops compute exactly in the outer field and
   reduce by CHECK — `x·y = q·p + r` with `q, r < p` (hinted by the new
   `unconstrained_gl_divmod`, pinned by one degree-2 identity and two
   8-byte range checks), `x + y`/`x + p − y` with a boolean `q`, the
   inverse hinted (`unconstrained_gl_inverse`) and pinned by one mul.
   Width **7,594 vs native 7,176 (6%)**; FFT cost **1.44e11 — 1.32×
   native**; interpreter execution 12 s vs 7 s native (was 65 s); toy KZG
   wrap **33 s / 763 KB** (was 21 min / 43 MB), with arkworks' `asm` and
   `parallel` MSM/FFT enabled in multi-stark.
   Soundness needs |F| > 2p²; the module still runs under Goldilocks
   (hint `(0, v)`, degenerate but correct identities) for the self-tests
   and the interpreter gate. Beware evaluation order in the outer field:
   `x − y + p` wraps at `x − y`; `x + p − y` does not.
3. Remaining knobs for kernel scale: fewer stage-2 queries for the wrapped
   pair (stage-3 area is linear in them); lazy reduction in `eg_mul`
   (`a0·b0 + 7·a1·b1 < 8p²` is still exact — 2 reductions instead of 7,
   needs a 67-bit range check on q); a codegen'd Fr runner.

### Phase D — KZG instantiation, end-to-end at toy scale [GATE PASSED]

LANDED: the full stage-3 path at factorial scale. `AiurField` for
`Scalar`; `AiurSystem::build_kzg`; the FFI surface (`AiurKzgSystem`:
build with a dev SRS / `proveMultiStark` over raw advice blobs /
native `verify`), with the toplevel decoder and advice-buffer builder
generic over the field (`LeanField`, `verifier_io_buffer_in`). The
`kzg-verifier` suite proves the FOREIGN verifier's acceptance of a
factorial stage-2-style proof (3 inner queries) over Fr under
`KzgConfig` and verifies it natively; a tampered wrap proof rejects.

Measured (dev SRS 2^17, single-threaded, interpreter execution),
after the Phase-C memoization + pointer representation: **wrap proof
854 KB, prove ~6.5 min** for a 30 KB inner proof (~7.2k effective
columns × ~112 B each — proof size is Θ(total width) under per-column
KZG, constant in trace height; the pre-fix call-site splicing measured
386k columns / 43 MB / 21 min). Truly kilobyte-scale terminal proofs
remain a stage-4 (Plonkish, O(1) polynomials) property.

Remaining in this phase:

- Codegen: the foreign toplevel gets its own generated witness runner
  over Fr (`aiur_multi_stark_foreign.rs` or similar) — witness
  generation is native Rust Fr arithmetic, fast (today's interpreter
  execution over Fr is a large share of the 21 min).
- Parallel MSM/iFFT in the KZG prover (pulled forward from Phase E if
  prove time stays the bottleneck).

### Phase E — scale and productionize

- Kernel-scale stage-2 proof wrapped end-to-end.
- Ceremony SRS loader (`Srs` is bring-your-own; monomial powers-of-tau
  only): Filecoin's 2^27 BLS12-381 setup is the likely fit — foreign
  traces are much taller than the native verifier's ~2^21; truncate to
  a power of two, `Srs::validate()` on load.
- Parallel MSM/FFT in the KZG prover (ark parallel features) after
  measuring.
- Final parameter tuning across the stage-2/stage-3 boundary.

## 3b. The generic verifier (mirrors `pcs-traits`)

The Aiur verifier is structured like the Rust one: a core written against
interface NAMES, plus one merged implementation per interface (exactly one,
same names by design — the mechanism the native/foreign field pair always
used). Interfaces and their current implementations:

| interface | names the core refers to | implementations |
|---|---|---|
| Field (`Ix/MultiStark/Field/`) | `Val`, `Ext`; `val_zero/one/two/generator/two_adic_root`, `ext_w`; `val_add/sub/neg/mul/is_zero/inverse`, `ext_add/sub/neg/mul/inverse/div/eq`; `val_from_bytes`, `val_to_bytes`, `val_from_u16`, `bytes_lt_modulus` | `goldilocksNative` (`Val = G`), `goldilocksForeign` (Goldilocks in a large outer field) |
| Pcs (`Ix/MultiStark/Pcs/`) | `Commitment`, `PcsProof`, `PcsParams`; `read_commitment_at`, `read_pcs_proof`, `read_vk_commitment`, `read_pcs_params`; `commitment_onto`, `snoc_commitment`, `pcs_empty_commitment`; `pcs_verify` | `pcsFri` (Blake3 Merkle MMCS + FRI) |
| Transcript (`Ix/MultiStark/Transcript/`) | `ch_sample8/field/ext/bits`, `ch_observe_val`, `snoc_b8`, `b8_onto`, `limbs_onto`, `log_degrees_onto`, `accs_onto`, `rev_onto`, `seed_tag_onto` | `transcriptBlake3` (blake3 is fixed by design) |
| Domain (`Ix/MultiStark/Domain.lean`) | `two_adic_gen`, `pow2`, `trace_vanishing`, `trace_selectors`, `ext_exp_pow2` | `twoAdicDomain` (shared by every PCS) |

Assembly: `multiStarkFullOver field pcs` — `multiStark` = native × FRI,
`multiStarkForeign` = foreign × FRI. The refactor was pinned as a semantic
no-op: identical circuit widths (5072/2104, 5250/2344) and FFT costs on the
saved 40-query proof (1.0888e11 / 1.4405e11); codegen re-emits only in
function order; every suite green.

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
