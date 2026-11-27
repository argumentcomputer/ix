# Certified Lean-to-Formal-Aiur Compiler (`IxCCAiur`) & Multi-Endpoint Compression

Status: current, 2026-11-26.

This document describes the architecture, soundness chain, frontend contract,
certified optimization passes, multi-endpoint compression pipeline, and
measured CPU performance of `IxCCAiur` and its certified `SingleCircuit`
(Endpoint 1) and `BLS12-381` (Endpoint 2) extensions.

Package-level CLI and module reference: [IxCCAiur/README.md](../IxCCAiur/README.md).
Existing L3 BN254 pipeline architecture: [aiur-compression-architecture.md](aiur-compression-architecture.md).

---

## 1. Architecture overview

Hand-writing zk circuits in a separate DSL (`Aiur`) and maintaining external
refinement proofs back to a Lean specification scales poorly as verifier and
VM circuits grow. `IxCCAiur` eliminates per-circuit refinement proofs by
certifying the compiler pipeline itself:

1. **Ordinary Lean 4 source** (annotated via `open scoped Ix.Circuit`) is
   compiled by `ix compile` into an anonymous Ixon v3 closure (`.ixe`) plus
   deterministic sidecar JSON files (`--circuit-schedule-out`,
   `--circuit-guesses-out`). Because all `Ix.Circuit` attributes live in a
   persistent sidecar environment extension, **Ixon content addresses are
   strictly invariant** under circuit annotations.
2. **IxCC front-half recheck** (`IxCC.Recheck.ingress` / `frontAuto`,
   `produceFir`, canonical relevance check, `Recheck.runFir`) compiles the
   closure to `IxCC.Fir.Program` and checks its front-half certificate.
3. **IxCCAiur certified lowering & optimization** lowers `IxCC.Fir.Program` to
   `Aiur.Modules.Program` over Goldilocks, BN254 `Fr`, or BLS12-381 `Fr` via a
   chain of proved passes (`GuessLower`, `TypedLower` + `Peephole`,
   `InlineFuse`, `PartialEval`, `FieldLower`, `CompressionIntrinsics`,
   `WitnessIO`), verifies the prepared world (`TypedWorld.check`), and compiles
   the circuits with `Aiur.Optimized` (+ optional `DegreeBudget`).
4. **Formal Aiur certified backends** lower the exported `.ixa` program to:
   - **Multi-chip Goldilocks STARK** (`ixcc_prove`),
   - **Endpoint 1: Single-circuit (`num_circuits == 1`) Goldilocks STARK**
     (`Aiur.Tiling.SingleCircuit`, optional `Aiur.Tiling.VectorRom`,
     `single_circuit_prove`),
   - **Endpoint 2: BLS12-381 KZG / PLONK / SCS** (`Aiur.Plonk.BLS12381`,
     `Aiur.Tiling.BLS12381`, `plonk_export --bls12-381`, `tools/gnark`
     `curve: "bls12-381"` with `sw_bls12381.PairingCheck`),
   - **Endpoint 3: BN254 L3 compression stages** (`ix-aiur-stages-v1` with
     optional `"entry"`, `"advice"`, and `"field"` manifest overrides).

`IxCC` and `IxCK` remain 100% Mathlib-free; `IxCCAiur` sits in its own package
importing both `IxCC` and `Aiur`.

---

## 2. End-to-end soundness chain and trust surface

Every headline theorem in `IxCCAiur` is pinned in
`IxCCAiur/IxCCAiur/Audit.lean` via `#guard_msgs` signature checks and
`#print axioms` checks, and independently re-verified by
`lake -d IxCCAiur env leanchecker IxCCAiur.Audit`.

| Layer | Proved theorems (Lean 4 standard axioms only) |
|---|---|
| Front-half compilation | `IxCC.Recheck.runFir` (`IxCC.Recheck.sound`, `IxCC.Fir.Proof.*`) |
| Base lowering & gadgets | `Backward.eval_code_sound`, `Gadgets.{pAdd,pSub,pMul,divmod,pDiv,pMod,pPred,pLand,pLor,pXor,pBeq,wDivmod}_sound`, `Compose.accepted_nat_backward`, `Progress.accepted_nat`, `Instance.accepted_nat` |
| Typed unboxed lowering & peephole | `TypedWorld.{u8ByteSpec_of_check,u32Contracts_of_check}`, `TypedGadgets.U32Contracts.ofCheck`, `Peephole.evalExpr_*_sound`, `TypedBackward.{typedLoweredWorld_of_check_all,typed_backward_sound,typed_circuit_sound,typed_circuit_sound_goldilocks}`, `TypedClaim.{typed_accepted_nat,typed_accepted_enum}` |
| Certified optimizers | `InlineFuseProof` (sharing-aware inlining, let-flattening, peephole, dead-fn pruning), `PartialEvalProof` (heap-dereferencing partial evaluation), `FieldLowerProof` (native `Field` intrinsic lowering across Goldilocks / BN254 / BLS12-381), `GuessLowerProof` (Tier-2 non-deterministic witnesses) |
| Compression I/O & ABI | `Blake3Spec` (24 standalone `EvalFn` contracts), `WitnessIO.{starkIo_read_channel_sound,kzgIo_read_stream_sound,witness_stream_exists,witness_wrapper_sound,witness_wrapper_assertOk_sound}`, `CompressionIntrinsics.{bls12381_emulated_product_bound,bls12381_emulated_reduction_bound,lowerCompressionOps_plain,aliasEntry_sound,aliasEntry_sound_of_check}` |
| Artifact certificate | `CompiledCert.{Cert,TypedCert}` composing `IxCCAiur` with `Aiur.Audit` |
| Circuit-level passes | `Aiur.Optimized.{DegreeBudget,Split,Vectorize}`, `Aiur.Tiling.{SingleCircuit,VectorRom,BLS12381}`, `Aiur.Plonk.BLS12381` |

### What stays outside the Lean proof boundary

- **Cryptographic proof systems & setups:** `multi-stark` STARK/FRI/LogUp/PCS,
  packed SHPLONK, `gnark` PLONK (`BN254` and `BLS12-381`), Solidity verifiers,
  and trusted SRS ceremonies (Ignition for BN254; Filecoin/Powers-of-Tau for
  BLS12-381).
- **Prover-only components (not soundness-relevant):** host hint / advice
  computation (`ixcc.divmod64`, `"ixcc.guess.<fn>"`, `StarkIO`/`KzgIO` streams),
  witness solving (`aiur_plonk_scs_wires.go`), GPU kernels, and caching. Any
  wrong hint or witness fails circuit constraints or proof verification.
- **Native driver evaluation of world checks:** `ixcc-aiur` executes
  `World.checkWorld` / `TypedWorld.check` natively before writing `.ixa` and
  `PACKAGE.ixa.pin.json` (the same check can be discharged in the Lean kernel
  for concrete pinned instances as in `Fib.lean`, `Gcd.lean`, and `Roots.lean`).

---

## 3. Zero-TCB `Ix.Circuit` frontend contract

Defined in `Ix/Compile/CircuitContract/{Basic,Attr,Emit}.lean` and activated
strictly inside `open scoped Ix.Circuit`:

- **Zero `TokenTable` pollution:** Every attribute name, representation tag,
  and `checked def` keyword uses `nonReservedSymbol`, adding zero global parser
  tokens.
- **Zero Ixon address mutation:** Attributes write only to
  `Ix.Compile.CircuitContract.circuitAttrExtension` (`SimplePersistentEnvExtension`)
  without modifying any `Lean.ConstantInfo`. Removing `open scoped Ix.Circuit`
  and all `@[circuit_*]` attributes produces bit-for-bit identical Ixon
  addresses (verified on `MultiStarkV6Pure`: 5,409/5,409; `CompressWrapPure`:
  380/380; `KzgPackedPure`: 270/270).
- **Deterministic sidecars:** `ix compile --circuit-schedule-out SCHEDULE.json`
  emits `"ixcc/circuit-schedule/1"` keyed by Ixon content address, and
  `--circuit-guesses-out GUESSES.json` emits Tier-2 guess metadata.

### Attribute & declaration surface

| Construct | Meaning |
|---|---|
| `@[circuit_inline]` / `@[circuit_noinline]` | Controls inlining in `InlineFuse` (and preserves boundaries across ANF inlining). |
| `@[circuit_group "name"]` | Assigns chip grouping hint. |
| `@[circuit_unroll N]` | Bounded loop/recursion unroll hint. |
| `@[circuit_lanes K]` | Requests `K`-lane horizontal chip vectorization (`Aiur.Optimized.Vectorize`). |
| `@[circuit_budget maxChips maxCols maxCalls maxMem [maxTotalCols]]` | Optional compile-time chip/column budget ceilings (`_` leaves a ceiling unchecked). |
| `@[circuit_range_table small\|pair\|auto]` | Selects 256-row `U8Byte` table, 65,536-row `UInt8` pair table, or automatic selection. |
| `@[circuit_static]` | Explicitly forces compile-time partial evaluation of a function (see §5 ergonomics note). |
| `@[circuit_repr(field\|u32\|u64\|limbs k b\|flat_array n\|word_stream)]` | Advisory data-representation directive. |
| `@[circuit_intrinsic "name"]` | Binds a pure Lean reference function to a certified backend intrinsic (`field.*`, `goldilocks.*`, `blake3.*`, `stark.io.*`, `kzg.io.*`). `Driver.intrinsicAddresses` automatically shields intrinsic definitions from ANF inlining so `FieldLower` / `CompressionIntrinsics` match them cleanly. |
| `@[circuit_split_fastpath]` | Marks a function for `C3` fast-path / cold-path chip splitting (`Aiur.Optimized.Split`). |
| `@[circuit_guess checker soundThm [completeThm]]` | Post-hoc Tier-2 non-deterministic witness linkage matching `IxCC.Src.Table.Guess.checkGuess`. |
| `checked def f (x : T) : R := hint body where check pred by <soundness> [complete by <completeness>]` | Desugars to ordinary `def f`, `def f.check`, `theorem f.check_unique`, optional `theorem f.check_complete`, and registers a `CircuitGuessSpec` sidecar. |

---

## 4. Tier-2 guesses, universal host advice, and existential NP `WitnessIO`

### Tier-2 non-deterministic `guess` witnesses

Expensive inverse/division/modular-reduction computations (e.g., $\mathbb{F}_{p^3}$
inversion, multi-limb `Fq` reduction/inverse, scalar division) can be specified
as total Lean functions with a `checked def` verification predicate. Under
`ixcc-aiur --enable-guesses --advice-out ADVICE.ixa`:

1. `GuessLower` replaces calls to the hinted function `f` with a non-deterministic
   hint read on channel `"ixcc.guess.<fn>"` followed by the compiled checker
   `f.check` and `assert_eq!(ok, 1)`.
2. `GuessLowerProof` proves that any accepted Aiur derivation satisfying the
   checker produces the exact unique value of `f` (using `f.check_unique`).
3. `ADVICE.ixa` captures the unmodified pre-guess bytecode. Both `ixcc_prove`
   and `single_circuit_prove` accept `--advice ADVICE.ixa` and execute the
   original function in the Aiur interpreter to answer **every**
   `"ixcc.guess.<fn>"` channel automatically — **zero per-function Rust
   hardcoding**.
4. Passing `--tamper-hint CHANNEL` intentionally corrupts advice on that
   channel to verify constraint rejection end-to-end.

### Existential NP `WitnessIO` (`IxCCAiur.WitnessIO`)

Production compression verifiers receive proof, key, and claims bytes as
prover-supplied witness streams rather than public inputs. `WitnessIO` adds:

- Plain Formal Aiur ingress modules `StarkIO` (`stark.io.info`, `stark.io.read1`,
  `stark.io.read8`) and `KzgIO` (`kzg.io.length`, `kzg.io.read4`,
  `kzg.io.read1`, `kzg.io.div`), matching `MultiStark`'s exact host channels
  and validating every byte/word through `UInt8::from_field` / `UInt32::from_fields`.
- **Existential NP soundness** (`witness_stream_exists`, `witness_wrapper_sound`,
  `witness_wrapper_assertOk_sound`): independent of the untrusted host oracle,
  any finite `EvalFn` derivation of a wrapper entry accepting public input `pub`
  implies the existence of finite, valid byte streams `ws : List (List UInt8)`
  satisfying the inner backward-sound verifier predicate.

### Compression intrinsics & `--entry-name` / `--assert-ok` ABI (`IxCCAiur.CompressionIntrinsics`)

To avoid unintended intrinsic rewriting on ordinary programs, non-field
compression intrinsics in `Driver.lean` are strictly opt-in via explicit CLI
flags:

- `--field-lower`: lowers `@[circuit_intrinsic "field.*"]`
  (`add`, `sub`, `mul`, `neg`, `inv`, `div`, `is_zero`, `eq`) to native ambient
  `Field` operations over Goldilocks, BN254 `Fr`, or BLS12-381 `Fr`.
- `--emulate-goldilocks`: links `Aiur.Library.Field.Goldilocks.Emulated` and
  enables `goldilocks.{add,sub,mul,neg,inv,is_zero,eq,ext_add,ext_sub,ext_mul,ext_inv}`
  over BN254 or BLS12-381 (backed by `bls12381_emulated_product_bound` and
  `bls12381_emulated_reduction_bound` proving zero ambient wrap-around).
- `--link-blake3`: links `Aiur.Library.Blake3` (certified by `Blake3Spec`) and
  enables `blake3.{compress_init,hash,pack_digest}`.
- `--witness-io`: links `StarkIO`/`KzgIO` and enables `stark.io.*` / `kzg.io.*`.
- `--entry-name NAME [--assert-ok]`: exports `Prog::main0` under an exact
  stage-compatible entry name (e.g., `CompressWrap::verify_root`,
  `CompressNarrowFixed::step_v1`, `CompressFinalNarrow::verify_accumulator_v1`),
  optionally asserting `result == 1` and returning unit `()`, certified by
  `aliasEntry_sound`.

---

## 5. Certified optimization and backend passes

1. **Shape-directed unboxed lowering (`TypedLower` + `Peephole` + `TypedWorld`):**
   Unboxes `Nat`, `UInt8`, `UInt32`, `UInt64`, flat records, and enumerations;
   replaces tagged `Obj` heap allocations with direct field/tuple/byte-word
   operations; fuses multi-input `UInt32` additions and BLAKE3 rotations
   (`add3`, `rotr8`, `rotr16`, `xor_rotr7`, `xor_rotr12`, byte shifts).
   `TypedWorld.checkU32Functions` checks all 30 `UInt8`/`UInt32` library ASTs
   and feeds `TypedBackward.typedLoweredWorld_of_check_all`.
2. **Inline & fuse (`InlineFuse` + `InlineFuseProof`):**
   Sharing-aware function inlining, let-flattening, peephole simplification,
   and unreachable-function pruning.
3. **Compile-time partial evaluation (`PartialEval` + `PartialEvalProof`):**
   Specializes functions over statically known inputs (including dereferencing
   immutable heap DAGs such as fixed predecessor verification keys), collapsing
   interpreter loops and fixed ROM tables into straight-line field arithmetic.
   > **Compiler ergonomics note (`@[circuit_static]` vs. auto-specialization):**
   > Setting `@[circuit_static]` populates `PartialEval.Config.staticFns`, which
   > bypasses the dynamic-argument guard (`!dynFns.contains nm && svArgs.any SVal.hasStatic`)
   > and can self-unroll recursive DAG evaluators on dynamic inputs. For
   > recursive evaluators such as `evalAt` or `KzgAlgebra` helpers, omit
   > `@[circuit_static]` (use `@[circuit_inline]` / `@[circuit_noinline]`
   > instead) so `PartialEval` auto-specializes strictly when static VK
   > arguments are present.
4. **Native ambient field lowering (`FieldLower` + `FieldLowerProof`):**
   Replaces modular arithmetic reference helpers annotated with
   `@[circuit_intrinsic "field.*"]` with direct ambient `Field` operations
   (Goldilocks, BN254 `Fr`, or BLS12-381 `Fr`). When no byte/word lookups
   remain after partial evaluation and field lowering, the lowered program
   automatically downgrades to `TableTier.none` (0 fixed table rows).
5. **Quotient-aware degree budgeting (`Aiur.Optimized.DegreeBudget`, C7b):**
   Matches `Aiur.MultiStarkSpec.retune`, proving free polynomial constraint
   degree slack whenever LogUp lookup groups already determine quotient degree.
   Exposed via `--degree-budget --log-blowup N`.
6. **Chip splitting (`Aiur.Optimized.Split`, C3) & horizontal vectorization
   (`Aiur.Optimized.Vectorize`):**
   Certified fast-path / cold-path splitting across mutually exclusive boolean
   selectors on a shared LogUp channel, and `K`-lane horizontal chip
   vectorization preserving exact polynomial constraint degree.
7. **Certified vectorized ROM (`Aiur.Tiling.VectorRom`, C6):**
   Packs `K` consecutive ROM entries per physical row in `wide_export --vector-rom K`,
   cutting ROM height and preprocessed address storage by `K×`.

---

## 6. Multi-endpoint compression architecture

### Endpoint 1: Single-circuit (`num_circuits == 1`) Goldilocks STARK

- **Formal certification:** `Aiur.Tiling.SingleCircuit` (`pack airs rows`)
  merges multiple row-local `WideStage.Air` circuits horizontally into one
  uniform-height circuit (`num_circuits == 1`) with zero row overhead on
  full-height tables (`wide_single_circuit_sound_goldilocks`,
  `wide_vector_rom_single_circuit_sound_goldilocks`,
  `narrow_compact_single_circuit_sound_goldilocks`).
- **Exporters:**
  - `wide_export --goldilocks --single-circuit --pow2-rows [--vector-rom K]`
    (`ix-wide-layout-1`),
  - `tiling_export2 --goldilocks --single-circuit --pow2-rows`
    (`ix-tiling-v2-layout-1`).
- **Live prover:** `crates/aiur/examples/single_circuit_prove.rs` auto-detects
  both layout formats and supports `--advice ADVICE.ixa`, `--tamper-hint CHANNEL`,
  `--pin PIN.json`, `--stark-io KEY CLAIMS PROOF`, `--stark-128`, and
  `--controls`.

### Endpoint 2: BLS12-381 KZG / PLONK / SCS

- **Formal certification:**
  - `Aiur.Library.Field.BLS12381.Prime` — pure Lean 4 Lucas primality
    certificates for the BLS12-381 scalar prime `r` (zero primality oracles or
    extra axioms),
  - All 28 modules under `Aiur/Aiur/Plonk/` generalized over arbitrary prime
    `p`, instantiated in `Aiur.Plonk.BLS12381`,
  - End-to-end tiling and single-circuit corollaries in `Aiur.Tiling.BLS12381`.
- **Exporters:** `tiling_export2 --bls12-381`, `wide_export --bls12-381`, and
  `plonk_export --bls12-381` (plus `plonk_check_stage` and `plonk_beta_test`).
- **Gnark terminal (`tools/gnark`):** `aiur_plonk_scs.go`,
  `aiur_plonk_pairing.go`, `aiur_plonk_scs_prepare.go`, `aiur_plonk_prover.go`,
  and `ffi_aiur_plonk.go` support `"curve": "bls12-381"` in `pairing.json`:
  - **22 private output words** (two affine BLS12-381 G1 points, each encoded
    as `5 x` + `5 y` + `1 inf` in `affine-u80-v1`: four 80-bit limbs + one
    61-bit top limb = 381 bits, range-checked against `Fq`),
  - Constrained via `sw_bls12381.PairingCheck` against two canonical G2
    anchors,
  - Dedicated CGo verifier export `ix_gnark_aiur_bls_verify`,
  - **CPU-only note:** BLS12-381 PLONK runs on CPU (`openAiurProver` rejects
    `CUDA=true` on BLS12-381; custom CUDA PLONK is BN254-only).
- **Rust runtime (`crates/proof-compression/src/aiur_backend/bls12_381.rs`):**
  Provides `Bls12381` (`FieldBackend` over `ark_bls12_381::Fr`), canonical
  `encode_fq`/`decode_fq`/`encode_g1`/`decode_g1`/`encode_g2_coordinates`, and
  `WidePackage` execution helpers.

### Endpoint 3 & `ix-aiur-stages-v1` manifest integration

The existing L3 pipeline drivers (`crates/stark-verifier/src/compress_wrap.rs`
and `crates/proof-compression/src/aiur_backend/{plonk,stages}/`) accept
optional manifest fields so `ixcc-aiur`-compiled circuits plug in cleanly with
full backwards compatibility:

- `"entry"` — overrides the default hardcoded entry symbol,
- `"advice"` — loads an `ADVICE.ixa` package to answer `"ixcc.guess.<fn>"`
  channels,
- `"field"` — selects `"bn254"` (default) or `"bls12-381"` for KZG/PLONK
  stages and export cache keys.

### Pure annotated Lean 4 production compression verifiers

- **`IxCCAiur/Compression/{StarkWire,CompressWrapPure}.lean`**: Complete
  full-modulus 64-bit Goldilocks ($p_{\mathrm{GL}} = 2^{64} - 2^{32} + 1$)
  Protocol `v6` `CompressWrap` / `CompressGL` verifier (exact keyed BLAKE3
  transcript, batched MMCS frontier sort/merge/fold, AIR + LogUp OOD, multi-arity
  FRI over $\mathbb{F}_{p^3}$, `"ix/compress-wrap/v1\0"` 84-byte statement
  digest, trailing-byte rejection). 61 `#guard`s, 380/380 identical Ixon
  addresses.
- **`IxCCAiur/Compression/{KzgWire,KzgPackedPure}.lean`**: Single-source
  multi-curve (parameterized by `CurveParams` for both **BN254** and
  **BLS12-381**) packed-SHPLONK KZG verifier (`KzgAlgebra`, `KzgPackedShape`,
  `KzgPcsPacked`, `KzgPackedVerifier`, `CompressBNPacked`,
  `CompressNarrowFixed.stepV1`, `CompressFinalNarrow.verifyAccumulatorV1`
  emitting 18 or 22 affine-u80 words). 104 `#guard`s, 270/270 identical Ixon
  addresses.

---

## 7. Measured CPU benchmarks & relative comparisons

All figures below were measured on the 64-core Linux CPU host (no GPU attached;
full GPU pipeline benchmarks for compiled vs. hand-written L3 stages are
pending GPU host availability).

### Pure Lean compiled circuits vs. hand-written baselines & optimizer impact

| Target & Configuration | Active Circuits / Chips | Rows or Columns | S1 Words | Prove / Verify (CPU) | Proof Size | Controls & Pin |
|---|---|---|---:|---|---|---|
| `Blake3Block` (0-annot pure Lean) vs. hand-written `Aiur.Library.Blake3` | multi | max **547 cols** *(vs. 819)* | — | **76.9 / 8.64 ms** *(vs. 79.7 / 9.08 ms)* | **1.48 MB** *(vs. 1.82 MB)* | 34/34 rejected |
| `Blake3Block` Endpoint 1 Single-Circuit (`tiling_export2 --single-circuit --pow2-rows`) | **1** | 16 main cols, 2 constr | — | **633 / 2.47 ms** | **318.7–323.1 KB** | 100% rejected |
| `KzgAlgebraPure.entryFullFrame` (`--typed --inline-fuse --partial-eval --field-lower`) | **8** *(was 24)* | 515 (`259/256/0`) | **3,541 (-85.5%)** | **17.1 / 3.45 ms** (`3.5×` faster) | **596.6 KB (-64.9%)** | 5/5 wrong claims, `--pin` OK |
| `MultiStarkV6Pure.entryVerifyV6Compact` (multi-chip + 3 guesses + `--degree-budget`) | 58 | 3,663 (`3385/256/22`) | 59,940 | **66.9 / 19.5 ms** | 5,634 KB | 8/8 claims, 3/3 hints, `--pin` OK |
| `MultiStarkV6Pure.entryVerifyV6Blake3` (7-round keyed BLAKE3 + 4 pillars + 3 guesses) | 61 | 69,537 (`2699/66816/22`) | 559,103 | **180.6 / 27.1 ms** | 7,748 KB | 8/8 claims, 3/3 hints |
| `MultiStarkV6Pure.entryVerifyV6Compact` **Endpoint 1 Single-Circuit** (`tiling_export2`, `--stark-128`) | **1** | 65,536 × 32 main (`4` constr, `25` lkp) | — | **281.8 / 4.11 ms** *(w/ `--advice`: `572.8 KB` / `4.28 ms`)* | **434.4 KB** | 100% `--controls`, 3/3 hints |
| `MultiStarkV6Pure` **VectorRom (`C6`)** (`wide_export --single-circuit --vector-rom 4` vs. `K=1`) | **1** | **2.0× fewer ROM rows**, `-48.4%` cells | — | **1.86× faster prove** | single-circuit | `--controls` OK |
| `CompressWrapPure.entryCompressWrapSmoke` (`--entry-name CompressWrap::verify_root --assert-ok --field-lower`, full 64-bit `> 2^56` GL args) | multi | — | — | **172.5 / 54.3 ms** (`output: []`) | multi-chip | 7/7 wrong claims, `--pin` OK |

### `KzgPackedPure` static specialization (`--partial-eval --field-lower`) & BN254 vs. BLS12-381 comparison

| Comparison | BN254 | BLS12-381 | Relative Delta |
|---|---:|---:|---|
| `KzgPackedPure.entryAlgebraStatic*` baseline (`--typed --inline-fuse`) | 35 chips, 1,103 cols, 302 calls, `byte256` | 35 chips, 1,103 cols, 302 calls, `byte256` | identical baseline |
| `KzgPackedPure.entryAlgebraStatic*` optimized (`--partial-eval --field-lower`) | **3 chips, 139 cols (`7.9×↓`), 2 calls (`151×↓`), 0 ROM, `TableTier.none`** | **3 chips, 139 cols (`7.9×↓`), 2 calls (`151×↓`), 0 ROM, `TableTier.none`** | **0.0%** (`tiling_export2 --bls12-381 --single-circuit`: `512 × 32` main in `659 ms`) |
| `KzgPackedPure.entryNarrowStep*` (full narrow step + 2/2 `Fq` guesses) | 2,608 cols (`4×80b` `Fq`) | 2,620 cols (`5×80b` `Fq`) | **+0.46% cols** |
| `tools/gnark` `ix-aiur-scs-v1` + `PairingCheck` (`aiur_plonk_bls_test.go`, synthetic SCS) | 1,796,075 constraints | 2,241,382 constraints (`27.1 s` CPU prove, `4 ms` verify, `744 B` native / `1,184 B` Solidity, 7/7 neg controls) | **+24.8% constraints** |
| Live Pure Lean `KzgAlgebraPure.expPower2` → `plonk_export --bls12-381` → `gnark` BLS12-381 PLONK | — | **315,877 constraints @ `2^19`**, **3.96 s** CPU prove, **3 ms** verify | live end-to-end verified |
