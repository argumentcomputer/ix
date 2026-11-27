import Ix.Cert.AiurCompression.EndToEnd

/-! # Aiur Compression Pipeline Soundness & TCB Audit (`Ix.Cert.AiurCompression.Audit`)

Mechanically pins (via `#guard_msgs` on `#check` and `#print axioms`) the stage-level
lemmas, AST lower-bound pins, codec/policy injectivity theorems, single-layer statement
uniqueness, negative controls, and withdrawn-bundle inconsistency theorems for the
Lean-compiled Aiur proof-compression pipeline (no end-to-end theorem exists; see item 5
and the open TCB gap checklist below):

```text
  ix_aggr (MultiStark.aggregateProgram; shipped v6 uses Fp^3 + 32-byte BLAKE3-256;
           the 64-byte BLAKE2b-512 profile in `AiurCompression128Ok` is not shipped)
    │  modeled single-layer digest: Blake3("ix/compress-wrap/v1\0" || rootKeyPin[32] || Blake3(rootClaims))
    │  (deployed `--aiur-stages` terminal publishes a two-layer hash through the wrapper key)
    ▼
  Stage 1: CompressWrap     (Goldilocks wide tiling: Aiur.Tiling.Claims.wide_heap_sound_goldilocks_exported)
    │  8 u32 statement words
    ▼
  Stage 2: CompressGL       (BN254/BLS12-381 grouped wide tiling: grouped_heap_sound_{bn254_exported,shared_compiled})
    │  8 u32 statement words + deferred KZG accumulator (0 → cur₁)
    ▼
  Stage 3: CompressNarrowFixed (compact narrow tiling: narrow_heap_sound_compact_exported)
    │  packed policy digest + stage counter + 8 u32 words + folded accumulator (cur₁ → cur₂)
    ▼
  Stage 4: CompressFinalNarrow (shared-heap PLONK: Aiur.Plonk.plonk_shared_heap_sound)
    │  (statement_low, statement_high) ∈ [0, 2^128)^2 + canonical u80 affine deferred points
    ▼
  Outer Verifier: native Rust PLONK (`plonk::native`) / Groth16 (modeled by
                  OuterRelation.gnark_folded_pairing_sound /
                  Bls12381.OuterRelation.bls12381_gnark_folded_pairing_sound)
```

## Pinned Stage-Level Properties (Mechanically Checked, Zero Custom Axioms)
1. **Program AST & Configuration Pins (`ProgramPins.lean`)**:
   Kernel-checked AST pins over the pure `MultiStark` source programs
   (`compressWrapProgram`, `CompressGL.program`, `Source.kzgPackedTerminal`,
   `Source.compressBN`, `Source.compressBNPacked`, `Source.kzgPackedDeserialize`,
   `Final.source`), plus pure export validation (`validateFinalNarrowConfig`) proving
   the 21-word `step_v1` header coverage and `minStage ≥ 2` guard. The pins are lower bounds
   (named callees present, minimum assertion counts), not program identity, and none exists for
   the deployed `CompressNarrowFixed`/`CompressFinalNarrow` wrappers.
2. **Statement-Digest Binding & Manifest Integrity (`StatementBinding.lean`)**:
   Injectivity of `"ix/compress-wrap/v1\0"` preimages, `32 B ↔ 8×u32 ↔ 2×u128 ↔ Fr²`
   codecs across both BN254 and BLS12-381, Goldilocks-over-`Fr` no-wrap bounds,
   208-byte `IXAUKG01` `PackedPolicy` encoding injectivity, `ix-aiur-stages-v1` manifest
   anchor/key chain integrity, and collision-or-uniqueness for the single-layer
   `AiurStageStatementChain` model (not the deployed two-layer `--aiur-stages` terminal hash).
3. **Deferred KZG Folding & Affine Output Codecs (`DeferredFold.lean`)**:
   Exact Schwartz–Zippel soundness (`card ≤ 1` bad weights out of `|Fr|`) for L3 2-stage
   and arbitrary `k`-stage deferred pairing accumulation over BN254 and BLS12-381
   (with mandatory `G1` prime-order subgroup preservation on BLS12-381), plus injectivity
   of canonical `4×u80` (BN254) and `5×u80` (BLS12-381) affine coordinates.
4. **Compiler / Tiling / PLONK Witness Bridges (`StageBridge.lean`)**:
   Direct wrappers around the proved Aiur compiler theorems (`wide_heap_sound_goldilocks_exported`,
   `grouped_heap_sound_bn254_exported`, `grouped_heap_sound_shared_compiled`,
   `narrow_heap_sound_compact_exported`, `plonk_shared_heap_sound`).
5. **Statement Uniqueness & Negative Controls (`EndToEnd.lean`)**:
   statement uniqueness for the single-layer `AiurStageStatementChain` (not the deployed
   two-layer `--aiur-stages` statement), and 6 constructive negative controls rejecting wrong root
   key pins, tampered statement words/limbs, cross-curve/unchecked-cofactor/torsion downgrades,
   protocol/FRI downgrades, unpinned manifests, and policy/stage/header tampering.
   **No end-to-end theorem.** The former headlines `aiur_compression_l3_bn254_end_to_end` and
   `aiur_compression_128bit_bls12381_end_to_end` were withdrawn: their
   bundles have no inhabitant, pinned below as `Bn254AiurCompressionTcbGaps.inconsistent` and
   `Bls12381AiurCompressionTcbGaps.inconsistent`.

## Remaining Open TCB Gap Checklist (Not Yet Stated as Satisfiable Hypotheses)
The items below are the open steps. The records `Bn254AiurCompressionTcbGaps` /
`Bls12381AiurCompressionTcbGaps` that listed them as fields are inconsistent (their bridges
quantify over every statement and every free result record), so they do not state these items:
- **Program Functional-Refinement Contracts (4)**:
  1. `Bn254FinalSemanticContract` / `Bls12381FinalSemanticContract`: `EvalFn` of
     `CompressFinalNarrow::verify_accumulator_v1` implies `CompressNarrowFixed` KZG verification +
     policy/anchor/stage binding + deferred fold.
  2. `Bn254NarrowSemanticContract` / `Bls12381NarrowSemanticContract`: `EvalFn` of
     `CompressNarrowFixed::step_v1` implies `CompressGL` KZG verification + stage-1
     zero-accumulator check + deferred fold.
  3. `CompressGLSemanticContract`: `EvalFn` of `CompressGL::verify_root` implies Goldilocks
     `CompressWrap` MultiSTARK verification over emulated Goldilocks arithmetic.
  4. `CompressWrapSemanticContract`: `EvalFn` of `CompressWrap::verify_root` implies
     `"ix/compress-wrap/v1\0"` binding + `ix_aggr` root tree certification.
- **Cryptographic / PCS Extraction Bridges (5)**:
  5. Native Rust PLONK outer SCS relation (`crates/proof-compression/src/aiur_backend/plonk/native/`
     and `crates/proof-compression/src/aiur_backend/plonk/scs.rs`) ⇔ `PlonkSharedTerminalWitness`.
  6. Deferred KZG accumulator (`pairingVal = 1` + `G1` subgroup on BLS12-381) ⇔
     `NarrowCompactStageWitness` (Stage 3) and `Bn254GroupedWideStageWitness` /
     `FieldGroupedSharedStageWitness` (Stage 2).
  7. Goldilocks MultiSTARK FRI/PCS verification ⇔ `GoldilocksWideStageWitness` (Stage 1).
  8. BLS12-381 `PlonkSharedTerminalWitness` instantiation (while `Aiur.Plonk.SharedSound` is
     polymorphic over `ZMod p`, `PlonkSharedTerminalWitness` in `StageBridge.lean` currently
     instantiates `plonk_shared_heap_sound` at `BN254Fr` and reuses
     `FieldGroupedSharedStageWitness` for `BLS12381Fr`).
  9. Pure-Lean `Blake3.Pure.hash` replacement in `MultiStark.Compress{GLFixed,NarrowFixed,FinalNarrow}.source`:
     those 3 templates currently invoke `@[extern]` `Blake3.Rust.hash` (whose Lean body references
     a `native_decide` axiom), so pure AST pinning covers `compressWrapProgram`, `CompressGL.program`,
     `Source.kzgPackedTerminal`, `Source.compressBN*`, `Source.kzgPackedDeserialize`, `Final.source`,
     and pure `validateFinalNarrowConfig` until those 3 templates switch to `Blake3.Pure.hash`.
- **Standard External Assumptions**:
  10. KZG trusted-setup SRS / AGM knowledge extraction, BLAKE3/SHA-256 collision resistance
      (explicitly disjuncted as `Blake3Collision` / `Sha256Collision`), Fiat–Shamir ROM,
      and trusted artifact key-writer (`ix compress write-keys`) matching the Lean source.

Every theorem pinned below depends STRICTLY on standard Lean axioms
(`propext`, `Classical.choice`, `Quot.sound`) — zero `sorry`, zero custom axioms,
zero `native_decide`, zero `bv_decide`.
-/

/-! ## 1. Withdrawn Bundles, Escape Predicates & Statement Uniqueness (`#check` & `#print axioms`) -/

/--
info: @Ix.Cert.AiurCompression.Bn254AiurCompressionTcbGaps.inconsistent : ∀ {sha256 : List UInt8 → List UInt8}
  {manifest : Ix.Cert.AiurCompression.StageManifest} {finalCfg : MultiStark.Final.Configuration}
  {finalHeaders : List Ix.Cert.AiurCompression.NarrowClaimHeader}
  {bp : Ix.Cert.Compression.OuterRelation.BilinearPairing} {outerKeys deferredKeys : bp.G2 × bp.G2}
  {vk : Ix.Cert.Compression.OuterRelation.GnarkVerifyingKey} {inp : Ix.Cert.Compression.OuterRelation.OuterInputs}
  {stmtLow stmtHigh : ℕ} {d0 d1 : bp.G1} {finalPolicy : Ix.Cert.AiurCompression.PackedPolicy}
  {w₂ : Ix.Cert.Compression.Foreign.BN254Fr} {prevAcc cur₂ : bp.G1 × bp.G1} {wrapSrc : Aiur.Generic.Source MultiStark.F}
  {wrapEntries : List String} {glSrc : Aiur.Generic.Source Ix.Cert.Compression.Foreign.BN254Fr}
  {glEntries : List String} {narrowSrc : Aiur.Generic.Source Ix.Cert.Compression.Foreign.BN254Fr}
  {narrowEntries : List String} {finalSrc : Aiur.Generic.Source Ix.Cert.Compression.Foreign.BN254Fr}
  {finalEntries : List String}
  {sem :
    Aggr.AggrSemantics Address Address Ix.DynamicLink.EvalAssumption Address Ix.Cert.MultiStark.K
      Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
  {batchClaim :
    ℕ →
      Aggr.ValidatorMode Address →
        (Address → Prop) → (Address → Prop) → (Address → Prop) → (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
  {rootStmt :
    Aggr.AggrNodeStmt Address Address Ix.DynamicLink.EvalAssumption Address Ix.Cert.MultiStark.K
      Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
  {t : Ix.Cert.Aggr.AcceptedAggrTree sem batchClaim rootStmt} {nodeProbs : List ℝ} {ε : ℝ}
  (gaps :
    Ix.Cert.AiurCompression.Bn254AiurCompressionTcbGaps sha256 manifest finalCfg finalHeaders bp outerKeys deferredKeys
      vk inp stmtLow stmtHigh d0 d1 finalPolicy w₂ prevAcc cur₂ wrapSrc wrapEntries glSrc glEntries narrowSrc
      narrowEntries finalSrc finalEntries t nodeProbs ε),
  False
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.Bn254AiurCompressionTcbGaps.inconsistent

/--
info: @Ix.Cert.AiurCompression.Bls12381AiurCompressionTcbGaps.inconsistent : ∀ {sha256 : List UInt8 → List UInt8}
  {manifest : Ix.Cert.AiurCompression.StageManifest} {finalCfg : MultiStark.Final.Configuration}
  {finalHeaders : List Ix.Cert.AiurCompression.NarrowClaimHeader}
  {assumptions : Ix.Cert.Compression.Bls12381.EndToEnd.Bls12381CryptoAssumptions}
  {starkParams : Ix.Cert.MultiStark.StarkParams} {requireUd : Bool}
  {bp : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381BilinearPairing} {outerKeys deferredKeys : bp.G2 × bp.G2}
  {vk : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381GnarkVerifyingKey}
  {inp : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381OuterInputs} {stmtLow stmtHigh : ℕ} {d0 d1 : bp.G1}
  {finalPolicy : Ix.Cert.AiurCompression.PackedPolicy} {w₂ : Ix.Cert.Compression.Bls12381.Field.BLS12381Fr}
  {prevAcc cur₂ : bp.G1 × bp.G1} {wrapSrc : Aiur.Generic.Source MultiStark.F} {wrapEntries : List String}
  {glSrc : Aiur.Generic.Source Ix.Cert.Compression.Bls12381.Field.BLS12381Fr} {glEntries : List String}
  {narrowSrc : Aiur.Generic.Source Ix.Cert.Compression.Bls12381.Field.BLS12381Fr} {narrowEntries : List String}
  {finalSrc : Aiur.Generic.Source Ix.Cert.Compression.Bls12381.Field.BLS12381Fr} {finalEntries : List String}
  {sem :
    Aggr.AggrSemantics Address Address Ix.DynamicLink.EvalAssumption Address Ix.Cert.MultiStark.K
      Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
  {batchClaim :
    ℕ →
      Aggr.ValidatorMode Address →
        (Address → Prop) → (Address → Prop) → (Address → Prop) → (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
  {rootStmt :
    Aggr.AggrNodeStmt Address Address Ix.DynamicLink.EvalAssumption Address Ix.Cert.MultiStark.K
      Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
  {t : Ix.Cert.Aggr.AcceptedAggrTree sem batchClaim rootStmt} {nodeProbs : List ℝ} {ε : ℝ}
  (gaps :
    Ix.Cert.AiurCompression.Bls12381AiurCompressionTcbGaps sha256 manifest finalCfg finalHeaders assumptions starkParams
      requireUd bp outerKeys deferredKeys vk inp stmtLow stmtHigh d0 d1 finalPolicy w₂ prevAcc cur₂ wrapSrc wrapEntries
      glSrc glEntries narrowSrc narrowEntries finalSrc finalEntries t nodeProbs ε),
  False
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.Bls12381AiurCompressionTcbGaps.inconsistent

/--
info: 'Ix.Cert.AiurCompression.Bn254AiurCompressionTcbGaps.inconsistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.Bn254AiurCompressionTcbGaps.inconsistent

/--
info: 'Ix.Cert.AiurCompression.Bls12381AiurCompressionTcbGaps.inconsistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.Bls12381AiurCompressionTcbGaps.inconsistent

/-- info: @Ix.Cert.AiurCompression.bn254AiurEscape_false_on_honest : ∀ {vk : Ix.Cert.Compression.OuterRelation.GnarkVerifyingKey}
  {inp : Ix.Cert.Compression.OuterRelation.OuterInputs} (bp : Ix.Cert.Compression.OuterRelation.BilinearPairing)
  (outerKeys deferredKeys : bp.G2 × bp.G2) (leftOf rightOf : Ix.Cert.Compression.OuterRelation.OuterOutputs → bp.G1)
  (d0 d1 : bp.G1) (ρ : Ix.Cert.Compression.Foreign.BN254Fr)
  (acc :
    Ix.Cert.Compression.OuterRelation.GnarkOuterAccepted vk inp fun out =>
      Ix.Cert.Compression.OuterRelation.FoldedPairingCheck bp outerKeys deferredKeys (leftOf out) (rightOf out) d0 d1 ρ)
  (manifest : Ix.Cert.AiurCompression.StageManifest) (finalPolicy : Ix.Cert.AiurCompression.PackedPolicy)
  (w₂ : Ix.Cert.Compression.Foreign.BN254Fr) (prevAcc cur₂ : bp.G1 × bp.G1),
  acc.outerProgram = vk.expectedProgram →
    finalPolicy = manifest.policy →
      (∀ (out : Ix.Cert.Compression.OuterRelation.OuterOutputs),
          vk.expectedProgram.Satisfied inp out → bp.outerPairingVal outerKeys (leftOf out) (rightOf out) = 1) →
        bp.deferredPairingVal deferredKeys d0 d1 = 1 →
          Ix.Cert.AiurCompression.bn254DeferredVal bp deferredKeys prevAcc = 1 ∧
                Ix.Cert.AiurCompression.bn254DeferredVal bp deferredKeys cur₂ = 1 ∨
              Ix.Cert.AiurCompression.bn254DeferredVal bp deferredKeys
                  (Ix.Cert.AiurCompression.bn254FoldStep bp w₂ prevAcc cur₂) ≠
                1 →
            ¬Ix.Cert.AiurCompression.Bn254AiurEscape bp outerKeys deferredKeys leftOf rightOf d0 d1 ρ acc manifest
                finalPolicy w₂ prevAcc cur₂ -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.bn254AiurEscape_false_on_honest

/-- info: @Ix.Cert.AiurCompression.bls12381AiurEscape_false_on_honest : ∀
  {vk : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381GnarkVerifyingKey}
  {inp : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381OuterInputs}
  (bp : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381BilinearPairing) (outerKeys deferredKeys : bp.G2 × bp.G2)
  (leftOf rightOf : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381OuterOutputs → bp.G1) (d0 d1 : bp.G1)
  (ρ : Ix.Cert.Compression.Bls12381.Field.BLS12381Fr)
  (acc :
    Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381GnarkOuterAccepted vk inp fun out =>
      Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381FoldedPairingCheck bp outerKeys deferredKeys (leftOf out)
        (rightOf out) d0 d1 ρ)
  (manifest : Ix.Cert.AiurCompression.StageManifest) (finalPolicy : Ix.Cert.AiurCompression.PackedPolicy)
  (w₂ : Ix.Cert.Compression.Bls12381.Field.BLS12381Fr) (prevAcc cur₂ : bp.G1 × bp.G1),
  acc.outerProgram = vk.expectedProgram →
    finalPolicy = manifest.policy →
      (∀ (out : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381OuterOutputs),
          vk.expectedProgram.Satisfied inp out → bp.outerPairingVal outerKeys (leftOf out) (rightOf out) = 1) →
        bp.deferredPairingVal deferredKeys d0 d1 = 1 →
          Ix.Cert.AiurCompression.bls12381DeferredVal bp deferredKeys prevAcc = 1 ∧
                Ix.Cert.AiurCompression.bls12381DeferredVal bp deferredKeys cur₂ = 1 ∨
              Ix.Cert.AiurCompression.bls12381DeferredVal bp deferredKeys
                  (Ix.Cert.AiurCompression.bls12381FoldStep bp w₂ prevAcc cur₂) ≠
                1 →
            ¬Ix.Cert.AiurCompression.Bls12381AiurEscape bp outerKeys deferredKeys leftOf rightOf d0 d1 ρ acc manifest
                finalPolicy w₂ prevAcc cur₂ -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.bls12381AiurEscape_false_on_honest

/-- info: @Ix.Cert.AiurCompression.aiur_compression_statement_binding_unique : ∀ {pin₁ pin₂ : Vector UInt8 32}
  (c₁ : Ix.Cert.AiurCompression.AiurStageStatementChain pin₁)
  (c₂ : Ix.Cert.AiurCompression.AiurStageStatementChain pin₂),
  ↑c₁.terminalLow = ↑c₂.terminalLow ∧ ↑c₁.terminalHigh = ↑c₂.terminalHigh ∨
      ↑c₁.terminalLow = ↑c₂.terminalLow ∧ ↑c₁.terminalHigh = ↑c₂.terminalHigh →
    Ix.Cert.AiurCompression.Blake3Collision
        (Ix.Cert.AiurCompression.compressWrapPreimage pin₁.toList
          (Vector.toList (Blake3.Pure.digest c₁.rootClaimsBytes)))
        (Ix.Cert.AiurCompression.compressWrapPreimage pin₂.toList
          (Vector.toList (Blake3.Pure.digest c₂.rootClaimsBytes))) ∨
      Ix.Cert.AiurCompression.Blake3Collision c₁.rootKeyBytes c₂.rootKeyBytes ∨
        Ix.Cert.AiurCompression.Blake3Collision c₁.rootClaimsBytes c₂.rootClaimsBytes ∨
          pin₁ = pin₂ ∧ c₁.rootKeyBytes = c₂.rootKeyBytes ∧ c₁.rootClaimsBytes = c₂.rootClaimsBytes -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.aiur_compression_statement_binding_unique

/-- info: 'Ix.Cert.AiurCompression.bn254AiurEscape_false_on_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.bn254AiurEscape_false_on_honest

/-- info: 'Ix.Cert.AiurCompression.bls12381AiurEscape_false_on_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.bls12381AiurEscape_false_on_honest

/-- info: 'Ix.Cert.AiurCompression.aiur_compression_statement_binding_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.aiur_compression_statement_binding_unique

/-! ## 2. Constructive Negative Controls (`#check` & `#print axioms`) -/

/-- info: Ix.Cert.AiurCompression.negControl_wrong_root_key_pin : ∀ (trustedPin : Vector UInt8 32)
  (rogueKeyBytes claimsBytes : List UInt8),
  Blake3.Pure.digest rogueKeyBytes ≠ trustedPin →
    (∀ (c : Ix.Cert.AiurCompression.AiurStageStatementChain trustedPin), c.rootKeyBytes ≠ rogueKeyBytes) ∧
      Ix.Cert.AiurCompression.compressWrapPreimage (Vector.toList (Blake3.Pure.digest rogueKeyBytes))
          (Vector.toList (Blake3.Pure.digest claimsBytes)) ≠
        Ix.Cert.AiurCompression.compressWrapPreimage trustedPin.toList (Vector.toList (Blake3.Pure.digest claimsBytes)) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.negControl_wrong_root_key_pin

/-- info: Ix.Cert.AiurCompression.negControl_tampered_statement_words : ∀ (low : ℕ) {ws₁ ws₂ : List ℕ},
  ws₁.length = 8 →
    (∀ w ∈ ws₁, w < 2 ^ 32) →
      ws₂.length = 8 →
        (∀ w ∈ ws₂, w < 2 ^ 32) →
          ws₁ ≠ ws₂ →
            ↑low + 1 ≠ ↑low ∧
              ↑low + 1 ≠ ↑low ∧
                ¬(↑(Ix.Cert.AiurCompression.packU32WordsToLimbs ws₁).1 =
                        ↑(Ix.Cert.AiurCompression.packU32WordsToLimbs ws₂).1 ∧
                      ↑(Ix.Cert.AiurCompression.packU32WordsToLimbs ws₁).2 =
                        ↑(Ix.Cert.AiurCompression.packU32WordsToLimbs ws₂).2) ∧
                  ¬(↑(Ix.Cert.AiurCompression.packU32WordsToLimbs ws₁).1 =
                        ↑(Ix.Cert.AiurCompression.packU32WordsToLimbs ws₂).1 ∧
                      ↑(Ix.Cert.AiurCompression.packU32WordsToLimbs ws₁).2 =
                        ↑(Ix.Cert.AiurCompression.packU32WordsToLimbs ws₂).2) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.negControl_tampered_statement_words

/-- info: Ix.Cert.AiurCompression.negControl_cross_curve_downgrade : ∀ (extDeg protoVer digestBytes : ℕ)
  (starkParams : Ix.Cert.MultiStark.StarkParams) (requireUd : Bool)
  (spec : Ix.Cert.Compression.Security128.PairingCurveSpec) (P : Ix.Cert.Compression.Bls12381.CurveMsm.bls12381G1.Point)
  (z τ : Ix.Cert.Compression.Bls12381.Field.BLS12381Fr),
  ¬Ix.Cert.AiurCompression.AiurCompression128Ok extDeg protoVer digestBytes starkParams requireUd
        Ix.Cert.AiurCompression.OuterPairingCurve.bn254 spec ∧
    ¬Ix.Cert.AiurCompression.AiurCompression128Ok extDeg protoVer digestBytes starkParams requireUd
          Ix.Cert.AiurCompression.OuterPairingCurve.bls12381 Ix.Cert.Compression.Security128.bls12381UncheckedSpec ∧
      ¬Ix.Cert.Compression.Bls12381.CurveMsm.InPrimeSubgroup
            Ix.Cert.Compression.Bls12381.CurveMsm.bls12381TorsionPoint ∧
        ¬Ix.Cert.Compression.Bls12381.RecursiveKzg.Bls12381KzgPairingCheck
            Ix.Cert.Compression.Bls12381.CurveMsm.bls12381TorsionPoint P z τ -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.negControl_cross_curve_downgrade

/-- info: Ix.Cert.AiurCompression.negControl_protocol_downgrade : ¬Ix.Cert.AiurCompression.AiurCompression128Ok 2 6 64
      Ix.Cert.MultiStark.Security128.v6Ud160Params true Ix.Cert.AiurCompression.OuterPairingCurve.bls12381
      Ix.Cert.Compression.Security128.bls12381CurveSpec ∧
  ¬Ix.Cert.AiurCompression.AiurCompression128Ok 3 5 64 Ix.Cert.MultiStark.Security128.v6Ud160Params true
        Ix.Cert.AiurCompression.OuterPairingCurve.bls12381 Ix.Cert.Compression.Security128.bls12381CurveSpec ∧
    ¬Ix.Cert.AiurCompression.AiurCompression128Ok 3 6 32 Ix.Cert.MultiStark.Security128.v6Ud160Params true
          Ix.Cert.AiurCompression.OuterPairingCurve.bls12381 Ix.Cert.Compression.Security128.bls12381CurveSpec ∧
      ¬Ix.Cert.AiurCompression.AiurCompression128Ok 3 6 48 Ix.Cert.MultiStark.Security128.v6Ud160Params true
            Ix.Cert.AiurCompression.OuterPairingCurve.bls12381 Ix.Cert.Compression.Security128.bls12381CurveSpec ∧
        ¬Ix.Cert.AiurCompression.AiurCompression128Ok 3 6 64 Ix.Cert.MultiStark.Security128.v5Default100Params true
              Ix.Cert.AiurCompression.OuterPairingCurve.bls12381 Ix.Cert.Compression.Security128.bls12381CurveSpec ∧
          ¬Ix.Cert.AiurCompression.AiurCompression128Ok 3 6 64 Ix.Cert.MultiStark.Security128.deceptive455Params false
              Ix.Cert.AiurCompression.OuterPairingCurve.bls12381 Ix.Cert.Compression.Security128.bls12381CurveSpec -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.negControl_protocol_downgrade

/-- info: Ix.Cert.AiurCompression.negControl_unpinned_manifest : ∀ (sha256 : List UInt8 → List UInt8)
  (m : Ix.Cert.AiurCompression.StageManifest) (bytes : List UInt8),
  ¬Ix.Cert.AiurCompression.ProductPin.Pinned sha256 { bytes := bytes, blake3Pin := none, sha256Pin := none } ∧
    (m.glKey.blake3Pin = none → m.glKey.sha256Pin = none → ¬Ix.Cert.AiurCompression.ManifestPinned sha256 m) ∧
      (m.format ≠ Ix.Cert.AiurCompression.stagesManifestFormat → ¬Ix.Cert.AiurCompression.ManifestPinned sha256 m) ∧
        (Blake3.Pure.digest m.manifestBytes ≠ m.manifestCallerPin → ¬Ix.Cert.AiurCompression.ManifestPinned sha256 m) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.negControl_unpinned_manifest

/-- info: Ix.Cert.AiurCompression.negControl_policy_key_and_stage_tampering : ∀ (sha256 : List UInt8 → List UInt8)
  (m : Ix.Cert.AiurCompression.StageManifest) {p₁ p₂ : Ix.Cert.AiurCompression.PackedPolicy},
  p₁.WellFormed →
    p₂.WellFormed →
      ∀ (cfg : MultiStark.Final.Configuration) (headers : List Ix.Cert.AiurCompression.NarrowClaimHeader),
        (p₁.glKeyDigest ≠ p₂.glKeyDigest → p₁.encode ≠ p₂.encode) ∧
          (p₁.anchors ≠ p₂.anchors → p₁.encode ≠ p₂.encode) ∧
            (Vector.toList (Blake3.Pure.digest m.glKey.bytes) ≠ m.policy.glKeyDigest →
                ¬Ix.Cert.AiurCompression.ManifestPinned sha256 m) ∧
              (cfg.minStage < 2 → Ix.Cert.AiurCompression.validateFinalNarrowConfig cfg headers ≠ Except.ok ()) ∧
                ((List.map (fun x => x.values) headers).sum ≠ 21 →
                  Ix.Cert.AiurCompression.validateFinalNarrowConfig cfg headers ≠ Except.ok ()) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.negControl_policy_key_and_stage_tampering

/-- info: 'Ix.Cert.AiurCompression.negControl_wrong_root_key_pin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.negControl_wrong_root_key_pin

/-- info: 'Ix.Cert.AiurCompression.negControl_tampered_statement_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.negControl_tampered_statement_words

/-- info: 'Ix.Cert.AiurCompression.negControl_cross_curve_downgrade' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.negControl_cross_curve_downgrade

/-- info: 'Ix.Cert.AiurCompression.negControl_protocol_downgrade' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.negControl_protocol_downgrade

/-- info: 'Ix.Cert.AiurCompression.negControl_unpinned_manifest' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.negControl_unpinned_manifest

/-- info: 'Ix.Cert.AiurCompression.negControl_policy_key_and_stage_tampering' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.negControl_policy_key_and_stage_tampering

/-! ## 3. Deployed MultiStark AST & Export-Configuration Pins -/

/-- info: Ix.Cert.AiurCompression.compressWrapProgram_ast_pinned : Ix.Cert.AiurCompression.CompressWrapAstPinned MultiStark.compressWrapProgram = true -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.compressWrapProgram_ast_pinned

/-- info: Ix.Cert.AiurCompression.compressGLProgram_ast_pinned : Ix.Cert.AiurCompression.CompressGLAstPinned MultiStark.CompressGL.program = true -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.compressGLProgram_ast_pinned

/-- info: Ix.Cert.AiurCompression.kzgPackedTerminal_ast_pinned : Ix.Cert.AiurCompression.KzgPackedTerminalAstPinned MultiStark.Source.kzgPackedTerminal = true -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.kzgPackedTerminal_ast_pinned

/-- info: Ix.Cert.AiurCompression.compressBN_previous_ast_pinned : Ix.Cert.MultiStarkRefinement.fnHasCallsAndAsserts MultiStark.Source.compressBN "CompressBN" "previous" ["take8", "KzgAccumulator::unpack"] 7 = true ∧ (match Ix.Cert.MultiStarkRefinement.findModuleFunction? MultiStark.Source.compressBN "CompressBN" "previous" with | some fdecl => Ix.Cert.MultiStarkRefinement.exprMatchLitArms fdecl.body | none => []) = [1] -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.compressBN_previous_ast_pinned

/-- info: Ix.Cert.AiurCompression.compressBNPacked_fold_ast_pinned : Ix.Cert.AiurCompression.fnGlobalsEq MultiStark.Source.compressBNPacked "CompressBNPacked" "fold_domain" Ix.Cert.AiurCompression.foldDomainGlobalsRev = true ∧ Ix.Cert.MultiStarkRefinement.fnHasCallsAndAsserts MultiStark.Source.compressBNPacked "CompressBNPacked" "fold_weight" ["KzgIO::fields_to_bytes", "BN254G1::point_list_bytes", "CompressBN::digest_onto", "KzgIO::prepend4", "UInt32::to_bytes", "KzgIO::digest_word", "KzgTranscript::sample", "KzgTranscript::observe_bytes", "fold_domain", "Fields::is_zero"] 1 = true ∧ Ix.Cert.MultiStarkRefinement.fnHasCallsAndAsserts MultiStark.Source.compressBNPacked "CompressBNPacked" "fold" ["fold_weight", "KzgMsm::msm", "BN254G1::add"] 0 = true -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.compressBNPacked_fold_ast_pinned

/-- info: Ix.Cert.AiurCompression.kzgPackedDeserialize_formats_ast_pinned : Ix.Cert.AiurCompression.fnHasLiterals MultiStark.Source.kzgPackedDeserialize "KzgPackedDeserialize" "chain_policy" [73, 88, 65, 85, 75, 71, 48, 49, 128] = true ∧ Ix.Cert.AiurCompression.fnHasLiterals MultiStark.Source.kzgPackedDeserialize "KzgPackedDeserialize" "key" [73, 88, 65, 85, 83, 75, 48, 50, 29, 0, 1, 28, 128] = true ∧ Ix.Cert.AiurCompression.fnHasLiterals MultiStark.Source.kzgPackedDeserialize "KzgPackedDeserialize" "proof" [73, 88, 65, 85, 83, 80, 48, 49] = true -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.kzgPackedDeserialize_formats_ast_pinned

/-- info: @Ix.Cert.AiurCompression.finalSource_ok_spec : ∀ {cfg : MultiStark.Final.Configuration} {prog : Aiur.Modules.Program ℕ}, MultiStark.Final.source cfg = Except.ok prog → Ix.Cert.AiurCompression.FinalConfigValid cfg ∧ Ix.Cert.AiurCompression.CompressFinalAstPinned prog = true -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.finalSource_ok_spec

/-- info: @Ix.Cert.AiurCompression.validateFinalNarrowConfig_ok_spec : ∀ {cfg : MultiStark.Final.Configuration} {headers : List Ix.Cert.AiurCompression.NarrowClaimHeader}, Ix.Cert.AiurCompression.validateFinalNarrowConfig cfg headers = Except.ok () → Ix.Cert.AiurCompression.FinalNarrowConfigValid cfg headers -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.validateFinalNarrowConfig_ok_spec

/-- info: 'Ix.Cert.AiurCompression.compressWrapSource_ast_pinned' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.compressWrapSource_ast_pinned

/-- info: 'Ix.Cert.AiurCompression.compressWrapProgram_ast_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.compressWrapProgram_ast_pinned

/-- info: 'Ix.Cert.AiurCompression.compressGLSource_ast_pinned' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.compressGLSource_ast_pinned

/-- info: 'Ix.Cert.AiurCompression.compressGLProgram_ast_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.compressGLProgram_ast_pinned

/-- info: 'Ix.Cert.AiurCompression.kzgPackedTerminal_ast_pinned' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.kzgPackedTerminal_ast_pinned

/-- info: 'Ix.Cert.AiurCompression.compressBN_previous_ast_pinned' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.compressBN_previous_ast_pinned

/-- info: 'Ix.Cert.AiurCompression.compressBNPacked_fold_ast_pinned' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.compressBNPacked_fold_ast_pinned

/-- info: 'Ix.Cert.AiurCompression.kzgPackedDeserialize_formats_ast_pinned' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.kzgPackedDeserialize_formats_ast_pinned

/-- info: 'Ix.Cert.AiurCompression.finalSource_ok_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.finalSource_ok_spec

/-- info: 'Ix.Cert.AiurCompression.validateFinalNarrowConfig_ok_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.validateFinalNarrowConfig_ok_spec

/-- info: 'Ix.Cert.AiurCompression.validateFinalNarrowConfig_rejects_stage_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.validateFinalNarrowConfig_rejects_stage_one

/-- info: 'Ix.Cert.AiurCompression.validateFinalNarrowConfig_rejects_wrong_header_width' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.validateFinalNarrowConfig_rejects_wrong_header_width

/-! ## 4. Statement Binding, Codecs, Policy & Manifest Integrity -/

/-- info: @Ix.Cert.AiurCompression.compressWrap_statement_binds_root_or_collision : ∀ {k₁ c₁ k₂ c₂ : List UInt8}, k₁.length = 32 → k₂.length = 32 → Ix.Cert.AiurCompression.compressWrapStatementDigest k₁ c₁ = Ix.Cert.AiurCompression.compressWrapStatementDigest k₂ c₂ → Ix.Cert.AiurCompression.Blake3Collision (Ix.Cert.AiurCompression.compressWrapPreimage k₁ c₁) (Ix.Cert.AiurCompression.compressWrapPreimage k₂ c₂) ∨ k₁ = k₂ ∧ c₁ = c₂ -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.compressWrap_statement_binds_root_or_collision

/-- info: @Ix.Cert.AiurCompression.PackedPolicy.encode_injective : ∀ {p₁ p₂ : Ix.Cert.AiurCompression.PackedPolicy}, p₁.WellFormed → p₂.WellFormed → p₁.encode = p₂.encode → p₁ = p₂ -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.PackedPolicy.encode_injective

/-- info: @Ix.Cert.AiurCompression.manifestPinned_chain_integrity : ∀ {sha256 : List UInt8 → List UInt8} {m : Ix.Cert.AiurCompression.StageManifest}, Ix.Cert.AiurCompression.ManifestPinned sha256 m → m.glKeyAnchors = m.outerPairingAnchors ∧ m.narrowKeyAnchors = m.outerPairingAnchors ∧ m.finalAnchors = m.outerPairingAnchors ∧ m.policy.glKeyDigest = Vector.toList (Blake3.Pure.digest m.glKey.bytes) ∧ m.policy.narrowKeyDigest = Vector.toList (Blake3.Pure.digest m.narrowKey.bytes) ∧ m.finalPolicyDigestWords = Ix.Cert.AiurCompression.packBytes32ToU32Words m.policy.digest.toList -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.manifestPinned_chain_integrity

/-- info: Ix.Cert.AiurCompression.aiurCompression128_v6_ud_bls12381_ok : Ix.Cert.AiurCompression.AiurCompression128Ok 3 6 64 Ix.Cert.MultiStark.Security128.v6Ud160Params true Ix.Cert.AiurCompression.OuterPairingCurve.bls12381 Ix.Cert.Compression.Security128.bls12381CurveSpec -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.aiurCompression128_v6_ud_bls12381_ok

/-- info: Ix.Cert.AiurCompression.aiurCompression128_v6_johnson128_bls12381_ok : Ix.Cert.AiurCompression.AiurCompression128Ok 3 6 64 Ix.Cert.MultiStark.Security128.v6Johnson128Params false Ix.Cert.AiurCompression.OuterPairingCurve.bls12381 Ix.Cert.Compression.Security128.bls12381CurveSpec -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.aiurCompression128_v6_johnson128_bls12381_ok

/-- info: 'Ix.Cert.AiurCompression.compressWrap_statement_binds_root_or_collision' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.compressWrap_statement_binds_root_or_collision

/-- info: 'Ix.Cert.AiurCompression.packBytes32ToU32Words_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.packBytes32ToU32Words_injective

/-- info: 'Ix.Cert.AiurCompression.unpack_pack_u32Words_roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.unpack_pack_u32Words_roundtrip

/-- info: 'Ix.Cert.AiurCompression.packU32WordsToLimbs_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.packU32WordsToLimbs_injective

/-- info: 'Ix.Cert.AiurCompression.limbs_embed_bn254_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.limbs_embed_bn254_injective

/-- info: 'Ix.Cert.AiurCompression.limbs_embed_bls12381_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.limbs_embed_bls12381_injective

/-- info: 'Ix.Cert.AiurCompression.goldilocks_emulation_no_wrap_bn254' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.goldilocks_emulation_no_wrap_bn254

/-- info: 'Ix.Cert.AiurCompression.goldilocks_emulation_no_wrap_bls12381' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.goldilocks_emulation_no_wrap_bls12381

/-- info: 'Ix.Cert.AiurCompression.PackedPolicy.encode_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.PackedPolicy.encode_length

/-- info: 'Ix.Cert.AiurCompression.PackedPolicy.encode_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.PackedPolicy.encode_injective

/-- info: 'Ix.Cert.AiurCompression.packedPolicy_digest_binds_or_collision' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.packedPolicy_digest_binds_or_collision

/-- info: 'Ix.Cert.AiurCompression.manifestPinned_chain_integrity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.manifestPinned_chain_integrity

/-- info: 'Ix.Cert.AiurCompression.statementChain_unique_bn254_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.statementChain_unique_bn254_or_collision

/-- info: 'Ix.Cert.AiurCompression.statementChain_unique_bls12381_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.statementChain_unique_bls12381_or_collision

/-- info: 'Ix.Cert.AiurCompression.aiurCompression128_v6_ud_bls12381_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.aiurCompression128_v6_ud_bls12381_ok

/-- info: 'Ix.Cert.AiurCompression.aiurCompression128_v6_johnson128_bls12381_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.aiurCompression128_v6_johnson128_bls12381_ok

/-! ## 5. Deferred KZG Folding & Canonical Affine Codecs -/

/-- info: Ix.Cert.AiurCompression.bn254_l3_deferred_fold_sound : ∀ (bp : Ix.Cert.Compression.OuterRelation.BilinearPairing) (anchors : bp.G2 × bp.G2) (w₁ w₂ : Ix.Cert.Compression.Foreign.BN254Fr) (cur₁ cur₂ : bp.G1 × bp.G1), Ix.Cert.AiurCompression.bn254DeferredVal bp anchors (Ix.Cert.AiurCompression.bn254FoldStep bp w₂ (Ix.Cert.AiurCompression.bn254FoldStep bp w₁ (0, 0) cur₁) cur₂) = 1 → Ix.Cert.AiurCompression.bn254DeferredVal bp anchors cur₁ = 1 ∧ Ix.Cert.AiurCompression.bn254DeferredVal bp anchors cur₂ = 1 ∨ Ix.Cert.AiurCompression.bn254DeferredVal bp anchors (Ix.Cert.AiurCompression.bn254FoldStep bp w₂ (Ix.Cert.AiurCompression.bn254FoldStep bp w₁ (0, 0) cur₁) cur₂) = 1 ∧ {w' | Ix.Cert.AiurCompression.bn254DeferredVal bp anchors (Ix.Cert.AiurCompression.bn254FoldStep bp w' (Ix.Cert.AiurCompression.bn254FoldStep bp w₁ (0, 0) cur₁) cur₂) = 1}.card ≤ 1 -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.bn254_l3_deferred_fold_sound

/-- info: Ix.Cert.AiurCompression.bn254_kstage_deferred_fold_sound : ∀ (bp : Ix.Cert.Compression.OuterRelation.BilinearPairing) (anchors : bp.G2 × bp.G2) (stages : List (Ix.Cert.Compression.Foreign.BN254Fr × bp.G1 × bp.G1)), Ix.Cert.AiurCompression.bn254DeferredVal bp anchors (Ix.Cert.AiurCompression.bn254FoldChain bp stages) = 1 → (∀ s ∈ stages, Ix.Cert.AiurCompression.bn254DeferredVal bp anchors s.2 = 1) ∨ ∃ i, have w := stages[↑i].1; have cur := stages[↑i].2; have prev := Ix.Cert.AiurCompression.bn254FoldChain bp (List.drop (↑i + 1) stages); Ix.Cert.AiurCompression.bn254DeferredVal bp anchors (Ix.Cert.AiurCompression.bn254FoldStep bp w prev cur) = 1 ∧ {w' | Ix.Cert.AiurCompression.bn254DeferredVal bp anchors (Ix.Cert.AiurCompression.bn254FoldStep bp w' prev cur) = 1}.card ≤ 1 -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.bn254_kstage_deferred_fold_sound

/-- info: Ix.Cert.AiurCompression.bn254_kstage_deferred_fold_nonvacuous : ∀ (bp : Ix.Cert.Compression.OuterRelation.BilinearPairing) (anchors : bp.G2 × bp.G2) (stages : List (Ix.Cert.Compression.Foreign.BN254Fr × bp.G1 × bp.G1)), (∀ s ∈ stages, Ix.Cert.AiurCompression.bn254DeferredVal bp anchors s.2 = 1) → ¬∃ i, have w := stages[↑i].1; have cur := stages[↑i].2; have prev := Ix.Cert.AiurCompression.bn254FoldChain bp (List.drop (↑i + 1) stages); Ix.Cert.AiurCompression.bn254DeferredVal bp anchors (Ix.Cert.AiurCompression.bn254FoldStep bp w prev cur) = 1 ∧ {w' | Ix.Cert.AiurCompression.bn254DeferredVal bp anchors (Ix.Cert.AiurCompression.bn254FoldStep bp w' prev cur) = 1}.card ≤ 1 -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.bn254_kstage_deferred_fold_nonvacuous

/-- info: Ix.Cert.AiurCompression.bls12381_l3_deferred_fold_sound : ∀ (bp : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381BilinearPairing) (anchors : bp.G2 × bp.G2) (w₁ w₂ : Ix.Cert.Compression.Bls12381.Field.BLS12381Fr) {cur₁ cur₂ : bp.G1 × bp.G1}, Ix.Cert.AiurCompression.BlsPairInSubgroup bp cur₁ → Ix.Cert.AiurCompression.BlsPairInSubgroup bp cur₂ → Ix.Cert.AiurCompression.bls12381DeferredVal bp anchors (Ix.Cert.AiurCompression.bls12381FoldStep bp w₂ (Ix.Cert.AiurCompression.bls12381FoldStep bp w₁ (0, 0) cur₁) cur₂) = 1 → Ix.Cert.AiurCompression.BlsPairInSubgroup bp (Ix.Cert.AiurCompression.bls12381FoldStep bp w₂ (Ix.Cert.AiurCompression.bls12381FoldStep bp w₁ (0, 0) cur₁) cur₂) ∧ (Ix.Cert.AiurCompression.bls12381DeferredVal bp anchors cur₁ = 1 ∧ Ix.Cert.AiurCompression.bls12381DeferredVal bp anchors cur₂ = 1 ∨ Ix.Cert.AiurCompression.bls12381DeferredVal bp anchors (Ix.Cert.AiurCompression.bls12381FoldStep bp w₂ (Ix.Cert.AiurCompression.bls12381FoldStep bp w₁ (0, 0) cur₁) cur₂) = 1 ∧ {w' | Ix.Cert.AiurCompression.bls12381DeferredVal bp anchors (Ix.Cert.AiurCompression.bls12381FoldStep bp w' (Ix.Cert.AiurCompression.bls12381FoldStep bp w₁ (0, 0) cur₁) cur₂) = 1}.card ≤ 1) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.bls12381_l3_deferred_fold_sound

/-- info: Ix.Cert.AiurCompression.bls12381_kstage_deferred_fold_sound : ∀ (bp : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381BilinearPairing) (anchors : bp.G2 × bp.G2) (stages : List (Ix.Cert.Compression.Bls12381.Field.BLS12381Fr × bp.G1 × bp.G1)), (∀ s ∈ stages, Ix.Cert.AiurCompression.BlsPairInSubgroup bp s.2) → Ix.Cert.AiurCompression.bls12381DeferredVal bp anchors (Ix.Cert.AiurCompression.bls12381FoldChain bp stages) = 1 → Ix.Cert.AiurCompression.BlsPairInSubgroup bp (Ix.Cert.AiurCompression.bls12381FoldChain bp stages) ∧ ((∀ s ∈ stages, Ix.Cert.AiurCompression.bls12381DeferredVal bp anchors s.2 = 1) ∨ ∃ i, have w := stages[↑i].1; have cur := stages[↑i].2; have prev := Ix.Cert.AiurCompression.bls12381FoldChain bp (List.drop (↑i + 1) stages); Ix.Cert.AiurCompression.BlsPairInSubgroup bp prev ∧ Ix.Cert.AiurCompression.BlsPairInSubgroup bp cur ∧ Ix.Cert.AiurCompression.bls12381DeferredVal bp anchors (Ix.Cert.AiurCompression.bls12381FoldStep bp w prev cur) = 1 ∧ {w' | Ix.Cert.AiurCompression.bls12381DeferredVal bp anchors (Ix.Cert.AiurCompression.bls12381FoldStep bp w' prev cur) = 1}.card ≤ 1) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.bls12381_kstage_deferred_fold_sound

/-- info: Ix.Cert.AiurCompression.bls12381_kstage_deferred_fold_nonvacuous : ∀ (bp : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381BilinearPairing) (anchors : bp.G2 × bp.G2) (stages : List (Ix.Cert.Compression.Bls12381.Field.BLS12381Fr × bp.G1 × bp.G1)), (∀ s ∈ stages, Ix.Cert.AiurCompression.BlsPairInSubgroup bp s.2) → (∀ s ∈ stages, Ix.Cert.AiurCompression.bls12381DeferredVal bp anchors s.2 = 1) → ¬∃ i, have w := stages[↑i].1; have cur := stages[↑i].2; have prev := Ix.Cert.AiurCompression.bls12381FoldChain bp (List.drop (↑i + 1) stages); Ix.Cert.AiurCompression.BlsPairInSubgroup bp prev ∧ Ix.Cert.AiurCompression.BlsPairInSubgroup bp cur ∧ Ix.Cert.AiurCompression.bls12381DeferredVal bp anchors (Ix.Cert.AiurCompression.bls12381FoldStep bp w prev cur) = 1 ∧ {w' | Ix.Cert.AiurCompression.bls12381DeferredVal bp anchors (Ix.Cert.AiurCompression.bls12381FoldStep bp w' prev cur) = 1}.card ≤ 1 -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.bls12381_kstage_deferred_fold_nonvacuous

/-- info: 'Ix.Cert.AiurCompression.bn254_foldStep_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.bn254_foldStep_sound

/-- info: 'Ix.Cert.AiurCompression.bn254_l3_deferred_fold_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.bn254_l3_deferred_fold_sound

/-- info: 'Ix.Cert.AiurCompression.bn254_kstage_deferred_fold_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.bn254_kstage_deferred_fold_sound

/-- info: 'Ix.Cert.AiurCompression.bn254_kstage_deferred_fold_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.bn254_kstage_deferred_fold_nonvacuous

/-- info: 'Ix.Cert.AiurCompression.bls12381_foldStep_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.bls12381_foldStep_sound

/-- info: 'Ix.Cert.AiurCompression.bls12381_l3_deferred_fold_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.bls12381_l3_deferred_fold_sound

/-- info: 'Ix.Cert.AiurCompression.bls12381_kstage_deferred_fold_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.bls12381_kstage_deferred_fold_sound

/-- info: 'Ix.Cert.AiurCompression.bls12381_kstage_deferred_fold_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.bls12381_kstage_deferred_fold_nonvacuous

/-- info: 'Ix.Cert.AiurCompression.bn254AffineU80_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.bn254AffineU80_injective

/-- info: 'Ix.Cert.AiurCompression.bls12381AffineU80_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.bls12381AffineU80_injective

/-! ## 6. Stage-Bridge Wrappers & Underlying Compiler / Tiling / PLONK / CertiFRI Pins -/

/-- info: 'Ix.Cert.AiurCompression.GoldilocksWideStageWitness.eval_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.GoldilocksWideStageWitness.eval_sound

/-- info: 'Ix.Cert.AiurCompression.Bn254GroupedWideStageWitness.eval_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.Bn254GroupedWideStageWitness.eval_sound

/-- info: 'Ix.Cert.AiurCompression.FieldGroupedSharedStageWitness.eval_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.FieldGroupedSharedStageWitness.eval_sound

/-- info: 'Ix.Cert.AiurCompression.NarrowCompactStageWitness.eval_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.NarrowCompactStageWitness.eval_sound

/-- info: 'Ix.Cert.AiurCompression.PlonkSharedTerminalWitness.eval_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.PlonkSharedTerminalWitness.eval_sound

/-- info: 'Aiur.Tiling.Claims.wide_heap_sound_goldilocks_exported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Aiur.Tiling.Claims.wide_heap_sound_goldilocks_exported

/-- info: 'Aiur.Tiling.Claims.grouped_heap_sound_bn254_exported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Aiur.Tiling.Claims.grouped_heap_sound_bn254_exported

/-- info: 'Aiur.Tiling.Grouped.grouped_heap_sound_shared_compiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Aiur.Tiling.Grouped.grouped_heap_sound_shared_compiled

/-- info: 'Aiur.Tiling.Claims.narrow_heap_sound_compact_exported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Aiur.Tiling.Claims.narrow_heap_sound_compact_exported

/-- info: 'Aiur.Plonk.plonk_shared_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Aiur.Plonk.plonk_shared_heap_sound

/-- info: 'Ix.Cert.Compression.OuterRelation.gnark_folded_pairing_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.OuterRelation.gnark_folded_pairing_sound

/-- info: 'Ix.Cert.Compression.Bls12381.OuterRelation.bls12381_gnark_folded_pairing_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.OuterRelation.bls12381_gnark_folded_pairing_sound

/-- info: 'CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_blake2b512_johnson_lb3_78_128_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_blake2b512_johnson_lb3_78_128_unconditional
