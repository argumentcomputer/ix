import Ix.Cert.AiurCompression.EndToEnd
import Ix.Cert.AiurCompression.Consistency

/-! # Aiur Compression Pipeline Soundness, Consistency & TCB Audit (`Ix.Cert.AiurCompression.Audit`)

Mechanically pins (via `#guard_msgs` on `#check` and `#print axioms`) the non-vacuous
end-to-end L3 BN254 Aiur proof-compression soundness theorem, its constructive satisfiability
witnesses (proving non-vacuity and ruling out inconsistent hypothesis bundles), exact
`MultiStark` AST pins, statement-binding and manifest integrity theorems, deferred KZG folding,
exempt-SCC compiler/tiling/PLONK depth bridges, and negative controls:

```text
  ix_aggr (MultiStark.aggregateProgram)
    │  Stage 0 → Stage 1 digest: Blake3("ix/compress-wrap/v1\0" || rootKeyPin[32] || Blake3(rootClaims))
    ▼
  Stage 1: CompressWrap        (Goldilocks wide tiling: DepthBridge.wide_heap_sound_goldilocks_structural)
    │  two-layer `--aiur-stages` wrapper digest (or single-layer direct root digest)
    ▼
  Stage 2: CompressGL          (BN254 grouped wide tiling: DepthBridge.grouped_heap_sound_bn254_structural)
    │  8 u32 statement words + deferred KZG accumulator (0 → cur₁)
    ▼
  Stage 3: CompressNarrowFixed (compact narrow tiling: DepthBridge.narrow_heap_sound_compact_structural)
    │  packed policy digest + stage 1 + 8 u32 words + folded accumulator (cur₁ → cur₂)
    ▼
  Stage 4: CompressFinalNarrow (shared-heap PLONK SCS: DepthBridge.plonk_shared_heap_sound_structural)
    │  (statement_low, statement_high) ∈ [0, 2^128)^2 + 18-word `affine-u80-v1` deferred pair
    ▼
  Outer Verifier: pure-Rust native PLONK (`aiur_backend::plonk::native`, `ix-aiur-scs-v1`)
                  & `contracts/plonk/src/IxL3PlonkVerifier.sol` (OuterRelation.aiur_scs_outer_sound)
```

## Pinned Properties & Non-Vacuity Guarantee (Zero Custom Axioms)
1. **End-to-End L3 BN254 Soundness (`EndToEnd.lean`)**:
   `aiur_compression_l3_bn254_sound` composes the `ix-aiur-scs-v1` outer native PLONK verifier
   with all four Aiur compression stages and `ix_aggr` certification under both the deployed
   two-layer `WrapPolicy::statement_for` / `IxL3PlonkVerifier.sol` statement chain
   (`StatementPolicy.twoLayerWrap`) and the single-layer fixed-wrapper policy
   (`StatementPolicy.singleLayerDirect`). Stage 3 → Stage 4 accumulator handoff
   (`prevAcc = acc₁`) and terminal 18-word `affine-u80-v1` outputs are decoded directly from each
   execution's returned `SourceValue` via `DepthBridge.represents_field_tuple`.
2. **Constructive Satisfiability / Non-Vacuity Gate (`Consistency.lean`)**:
   `Consistency.bn254AiurCompression_consistent` (two-layer mode) and
   `Consistency.bn254AiurCompression_singleLayer_consistent` (single-layer mode) constructively
   inhabit the complete `Bn254AiurCompressionTcbGaps` hypothesis bundle over a nontrivial pairing
   (`toyPairing_nontrivial`: `e(1, 1) ≠ 1`) with real kernel-compiled stage witnesses across all
   four stages (`GoldilocksWideStageWitness`, `Bn254GroupedWideStageWitness`,
   `NarrowCompactStageWitness`, `PlonkSharedTerminalWitness`), AND prove `¬ Bn254AiurEscape` so
   the main non-escape soundness conclusion is genuinely reachable.
3. **Outer Native PLONK SCS Relation & Negative Controls (`OuterRelation.lean`, `EndToEnd.lean`)**:
   `aiur_scs_outer_sound` models the pure-Rust `aiur_backend::plonk::native` `ix-aiur-scs-v1`
   verifier and `contracts/plonk/src/IxL3PlonkVerifier.sol` (SHA-256 pinning of SCS and pairing
   parameters, `[statement_low, statement_high]` public limbs, 18-word `affine-u80-v1` output
   decoding, and BN254 deferred pairing check), backed by constructive negative controls rejecting
   tampered public limbs, non-canonical infinity flags, wrong root key pins, tampered statement
   words, unpinned manifests, policy/stage/header tampering, and BLS12-381 3-torsion points.
4. **Exact Program AST & Export-Configuration Pins (`ProgramPins.lean`)**:
   Exact function-list AST equality (`moduleFunctionsExactPinned`, implying identical serialized
   pure-Lean BLAKE3 AST digests) for `MultiStark.compressWrapProgram`, `CompressGL.program`,
   `Source.kzgPackedTerminal`, `Source.compressBN`, `Source.compressBNPacked`,
   `Source.kzgPackedDeserialize`, and `MultiStark.Final.source`, plus `validateFinalNarrowConfig`
   (`minStage ≥ 2`, 21-word `step_v1` header coverage) and mutation rejection
   (`exactPin_rejects_dropped_anchor_check`).
5. **Statement Binding, Deferred Folding & Exempt-SCC Depth Bridges
   (`StatementBinding.lean`, `DeferredFold.lean`, `DepthBridge.lean`, `StageBridge.lean`)**:
   Full two-layer & single-layer statement chain injectivity, `PackedPolicy` (`IXAUKG01`) and
   `StageManifest` (`ix-aiur-stages-v1`) integrity, exact Schwartz–Zippel deferred KZG folding,
   and exempt-SCC (`Physical.Prepared.DepthCertified`) compiler/tiling/PLONK soundness theorems.

## Per-Curve Coverage Fence
- **BN254 (Full End-to-End + Constructive Consistency):** Full non-vacuous end-to-end soundness
  (`aiur_compression_l3_bn254_sound`), constructive satisfiability for both statement policies
  (`bn254AiurCompression_consistent`, `bn254AiurCompression_singleLayer_consistent`), outer native
  PLONK SCS relation (`aiur_scs_outer_sound`), exact `MultiStark` AST pins, and all 4 exempt-SCC
  stage bridges.
- **BLS12-381 (Proved Building Blocks; End-to-End Deferred):** Proved `StatementBinding` codecs,
  Goldilocks-over-`Fr` no-wrap bounds, and statement-chain uniqueness; proved subgroup-enforced
  L3 and `k`-stage deferred KZG folding + non-vacuity (`bls12381_l3_deferred_fold_sound`,
  `bls12381_kstage_deferred_fold_sound`, `bls12381_kstage_deferred_fold_nonvacuous`); proved
  canonical `5×u80` affine coordinate injectivity (`bls12381AffineU80_injective`); proved
  exempt-SCC BLS12-381 shared-map PLONK SCS soundness (`plonk_shared_heap_sound_certified_bls12381`,
  `plonk_shared_heap_sound_structural_bls12381`); and constructive 3-torsion rejection
  (`negControl_bls12381_torsion_rejected`). No end-to-end BLS12-381 compression theorem is
  claimed because `MultiStark` currently ships BN254 recursive KZG verifier templates only.

## Relation to `IxCCAiur`
For Lean-compiled compression stages emitted through `IxCCAiur`:
- `IxCC.AiurBackend.CompiledCert.Cert` (`IxCCAiur/IxCCAiur/CompiledCert.lean`) discharges the
  static compiler-depth hypotheses (`Physical.Prepared.DepthCertified`, `cfg.bits ≤ 24`,
  `plan.WellFormedActivation`, entry resolution, and pure-Lean BLAKE3 `.ixa` pinning).
- `IxCC.AiurBackend.CompressionIntrinsics` (`IxCCAiur/IxCCAiur/CompressionIntrinsics.lean`)
  certifies compression intrinsic lowering and custom entry-point aliasing (`aliasEntry_sound`)
  for all four stage entry signatures.

## Explicit Remaining TCB Gap Checklist (Satisfiable, Execution-Indexed Hypotheses)
The open proof-engineering obligations factored cleanly into `Bn254AiurCompressionTcbGaps` are:
1. **Program Functional-Refinement Contracts (4):**
   `finalSemantic` (`CompressFinalNarrow::verify_accumulator_v1`),
   `narrowSemantic` (`CompressNarrowFixed::step_v1`),
   `glSemantic` (`CompressGL::verify_root`), and
   `wrapSemantic` (`CompressWrap::verify_root`, in `twoLayerWrap` mode).
2. **Cryptographic / PCS Extraction Bridges (5):**
   `outerToFinalScs` (native Rust PLONK `ix-aiur-scs-v1` ⇔ `PlonkSharedTerminalWitness`),
   `narrowKzgToTiling` (Stage 3 KZG pairing ⇔ `NarrowCompactStageWitness`),
   `glKzgToGroupedWide` (Stage 2 KZG pairing ⇔ `Bn254GroupedWideStageWitness`),
   `wrapFriToWideGoldilocks` (Stage 1 Goldilocks MultiSTARK ⇔ `GoldilocksWideStageWitness`), and
   `rootFriToAggr` (Stage 0 root MultiSTARK ⇔ `AcceptedAggrTree`).
3. **Pure-Lean `Blake3.Pure.hash` in Key-Embedding Templates:**
   Replacing `@[extern]` `Blake3.Rust.hash` with `Blake3.Pure.hash` inside
   `MultiStark.Compress{GLFixed,NarrowFixed,FinalNarrow}.source` so their runtime generators can
   be pinned directly against `expected{CompressGLFixed,NarrowFixed,FinalNarrow}Template` without
   importing `native_decide`.
4. **Standard Cryptographic Assumptions:**
   KZG trusted-setup SRS / AGM knowledge extraction, BLAKE3/SHA-256 collision resistance
   (explicitly disjuncted in `Bn254AiurEscape`), Fiat–Shamir ROM, and trusted artifact key
   generation (`ix compress write-keys`) matching the pinned Lean source.

Every theorem pinned below depends STRICTLY on standard Lean axioms
(`propext`, `Classical.choice`, `Quot.sound`) — zero `sorry`, zero custom axioms,
zero `native_decide`, zero `bv_decide`.
-/

/-! ## 1. End-to-End Soundness, Escape Non-Vacuity & Constructive Consistency -/

/--
info: @Ix.Cert.AiurCompression.aiur_compression_l3_bn254_sound : ∀ {sha256 : List UInt8 → List UInt8}
  {manifest : Ix.Cert.AiurCompression.StageManifest} {stmtPolicy : Ix.Cert.AiurCompression.StatementPolicy}
  {rootClaimsBytes : List UInt8} {finalCfg : MultiStark.Final.Configuration}
  {finalHeaders : List Ix.Cert.AiurCompression.NarrowClaimHeader}
  {bp : Ix.Cert.Compression.OuterRelation.BilinearPairing} {vk : Ix.Cert.AiurCompression.AiurScsVerifyingKey bp sha256}
  {packedCodec : Ix.Cert.AiurCompression.Bn254PackedAccCodec bp} {stmtLow stmtHigh : ℕ}
  {wrapSrc : Aiur.Generic.Source MultiStark.F} {wrapEntries : List String}
  {glSrc : Aiur.Generic.Source Ix.Cert.Compression.Foreign.BN254Fr} {glEntries : List String}
  {narrowSrc : Aiur.Generic.Source Ix.Cert.Compression.Foreign.BN254Fr} {narrowEntries : List String}
  {finalSrc : Aiur.Generic.Source Ix.Cert.Compression.Foreign.BN254Fr} {finalEntries : List String}
  {sem :
    Aggr.AggrSemantics Address Address Ix.DynamicLink.EvalAssumption Address Ix.Cert.MultiStark.K
      Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
  {batchClaim :
    ℕ →
      Aggr.ValidatorMode Address →
        (Address → Prop) → (Address → Prop) → (Address → Prop) → (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
  {claimsBindStmt :
    List UInt8 →
      Aggr.AggrNodeStmt Address Address Ix.DynamicLink.EvalAssumption Address Ix.Cert.MultiStark.K
          Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry →
        Prop}
  {ε : ℝ} (acc : Ix.Cert.AiurCompression.AiurScsOuterAccepted vk stmtLow stmtHigh)
  (gaps :
    Ix.Cert.AiurCompression.Bn254AiurCompressionTcbGaps sha256 manifest stmtPolicy rootClaimsBytes finalCfg finalHeaders
      bp vk packedCodec stmtLow stmtHigh wrapSrc wrapEntries glSrc glEntries narrowSrc narrowEntries finalSrc
      finalEntries sem batchClaim claimsBindStmt ε),
  Ix.Cert.AiurCompression.Bn254AiurEscape acc gaps ∨
    Ix.Cert.AiurCompression.FinalNarrowConfigValid finalCfg finalHeaders ∧
      manifest.glKeyAnchors = manifest.outerPairingAnchors ∧
        manifest.narrowKeyAnchors = manifest.outerPairingAnchors ∧
          manifest.finalAnchors = manifest.outerPairingAnchors ∧
            ∃ value₄ heap₄ finalPolicy w₂ prevAcc cur₂ prevAccWords,
              Aiur.Generic.SourceSemantics.EvalFn finalSrc.world Ix.Cert.AiurCompression.compressFinalNarrowEntry
                  (Ix.Cert.AiurCompression.compressFinalArgs Ix.Cert.Compression.Foreign.BN254Fr stmtLow stmtHigh) []
                  value₄ heap₄ ∧
                gaps.FinalExecRel stmtLow stmtHigh value₄ heap₄ finalPolicy w₂ prevAcc cur₂ prevAccWords ∧
                  finalPolicy = manifest.policy ∧
                    Ix.Cert.AiurCompression.bn254DeferredVal bp vk.expectedSpec.anchors cur₂ = 1 ∧
                      Ix.Cert.AiurCompression.bn254DeferredVal bp vk.expectedSpec.anchors prevAcc = 1 ∧
                        ∃ value₃ heap₃ narrowPolicy w₁ cur₁,
                          Aiur.Generic.SourceSemantics.EvalFn narrowSrc.world
                              Ix.Cert.AiurCompression.compressNarrowFixedEntry
                              (Ix.Cert.AiurCompression.compressNarrowArgs Ix.Cert.Compression.Foreign.BN254Fr
                                finalCfg.policyDigest 1
                                (stmtPolicy.terminalStatementWords manifest.rootKeyPin rootClaimsBytes))
                              [] value₃ heap₃ ∧
                            gaps.NarrowExecRel finalCfg.policyDigest
                                (stmtPolicy.terminalStatementWords manifest.rootKeyPin rootClaimsBytes) value₃ heap₃
                                narrowPolicy w₁ cur₁ ∧
                              narrowPolicy = manifest.policy ∧
                                prevAcc = ⋯ ∧
                                  Ix.Cert.AiurCompression.bn254DeferredVal bp vk.expectedSpec.anchors cur₁ = 1 ∧ ⋯
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.aiur_compression_l3_bn254_sound

/-- info: 'Ix.Cert.AiurCompression.aiur_compression_l3_bn254_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.aiur_compression_l3_bn254_sound

/--
info: @Ix.Cert.AiurCompression.bn254AiurEscape_false_on_honest : ∀ {sha256 : List UInt8 → List UInt8}
  {manifest : Ix.Cert.AiurCompression.StageManifest} {stmtPolicy : Ix.Cert.AiurCompression.StatementPolicy}
  {rootClaimsBytes : List UInt8} {finalCfg : MultiStark.Final.Configuration}
  {finalHeaders : List Ix.Cert.AiurCompression.NarrowClaimHeader}
  {bp : Ix.Cert.Compression.OuterRelation.BilinearPairing} {vk : Ix.Cert.AiurCompression.AiurScsVerifyingKey bp sha256}
  {packedCodec : Ix.Cert.AiurCompression.Bn254PackedAccCodec bp} {stmtLow stmtHigh : ℕ}
  {wrapSrc : Aiur.Generic.Source MultiStark.F} {wrapEntries : List String}
  {glSrc : Aiur.Generic.Source Ix.Cert.Compression.Foreign.BN254Fr} {glEntries : List String}
  {narrowSrc : Aiur.Generic.Source Ix.Cert.Compression.Foreign.BN254Fr} {narrowEntries : List String}
  {finalSrc : Aiur.Generic.Source Ix.Cert.Compression.Foreign.BN254Fr} {finalEntries : List String}
  {sem :
    Aggr.AggrSemantics Address Address Ix.DynamicLink.EvalAssumption Address Ix.Cert.MultiStark.K
      Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
  {batchClaim :
    ℕ →
      Aggr.ValidatorMode Address →
        (Address → Prop) → (Address → Prop) → (Address → Prop) → (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
  {claimsBindStmt :
    List UInt8 →
      Aggr.AggrNodeStmt Address Address Ix.DynamicLink.EvalAssumption Address Ix.Cert.MultiStark.K
          Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry →
        Prop}
  {ε : ℝ} (acc : Ix.Cert.AiurCompression.AiurScsOuterAccepted vk stmtLow stmtHigh)
  (gaps :
    Ix.Cert.AiurCompression.Bn254AiurCompressionTcbGaps sha256 manifest stmtPolicy rootClaimsBytes finalCfg finalHeaders
      bp vk packedCodec stmtLow stmtHigh wrapSrc wrapEntries glSrc glEntries narrowSrc narrowEntries finalSrc
      finalEntries sem batchClaim claimsBindStmt ε),
  acc.provenScsBytes = vk.scsBytes →
    acc.provenPairingBytes = vk.pairingBytes →
      ∀
        (hFinalHonest :
          ∀ (value₄ : Aiur.SourceValue Ix.Cert.Compression.Foreign.BN254Fr)
            (heap₄ : Aiur.Heap Ix.Cert.Compression.Foreign.BN254Fr) (finalPolicy : Ix.Cert.AiurCompression.PackedPolicy)
            (w₂ : Ix.Cert.Compression.Foreign.BN254Fr) (prevAcc cur₂ : bp.G1 × bp.G1)
            (prevAccWords : List Ix.Cert.Compression.Foreign.BN254Fr),
            Aiur.Generic.SourceSemantics.EvalFn finalSrc.world Ix.Cert.AiurCompression.compressFinalNarrowEntry
                (Ix.Cert.AiurCompression.compressFinalArgs Ix.Cert.Compression.Foreign.BN254Fr stmtLow stmtHigh) []
                value₄ heap₄ →
              gaps.FinalExecRel stmtLow stmtHigh value₄ heap₄ finalPolicy w₂ prevAcc cur₂ prevAccWords →
                finalPolicy = manifest.policy ∧
                  (Ix.Cert.AiurCompression.bn254DeferredVal bp vk.expectedSpec.anchors prevAcc = 1 ∧
                      Ix.Cert.AiurCompression.bn254DeferredVal bp vk.expectedSpec.anchors cur₂ = 1 ∨
                    Ix.Cert.AiurCompression.bn254DeferredVal bp vk.expectedSpec.anchors
                        (Ix.Cert.AiurCompression.bn254FoldStep bp w₂ prevAcc cur₂) ≠
                      1))
        (hNarrowHonest :
          ∀ (value₃ : Aiur.SourceValue Ix.Cert.Compression.Foreign.BN254Fr)
            (heap₃ : Aiur.Heap Ix.Cert.Compression.Foreign.BN254Fr)
            (narrowPolicy : Ix.Cert.AiurCompression.PackedPolicy) (w₁ : Ix.Cert.Compression.Foreign.BN254Fr)
            (cur₁ : bp.G1 × bp.G1),
            Aiur.Generic.SourceSemantics.EvalFn narrowSrc.world Ix.Cert.AiurCompression.compressNarrowFixedEntry
                (Ix.Cert.AiurCompression.compressNarrowArgs Ix.Cert.Compression.Foreign.BN254Fr finalCfg.policyDigest 1
                  (stmtPolicy.terminalStatementWords manifest.rootKeyPin rootClaimsBytes))
                [] value₃ heap₃ →
              gaps.NarrowExecRel finalCfg.policyDigest
                  (stmtPolicy.terminalStatementWords manifest.rootKeyPin rootClaimsBytes) value₃ heap₃ narrowPolicy w₁
                  cur₁ →
                narrowPolicy = manifest.policy),
        (match stmtPolicy, gaps, hFinalHonest, hNarrowHonest with
          | Ix.Cert.AiurCompression.StatementPolicy.twoLayerWrap wp, gaps, hFinalHonest, hNarrowHonest =>
            (∀ (value₂ : Aiur.SourceValue Ix.Cert.Compression.Foreign.BN254Fr)
                (heap₂ : Aiur.Heap Ix.Cert.Compression.Foreign.BN254Fr) (innerKeyBytes innerClaimsBytes : List UInt8),
                Aiur.Generic.SourceSemantics.EvalFn glSrc.world MultiStark.CompressGL.entry
                    (Ix.Cert.AiurCompression.compressGLArgs Ix.Cert.Compression.Foreign.BN254Fr
                      (wp.glStatementWords
                        (Ix.Cert.AiurCompression.rootStatementWords manifest.rootKeyPin rootClaimsBytes)))
                    [] value₂ heap₂ →
                  gaps.GlExecRel
                      (wp.glStatementWords
                        (Ix.Cert.AiurCompression.rootStatementWords manifest.rootKeyPin rootClaimsBytes))
                      value₂ heap₂ innerKeyBytes innerClaimsBytes →
                    Blake3.Pure.digest innerKeyBytes = wp.wrapKeyDigest ∧
                      innerClaimsBytes =
                        wp.claimsBytes
                          (Ix.Cert.AiurCompression.rootStatementWords manifest.rootKeyPin rootClaimsBytes)) ∧
              ∀ (value₁ : Aiur.SourceValue MultiStark.F) (heap₁ : Aiur.Heap MultiStark.F)
                (rootKeyBytes' rootClaimsBytes' : List UInt8),
                Aiur.Generic.SourceSemantics.EvalFn wrapSrc.world Ix.Cert.AiurCompression.compressWrapEntry
                    (Ix.Cert.AiurCompression.compressWrapArgs
                      (Ix.Cert.AiurCompression.rootStatementWords manifest.rootKeyPin rootClaimsBytes))
                    [] value₁ heap₁ →
                  gaps.WrapExecRel (Ix.Cert.AiurCompression.rootStatementWords manifest.rootKeyPin rootClaimsBytes)
                      value₁ heap₁ rootKeyBytes' rootClaimsBytes' →
                    Blake3.Pure.digest rootKeyBytes' = manifest.rootKeyPin ∧ rootClaimsBytes' = rootClaimsBytes
          | Ix.Cert.AiurCompression.StatementPolicy.singleLayerDirect, gaps, hFinalHonest, hNarrowHonest =>
            ∀ (value₂ : Aiur.SourceValue Ix.Cert.Compression.Foreign.BN254Fr)
              (heap₂ : Aiur.Heap Ix.Cert.Compression.Foreign.BN254Fr) (innerKeyBytes innerClaimsBytes : List UInt8),
              Aiur.Generic.SourceSemantics.EvalFn glSrc.world MultiStark.CompressGL.entry
                  (Ix.Cert.AiurCompression.compressGLArgs Ix.Cert.Compression.Foreign.BN254Fr
                    (Ix.Cert.AiurCompression.rootStatementWords manifest.rootKeyPin rootClaimsBytes))
                  [] value₂ heap₂ →
                gaps.GlExecRel (Ix.Cert.AiurCompression.rootStatementWords manifest.rootKeyPin rootClaimsBytes) value₂
                    heap₂ innerKeyBytes innerClaimsBytes →
                  Blake3.Pure.digest innerKeyBytes = manifest.rootKeyPin ∧ innerClaimsBytes = rootClaimsBytes) →
          ¬Ix.Cert.AiurCompression.Bn254AiurEscape acc gaps
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.bn254AiurEscape_false_on_honest

/-- info: 'Ix.Cert.AiurCompression.bn254AiurEscape_false_on_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.bn254AiurEscape_false_on_honest

/--
info: Ix.Cert.AiurCompression.Consistency.bn254AiurCompression_consistent : ∃ sha256 manifest wp rootClaimsBytes finalCfg
  finalHeaders bp vk packedCodec stmtLow stmtHigh wrapSrc wrapEntries glSrc glEntries narrowSrc narrowEntries finalSrc
  finalEntries sem batchClaim claimsBindStmt ε acc gaps,
  (∃ P Q, bp.e P Q ≠ 1) ∧ ¬Ix.Cert.AiurCompression.Bn254AiurEscape acc gaps
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.Consistency.bn254AiurCompression_consistent

/--
info: 'Ix.Cert.AiurCompression.Consistency.bn254AiurCompression_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.Consistency.bn254AiurCompression_consistent

/--
info: Ix.Cert.AiurCompression.Consistency.bn254AiurCompression_singleLayer_consistent : ∃ sha256 manifest rootClaimsBytes
  finalCfg finalHeaders bp vk packedCodec stmtLow stmtHigh wrapSrc wrapEntries glSrc glEntries narrowSrc narrowEntries
  finalSrc finalEntries sem batchClaim claimsBindStmt ε acc gaps,
  (∃ P Q, bp.e P Q ≠ 1) ∧ ¬Ix.Cert.AiurCompression.Bn254AiurEscape acc gaps
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.Consistency.bn254AiurCompression_singleLayer_consistent

/--
info: 'Ix.Cert.AiurCompression.Consistency.bn254AiurCompression_singleLayer_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.Consistency.bn254AiurCompression_singleLayer_consistent

/-- info: Ix.Cert.AiurCompression.Consistency.toyPairing_nontrivial : Ix.Cert.AiurCompression.Consistency.toyPairing.e 1 1 ≠ 1 -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.Consistency.toyPairing_nontrivial

/-- info: 'Ix.Cert.AiurCompression.Consistency.toyPairing_nontrivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.Consistency.toyPairing_nontrivial

/--
info: @Ix.Cert.AiurCompression.aiur_compression_statement_binding_unique : ∀
  {pol₁ pol₂ : Ix.Cert.AiurCompression.StatementPolicy} {pin₁ pin₂ : Vector UInt8 32}
  (c₁ : Ix.Cert.AiurCompression.AiurStageStatementChain pol₁ pin₁)
  (c₂ : Ix.Cert.AiurCompression.AiurStageStatementChain pol₂ pin₂),
  (pol₁ = Ix.Cert.AiurCompression.StatementPolicy.singleLayerDirect ↔
      pol₂ = Ix.Cert.AiurCompression.StatementPolicy.singleLayerDirect) →
    ↑c₁.terminalLow = ↑c₂.terminalLow ∧ ↑c₁.terminalHigh = ↑c₂.terminalHigh ∨
        ↑c₁.terminalLow = ↑c₂.terminalLow ∧ ↑c₁.terminalHigh = ↑c₂.terminalHigh →
      Ix.Cert.AiurCompression.StatementChainCollision c₁ c₂ ∨
        pol₁ = pol₂ ∧ pin₁ = pin₂ ∧ c₁.rootKeyBytes = c₂.rootKeyBytes ∧ c₁.rootClaimsBytes = c₂.rootClaimsBytes
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.aiur_compression_statement_binding_unique

/--
info: 'Ix.Cert.AiurCompression.aiur_compression_statement_binding_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.aiur_compression_statement_binding_unique

/-! ## 2. Outer Native Rust PLONK SCS Relation & Constructive Negative Controls -/

/--
info: @Ix.Cert.AiurCompression.aiur_scs_outer_sound : ∀ {bp : Ix.Cert.Compression.OuterRelation.BilinearPairing}
  {sha256 : List UInt8 → List UInt8} {vk : Ix.Cert.AiurCompression.AiurScsVerifyingKey bp sha256} {stmtLow stmtHigh : ℕ}
  (acc : Ix.Cert.AiurCompression.AiurScsOuterAccepted vk stmtLow stmtHigh),
  Ix.Cert.AiurCompression.Sha256Collision sha256 acc.provenScsBytes vk.scsBytes ∨
    Ix.Cert.AiurCompression.Sha256Collision sha256 acc.provenPairingBytes vk.pairingBytes ∨
      vk.expectedSpec.scs.Satisfied acc.wireAssignment [↑stmtLow, ↑stmtHigh] acc.commitOracle ∧
        acc.wireAssignment 0 = ↑stmtLow ∧
          acc.wireAssignment 1 = ↑stmtHigh ∧
            Ix.Cert.AiurCompression.AiurScsPairingCheck vk.expectedSpec acc.wireAssignment
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.aiur_scs_outer_sound

/-- info: 'Ix.Cert.AiurCompression.aiur_scs_outer_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.aiur_scs_outer_sound

/--
info: @Ix.Cert.AiurCompression.aiurScs_rejects_wrong_public_limb : ∀ {bp : Ix.Cert.Compression.OuterRelation.BilinearPairing}
  (spec : Ix.Cert.AiurCompression.AiurScsOuterSpec bp) (w : ℕ → Ix.Cert.Compression.Foreign.BN254Fr)
  (H : List Ix.Cert.Compression.Foreign.BN254Fr → Ix.Cert.Compression.Foreign.BN254Fr) (stmtLow stmtHigh : ℕ),
  spec.scs.Satisfied w [↑stmtLow, ↑stmtHigh] H → ¬spec.scs.Satisfied w [↑stmtLow + 1, ↑stmtHigh] H
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.aiurScs_rejects_wrong_public_limb

/-- info: 'Ix.Cert.AiurCompression.aiurScs_rejects_wrong_public_limb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.aiurScs_rejects_wrong_public_limb

/--
info: @Ix.Cert.AiurCompression.aiurScs_rejects_noncanonical_output : ∀
  {bp : Ix.Cert.Compression.OuterRelation.BilinearPairing} (spec : Ix.Cert.AiurCompression.AiurScsOuterSpec bp)
  (w : ℕ → Ix.Cert.Compression.Foreign.BN254Fr),
  (w (spec.outputWires.getD 8 0)).val ≠ 0 ∧ (w (spec.outputWires.getD 8 0)).val ≠ 1 →
    ¬Ix.Cert.AiurCompression.AiurScsPairingCheck spec w
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.aiurScs_rejects_noncanonical_output

/-- info: 'Ix.Cert.AiurCompression.aiurScs_rejects_noncanonical_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.aiurScs_rejects_noncanonical_output

/--
info: Ix.Cert.AiurCompression.negControl_wrong_root_key_pin : ∀ (pol : Ix.Cert.AiurCompression.StatementPolicy)
  (trustedPin : Vector UInt8 32) (rogueKeyBytes claimsBytes : List UInt8),
  Blake3.Pure.digest rogueKeyBytes ≠ trustedPin →
    (∀ (c : Ix.Cert.AiurCompression.AiurStageStatementChain pol trustedPin), c.rootKeyBytes ≠ rogueKeyBytes) ∧
      Ix.Cert.AiurCompression.compressWrapPreimage (Vector.toList (Blake3.Pure.digest rogueKeyBytes))
          (Vector.toList (Blake3.Pure.digest claimsBytes)) ≠
        Ix.Cert.AiurCompression.compressWrapPreimage trustedPin.toList (Vector.toList (Blake3.Pure.digest claimsBytes))
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.negControl_wrong_root_key_pin

/-- info: 'Ix.Cert.AiurCompression.negControl_wrong_root_key_pin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.negControl_wrong_root_key_pin

/--
info: Ix.Cert.AiurCompression.negControl_tampered_statement_words : ∀ (low : ℕ) {ws₁ ws₂ : List ℕ},
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
                        ↑(Ix.Cert.AiurCompression.packU32WordsToLimbs ws₂).2)
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.negControl_tampered_statement_words

/-- info: 'Ix.Cert.AiurCompression.negControl_tampered_statement_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.negControl_tampered_statement_words

/--
info: Ix.Cert.AiurCompression.negControl_unpinned_manifest : ∀ (sha256 : List UInt8 → List UInt8)
  (m : Ix.Cert.AiurCompression.StageManifest) (bytes : List UInt8),
  ¬Ix.Cert.AiurCompression.ProductPin.Pinned sha256 { bytes := bytes, blake3Pin := none, sha256Pin := none } ∧
    (m.glKey.blake3Pin = none → m.glKey.sha256Pin = none → ¬Ix.Cert.AiurCompression.ManifestPinned sha256 m) ∧
      (m.format ≠ Ix.Cert.AiurCompression.stagesManifestFormat → ¬Ix.Cert.AiurCompression.ManifestPinned sha256 m) ∧
        (Blake3.Pure.digest m.manifestBytes ≠ m.manifestCallerPin → ¬Ix.Cert.AiurCompression.ManifestPinned sha256 m)
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.negControl_unpinned_manifest

/-- info: 'Ix.Cert.AiurCompression.negControl_unpinned_manifest' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.negControl_unpinned_manifest

/--
info: Ix.Cert.AiurCompression.negControl_policy_key_and_stage_tampering : ∀ (sha256 : List UInt8 → List UInt8)
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
                  Ix.Cert.AiurCompression.validateFinalNarrowConfig cfg headers ≠ Except.ok ())
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.negControl_policy_key_and_stage_tampering

/-- info: 'Ix.Cert.AiurCompression.negControl_policy_key_and_stage_tampering' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.negControl_policy_key_and_stage_tampering

/--
info: Ix.Cert.AiurCompression.negControl_bls12381_torsion_rejected : ∀
  (P : Ix.Cert.Compression.Bls12381.CurveMsm.bls12381G1.Point) (z τ : Ix.Cert.Compression.Bls12381.Field.BLS12381Fr),
  ¬Ix.Cert.Compression.Bls12381.CurveMsm.InPrimeSubgroup Ix.Cert.Compression.Bls12381.CurveMsm.bls12381TorsionPoint ∧
    ¬Ix.Cert.Compression.Bls12381.RecursiveKzg.Bls12381KzgPairingCheck
        Ix.Cert.Compression.Bls12381.CurveMsm.bls12381TorsionPoint P z τ
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.negControl_bls12381_torsion_rejected

/--
info: 'Ix.Cert.AiurCompression.negControl_bls12381_torsion_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.negControl_bls12381_torsion_rejected

/-! ## 3. Exact MultiStark AST & Export-Configuration Pins -/

/--
info: Ix.Cert.AiurCompression.compressWrapProgram_exact_pinned : Ix.Cert.AiurCompression.programContainsModulesExact
  MultiStark.compressWrapProgram (MultiStark.compressWrapSource.toField MultiStark.F)
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.compressWrapProgram_exact_pinned

/-- info: 'Ix.Cert.AiurCompression.compressWrapProgram_exact_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.compressWrapProgram_exact_pinned

/--
info: Ix.Cert.AiurCompression.compressGLProgram_exact_pinned : Ix.Cert.AiurCompression.programContainsModulesExact
  MultiStark.CompressGL.program (MultiStark.CompressGL.source.toField MultiStark.CompressGL.F)
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.compressGLProgram_exact_pinned

/-- info: 'Ix.Cert.AiurCompression.compressGLProgram_exact_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.compressGLProgram_exact_pinned

/--
info: Ix.Cert.AiurCompression.kzgPackedTerminal_exact_pinned : Ix.Cert.AiurCompression.moduleFunctionsExactPinned
    MultiStark.Source.kzgPackedTerminal "KzgPackedTerminal" Ix.Cert.AiurCompression.expectedKzgPackedTerminalFunctions ∧
  List.map (fun x => x.name) Ix.Cert.AiurCompression.expectedKzgPackedTerminalFunctions =
    ["key_words", "ids", "lookups", "circuits", "key", "eval_at", "fold_roots", "lookup_fingerprint", "group_summary",
      "fold_lookups", "verify_frames", "verify_key", "verify"]
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.kzgPackedTerminal_exact_pinned

/-- info: 'Ix.Cert.AiurCompression.kzgPackedTerminal_exact_pinned' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.kzgPackedTerminal_exact_pinned

/--
info: Ix.Cert.AiurCompression.compressBN_exact_pinned : Ix.Cert.AiurCompression.moduleFunctionsExactPinned
    MultiStark.Source.compressBN "CompressBN" Ix.Cert.AiurCompression.expectedCompressBNFunctions ∧
  List.map (fun x => x.name) Ix.Cert.AiurCompression.expectedCompressBNFunctions =
    ["take8", "previous", "digest_onto", "domain", "fold", "step_v1", "compress_v1"]
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.compressBN_exact_pinned

/-- info: 'Ix.Cert.AiurCompression.compressBN_exact_pinned' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.compressBN_exact_pinned

/--
info: Ix.Cert.AiurCompression.compressBNPacked_exact_pinned : Ix.Cert.AiurCompression.moduleFunctionsExactPinned
    MultiStark.Source.compressBNPacked "CompressBNPacked" Ix.Cert.AiurCompression.expectedCompressBNPackedFunctions ∧
  List.map (fun x => x.name) Ix.Cert.AiurCompression.expectedCompressBNPackedFunctions =
    ["fold_domain", "fold_weight", "fold"]
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.compressBNPacked_exact_pinned

/-- info: 'Ix.Cert.AiurCompression.compressBNPacked_exact_pinned' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.compressBNPacked_exact_pinned

/--
info: Ix.Cert.AiurCompression.kzgPackedDeserialize_exact_pinned : Ix.Cert.AiurCompression.moduleFunctionsExactPinned
    MultiStark.Source.kzgPackedDeserialize "KzgPackedDeserialize"
    Ix.Cert.AiurCompression.expectedKzgPackedDeserializeFunctions ∧
  (["chain_policy", "key", "proof"].all fun n =>
      (List.map (fun x => x.name) Ix.Cert.AiurCompression.expectedKzgPackedDeserializeFunctions).contains n) =
    true
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.kzgPackedDeserialize_exact_pinned

/-- info: 'Ix.Cert.AiurCompression.kzgPackedDeserialize_exact_pinned' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.kzgPackedDeserialize_exact_pinned

/--
info: @Ix.Cert.AiurCompression.finalSource_ok_spec : ∀ {cfg : MultiStark.Final.Configuration} {prog : Aiur.Modules.Program ℕ},
  MultiStark.Final.source cfg = Except.ok prog →
    Ix.Cert.AiurCompression.FinalConfigValid cfg ∧
      Ix.Cert.AiurCompression.moduleFunctionsExactPinned prog "CompressFinal"
        Ix.Cert.AiurCompression.expectedCompressFinalFunctions
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.finalSource_ok_spec

/-- info: 'Ix.Cert.AiurCompression.finalSource_ok_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.finalSource_ok_spec

/--
info: Ix.Cert.AiurCompression.exactPin_rejects_dropped_anchor_check : ¬Ix.Cert.AiurCompression.FinalNarrowExactPinned
    Ix.Cert.AiurCompression.mutatedFinalNarrowNoAnchorCheck
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.exactPin_rejects_dropped_anchor_check

/--
info: 'Ix.Cert.AiurCompression.exactPin_rejects_dropped_anchor_check' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.exactPin_rejects_dropped_anchor_check

/--
info: @Ix.Cert.AiurCompression.moduleFunctionsExactPinned_implies_digest_eq : ∀ {prog : Aiur.Modules.Program ℕ}
  {modName : String} {expectedFns : List (Aiur.Generic.Function ℕ)},
  Ix.Cert.AiurCompression.moduleFunctionsExactPinned prog modName expectedFns →
    Ix.Cert.AiurCompression.astDigestModuleFunctions prog modName =
      some (Ix.Cert.AiurCompression.astDigestFunctions expectedFns)
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.moduleFunctionsExactPinned_implies_digest_eq

/--
info: 'Ix.Cert.AiurCompression.moduleFunctionsExactPinned_implies_digest_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.moduleFunctionsExactPinned_implies_digest_eq

/--
info: @Ix.Cert.AiurCompression.validateFinalNarrowConfig_ok_spec : ∀ {cfg : MultiStark.Final.Configuration}
  {headers : List Ix.Cert.AiurCompression.NarrowClaimHeader},
  Ix.Cert.AiurCompression.validateFinalNarrowConfig cfg headers = Except.ok () →
    Ix.Cert.AiurCompression.FinalNarrowConfigValid cfg headers
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.validateFinalNarrowConfig_ok_spec

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

/--
info: @Ix.Cert.AiurCompression.compressWrap_statement_binds_root_or_collision : ∀ {k₁ c₁ k₂ c₂ : List UInt8},
  k₁.length = 32 →
    k₂.length = 32 →
      Ix.Cert.AiurCompression.compressWrapStatementDigest k₁ c₁ =
          Ix.Cert.AiurCompression.compressWrapStatementDigest k₂ c₂ →
        Ix.Cert.AiurCompression.Blake3Collision (Ix.Cert.AiurCompression.compressWrapPreimage k₁ c₁)
            (Ix.Cert.AiurCompression.compressWrapPreimage k₂ c₂) ∨
          k₁ = k₂ ∧ c₁ = c₂
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.compressWrap_statement_binds_root_or_collision

/-- info: 'Ix.Cert.AiurCompression.compressWrap_statement_binds_root_or_collision' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.compressWrap_statement_binds_root_or_collision

/--
info: @Ix.Cert.AiurCompression.rootClaimsBytesOfClaim_binds_or_collision : ∀ {p₁ p₂ : List ℕ} {c₁ c₂ : List UInt8},
  p₁.length = 10 →
    p₂.length = 10 →
      (∀ w ∈ p₁, w < Ix.Cert.Compression.Foreign.goldilocksP) →
        (∀ w ∈ p₂, w < Ix.Cert.Compression.Foreign.goldilocksP) →
          Ix.Cert.AiurCompression.rootClaimsBytesOfClaim p₁ c₁ = Ix.Cert.AiurCompression.rootClaimsBytesOfClaim p₂ c₂ →
            Ix.Cert.AiurCompression.Blake3Collision c₁ c₂ ∨ p₁ = p₂ ∧ c₁ = c₂
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.rootClaimsBytesOfClaim_binds_or_collision

/--
info: 'Ix.Cert.AiurCompression.rootClaimsBytesOfClaim_binds_or_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.rootClaimsBytesOfClaim_binds_or_collision

/--
info: @Ix.Cert.AiurCompression.WrapPolicySpec.claimsBytes_injective : ∀ {wp₁ wp₂ : Ix.Cert.AiurCompression.WrapPolicySpec}
  {r₁ r₂ : List ℕ},
  r₁.length = 8 →
    r₂.length = 8 →
      (∀ w ∈ r₁, w < 2 ^ 32) →
        (∀ w ∈ r₂, w < 2 ^ 32) →
          wp₁.wrapKeyDigest = wp₂.wrapKeyDigest → wp₁.claimsBytes r₁ = wp₂.claimsBytes r₂ → wp₁ = wp₂ ∧ r₁ = r₂
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.WrapPolicySpec.claimsBytes_injective

/--
info: 'Ix.Cert.AiurCompression.WrapPolicySpec.claimsBytes_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.WrapPolicySpec.claimsBytes_injective

/--
info: @Ix.Cert.AiurCompression.PackedPolicy.encode_injective : ∀ {p₁ p₂ : Ix.Cert.AiurCompression.PackedPolicy},
  p₁.WellFormed → p₂.WellFormed → p₁.encode = p₂.encode → p₁ = p₂
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.PackedPolicy.encode_injective

/-- info: 'Ix.Cert.AiurCompression.PackedPolicy.encode_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.PackedPolicy.encode_injective

/--
info: @Ix.Cert.AiurCompression.manifestPinned_chain_integrity : ∀ {sha256 : List UInt8 → List UInt8}
  {m : Ix.Cert.AiurCompression.StageManifest},
  Ix.Cert.AiurCompression.ManifestPinned sha256 m →
    m.glKeyAnchors = m.outerPairingAnchors ∧
      m.narrowKeyAnchors = m.outerPairingAnchors ∧
        m.finalAnchors = m.outerPairingAnchors ∧
          m.policy.glKeyDigest = Vector.toList (Blake3.Pure.digest m.glKey.bytes) ∧
            m.policy.narrowKeyDigest = Vector.toList (Blake3.Pure.digest m.narrowKey.bytes) ∧
              m.finalPolicyDigestWords = Ix.Cert.AiurCompression.packBytes32ToU32Words m.policy.digest.toList
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.manifestPinned_chain_integrity

/-- info: 'Ix.Cert.AiurCompression.manifestPinned_chain_integrity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.manifestPinned_chain_integrity

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

/-- info: 'Ix.Cert.AiurCompression.packedPolicy_digest_binds_or_collision' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.packedPolicy_digest_binds_or_collision

/-- info: 'Ix.Cert.AiurCompression.statementChain_unique_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.statementChain_unique_or_collision

/--
info: 'Ix.Cert.AiurCompression.statementChain_unique_bn254_or_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.statementChain_unique_bn254_or_collision

/--
info: 'Ix.Cert.AiurCompression.statementChain_unique_bls12381_or_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.statementChain_unique_bls12381_or_collision

/-! ## 5. Deferred KZG Folding & Canonical Affine Codecs (BN254 & BLS12-381) -/

/--
info: Ix.Cert.AiurCompression.bn254_l3_deferred_fold_sound : ∀ (bp : Ix.Cert.Compression.OuterRelation.BilinearPairing)
  (anchors : bp.G2 × bp.G2) (w₁ w₂ : Ix.Cert.Compression.Foreign.BN254Fr) (cur₁ cur₂ : bp.G1 × bp.G1),
  Ix.Cert.AiurCompression.bn254DeferredVal bp anchors
        (Ix.Cert.AiurCompression.bn254FoldStep bp w₂ (Ix.Cert.AiurCompression.bn254FoldStep bp w₁ (0, 0) cur₁) cur₂) =
      1 →
    Ix.Cert.AiurCompression.bn254DeferredVal bp anchors cur₁ = 1 ∧
        Ix.Cert.AiurCompression.bn254DeferredVal bp anchors cur₂ = 1 ∨
      Ix.Cert.AiurCompression.bn254DeferredVal bp anchors
            (Ix.Cert.AiurCompression.bn254FoldStep bp w₂ (Ix.Cert.AiurCompression.bn254FoldStep bp w₁ (0, 0) cur₁)
              cur₂) =
          1 ∧
        {w' |
              Ix.Cert.AiurCompression.bn254DeferredVal bp anchors
                  (Ix.Cert.AiurCompression.bn254FoldStep bp w' (Ix.Cert.AiurCompression.bn254FoldStep bp w₁ (0, 0) cur₁)
                    cur₂) =
                1}.card ≤
          1
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.bn254_l3_deferred_fold_sound

/-- info: 'Ix.Cert.AiurCompression.bn254_l3_deferred_fold_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.bn254_l3_deferred_fold_sound

/--
info: Ix.Cert.AiurCompression.bn254_kstage_deferred_fold_sound : ∀ (bp : Ix.Cert.Compression.OuterRelation.BilinearPairing)
  (anchors : bp.G2 × bp.G2) (stages : List (Ix.Cert.Compression.Foreign.BN254Fr × bp.G1 × bp.G1)),
  Ix.Cert.AiurCompression.bn254DeferredVal bp anchors (Ix.Cert.AiurCompression.bn254FoldChain bp stages) = 1 →
    (∀ s ∈ stages, Ix.Cert.AiurCompression.bn254DeferredVal bp anchors s.2 = 1) ∨
      ∃ i,
        have w := stages[↑i].1;
        have cur := stages[↑i].2;
        have prev := Ix.Cert.AiurCompression.bn254FoldChain bp (List.drop (↑i + 1) stages);
        Ix.Cert.AiurCompression.bn254DeferredVal bp anchors (Ix.Cert.AiurCompression.bn254FoldStep bp w prev cur) = 1 ∧
          {w' |
                Ix.Cert.AiurCompression.bn254DeferredVal bp anchors
                    (Ix.Cert.AiurCompression.bn254FoldStep bp w' prev cur) =
                  1}.card ≤
            1
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.bn254_kstage_deferred_fold_sound

/-- info: 'Ix.Cert.AiurCompression.bn254_kstage_deferred_fold_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.bn254_kstage_deferred_fold_sound

/--
info: Ix.Cert.AiurCompression.bn254_kstage_deferred_fold_nonvacuous : ∀
  (bp : Ix.Cert.Compression.OuterRelation.BilinearPairing) (anchors : bp.G2 × bp.G2)
  (stages : List (Ix.Cert.Compression.Foreign.BN254Fr × bp.G1 × bp.G1)),
  (∀ s ∈ stages, Ix.Cert.AiurCompression.bn254DeferredVal bp anchors s.2 = 1) →
    ¬∃ i,
        have w := stages[↑i].1;
        have cur := stages[↑i].2;
        have prev := Ix.Cert.AiurCompression.bn254FoldChain bp (List.drop (↑i + 1) stages);
        Ix.Cert.AiurCompression.bn254DeferredVal bp anchors (Ix.Cert.AiurCompression.bn254FoldStep bp w prev cur) = 1 ∧
          {w' |
                Ix.Cert.AiurCompression.bn254DeferredVal bp anchors
                    (Ix.Cert.AiurCompression.bn254FoldStep bp w' prev cur) =
                  1}.card ≤
            1
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.bn254_kstage_deferred_fold_nonvacuous

/--
info: 'Ix.Cert.AiurCompression.bn254_kstage_deferred_fold_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.bn254_kstage_deferred_fold_nonvacuous

/--
info: Ix.Cert.AiurCompression.bls12381_l3_deferred_fold_sound : ∀
  (bp : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381BilinearPairing) (anchors : bp.G2 × bp.G2)
  (w₁ w₂ : Ix.Cert.Compression.Bls12381.Field.BLS12381Fr) {cur₁ cur₂ : bp.G1 × bp.G1},
  Ix.Cert.AiurCompression.BlsPairInSubgroup bp cur₁ →
    Ix.Cert.AiurCompression.BlsPairInSubgroup bp cur₂ →
      Ix.Cert.AiurCompression.bls12381DeferredVal bp anchors
            (Ix.Cert.AiurCompression.bls12381FoldStep bp w₂ (Ix.Cert.AiurCompression.bls12381FoldStep bp w₁ (0, 0) cur₁)
              cur₂) =
          1 →
        Ix.Cert.AiurCompression.BlsPairInSubgroup bp
            (Ix.Cert.AiurCompression.bls12381FoldStep bp w₂ (Ix.Cert.AiurCompression.bls12381FoldStep bp w₁ (0, 0) cur₁)
              cur₂) ∧
          (Ix.Cert.AiurCompression.bls12381DeferredVal bp anchors cur₁ = 1 ∧
              Ix.Cert.AiurCompression.bls12381DeferredVal bp anchors cur₂ = 1 ∨
            Ix.Cert.AiurCompression.bls12381DeferredVal bp anchors
                  (Ix.Cert.AiurCompression.bls12381FoldStep bp w₂
                    (Ix.Cert.AiurCompression.bls12381FoldStep bp w₁ (0, 0) cur₁) cur₂) =
                1 ∧
              {w' |
                    Ix.Cert.AiurCompression.bls12381DeferredVal bp anchors
                        (Ix.Cert.AiurCompression.bls12381FoldStep bp w'
                          (Ix.Cert.AiurCompression.bls12381FoldStep bp w₁ (0, 0) cur₁) cur₂) =
                      1}.card ≤
                1)
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.bls12381_l3_deferred_fold_sound

/-- info: 'Ix.Cert.AiurCompression.bls12381_l3_deferred_fold_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.bls12381_l3_deferred_fold_sound

/--
info: Ix.Cert.AiurCompression.bls12381_kstage_deferred_fold_sound : ∀
  (bp : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381BilinearPairing) (anchors : bp.G2 × bp.G2)
  (stages : List (Ix.Cert.Compression.Bls12381.Field.BLS12381Fr × bp.G1 × bp.G1)),
  (∀ s ∈ stages, Ix.Cert.AiurCompression.BlsPairInSubgroup bp s.2) →
    Ix.Cert.AiurCompression.bls12381DeferredVal bp anchors (Ix.Cert.AiurCompression.bls12381FoldChain bp stages) = 1 →
      Ix.Cert.AiurCompression.BlsPairInSubgroup bp (Ix.Cert.AiurCompression.bls12381FoldChain bp stages) ∧
        ((∀ s ∈ stages, Ix.Cert.AiurCompression.bls12381DeferredVal bp anchors s.2 = 1) ∨
          ∃ i,
            have w := stages[↑i].1;
            have cur := stages[↑i].2;
            have prev := Ix.Cert.AiurCompression.bls12381FoldChain bp (List.drop (↑i + 1) stages);
            Ix.Cert.AiurCompression.BlsPairInSubgroup bp prev ∧
              Ix.Cert.AiurCompression.BlsPairInSubgroup bp cur ∧
                Ix.Cert.AiurCompression.bls12381DeferredVal bp anchors
                      (Ix.Cert.AiurCompression.bls12381FoldStep bp w prev cur) =
                    1 ∧
                  {w' |
                        Ix.Cert.AiurCompression.bls12381DeferredVal bp anchors
                            (Ix.Cert.AiurCompression.bls12381FoldStep bp w' prev cur) =
                          1}.card ≤
                    1)
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.bls12381_kstage_deferred_fold_sound

/-- info: 'Ix.Cert.AiurCompression.bls12381_kstage_deferred_fold_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.bls12381_kstage_deferred_fold_sound

/--
info: Ix.Cert.AiurCompression.bls12381_kstage_deferred_fold_nonvacuous : ∀
  (bp : Ix.Cert.Compression.Bls12381.OuterRelation.Bls12381BilinearPairing) (anchors : bp.G2 × bp.G2)
  (stages : List (Ix.Cert.Compression.Bls12381.Field.BLS12381Fr × bp.G1 × bp.G1)),
  (∀ s ∈ stages, Ix.Cert.AiurCompression.BlsPairInSubgroup bp s.2) →
    (∀ s ∈ stages, Ix.Cert.AiurCompression.bls12381DeferredVal bp anchors s.2 = 1) →
      ¬∃ i,
          have w := stages[↑i].1;
          have cur := stages[↑i].2;
          have prev := Ix.Cert.AiurCompression.bls12381FoldChain bp (List.drop (↑i + 1) stages);
          Ix.Cert.AiurCompression.BlsPairInSubgroup bp prev ∧
            Ix.Cert.AiurCompression.BlsPairInSubgroup bp cur ∧
              Ix.Cert.AiurCompression.bls12381DeferredVal bp anchors
                    (Ix.Cert.AiurCompression.bls12381FoldStep bp w prev cur) =
                  1 ∧
                {w' |
                      Ix.Cert.AiurCompression.bls12381DeferredVal bp anchors
                          (Ix.Cert.AiurCompression.bls12381FoldStep bp w' prev cur) =
                        1}.card ≤
                  1
-/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.AiurCompression.bls12381_kstage_deferred_fold_nonvacuous

/--
info: 'Ix.Cert.AiurCompression.bls12381_kstage_deferred_fold_nonvacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.bls12381_kstage_deferred_fold_nonvacuous

/-- info: 'Ix.Cert.AiurCompression.bn254_foldStep_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.bn254_foldStep_sound

/-- info: 'Ix.Cert.AiurCompression.bls12381_foldStep_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.bls12381_foldStep_sound

/-- info: 'Ix.Cert.AiurCompression.bn254AffineU80_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.bn254AffineU80_injective

/-- info: 'Ix.Cert.AiurCompression.bls12381AffineU80_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.bls12381AffineU80_injective

/--
info: 'Ix.Cert.AiurCompression.decodeBn254AffineU80PointWords_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.decodeBn254AffineU80PointWords_roundtrip

/--
info: 'Ix.Cert.AiurCompression.decodeBn254AffineU80PointWords_rejects_bad_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.decodeBn254AffineU80PointWords_rejects_bad_flag

/-! ## 6. Exempt-SCC Depth Bridge & Stage Witnesses (BN254 & BLS12-381) -/

/--
info: 'Ix.Cert.AiurCompression.DepthBridge.wide_heap_sound_goldilocks_structural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.DepthBridge.wide_heap_sound_goldilocks_structural

/--
info: 'Ix.Cert.AiurCompression.DepthBridge.grouped_heap_sound_bn254_structural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.DepthBridge.grouped_heap_sound_bn254_structural

/--
info: 'Ix.Cert.AiurCompression.DepthBridge.grouped_heap_sound_shared_structural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.DepthBridge.grouped_heap_sound_shared_structural

/--
info: 'Ix.Cert.AiurCompression.DepthBridge.narrow_heap_sound_compact_structural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.DepthBridge.narrow_heap_sound_compact_structural

/--
info: 'Ix.Cert.AiurCompression.DepthBridge.plonk_shared_heap_sound_certified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.DepthBridge.plonk_shared_heap_sound_certified

/--
info: 'Ix.Cert.AiurCompression.DepthBridge.plonk_shared_heap_sound_structural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.DepthBridge.plonk_shared_heap_sound_structural

/--
info: 'Ix.Cert.AiurCompression.DepthBridge.plonk_shared_heap_sound_certified_bls12381' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.DepthBridge.plonk_shared_heap_sound_certified_bls12381

/--
info: 'Ix.Cert.AiurCompression.DepthBridge.plonk_shared_heap_sound_structural_bls12381' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.DepthBridge.plonk_shared_heap_sound_structural_bls12381

/-- info: 'Ix.Cert.AiurCompression.DepthBridge.represents_field_tuple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.DepthBridge.represents_field_tuple

/--
info: 'Ix.Cert.AiurCompression.GoldilocksWideStageWitness.eval_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.GoldilocksWideStageWitness.eval_sound

/--
info: 'Ix.Cert.AiurCompression.Bn254GroupedWideStageWitness.eval_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.Bn254GroupedWideStageWitness.eval_sound

/--
info: 'Ix.Cert.AiurCompression.NarrowCompactStageWitness.eval_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.NarrowCompactStageWitness.eval_sound

/--
info: 'Ix.Cert.AiurCompression.PlonkSharedTerminalWitness.eval_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.AiurCompression.PlonkSharedTerminalWitness.eval_sound
