import Ix.Cert.AiurCompression.StageBridge
import CertiFriProofs.Audit128

/-! # Escape Predicates, Statement Uniqueness & Constructive Negative Controls for Aiur Compression

No theorem in this module states end-to-end soundness of the compression chain
(`Outer plonk::native PLONK` → `CompressFinalNarrow` → `CompressNarrowFixed` → `CompressGL` →
`CompressWrap` → `ix_aggr` root).

Withdrawn: `aiur_compression_l3_bn254_end_to_end` and
`aiur_compression_128bit_bls12381_end_to_end` composed that chain under the hypothesis bundles
`Bn254AiurCompressionTcbGaps` / `Bls12381AiurCompressionTcbGaps`, which have no inhabitant
(`Bn254AiurCompressionTcbGaps.inconsistent`, `Bls12381AiurCompressionTcbGaps.inconsistent`), so
both held whatever they concluded. They also modelled the legacy `"ix/outer-ir/v1"` outer circuit
and a single-layer statement chain, neither of which the deployed `--aiur-stages` chain uses.

Remaining theorems:
1. `bn254AiurEscape_false_on_honest`, `bls12381AiurEscape_false_on_honest`: the escape
   predicates are not tautologies (false on the honest inputs they name).
2. `aiur_compression_statement_binding_unique`: two `AiurStageStatementChain`s with equal
   terminal limbs bind the same `(rootKeyPin, rootKeyBytes, rootClaimsBytes)` up to a concrete
   BLAKE3 collision. `AiurStageStatementChain` is the single-layer chain; the deployed
   `--aiur-stages` terminal statement is two hash layers deep (wrapper key and claim prefix), so
   this does not say which root a deployed L3 proof binds.
3. Six constructive negative-control theorems proving deterministic rejection of wrong root
   key pins, tampered statement limbs/words, cross-curve downgrades (BN254 on 128-bit profile,
   missing BLS12-381 G1 subgroup check, 3-torsion point injection), protocol/FRI downgrades
   (`v5`, `Fp^2`, 32-byte and retired 48-byte digests, `(2, 100, 0, 20)`, `(4, 55, 0, 0)`),
   unpinned/wrong-format manifests, and policy/stage/header tampering.

Zero `sorry`, zero custom `axiom`, zero `native_decide`, zero `bv_decide`.
-/

namespace Ix.Cert.AiurCompression

open Aiur Aiur.Tiling Aiur.Plonk
open Ix.Cert.Compression.Foreign
open Ix.Cert.Compression.NativeField
open Ix.Cert.Compression.OuterRelation
open Ix.Cert.Compression.Bls12381.Field
open Ix.Cert.Compression.Bls12381.CurveMsm
open Ix.Cert.Compression.Bls12381.OuterRelation
open Ix.Cert.Compression.Bls12381.EndToEnd
open Ix.Cert.MultiStark
open Ix.Cert.MultiStark.Security128
open Ix.Cert.Aggr

/-! ## 1. Helper: Packing Unpacked 128-Bit Limbs Round-Trip -/

private theorem pack4U32_unpackU128 {x : Nat} (hx : x < 2 ^ 128) :
    pack4U32ToU128 (x % 2 ^ 32) ((x / 2 ^ 32) % 2 ^ 32)
      ((x / 2 ^ 64) % 2 ^ 32) ((x / 2 ^ 96) % 2 ^ 32) = x := by
  unfold pack4U32ToU128
  omega

theorem pack_unpack_limbs_roundtrip {low high : Nat} (hLow : low < 2 ^ 128) (hHigh : high < 2 ^ 128) :
    packU32WordsToLimbs (unpackLimbsToU32Words low high) = (low, high) := by
  unfold packU32WordsToLimbs unpackLimbsToU32Words unpackU128To4U32
  simp only [List.cons_append, List.nil_append, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]
  rw [pack4U32_unpackU128 hLow, pack4U32_unpackU128 hHigh]

/-! ## 2. Explicit Cryptographic Escape Predicates (Collision or Folding-Challenge Bad Event) -/

/-- Exhaustive cryptographic escape disjunction for the L3 BN254 Aiur compression chain against
concrete transcript/witness parameters `(d0, d1, ρ, finalPolicy, w₂, prevAcc, cur₂)`:
either a concrete BLAKE3 collision occurred (on `"ix/outer-ir/v1"` or `"IXAUKG01"` policy bytes)
or one of the concrete Fiat–Shamir pairing-folding challenges (`ρ` in the outer `plonk::native`
terminal verifier, or `w₂` in
`CompressFinalNarrow`) satisfied its folded check while landing in an algebraic bad set of size
`≤ 1` out of `bn254FrModulus` (`≤ 2^{-253}`). -/
def Bn254AiurEscape
    {vk : GnarkVerifyingKey} {inp : OuterInputs}
    (bp : BilinearPairing) (outerKeys deferredKeys : bp.G2 × bp.G2)
    (leftOf rightOf : OuterOutputs → bp.G1) (d0 d1 : bp.G1) (ρ : BN254Fr)
    (acc : GnarkOuterAccepted vk inp
      (fun out => FoldedPairingCheck bp outerKeys deferredKeys (leftOf out) (rightOf out) d0 d1 ρ))
    (manifest : StageManifest)
    (finalPolicy : PackedPolicy) (w₂ : BN254Fr) (prevAcc cur₂ : bp.G1 × bp.G1) : Prop :=
  Blake3Collision acc.outerProgram.encode vk.expectedProgram.encode ∨
  Blake3Collision finalPolicy.encode manifest.policy.encode ∨
  (∃ out, vk.expectedProgram.Satisfied inp out ∧
    FoldedPairingCheck bp outerKeys deferredKeys (leftOf out) (rightOf out) d0 d1 ρ ∧
    (Finset.univ.filter fun ρ' : BN254Fr =>
      FoldedPairingCheck bp outerKeys deferredKeys (leftOf out) (rightOf out) d0 d1 ρ').card ≤ 1) ∨
  (bn254DeferredVal bp deferredKeys (bn254FoldStep bp w₂ prevAcc cur₂) = 1 ∧
    (Finset.univ.filter fun w' : BN254Fr =>
      bn254DeferredVal bp deferredKeys (bn254FoldStep bp w' prevAcc cur₂) = 1).card ≤ 1)

/-- Exhaustive cryptographic escape disjunction for the 128-bit BLS12-381 Aiur compression chain
against concrete transcript/witness parameters `(d0, d1, ρ, finalPolicy, w₂, prevAcc, cur₂)`:
either a concrete BLAKE3 collision occurred (on `"ix/outer-ir/v1"` or `"IXAUKG01"` policy bytes)
or a concrete pairing-folding challenge (`ρ` or `w₂`) satisfied its subgroup-enforced folded
check while hitting a bad set of size `≤ 1` out of `bls12381FrModulus` (`≤ 2^{-254}`). -/
def Bls12381AiurEscape
    {vk : Bls12381GnarkVerifyingKey} {inp : Bls12381OuterInputs}
    (bp : Bls12381BilinearPairing) (outerKeys deferredKeys : bp.G2 × bp.G2)
    (leftOf rightOf : Bls12381OuterOutputs → bp.G1) (d0 d1 : bp.G1) (ρ : BLS12381Fr)
    (acc : Bls12381GnarkOuterAccepted vk inp
      (fun out => Bls12381FoldedPairingCheck bp outerKeys deferredKeys
        (leftOf out) (rightOf out) d0 d1 ρ))
    (manifest : StageManifest)
    (finalPolicy : PackedPolicy) (w₂ : BLS12381Fr) (prevAcc cur₂ : bp.G1 × bp.G1) : Prop :=
  Blake3Collision acc.outerProgram.encode vk.expectedProgram.encode ∨
  Blake3Collision finalPolicy.encode manifest.policy.encode ∨
  (∃ out, vk.expectedProgram.Satisfied inp out ∧
    bp.AllInPrimeSubgroupG1 (leftOf out) (rightOf out) d0 d1 ∧
    Bls12381FoldedPairingCheck bp outerKeys deferredKeys (leftOf out) (rightOf out) d0 d1 ρ ∧
    (Finset.univ.filter fun ρ' : BLS12381Fr =>
      Bls12381FoldedPairingCheck bp outerKeys deferredKeys
        (leftOf out) (rightOf out) d0 d1 ρ').card ≤ 1) ∨
  (BlsPairInSubgroup bp prevAcc ∧
    BlsPairInSubgroup bp cur₂ ∧
    bls12381DeferredVal bp deferredKeys (bls12381FoldStep bp w₂ prevAcc cur₂) = 1 ∧
    (Finset.univ.filter fun w' : BLS12381Fr =>
      bls12381DeferredVal bp deferredKeys (bls12381FoldStep bp w' prevAcc cur₂) = 1).card ≤ 1)

/-- **Escape Predicate Is Not a Tautology (`bn254AiurEscape_false_on_honest`):**
Proves that `Bn254AiurEscape` is false on honest non-colliding inputs (and also when the deferred
fold check fails). It says nothing about whether any hypothesis bundle can be met. -/
theorem bn254AiurEscape_false_on_honest
    {vk : GnarkVerifyingKey} {inp : OuterInputs}
    (bp : BilinearPairing) (outerKeys deferredKeys : bp.G2 × bp.G2)
    (leftOf rightOf : OuterOutputs → bp.G1) (d0 d1 : bp.G1) (ρ : BN254Fr)
    (acc : GnarkOuterAccepted vk inp
      (fun out => FoldedPairingCheck bp outerKeys deferredKeys (leftOf out) (rightOf out) d0 d1 ρ))
    (manifest : StageManifest)
    (finalPolicy : PackedPolicy) (w₂ : BN254Fr) (prevAcc cur₂ : bp.G1 × bp.G1)
    (hProg : acc.outerProgram = vk.expectedProgram)
    (hPol : finalPolicy = manifest.policy)
    (hOuter : ∀ out, vk.expectedProgram.Satisfied inp out →
      bp.outerPairingVal outerKeys (leftOf out) (rightOf out) = 1)
    (hDef : bp.deferredPairingVal deferredKeys d0 d1 = 1)
    (hStage :
      (bn254DeferredVal bp deferredKeys prevAcc = 1 ∧
        bn254DeferredVal bp deferredKeys cur₂ = 1) ∨
      bn254DeferredVal bp deferredKeys (bn254FoldStep bp w₂ prevAcc cur₂) ≠ 1) :
    ¬ Bn254AiurEscape bp outerKeys deferredKeys leftOf rightOf d0 d1 ρ acc manifest
        finalPolicy w₂ prevAcc cur₂ := by
  rintro (hCol1 | hCol2 | ⟨out, hSat, _, hCardRho⟩ | ⟨hFoldEq, hCardW⟩)
  · exact hCol1.1 (congrArg OuterProgram.encode hProg)
  · exact hCol2.1 (congrArg PackedPolicy.encode hPol)
  · have hOut1 := hOuter out hSat
    have hmem : ∀ ρ' : BN254Fr, ρ' ∈ Finset.univ.filter fun ρ' : BN254Fr =>
        FoldedPairingCheck bp outerKeys deferredKeys (leftOf out) (rightOf out) d0 d1 ρ' := by
      intro ρ'
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (foldedPairingCheck_iff bp outerKeys deferredKeys _ _ _ _ _).mpr
        (by rw [hOut1, hDef, one_pow, mul_one])⟩
    exact zero_ne_one (Finset.card_le_one.mp hCardRho 0 (hmem 0) 1 (hmem 1))
  · rcases hStage with ⟨hPrev, hCur2⟩ | hNe
    · have hmem : ∀ w' : BN254Fr, w' ∈ Finset.univ.filter fun w' : BN254Fr =>
          bn254DeferredVal bp deferredKeys (bn254FoldStep bp w' prevAcc cur₂) = 1 := by
        intro w'
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by rw [bn254DeferredVal_foldStep, hPrev, hCur2, one_pow, mul_one]⟩
      exact zero_ne_one (Finset.card_le_one.mp hCardW 0 (hmem 0) 1 (hmem 1))
    · exact hNe hFoldEq

/-- **Escape Predicate Is Not a Tautology (`bls12381AiurEscape_false_on_honest`):**
Proves that `Bls12381AiurEscape` is false on honest prime-subgroup non-colliding inputs (and also
when the deferred fold check fails). It says nothing about whether any hypothesis bundle can be
met. -/
theorem bls12381AiurEscape_false_on_honest
    {vk : Bls12381GnarkVerifyingKey} {inp : Bls12381OuterInputs}
    (bp : Bls12381BilinearPairing) (outerKeys deferredKeys : bp.G2 × bp.G2)
    (leftOf rightOf : Bls12381OuterOutputs → bp.G1) (d0 d1 : bp.G1) (ρ : BLS12381Fr)
    (acc : Bls12381GnarkOuterAccepted vk inp
      (fun out => Bls12381FoldedPairingCheck bp outerKeys deferredKeys
        (leftOf out) (rightOf out) d0 d1 ρ))
    (manifest : StageManifest)
    (finalPolicy : PackedPolicy) (w₂ : BLS12381Fr) (prevAcc cur₂ : bp.G1 × bp.G1)
    (hProg : acc.outerProgram = vk.expectedProgram)
    (hPol : finalPolicy = manifest.policy)
    (hOuter : ∀ out, vk.expectedProgram.Satisfied inp out →
      bp.outerPairingVal outerKeys (leftOf out) (rightOf out) = 1)
    (hDef : bp.deferredPairingVal deferredKeys d0 d1 = 1)
    (hStage :
      (bls12381DeferredVal bp deferredKeys prevAcc = 1 ∧
        bls12381DeferredVal bp deferredKeys cur₂ = 1) ∨
      bls12381DeferredVal bp deferredKeys (bls12381FoldStep bp w₂ prevAcc cur₂) ≠ 1) :
    ¬ Bls12381AiurEscape bp outerKeys deferredKeys leftOf rightOf d0 d1 ρ acc manifest
        finalPolicy w₂ prevAcc cur₂ := by
  rintro (hCol1 | hCol2 | ⟨out, hSat, hSubAll, _, hCardRho⟩ | ⟨hPrevSub, hCur2Sub, hFoldEq, hCardW⟩)
  · exact hCol1.1 (congrArg Bls12381OuterProgram.encode hProg)
  · exact hCol2.1 (congrArg PackedPolicy.encode hPol)
  · have hOut1 := hOuter out hSat
    have hmem : ∀ ρ' : BLS12381Fr, ρ' ∈ Finset.univ.filter fun ρ' : BLS12381Fr =>
        Bls12381FoldedPairingCheck bp outerKeys deferredKeys (leftOf out) (rightOf out) d0 d1 ρ' := by
      intro ρ'
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _,
        (bls12381_foldedPairingCheck_iff bp outerKeys deferredKeys _ _ _ _ _).mpr
          ⟨hSubAll, by rw [hOut1, hDef, one_pow, mul_one]⟩⟩
    exact zero_ne_one (Finset.card_le_one.mp hCardRho 0 (hmem 0) 1 (hmem 1))
  · rcases hStage with ⟨hPrev, hCur2⟩ | hNe
    · have hmem : ∀ w' : BLS12381Fr, w' ∈ Finset.univ.filter fun w' : BLS12381Fr =>
          bls12381DeferredVal bp deferredKeys (bls12381FoldStep bp w' prevAcc cur₂) = 1 := by
        intro w'
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by
          rw [bls12381DeferredVal_foldStep bp deferredKeys w' hPrevSub hCur2Sub,
            hPrev, hCur2, one_pow, mul_one]⟩
      exact zero_ne_one (Finset.card_le_one.mp hCardW 0 (hmem 0) 1 (hmem 1))
    · exact hNe hFoldEq

/-! ## 3. Cross-Pipeline Statement-Binding Uniqueness (single-layer chain model) -/

/-- **Statement-Chain Uniqueness (`aiur_compression_statement_binding_unique`):**
Any two `AiurStageStatementChain`s whose outer public statement limbs agree in `BLS12381Fr`
(or `BN254Fr`) MUST certify the exact same `(rootKeyPin, rootKeyBytes, rootClaimsBytes)` up to
a concrete BLAKE3 collision. This is about the single-layer `AiurStageStatementChain`, not the
two-layer statement the deployed `--aiur-stages` terminal publishes. -/
theorem aiur_compression_statement_binding_unique {pin₁ pin₂ : Vector UInt8 32}
    (c₁ : AiurStageStatementChain pin₁) (c₂ : AiurStageStatementChain pin₂)
    (hAgree : ((c₁.terminalLow : BN254Fr) = (c₂.terminalLow : BN254Fr) ∧
               (c₁.terminalHigh : BN254Fr) = (c₂.terminalHigh : BN254Fr)) ∨
              ((c₁.terminalLow : BLS12381Fr) = (c₂.terminalLow : BLS12381Fr) ∧
               (c₁.terminalHigh : BLS12381Fr) = (c₂.terminalHigh : BLS12381Fr))) :
    Blake3Collision
        (compressWrapPreimage pin₁.toList (Blake3.Pure.digest c₁.rootClaimsBytes).toList)
        (compressWrapPreimage pin₂.toList (Blake3.Pure.digest c₂.rootClaimsBytes).toList) ∨
      Blake3Collision c₁.rootKeyBytes c₂.rootKeyBytes ∨
      Blake3Collision c₁.rootClaimsBytes c₂.rootClaimsBytes ∨
      (pin₁ = pin₂ ∧ c₁.rootKeyBytes = c₂.rootKeyBytes ∧ c₁.rootClaimsBytes = c₂.rootClaimsBytes) := by
  rcases hAgree with ⟨hl, hh⟩ | ⟨hl, hh⟩
  · exact statementChain_unique_bn254_or_collision c₁ c₂ hl hh
  · exact statementChain_unique_bls12381_or_collision c₁ c₂ hl hh

/-! ## 4. Constructive Negative Controls -/

/-- **Negative Control 1 (Wrong Root Key Pin Rejected):**
Substituting a rogue root key `rogueKeyBytes` whose BLAKE3 digest differs from `trustedPin`
cannot satisfy `AiurStageStatementChain trustedPin` and produces a strictly distinct
`"ix/compress-wrap/v1\0"` preimage. -/
theorem negControl_wrong_root_key_pin (trustedPin : Vector UInt8 32)
    (rogueKeyBytes claimsBytes : List UInt8)
    (hMismatch : Blake3.Pure.digest rogueKeyBytes ≠ trustedPin) :
    (∀ c : AiurStageStatementChain trustedPin, c.rootKeyBytes ≠ rogueKeyBytes) ∧
    compressWrapPreimage (Blake3.Pure.digest rogueKeyBytes).toList (Blake3.Pure.digest claimsBytes).toList ≠
      compressWrapPreimage trustedPin.toList (Blake3.Pure.digest claimsBytes).toList := by
  refine ⟨fun c heq => hMismatch (heq ▸ c.rootKey_pinned), fun hpre => hMismatch ?_⟩
  have ⟨hk, _⟩ := compressWrapPreimage_injective (by simp) (by simp) hpre
  exact Vector.ext fun i hi => by
    have := congrArg (fun l => l[i]?) hk
    simpa [Vector.getElem?_toList, hi] using this

/-- **Negative Control 2 (Tampered Statement Words / Limbs Rejected in Both `BN254Fr` and `BLS12381Fr`):**
1. Perturbing the low public limb by `+ 1` (the exact tamper test in `stages/terminal.rs:237`)
   strictly diverges in BOTH `BN254Fr` and `BLS12381Fr`.
2. Replacing any canonical 8-word statement `ws₁` by a distinct canonical 8-word statement `ws₂ ≠ ws₁`
   strictly changes the terminal `(low, high)` public inputs in BOTH `BN254Fr` and `BLS12381Fr`! -/
theorem negControl_tampered_statement_words
    (low : Nat) {ws₁ ws₂ : List Nat}
    (hl₁ : ws₁.length = 8) (hu₁ : ∀ w ∈ ws₁, w < 2 ^ 32)
    (hl₂ : ws₂.length = 8) (hu₂ : ∀ w ∈ ws₂, w < 2 ^ 32)
    (hne : ws₁ ≠ ws₂) :
    ((low : BN254Fr) + 1 ≠ (low : BN254Fr)) ∧
    ((low : BLS12381Fr) + 1 ≠ (low : BLS12381Fr)) ∧
    ¬ (((packU32WordsToLimbs ws₁).1 : BN254Fr) = ((packU32WordsToLimbs ws₂).1 : BN254Fr) ∧
       ((packU32WordsToLimbs ws₁).2 : BN254Fr) = ((packU32WordsToLimbs ws₂).2 : BN254Fr)) ∧
    ¬ (((packU32WordsToLimbs ws₁).1 : BLS12381Fr) = ((packU32WordsToLimbs ws₂).1 : BLS12381Fr) ∧
       ((packU32WordsToLimbs ws₁).2 : BLS12381Fr) = ((packU32WordsToLimbs ws₂).2 : BLS12381Fr)) := by
  have hb₁ := packU32WordsToLimbs_lt hl₁ hu₁
  have hb₂ := packU32WordsToLimbs_lt hl₂ hu₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; simp at h
  · intro h; simp at h
  · rintro ⟨hL, hH⟩
    have ⟨e1, e2⟩ := limbs_embed_bn254_injective hb₁.1 hb₁.2 hb₂.1 hb₂.2 hL hH
    exact hne (packU32WordsToLimbs_injective hl₁ hu₁ hl₂ hu₂ (Prod.ext e1 e2))
  · rintro ⟨hL, hH⟩
    have ⟨e1, e2⟩ := limbs_embed_bls12381_injective hb₁.1 hb₁.2 hb₂.1 hb₂.2 hL hH
    exact hne (packU32WordsToLimbs_injective hl₁ hu₁ hl₂ hu₂ (Prod.ext e1 e2))

/-- **Negative Control 3 (Cross-Curve Downgrade & Torsion Injection Rejected):**
1. BN254 is constructively rejected on `AiurCompression128Ok` for ALL STARK parameters and curve specs.
2. BLS12-381 omitting its mandatory `G1` subgroup check (`bls12381UncheckedSpec`) is rejected.
3. The concrete canonical BLS12-381 3-torsion point `(0, 2)` is rejected by `InPrimeSubgroup`
   and `Bls12381KzgPairingCheck`. -/
theorem negControl_cross_curve_downgrade
    (extDeg protoVer digestBytes : Nat) (starkParams : StarkParams) (requireUd : Bool)
    (spec : Ix.Cert.Compression.Security128.PairingCurveSpec) (P : bls12381G1.Point) (z τ : BLS12381Fr) :
    ¬ AiurCompression128Ok extDeg protoVer digestBytes starkParams requireUd .bn254 spec ∧
    ¬ AiurCompression128Ok extDeg protoVer digestBytes starkParams requireUd .bls12381
        Ix.Cert.Compression.Security128.bls12381UncheckedSpec ∧
    ¬ InPrimeSubgroup bls12381TorsionPoint ∧
    ¬ Ix.Cert.Compression.Bls12381.RecursiveKzg.Bls12381KzgPairingCheck bls12381TorsionPoint P z τ := by
  refine ⟨?_, ?_, bls12381_torsionPoint_not_inPrimeSubgroup,
    (Ix.Cert.Compression.Bls12381.RecursiveKzg.bls12381_kzg_pairingCheck_rejects_torsion P z τ).1⟩
  · intro h
    have hfq : 2 ^ 380 ≤ bn254FqModulus := h.2.2.1 ▸ h.2.1.1
    exact not_le_of_gt Ix.Cert.Compression.Security128.negControl_bn254_fq_below_380.2 hfq
  · intro h
    exact Ix.Cert.Compression.Security128.negControl_bls12381_missing_subgroup_check_rejected h.2.1

/-- **Negative Control 4 (Protocol / FRI Downgrade Rejected):**
Downgrading the Multi-STARK root/wrap layer to `Fp^2`, protocol `v5`, 32-byte `BLAKE3-256`
(classical-only) or retired 48-byte `BLAKE3-XOF48` digests, legacy `(2, 100, 0, 20)` queries,
or deceptive `(4, 55, 0, 0)` queries is constructively rejected by `AiurCompression128Ok` even
when paired with BLS12-381! -/
theorem negControl_protocol_downgrade :
    ¬ AiurCompression128Ok 2 6 64 v6Ud160Params true .bls12381
        Ix.Cert.Compression.Security128.bls12381CurveSpec ∧
    ¬ AiurCompression128Ok 3 5 64 v6Ud160Params true .bls12381
        Ix.Cert.Compression.Security128.bls12381CurveSpec ∧
    ¬ AiurCompression128Ok 3 6 32 v6Ud160Params true .bls12381
        Ix.Cert.Compression.Security128.bls12381CurveSpec ∧
    ¬ AiurCompression128Ok 3 6 48 v6Ud160Params true .bls12381
        Ix.Cert.Compression.Security128.bls12381CurveSpec ∧
    ¬ AiurCompression128Ok 3 6 64 v5Default100Params true .bls12381
        Ix.Cert.Compression.Security128.bls12381CurveSpec ∧
    ¬ AiurCompression128Ok 3 6 64 deceptive455Params false .bls12381
        Ix.Cert.Compression.Security128.bls12381CurveSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; exact negControl_fp2_rejected_128.2.1 h.1
  · intro h; have hv := h.1.2.1; unfold Aiur.protocolVersionV6 at hv; omega
  · intro h; have hd := h.1.2.2.1; unfold digestBytesBlake2b512 at hd; omega
  · intro h; have hd := h.1.2.2.1; unfold digestBytesBlake2b512 at hd; omega
  · intro h; exact absurd h.1.2.2.2 (by decide)
  · intro h; exact absurd h.1.2.2.2 (by decide)

/-- **Negative Control 5 (Unpinned Manifest, Wrong Format, or Tampered Manifest Rejected):**
1. Any setup product with `blake3Pin = none` and `sha256Pin = none` is rejected (`stages.rs:198`),
   so any `StageManifest` leaving e.g. `glKey` or `outerVk` unpinned fails `ManifestPinned`.
2. Any manifest with `format ≠ "ix-aiur-stages-v1"` fails `ManifestPinned`.
3. Any manifest whose bytes disagree with `manifestCallerPin` fails `ManifestPinned`. -/
theorem negControl_unpinned_manifest (sha256 : List UInt8 → List UInt8) (m : StageManifest)
    (bytes : List UInt8) :
    ¬ ProductPin.Pinned sha256 { bytes := bytes, blake3Pin := none, sha256Pin := none } ∧
    (m.glKey.blake3Pin = none → m.glKey.sha256Pin = none → ¬ ManifestPinned sha256 m) ∧
    (m.format ≠ stagesManifestFormat → ¬ ManifestPinned sha256 m) ∧
    (Blake3.Pure.digest m.manifestBytes ≠ m.manifestCallerPin → ¬ ManifestPinned sha256 m) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    rcases h.1 with hb | hs
    · simp at hb
    · simp at hs
  · intro hb hs hm
    rcases hm.glKey_ok.1 with h1 | h2
    · rw [hb] at h1; simp at h1
    · rw [hs] at h2; simp at h2
  · intro hfmt hm; exact hfmt hm.format_ok
  · intro hpin hm; exact hpin hm.caller_pin_ok

/-- **Negative Control 6 (Policy Key/Anchor Substitution & Terminal Stage/Header Tampering Rejected):**
1. Altering `glKeyDigest` or `anchors` in a well-formed `PackedPolicy` strictly changes its
   208-byte `IXAUKG01` encoding.
2. Substituting a rogue `glKey` whose BLAKE3 digest differs from `m.policy.glKeyDigest` violates
   `ManifestPinned`.
3. `_root_.MultiStark.FinalNarrow.source` rejects any stage `< 2` and any header width sum `≠ 21`. -/
theorem negControl_policy_key_and_stage_tampering
    (sha256 : List UInt8 → List UInt8) (m : StageManifest)
    {p₁ p₂ : PackedPolicy} (hp₁ : p₁.WellFormed) (hp₂ : p₂.WellFormed)
    (cfg : _root_.MultiStark.Final.Configuration) (headers : List NarrowClaimHeader) :
    (p₁.glKeyDigest ≠ p₂.glKeyDigest → p₁.encode ≠ p₂.encode) ∧
    (p₁.anchors ≠ p₂.anchors → p₁.encode ≠ p₂.encode) ∧
    ((Blake3.Pure.digest m.glKey.bytes).toList ≠ m.policy.glKeyDigest → ¬ ManifestPinned sha256 m) ∧
    (cfg.minStage < 2 → validateFinalNarrowConfig cfg headers ≠ .ok ()) ∧
    ((headers.map (·.values)).sum ≠ 21 → validateFinalNarrowConfig cfg headers ≠ .ok ()) := by
  refine ⟨?_, ?_, ?_, validateFinalNarrowConfig_rejects_stage_one cfg headers,
    validateFinalNarrowConfig_rejects_wrong_header_width cfg headers⟩
  · intro hne henc
    exact hne (congrArg PackedPolicy.glKeyDigest (PackedPolicy.encode_injective hp₁ hp₂ henc))
  · intro hne henc
    exact hne (congrArg PackedPolicy.anchors (PackedPolicy.encode_injective hp₁ hp₂ henc))
  · intro hne hm
    exact hne hm.policy_binds_glKey.symm

end Ix.Cert.AiurCompression
