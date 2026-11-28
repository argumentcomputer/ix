import Ix.Cert.AiurCompression.EndToEnd
import Aiur.Plonk.Layout

/-! # Constructive Satisfiability & Non-Vacuity Gate for L3 BN254 Aiur Compression

Constructively proves that the entire hypothesis bundle of `aiur_compression_l3_bn254_sound`
(`AiurScsOuterAccepted` + `Bn254AiurCompressionTcbGaps`) is **genuinely satisfiable** on a
non-trivial bilinear pairing model with real kernel-compiled Aiur programs and concrete witnesses
for ALL FOUR stages, AND proves that the cryptographic escape predicate `Bn254AiurEscape` is
**provably false** on those models so `aiur_compression_l3_bn254_sound` lands squarely in its
main non-escape soundness branch:

1. **Non-trivial pairing model (`toyPairing`):**
   `G1 = G2 = BN254Fr`, `GT = Multiplicative BN254Fr`, `e P Q = ofAdd (P * Q)`,
   with `toyPairing.e 1 1 ≠ 1` (`toyPairing_nontrivial`), non-zero fold challenges `w₁ = w₂ = 2`,
   non-zero stage pairs `cur₁ = (1, -1)` and `cur₂ = (-2, 2)`, and non-zero packed accumulator
   `prevAcc = (1, -1)`.
2. **Real kernel-compiled stage witnesses for all four L3 stages (symbolic over arbitrary digests):**
   - Stage 1 (`CompressWrap`): `GoldilocksWideStageWitness` over Goldilocks (`MultiStark.F`);
   - Stage 2 (`CompressGL`): `Bn254GroupedWideStageWitness` over `BN254Fr`;
   - Stage 3 (`CompressNarrowFixed`): `NarrowCompactStageWitness BN254Fr` with a checked
     `Periodic.Sharded BN254Fr` layout and balanced copy/message ledgers;
   - Stage 4 (`CompressFinalNarrow`): `PlonkSharedTerminalWitness` with a kernel-checked
     `DepthBridge.PlonkStageCert`, `PlonkStageWiring`, `emitCertifiedScs`, and `ChallengeGood`,
     linked directly to `AiurScsVerifyingKey` and `AiurScsOuterAccepted`.
3. **Both statement-policy modes verified non-vacuous:**
   - `bn254AiurCompression_consistent`: deployed two-layer `StatementPolicy.twoLayerWrap`;
   - `bn254AiurCompression_singleLayer_consistent`: single-layer `StatementPolicy.singleLayerDirect`.

Zero `sorry`, zero custom `axiom`, zero `native_decide`, zero `bv_decide`.
-/

namespace Ix.Cert.AiurCompression.Consistency

open Aiur Aiur.Circuit Aiur.Optimized Aiur.Tiling Aiur.Tiling.Bridge Aiur.Tiling.Grouped
open Aiur.Tiling.Periodic Aiur.Plonk
open Ix.Cert.Compression.Foreign
open Ix.Cert.Compression.OuterRelation
open Ix.Cert.MultiStark
open Ix.Cert.Aggr
open Ix.Cert.AiurCompression

/-! ## 1. Shared Algebraic, Polynomial & Minimal-Config Helpers -/

/-- Fallback empty `Chip` for `List.headD`. -/
def defaultChip (F : Type) : Chip F :=
  ⟨"", [], ⟨.tuple [], []⟩, 0, [], [], []⟩

/-- Fallback empty `WideStage.Air` for `List.headD`. -/
def defaultAirF (F : Type) [Zero F] : WideStage.Air F :=
  ⟨⟨0, 0, [], []⟩, 0, fun _ _ => 0⟩

/-- Minimal certified compiler config (all optional rewrite passes disabled so every compiler
pass is a clean symbolic identity on flat linear equality chips). -/
def minimalConfig : Optimized.Config where
  maxDegree := 3
  shareAuxiliaries := false
  eliminateSelectors := false
  propagateScopes := false
  simplifyConstraints := false
  propagateValues := false
  mergeLookups := false
  deduplicate := false

/-- Trivial acyclic depth configuration (no recursive chips, no range maps, `bits = 0 ≤ 24`). -/
def trivialDepthCfg : Depth.Config where
  limbs := []
  plans := []
  ranks := []
  structural := []

private theorem list_sum_map_range {M : Type} [AddCommMonoid M] (n : Nat) (f : Nat → M) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      Finset.sum_range_succ, ih]

/-- Normal simplified form of `var v - const c` under `Aiur.Optimized.Polynomial.simplify`. -/
def subConstPoly {F : Type} [Field F] [DecidableEq F] (v : Nat) (c : F) :
    Aiur.Optimized.Polynomial F :=
  if c = 0 then .var v else .sub (.var v) (.const c)

section SubConstLemmas

variable {F : Type} [Field F] [DecidableEq F]

omit [Field F] in
private theorem beq_var_const (v : Nat) (c : F) :
    ((Scalar.Circuit.ArithExpr.var v : Scalar.Circuit.ArithExpr F) == .const c) = false := rfl

omit [Field F] in
private theorem beq_const_var (c : F) (v : Nat) :
    ((Scalar.Circuit.ArithExpr.const c : Scalar.Circuit.ArithExpr F) == .var v) = false := rfl

omit [Field F] in
private theorem beq_sub_const (a b : Scalar.Circuit.ArithExpr F) (c : F) :
    (Scalar.Circuit.ArithExpr.sub a b == .const c) = false := rfl

omit [Field F] in
private theorem beq_sub_sub_var_const (v s : Nat) (c d : F) :
    ((Scalar.Circuit.ArithExpr.sub (.var v) (.const c) : Scalar.Circuit.ArithExpr F) ==
      .sub (.const d) (.var s)) = false := rfl

omit [Field F] in
private theorem beq_sub_mul (a b c d : Scalar.Circuit.ArithExpr F) :
    (Scalar.Circuit.ArithExpr.sub a b == .mul c d) = false := rfl

omit [Field F] in
private theorem beq_var_self (v : Nat) :
    ((Scalar.Circuit.ArithExpr.var v : Scalar.Circuit.ArithExpr F) == .var v) = true := by
  change (v == v) = true
  simp

theorem simplify_sub_var_const (v : Nat) (c : F) :
    Aiur.Optimized.Polynomial.simplify (.sub (.var v) (.const c)) = subConstPoly v c := by
  by_cases hc : c = 0 <;> simp [Aiur.Optimized.Polynomial.simplify, subConstPoly, hc, beq_var_const]

theorem simplify_subConstPoly (v : Nat) (c : F) :
    Aiur.Optimized.Polynomial.simplify (subConstPoly v c) = subConstPoly v c := by
  by_cases hc : c = 0 <;> simp [Aiur.Optimized.Polynomial.simplify, subConstPoly, hc, beq_var_const]

theorem subst_var_subConstPoly (v : Nat) (c : F) :
    (subConstPoly v c).subst Aiur.Optimized.Polynomial.var = subConstPoly v c := by
  by_cases hc : c = 0 <;> simp [Aiur.Optimized.Polynomial.subst, subConstPoly, hc]

theorem simplify_mul_one_subConstPoly (v : Nat) (c : F) :
    Aiur.Optimized.Polynomial.simplify (.mul (.const 1) (subConstPoly v c)) = subConstPoly v c := by
  by_cases hc : c = 0 <;> simp [Aiur.Optimized.Polynomial.simplify, subConstPoly, hc, beq_var_const]

theorem subConstPoly_beq_zero (v : Nat) (c : F) :
    (subConstPoly v c == .const 0) = false := by
  by_cases hc : c = 0 <;> simp [subConstPoly, hc, beq_var_const, beq_sub_const]

theorem subConstPoly_vars (v : Nat) (c : F) :
    (subConstPoly v c).vars = [v] := by
  by_cases hc : c = 0 <;> simp [Aiur.Optimized.Polynomial.vars, subConstPoly, hc]

theorem subConstPoly_degree (v : Nat) (c : F) :
    (subConstPoly v c).degree = 1 := by
  by_cases hc : c = 0 <;> simp [Aiur.Optimized.Polynomial.degree, Scalar.Circuit.ArithExpr.degree, subConstPoly, hc]

theorem subConstPoly_inBounds (v n : Nat) (c : F) :
    (subConstPoly v c).inBounds n = decide (v < n) := by
  by_cases hc : c = 0 <;> simp [Scalar.Circuit.ArithExpr.inBounds, subConstPoly, hc]

theorem subConstPoly_denote (v : Nat) (c : F) (a : Nat → F) :
    (subConstPoly v c).denote a = a v - c := by
  by_cases hc : c = 0 <;> simp [Scalar.Circuit.ArithExpr.denote, subConstPoly, hc]

theorem activation_subConstPoly_eq (v sel : Nat) (c : F) :
    Activation.polynomial sel (subConstPoly v c) =
      if c = 0 then .var v
      else if -c = 1 then .sub (.sub (.var v) (.const c)) (.sub (.const 1) (.var sel))
      else .sub (.sub (.var v) (.const c)) (.mul (.const (-c)) (.sub (.const 1) (.var sel))) := by
  unfold Activation.polynomial
  by_cases hc : c = 0
  · subst hc
    simp [subConstPoly, Scalar.Circuit.ArithExpr.denote, Aiur.Optimized.Polynomial.simplify,
      beq_const_var, beq_var_const]
  · have hneg0 : -c ≠ 0 := neg_ne_zero.mpr hc
    by_cases hneg1 : -c = 1
    · simp [subConstPoly, hc, Scalar.Circuit.ArithExpr.denote, Aiur.Optimized.Polynomial.simplify,
        hneg1, beq_var_const, beq_const_var, beq_sub_sub_var_const]
    · simp [subConstPoly, hc, Scalar.Circuit.ArithExpr.denote, Aiur.Optimized.Polynomial.simplify,
        hneg0, hneg1, beq_var_const, beq_const_var, beq_sub_mul]

theorem activation_subConstPoly_inBounds {v sel : Nat} (hv : v < sel) (c : F) :
    (Activation.polynomial sel (subConstPoly v c)).inBounds (sel + 1) = true := by
  rw [activation_subConstPoly_eq]
  split_ifs <;> simp [Scalar.Circuit.ArithExpr.inBounds, show v < sel + 1 by omega]

theorem poly_norm_activation_subConstPoly {i sel : Nat} (hlt : i < sel) (c : F) :
    Poly.norm (Poly.ofExpr (Activation.polynomial sel (subConstPoly i c))) =
      if c = 0 then [([i], (1 : F))] else [([i], (1 : F)), ([sel], -c)] := by
  have hne : i ≠ sel := Nat.ne_of_lt hlt
  have h10 : (1 : F) ≠ 0 := one_ne_zero
  rw [activation_subConstPoly_eq]
  by_cases hc : c = 0
  · subst hc
    simp [Tiling.Poly.ofExpr, Tiling.Poly.var, Tiling.Poly.norm, Tiling.Poly.insertTerm, h10]
  · have hneg0 : -c ≠ 0 := neg_ne_zero.mpr hc
    by_cases hneg1 : -c = 1
    · have hcneg : c = -1 := by linear_combination -hneg1
      subst hcneg
      have h1sub1 : (1 : F) + -1 = 0 := by ring
      simp [hc, hneg1, Tiling.Poly.ofExpr, Tiling.Poly.var, Tiling.Poly.const, Tiling.Poly.sub,
        Tiling.Poly.neg, Tiling.Poly.norm, Tiling.Poly.insertTerm, Tiling.Mono.lt,
        hne, hlt, h10, h1sub1]
    · simp [hc, hneg0, hneg1, Tiling.Poly.ofExpr, Tiling.Poly.var, Tiling.Poly.const,
        Tiling.Poly.sub, Tiling.Poly.neg, Tiling.Poly.mul, Tiling.Poly.norm,
        Tiling.Poly.insertTerm, Tiling.Mono.mul, Tiling.Mono.insert, Tiling.Mono.lt,
        hne, hlt, h10]

theorem poly_norm_linear_pair {i sel : Nat} (hlt : i < sel) (c : F) :
    Poly.norm ([([i], (1 : F)), ([sel], -c)]) =
      if c = 0 then [([i], (1 : F))] else [([i], (1 : F)), ([sel], -c)] := by
  have hne : i ≠ sel := Nat.ne_of_lt hlt
  have h10 : (1 : F) ≠ 0 := one_ne_zero
  by_cases hc : c = 0
  · subst hc
    simp [Poly.norm, Poly.insertTerm, h10]
  · have hneg0 : -c ≠ 0 := neg_ne_zero.mpr hc
    simp [Poly.norm, Poly.insertTerm, hne, hlt, h10, hneg0, hc, Mono.lt]

end SubConstLemmas

/-! ## 2. Non-Trivial Bilinear Pairing Model, Codecs, Policy, Manifest & `ix_aggr` Root

All BLAKE3 digests in this section remain **completely symbolic** (zero kernel evaluation of
`Blake3.Pure.digest`), while `toySha256 := id` satisfies every pin by `rfl`. -/

/-- Identity function used as abstract `sha256` in the consistency model. -/
def toySha256 (bs : List UInt8) : List UInt8 := bs

/-- Non-trivial bilinear pairing model over `BN254Fr`:
`G1 = G2 = BN254Fr`, `GT = Multiplicative BN254Fr`, `e P H = ofAdd (P * H)`.
Marked `abbrev` so `toyPairing.G1 = BN254Fr` and `toyPairing.G2 = BN254Fr` are transparent. -/
abbrev toyPairing : BilinearPairing where
  G1 := BN254Fr
  G2 := BN254Fr
  GT := Multiplicative BN254Fr
  smul := fun ρ P => ρ * P
  e := fun P H => Multiplicative.ofAdd (P * H)
  e_add := fun P Q H => by simp [add_mul, ofAdd_add]
  e_smul := fun ρ P H => by
    have hmul : (ρ.val • (P * H) : BN254Fr) = (ρ * P) * H := by
      rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_assoc]
    rw [← ofAdd_nsmul, hmul]
  gt_pow_order := fun x => by
    have hmod : (bn254FrModulus : BN254Fr) = 0 := ZMod.natCast_self bn254FrModulus
    have h1 : x ^ bn254FrModulus =
        Multiplicative.ofAdd (bn254FrModulus • Multiplicative.toAdd x) := by
      rw [ofAdd_nsmul, ofAdd_toAdd]
    rw [h1, nsmul_eq_mul, hmod, zero_mul]
    rfl

/-- `toyPairing` is strictly non-degenerate: `e(1, 1) ≠ 1`. -/
theorem toyPairing_nontrivial : toyPairing.e (1 : BN254Fr) (1 : BN254Fr) ≠ 1 := by
  intro h
  have h0 : (1 : BN254Fr) = 0 := by
    have h' := congrArg Multiplicative.toAdd h
    simp only [toyPairing, mul_one] at h'
    exact h'
  exact one_ne_zero h0

def toyAnchors : BN254Fr × BN254Fr := (1, 1)
def toyAnchorsBytes : List UInt8 := List.replicate 128 0

def toyAffineCodec : Bn254AffineCodec toyPairing where
  decodePoint := fun p => if p.infinity then some (0 : BN254Fr) else some (p.x.toNat : BN254Fr)
  decode_infinity := fun _ hp => by simp [hp]

def toyPackedCodec : Bn254PackedAccCodec toyPairing where
  decodePacked := fun ws =>
    match ws with
    | [a, b, _, _] => some (a, b)
    | _ => none
  decode_len := fun ws pair h => by
    rcases ws with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | _⟩⟩⟩⟩ <;> simp at h ⊢

-- Non-zero honest challenges and stage accumulator pairs
def toyW1 : BN254Fr := 2
def toyW2 : BN254Fr := 2
def toyCur1 : BN254Fr × BN254Fr := (1, -1)
def toyPrevAcc : BN254Fr × BN254Fr := (1, -1)
def toyPrevAccWords : List BN254Fr := [1, -1, 0, 0]
def toyCur2 : BN254Fr × BN254Fr := (-2, 2)

theorem toyW1_ne_zero : toyW1 ≠ 0 := by decide
theorem toyW2_ne_zero : toyW2 ≠ 0 := by decide

theorem toyCur1_passes : bn254DeferredVal toyPairing toyAnchors toyCur1 = 1 := by
  simp [bn254DeferredVal, toyPairing, toyAnchors, toyCur1]

theorem toyPrevAcc_passes : bn254DeferredVal toyPairing toyAnchors toyPrevAcc = 1 := toyCur1_passes

theorem toyCur2_passes : bn254DeferredVal toyPairing toyAnchors toyCur2 = 1 := by
  simp [bn254DeferredVal, toyPairing, toyAnchors, toyCur2]

theorem toyFold1_eq : bn254FoldStep toyPairing toyW1 (0, 0) toyCur1 = toyPrevAcc := by
  simp [bn254FoldStep, toyPairing, toyW1, toyCur1, toyPrevAcc]

theorem toyFold2_eq : bn254FoldStep toyPairing toyW2 toyPrevAcc toyCur2 = (0, 0) := by
  simp [bn254FoldStep, toyPairing, toyW2, toyPrevAcc, toyCur2]

-- Keys, claims, policy, and symbolic statement digests (ZERO BLAKE3 reduction!)
def toyRootKeyBytes : List UInt8 := [0x01]
def toyRootClaimsBytes : List UInt8 := [0x02]
def toyWrapKeyBytes : List UInt8 := [0x03]
def toyGlKeyBytes : List UInt8 := [0x04]
def toyNarrowKeyBytes : List UInt8 := [0x05]

def toyRootKeyPin : Vector UInt8 32 := Blake3.Pure.digest toyRootKeyBytes
def toyWrapKeyDigest : Vector UInt8 32 := Blake3.Pure.digest toyWrapKeyBytes

def toyWrapPolicy : WrapPolicySpec where
  wrapKeyDigest := toyWrapKeyDigest
  claimPrefix0 := 0
  claimPrefix1 := 1
  prefix0_lt := by decide
  prefix1_lt := by decide

def toyPolicy : PackedPolicy where
  anchors := toyAnchorsBytes
  glKeyDigest := (Blake3.Pure.digest toyGlKeyBytes).toList
  glEntry := 0
  narrowKeyDigest := (Blake3.Pure.digest toyNarrowKeyBytes).toList
  narrowEntry := 0

theorem toyPolicy_wf : toyPolicy.WellFormed :=
  ⟨by simp [toyPolicy, toyAnchorsBytes],
   Vector.length_toList,
   by change (0 : Nat) < 2 ^ 32; decide,
   Vector.length_toList,
   by change (0 : Nat) < 2 ^ 32; decide⟩

-- Symbolic 8-word digests & 128-bit terminal limbs
def toyRootWords : List Nat := rootStatementWords toyRootKeyPin toyRootClaimsBytes
def toyGlWords : List Nat := toyWrapPolicy.glStatementWords toyRootWords
def toyPolicyWords : List Nat := packBytes32ToU32Words toyPolicy.digest.toList
def toyTwoLimbs : Nat × Nat :=
  (StatementPolicy.twoLayerWrap toyWrapPolicy).terminalLimbs toyRootKeyPin toyRootClaimsBytes
def toyOneLimbs : Nat × Nat :=
  StatementPolicy.singleLayerDirect.terminalLimbs toyRootKeyPin toyRootClaimsBytes

theorem toyRootWords_canon : CanonicalU32Digest8 toyRootWords :=
  canonicalU32Digest8_rootStatementWords toyRootKeyPin toyRootClaimsBytes

theorem toyGlWords_canon : CanonicalU32Digest8 toyGlWords :=
  canonicalU32Digest8_terminalStatementWords (.twoLayerWrap toyWrapPolicy) toyRootKeyPin toyRootClaimsBytes

theorem toyPolicyWords_canon : CanonicalU32Digest8 toyPolicyWords :=
  canonicalU32Digest8_packBytes32 toyPolicy.digest.toList

theorem toyTwoLimbs_lt : toyTwoLimbs.1 < 2 ^ 128 ∧ toyTwoLimbs.2 < 2 ^ 128 :=
  (StatementPolicy.twoLayerWrap toyWrapPolicy).terminalLimbs_lt toyRootKeyPin toyRootClaimsBytes

theorem toyOneLimbs_lt : toyOneLimbs.1 < 2 ^ 128 ∧ toyOneLimbs.2 < 2 ^ 128 :=
  StatementPolicy.singleLayerDirect.terminalLimbs_lt toyRootKeyPin toyRootClaimsBytes

theorem toyTwoLimbs_unpack : unpackLimbsToU32Words toyTwoLimbs.1 toyTwoLimbs.2 = toyGlWords :=
  (StatementPolicy.twoLayerWrap toyWrapPolicy).unpack_terminalLimbs toyRootKeyPin toyRootClaimsBytes

theorem toyOneLimbs_unpack : unpackLimbsToU32Words toyOneLimbs.1 toyOneLimbs.2 = toyRootWords :=
  StatementPolicy.singleLayerDirect.unpack_terminalLimbs toyRootKeyPin toyRootClaimsBytes

def toyPin (bs : List UInt8) : ProductPin where
  bytes := bs
  blake3Pin := some (Blake3.Pure.digest bs)
  sha256Pin := some (toySha256 bs)

theorem toyPin_pinned (bs : List UInt8) : (toyPin bs).Pinned toySha256 :=
  ⟨Or.inl rfl, fun _ h => Option.some.inj h, fun _ h => Option.some.inj h⟩

def toyFinalCfg : _root_.MultiStark.Final.Configuration where
  policyDigest := toyPolicyWords
  anchors := toyAnchorsBytes.map (·.toNat)
  anchorCoordinates := []
  minStage := 2
  maxStage := 2

def toyFinalHeaders : List NarrowClaimHeader := [⟨0, 0, 21⟩]

theorem toyFinalCfg_validated : validateFinalNarrowConfig toyFinalCfg toyFinalHeaders = .ok () := by
  have h1 : (toyFinalCfg.policyDigest.length == 8 && toyFinalCfg.policyDigest.all (· < 2 ^ 32)) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
    exact toyPolicyWords_canon
  have h2 : (toyFinalCfg.anchors.length == 128 && toyFinalCfg.anchors.all (· < 256)) = true := by
    simp [toyFinalCfg, toyAnchorsBytes]
  have h3 : (decide (2 ≤ toyFinalCfg.minStage) && (toyFinalCfg.minStage == toyFinalCfg.maxStage) &&
      decide (toyFinalCfg.maxStage < 2 ^ 32)) = true := by
    change (decide (2 ≤ 2) && (2 == 2) && decide (2 < 2 ^ 32)) = true
    decide
  have h4 : (toyFinalHeaders.length != 0 && toyFinalHeaders.all (fun h =>
      h.tag < MultiStark.BN.modulus && h.key < MultiStark.BN.modulus && h.values != 0)) = true := by
    decide
  have h5 : ((toyFinalHeaders.map (·.values)).sum == 21) = true := by decide
  unfold validateFinalNarrowConfig
  simp only [h1, h2, h3, h4, h5, ↓reduceIte, pure, Except.pure]

def toyManifest (scsBytes : List UInt8) : StageManifest where
  format := stagesManifestFormat
  manifestBytes := [0x10]
  manifestCallerPin := Blake3.Pure.digest [0x10]
  rootKeyPin := toyRootKeyPin
  wrapPkg := toyPin [0x11]
  wrapLayout := toyPin [0x12]
  wrapKeyDigest := toyWrapKeyDigest
  wrapLayoutKeyPin := toyWrapKeyDigest
  glPkg := toyPin [0x13]
  glKey := toyPin toyGlKeyBytes
  narrowPkg := toyPin [0x14]
  narrowPolicyFile := toyPin toyPolicy.encode
  narrowKey := toyPin toyNarrowKeyBytes
  terminalPkg := toyPin [0x15]
  terminalScs := toyPin scsBytes
  preparedManifest := toyPin [0x16]
  outerVk := toyPin [0x17]
  policy := toyPolicy
  glKeyAnchors := toyAnchorsBytes
  narrowKeyAnchors := toyAnchorsBytes
  finalPolicyDigestWords := toyPolicyWords
  finalAnchors := toyAnchorsBytes
  outerPairingAnchors := toyAnchorsBytes

theorem toyManifest_pinned (scsBytes : List UInt8) :
    ManifestPinned toySha256 (toyManifest scsBytes) where
  format_ok := by simp only [toyManifest]
  caller_pin_ok := by simp only [toyManifest]
  wrapPkg_ok := toyPin_pinned [0x11]
  wrapLayout_ok := toyPin_pinned [0x12]
  wrapKey_matches_layout := by simp only [toyManifest]
  glPkg_ok := toyPin_pinned [0x13]
  glKey_ok := toyPin_pinned toyGlKeyBytes
  narrowPkg_ok := toyPin_pinned [0x14]
  narrowPolicy_ok := toyPin_pinned toyPolicy.encode
  narrowKey_ok := toyPin_pinned toyNarrowKeyBytes
  terminalPkg_ok := toyPin_pinned [0x15]
  terminalScs_ok := toyPin_pinned scsBytes
  preparedManifest_ok := toyPin_pinned [0x16]
  outerVk_ok := toyPin_pinned [0x17]
  policy_wf := toyPolicy_wf
  policy_file_matches := by simp only [toyManifest, toyPin]
  policy_binds_glKey := by simp only [toyManifest, toyPolicy, toyPin]
  policy_binds_narrowKey := by simp only [toyManifest, toyPolicy, toyPin]
  final_binds_policy := by simp only [toyManifest, toyPolicyWords]
  gl_anchors_match := by simp only [toyManifest, toyPolicy]
  narrow_anchors_match := by simp only [toyManifest, toyPolicy]
  final_anchors_match := by simp only [toyManifest, toyPolicy]
  outer_anchors_match := by simp only [toyManifest, toyPolicy]

-- Concrete toy `ix_aggr` semantics and zero-child leaf tree
def toyResidualMonoid : _root_.Aggr.ResidualMonoid K where
  zero := 0
  add := (· + ·)
  add_zero := add_zero
  zero_add := zero_add
  add_assoc := add_assoc

def toySem : _root_.Aggr.AggrSemantics Address Address Ix.DynamicLink.EvalAssumption Address K
    Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry where
  Checked := fun _ _ _ _ _ => True
  Dep := fun _ _ => False
  BindingValid := fun _ => True
  LiteralClassOf := fun _ _ => True
  EvalValid := fun _ _ _ => True
  DynamicLinkValid := fun _ => True
  LinkedRecords := fun _ _ _ _ => True
  residualMonoid := toyResidualMonoid
  shardCount := fun _ => 0
  shardResidual := fun _ _ => 0
  messagesAcc := fun _ => 0
  checked_mono_ax := fun _ _ => trivial
  checked_discharge_eval := fun _ _ _ => trivial
  checked_discharge_eval_via_link := fun _ _ _ _ _ => trivial
  evalValid_mono_ax := fun _ _ => trivial
  checked_to_class := fun _ _ => trivial
  batch_balance_sound := fun _ _ _ _ _ _ _ _ _ => ⟨fun _ _ _ => trivial, fun _ _ _ h => False.elim h⟩

def toyBatchClaim : Nat → _root_.Aggr.ValidatorMode Address → (Address → Prop) → (Address → Prop) →
    (Address → Prop) → (Ix.DynamicLink.EvalAssumption → Prop) → Prop :=
  fun _ _ _ _ _ _ => True

def toyRootStmt : _root_.Aggr.AggrNodeStmt Address Address Ix.DynamicLink.EvalAssumption Address K
    Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry :=
  .rangeStmt 0 0 0 (_root_.Aggr.rangeSum toySem.residualMonoid (toySem.shardResidual 0) 0 0)

def toyAggrTree : AcceptedAggrTree toySem toyBatchClaim toyRootStmt :=
  .rangeLeaf [] (le_refl 0) rfl

def toyClaimsBindStmt (bs : List UInt8)
    (s : _root_.Aggr.AggrNodeStmt Address Address Ix.DynamicLink.EvalAssumption Address K
      Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry) : Prop :=
  bs = toyRootClaimsBytes ∧ s = toyRootStmt

/-! ## 3. Shared `EvalFn` Inversion Lemmas -/

section EvalInversion

variable {F : Type} [Field F] [DecidableEq F]

private theorem evalExit_literal_false {world : Generic.SourceSemantics.World F}
    {types locals heap target result after} {c : F}
    (h : Generic.SourceSemantics.EvalExit world types locals (.literal c) heap target result after) :
    False := by
  cases h

private theorem evalExit_var_false {world : Generic.SourceSemantics.World F}
    {types locals heap target result after} {x : String}
    (h : Generic.SourceSemantics.EvalExit world types locals (.var x) heap target result after) :
    False := by
  cases h

private theorem evalArgsExit_literals_false {world : Generic.SourceSemantics.World F}
    {types locals target result} :
    ∀ {cs : List F} {before after},
      Generic.SourceSemantics.EvalArgsExit world types locals (cs.map .literal) before target result after →
      False
  | [], _, _, h => by cases h
  | _ :: cs, _, _, h => by
    cases h with
    | head hx => exact evalExit_literal_false hx
    | tail _ hrest => exact evalArgsExit_literals_false hrest

private theorem evalExit_tuple_literals_false {world : Generic.SourceSemantics.World F}
    {types locals heap target result after} {cs : List F}
    (h : Generic.SourceSemantics.EvalExit world types locals (.tuple (cs.map .literal)) heap target result after) :
    False := by
  cases h with
  | fromTuple hargs => exact evalArgsExit_literals_false hargs

private theorem evalArgs_literals {world : Generic.SourceSemantics.World F}
    {types locals} :
    ∀ {cs : List F} {before vs after},
      Generic.SourceSemantics.EvalArgs world types locals (cs.map .literal) before vs after →
      vs = cs.map Aiur.Value.field ∧ after = before
  | [], _, _, _, h => by cases h; exact ⟨rfl, rfl⟩
  | c :: cs, _, _, _, h => by
    cases h with
    | cons h1 h2 =>
      cases h1
      obtain ⟨hvs, ha⟩ := evalArgs_literals h2
      exact ⟨congrArg (Aiur.Value.field c :: ·) hvs, ha⟩

private theorem evalExpr_tuple_literals {world : Generic.SourceSemantics.World F}
    {types locals before result after} {cs : List F}
    (h : Generic.SourceSemantics.EvalExpr world types locals (.tuple (cs.map .literal)) before result after) :
    result = .tuple (cs.map Aiur.Value.field) ∧ after = before := by
  cases h with
  | tuple hargs =>
    obtain ⟨hvs, ha⟩ := evalArgs_literals hargs
    exact ⟨congrArg Aiur.Value.tuple hvs, ha⟩

private theorem evalExit_assertEq_var_literal_false {world : Generic.SourceSemantics.World F}
    {types locals heap target result after} {x : String} {c : F}
    (h : Generic.SourceSemantics.EvalExit world types locals
      (.builtin (.assertEq {}) [.var x, .literal c]) heap target result after) : False := by
  cases h with
  | fromBuiltin ha =>
    cases ha with
    | head hx => exact evalExit_var_false hx
    | tail _ ha2 =>
      cases ha2 with
      | head hc => exact evalExit_literal_false hc
      | tail _ ha3 => cases ha3

private theorem evalExit_assertEq_var_tuple_false {world : Generic.SourceSemantics.World F}
    {types locals heap target result after} {x : String} {cs : List F}
    (h : Generic.SourceSemantics.EvalExit world types locals
      (.builtin (.assertEq {}) [.var x, .tuple (cs.map .literal)]) heap target result after) : False := by
  cases h with
  | fromBuiltin ha =>
    cases ha with
    | head hx => exact evalExit_var_false hx
    | tail _ ha2 =>
      cases ha2 with
      | head hc => exact evalExit_tuple_literals_false hc
      | tail _ ha3 => cases ha3

private theorem evalExpr_assertEq_var_literal {world : Generic.SourceSemantics.World F}
    {types locals before result after} {x : String} {c : F}
    (h : Generic.SourceSemantics.EvalExpr world types locals
      (.builtin (.assertEq {}) [.var x, .literal c]) before result after) :
    locals.find? (·.1 == x) = some (x, .field c) ∧ result = .tuple [] ∧ after = before := by
  cases h with
  | builtin ha happ =>
    cases ha with
    | cons h1 ha2 =>
      cases h1 with
      | var hlook =>
        cases ha2 with
        | cons h2 ha3 =>
          cases h2
          cases ha3
          simp only [Generic.Builtin.apply, evalAssertEq_ok] at happ
          obtain ⟨_, heq, rfl⟩ := happ
          rw [heq] at hlook
          exact ⟨hlook, rfl, rfl⟩

private theorem evalExpr_assertEq_var_tuple {world : Generic.SourceSemantics.World F}
    {types locals before result after} {x : String} {cs : List F}
    (h : Generic.SourceSemantics.EvalExpr world types locals
      (.builtin (.assertEq {}) [.var x, .tuple (cs.map .literal)]) before result after) :
    locals.find? (·.1 == x) = some (x, .tuple (cs.map Aiur.Value.field)) ∧
    result = .tuple [] ∧ after = before := by
  cases h with
  | builtin ha happ =>
    cases ha with
    | cons h1 ha2 =>
      cases h1 with
      | var hlook =>
        cases ha2 with
        | cons h2 ha3 =>
          obtain ⟨hv, rfl⟩ := evalExpr_tuple_literals h2
          cases ha3
          simp only [Generic.Builtin.apply, evalAssertEq_ok] at happ
          obtain ⟨_, heq, rfl⟩ := happ
          rw [heq, hv] at hlook
          exact ⟨hlook, rfl, rfl⟩

private theorem evalExit_letAssertEq_var_literal {world : Generic.SourceSemantics.World F}
    {types locals body heap target result after} {x : String} {c : F}
    (h : Generic.SourceSemantics.EvalExit world types locals
      (.letValue .wildcard (.builtin (.assertEq {}) [.var x, .literal c]) body)
      heap target result after) :
    Generic.SourceSemantics.EvalExit world types locals body heap target result after := by
  cases h with
  | fromLetValue hbad => exact False.elim (evalExit_assertEq_var_literal_false hbad)
  | letBody hv hm hbody =>
    obtain ⟨_, rfl, rfl⟩ := evalExpr_assertEq_var_literal hv
    simp [Generic.SourceSemantics.World.matchPattern, Generic.SourceSemantics.matchPatternWith] at hm
    subst hm
    simpa using hbody

private theorem evalExit_letAssertEq_var_tuple {world : Generic.SourceSemantics.World F}
    {types locals body heap target result after} {x : String} {cs : List F}
    (h : Generic.SourceSemantics.EvalExit world types locals
      (.letValue .wildcard (.builtin (.assertEq {}) [.var x, .tuple (cs.map .literal)]) body)
      heap target result after) :
    Generic.SourceSemantics.EvalExit world types locals body heap target result after := by
  cases h with
  | fromLetValue hbad => exact False.elim (evalExit_assertEq_var_tuple_false hbad)
  | letBody hv hm hbody =>
    obtain ⟨_, rfl, rfl⟩ := evalExpr_assertEq_var_tuple hv
    simp [Generic.SourceSemantics.World.matchPattern, Generic.SourceSemantics.matchPatternWith] at hm
    subst hm
    simpa using hbody

private theorem evalExpr_letAssertEq_var_literal {world : Generic.SourceSemantics.World F}
    {types locals body before result after} {x : String} {c : F}
    (h : Generic.SourceSemantics.EvalExpr world types locals
      (.letValue .wildcard (.builtin (.assertEq {}) [.var x, .literal c]) body)
      before result after) :
    locals.find? (·.1 == x) = some (x, .field c) ∧
    Generic.SourceSemantics.EvalExpr world types locals body before result after := by
  cases h with
  | letValue hv hm hbody =>
    obtain ⟨hlook, rfl, rfl⟩ := evalExpr_assertEq_var_literal hv
    simp [Generic.SourceSemantics.World.matchPattern, Generic.SourceSemantics.matchPatternWith] at hm
    subst hm
    exact ⟨hlook, by simpa using hbody⟩

private theorem evalExpr_letAssertEq_var_tuple {world : Generic.SourceSemantics.World F}
    {types locals body before result after} {x : String} {cs : List F}
    (h : Generic.SourceSemantics.EvalExpr world types locals
      (.letValue .wildcard (.builtin (.assertEq {}) [.var x, .tuple (cs.map .literal)]) body)
      before result after) :
    locals.find? (·.1 == x) = some (x, .tuple (cs.map Aiur.Value.field)) ∧
    Generic.SourceSemantics.EvalExpr world types locals body before result after := by
  cases h with
  | letValue hv hm hbody =>
    obtain ⟨hlook, rfl, rfl⟩ := evalExpr_assertEq_var_tuple hv
    simp [Generic.SourceSemantics.World.matchPattern, Generic.SourceSemantics.matchPatternWith] at hm
    subst hm
    exact ⟨hlook, by simpa using hbody⟩

end EvalInversion

/-- Injectivity of `List.map (fun w => Value.field (w : F))` for canonical `u32` word lists
over any `ZMod p` with `2^32 < p`. -/
private theorem u32Words_eq_of_field_tuple_eq {p : Nat} [NeZero p] {A : Type} (hp : 2 ^ 32 < p)
    {xs ys : List Nat} (hxs : ∀ w ∈ xs, w < 2 ^ 32) (hys : ∀ w ∈ ys, w < 2 ^ 32)
    (heq : (xs.map fun w => (Aiur.Value.field (w : ZMod p) : Aiur.Value (ZMod p) A)) =
           (ys.map fun w => (Aiur.Value.field (w : ZMod p) : Aiur.Value (ZMod p) A))) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases heq
  | cons x xs ih =>
    cases ys with
    | nil => cases heq
    | cons y ys =>
      have ⟨hhd, htl⟩ := List.cons.inj heq
      have hhd' : (x : ZMod p) = (y : ZMod p) := Aiur.Value.field.inj hhd
      have hxy : x = y := by
        have hv := congrArg ZMod.val hhd'
        rw [ZMod.val_natCast, ZMod.val_natCast,
          Nat.mod_eq_of_lt (Nat.lt_trans (hxs x List.mem_cons_self) hp),
          Nat.mod_eq_of_lt (Nat.lt_trans (hys y List.mem_cons_self) hp)] at hv
        exact hv
      rw [hxy, ih (fun a ha => hxs a (List.mem_cons_of_mem _ ha))
        (fun b hb => hys b (List.mem_cons_of_mem _ hb)) htl]

/-! ## 4. Polymorphic Symbolic Single-Function Compiler Pipeline

Directly constructs `Generic.Source`, `Generic.Specialized`, `GenericArtifact` (via
`minimalConfig` and `parMapM_eq_mapM`), `Physical.Prepared`, `Physical.Prepared.DepthCertified`,
`Grouping.Plan`, and `Plan.WellFormedActivation` symbolically for any single-function
`assert_eq!`-on-flat-inputs program over any field `F`, with zero `decide` calls on `WellFounded.fix`,
`Task.spawn`, or `Blake3.Pure.digest`. -/

/-- A flat parameter value: either a single `Field` or a fixed-width `[Field; k]` tuple. -/
inductive FlatVal (F : Type) where
  | scalar (c : F)
  | arr (cs : List F)

namespace FlatVal

def words {F : Type} : FlatVal F → List F
  | .scalar c => [c]
  | .arr cs => cs

def width {F : Type} : FlatVal F → Nat
  | .scalar _ => 1
  | .arr cs => cs.length

def genericTy {F : Type} : FlatVal F → Generic.Ty
  | .scalar _ => .field
  | .arr cs => .tuple (List.replicate cs.length .field)

def coreTy {F : Type} : FlatVal F → Aiur.Ty
  | .scalar _ => .field
  | .arr cs => .tuple (List.replicate cs.length .field)

def genericExpr {F : Type} : FlatVal F → Generic.Expr F
  | .scalar c => .literal c
  | .arr cs => .tuple (cs.map .literal)

def coreExpr {F : Type} : FlatVal F → Aiur.Expr F
  | .scalar c => .literal c
  | .arr cs => .tuple (cs.map .literal)

def treeExpr {F : Type} : FlatVal F → Inlining.Tree F
  | .scalar c => .literal c
  | .arr cs => .tuple (cs.map .literal)

def wireVal {F : Type} (v : FlatVal F) : Aiur.WireValue F :=
  ⟨v.coreTy, v.words⟩

def sourceVal {F : Type} : FlatVal F → Aiur.SourceValue F
  | .scalar c => .field c
  | .arr cs => .tuple (cs.map .field)

def entryVal {F : Type} : FlatVal F → Aiur.Value F
  | .scalar c => .field c
  | .arr cs => .tuple (cs.map .field)

theorem words_length {F : Type} (v : FlatVal F) : v.words.length = v.width := by
  cases v <;> rfl

theorem genericTy_toCore {F : Type} (v : FlatVal F) : v.genericTy.toCore = v.coreTy := by
  cases v with
  | scalar _ => simp [genericTy, coreTy, Generic.Ty.toCore]
  | arr cs =>
    simp only [genericTy, coreTy, Generic.Ty.toCore]
    congr 1
    induction cs with
    | nil => rfl
    | cons _ _ ih => simp [List.replicate_succ, Generic.Ty.toCore, ih]

theorem genericTy_subst_nil {F : Type} (v : FlatVal F) : v.genericTy.subst [] = v.genericTy := by
  cases v with
  | scalar _ => simp [genericTy]
  | arr cs =>
    simp only [genericTy, Generic.Ty.subst]
    congr 1
    induction cs with
    | nil => rfl
    | cons _ _ ih => simp [List.replicate_succ, ih]

theorem coreTy_checkNames {F : Type} (v : FlatVal F) : v.coreTy.checkNames [] = .ok () := by
  cases v with
  | scalar _ => simp [coreTy, Aiur.Ty.checkNames]
  | arr cs =>
    simp only [coreTy, Aiur.Ty.checkNames]
    have hf : Aiur.Ty.checkNames [] .field = .ok () := by rw [Aiur.Ty.checkNames]
    have hfor : ∀ n, (forIn (m := Except Aiur.DeclError) (List.replicate n Aiur.Ty.field) PUnit.unit
        fun item _ => do let _ ← item.checkNames []; pure (.yield PUnit.unit)) = .ok PUnit.unit := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [List.replicate_succ, List.forIn_cons]
        simp only [hf, bind, Except.bind, pure, Except.pure]
        exact ih
    rw [hfor cs.length]
    rfl

theorem coreTy_layout {F : Type} (v : FlatVal F) :
    Aiur.Declarations.layout [] v.coreTy =
      Except.ok (match v with | .scalar _ => .field | .arr cs => .tuple (List.replicate cs.length .field)) := by
  cases v with
  | scalar _ =>
    simp [Aiur.Declarations.layout, coreTy, Aiur.Ty.checkNames, Aiur.Declarations.expand,
      Aiur.Ty.layoutWith, bind, Except.bind, pure, Except.pure]
  | arr cs =>
    have hlay : ∀ (res : String → Except Aiur.DeclError Aiur.Layout),
        Aiur.Ty.layoutWith res (.tuple (List.replicate cs.length .field)) =
          Except.ok (.tuple (List.replicate cs.length .field)) := by
      intro res
      rw [Aiur.Ty.layoutWith]
      have hf : Aiur.Ty.layoutWith res Aiur.Ty.field = .ok Aiur.Layout.field := by
        rw [Aiur.Ty.layoutWith]
      have hmap : ∀ n, (List.replicate n Aiur.Ty.field).mapM (Aiur.Ty.layoutWith res) =
          Except.ok (List.replicate n Aiur.Layout.field) := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih =>
          simp [List.replicate_succ, List.mapM_cons, hf, ih, bind, Except.bind, pure, Except.pure]
      simp [hmap, bind, Except.bind, pure, Except.pure]
    have hcheck : (Aiur.Ty.tuple (List.replicate cs.length .field)).checkNames [] = .ok () :=
      coreTy_checkNames (.arr cs)
    simp [Aiur.Declarations.layout, coreTy, hcheck, Aiur.Declarations.expand, hlay,
      bind, Except.bind, pure, Except.pure]

theorem coreTy_pointerFree {F : Type} (v : FlatVal F) : v.coreTy.pointerFree [] = true := by
  cases v with
  | scalar _ =>
    rw [Aiur.Ty.pointerFree, coreTy_layout]
    simp [Aiur.Layout.pointerFree]
  | arr cs =>
    rw [Aiur.Ty.pointerFree, coreTy_layout]
    dsimp only
    rw [Aiur.Layout.pointerFree]
    have hf : Aiur.Layout.field.pointerFree = true := by rw [Aiur.Layout.pointerFree]
    induction cs with
    | nil => rfl
    | cons _ _ ih => simp [List.replicate_succ, hf]

theorem coreTy_known {F : Type} (v : FlatVal F) : Aiur.Generic.knownType [] v.coreTy = true := by
  cases v with
  | scalar _ => simp [coreTy, Aiur.Generic.knownType]
  | arr cs =>
    simp only [coreTy, Aiur.Generic.knownType]
    have hf : Aiur.Generic.knownType [] Aiur.Ty.field = true := by rw [Aiur.Generic.knownType]
    induction cs with
    | nil => rfl
    | cons _ _ ih => simp [List.replicate_succ, hf]

theorem layout_width_replicate_field (n : Nat) :
    (Aiur.Layout.tuple (List.replicate n .field)).width = n := by
  induction n with
  | zero => simp [Aiur.Layout.width]
  | succ n ih =>
    simp [Aiur.Layout.width, List.replicate_succ] at ih ⊢
    omega

theorem coreTy_layout_width {F : Type} (v : FlatVal F) :
    ((Aiur.Declarations.layout [] v.coreTy).toOption.map Aiur.Layout.width) = some v.width := by
  cases v with
  | scalar _ =>
    rw [coreTy_layout]
    simp [Except.toOption, width, Aiur.Layout.width]
  | arr cs =>
    rw [coreTy_layout]
    simp [Except.toOption, width, layout_width_replicate_field]

theorem wireVal_decode {F : Type} [NatCast F] [Zero F] [DecidableEq F] (v : FlatVal F) :
    v.wireVal.decode [] = some v.entryVal := by
  cases v with
  | scalar c => exact Aiur.WireValue.decode_field [] c
  | arr cs =>
    have hdec : (Aiur.Layout.tuple (List.replicate cs.length .field)).decode cs =
        some (.tuple (cs.map .field)) := by
      simp only [Aiur.Layout.decode]
      have hlist : ∀ l : List F,
          Aiur.Layout.decodeList (List.replicate l.length .field) l = some (l.map .field) := by
        intro l
        induction l with
        | nil => simp [Aiur.Layout.decodeList]
        | cons x xs ih =>
          simp [List.replicate_succ, Aiur.Layout.decodeList, Aiur.Layout.decode, Aiur.Layout.width,
            ih, bind, Option.bind, pure]
      simp [hlist cs, bind, Option.bind, pure]
    have hwf : (Aiur.Value.tuple (Address := F) (cs.map Aiur.Value.field)).wellFormed [] = true := by
      simp only [Aiur.Value.wellFormed, List.map_map, Function.comp_def]
      induction cs with
      | nil => rfl
      | cons _ _ ih => simp []
    have hty : (Aiur.Value.tuple (Address := F) (cs.map Aiur.Value.field)).type =
        .tuple (List.replicate cs.length .field) := by
      simp only [Aiur.Value.type, List.map_map, Function.comp_def]
      congr 1
      induction cs with
      | nil => rfl
      | cons _ _ ih => simp [List.replicate_succ]
    have hlay : Aiur.Declarations.layout [] (.tuple (List.replicate cs.length .field)) =
        .ok (.tuple (List.replicate cs.length .field)) := coreTy_layout (.arr cs)
    simp [Aiur.WireValue.decode, wireVal, coreTy, words, entryVal, hlay, Except.toOption,
      hdec, Aiur.Value.hasType, hty, hwf, bind, Option.bind]

theorem mapAddress_sourceVal {F : Type} [Zero F] (v : FlatVal F) :
    Aiur.Value.mapAddress (fun _ => (0 : F)) v.sourceVal = v.entryVal := by
  cases v with
  | scalar _ => simp [sourceVal, entryVal, Aiur.Value.mapAddress]
  | arr cs =>
    simp [sourceVal, entryVal, Aiur.Value.mapAddress, List.map_map, Function.comp_def]

end FlatVal

/-- Specification of a single-function `assert_eq!`-on-flat-inputs program over field `F`. -/
structure FlatAssertSpec (F : Type) where
  fnName : String
  params : List (String × FlatVal F)
  outConsts : List F

namespace FlatAssertSpec

variable {F : Type} [Field F] [DecidableEq F]

def inConsts (s : FlatAssertSpec F) : List F :=
  s.params.flatMap fun p => p.2.words

def allConsts (s : FlatAssertSpec F) : List F :=
  s.inConsts ++ s.outConsts

def numVars (s : FlatAssertSpec F) : Nat :=
  s.allConsts.length

def resultGenericTy (s : FlatAssertSpec F) : Generic.Ty :=
  .tuple (List.replicate s.outConsts.length .field)

def resultCoreTy (s : FlatAssertSpec F) : Aiur.Ty :=
  .tuple (List.replicate s.outConsts.length .field)

def mkGenericBody (outConsts : List F) : List (String × FlatVal F) → Generic.Expr F
  | [] => .tuple (outConsts.map .literal)
  | (name, val) :: rest =>
    .letValue .wildcard (.builtin (.assertEq {}) [.var name, val.genericExpr])
      (mkGenericBody outConsts rest)

def mkCoreAssert (name : String) (val : FlatVal F) : Aiur.Expr F :=
  .letValue (.tuple [.bind "$assertLeft", .bind "$assertRight"])
    (.tuple [.var name, val.coreExpr])
    (.assertEq {} (.var "$assertLeft") (.var "$assertRight"))

def mkTreeAssert (name : String) (val : FlatVal F) : Inlining.Tree F :=
  .letValue (.tuple [.bind "$assertLeft", .bind "$assertRight"])
    (.tuple [.var name, val.treeExpr])
    (.assertEq {} (.var "$assertLeft") (.var "$assertRight"))

def mkCoreBody (outConsts : List F) : List (String × FlatVal F) → Aiur.Expr F
  | [] => .tuple (outConsts.map .literal)
  | (name, val) :: rest =>
    .letValue .wildcard (mkCoreAssert name val)
      (mkCoreBody outConsts rest)

def mkTreeBody (outConsts : List F) : List (String × FlatVal F) → Inlining.Tree F
  | [] => .tuple (outConsts.map .literal)
  | (name, val) :: rest =>
    .letValue .wildcard (mkTreeAssert name val)
      (mkTreeBody outConsts rest)

def genericFn (s : FlatAssertSpec F) : Generic.Function F where
  name := s.fnName
  params := s.params.map fun (n, v) => (n, v.genericTy)
  result := s.resultGenericTy
  body := mkGenericBody s.outConsts s.params

def genericProgram (s : FlatAssertSpec F) : Generic.Program F where
  functions := [s.genericFn]

def coreFn (s : FlatAssertSpec F) : Aiur.Function F where
  name := s.fnName
  params := s.params.map fun (n, v) => (n, v.coreTy)
  result := s.resultCoreTy
  body := mkCoreBody s.outConsts s.params

def coreProgram (s : FlatAssertSpec F) : Aiur.Program F where
  functions := [s.coreFn]

def source (s : FlatAssertSpec F) : Generic.Source F where
  program := s.genericProgram
  tables := { functions := [] }
  tablesChecked := by
    simp [Aiur.typecheck, Aiur.checkDeclarations, Aiur.duplicateName, Aiur.findDuplicate,
      Aiur.checkTables, Except.mapError, bind, Except.bind, pure, Except.pure]

def mkInputWires : Nat → List (String × FlatVal F) → List (Aiur.WireValue Witness)
  | _, [] => []
  | off, (_, v) :: rest =>
    ⟨v.coreTy, List.range' off v.width⟩ :: mkInputWires (off + v.width) rest

def inputWireVars (s : FlatAssertSpec F) : List (Aiur.WireValue Witness) :=
  mkInputWires 0 s.params

def outputWireVars (s : FlatAssertSpec F) : Aiur.WireValue Witness :=
  ⟨s.resultCoreTy, List.range' s.inConsts.length s.outConsts.length⟩

def trivialEqs (outOff outLen count : Nat) : List (Equation F) :=
  (List.replicate count ((List.range' outOff outLen).map fun i =>
    (⟨0, .sub (.var i) (.var i)⟩ : Equation F))).flatten

def zeroEqs (count : Nat) : List (Equation F) :=
  List.replicate count (⟨0, .const 0⟩ : Equation F)

def scopedChipRaw (s : FlatAssertSpec F) : ScopedChip F where
  name := s.fnName
  inputs := s.inputWireVars
  output := s.outputWireVars
  roles := (List.replicate s.inConsts.length Optimized.Role.input ++
    List.replicate s.outConsts.length Optimized.Role.output).toArray
  aliases := Array.replicate s.numVars none
  scopes := #[⟨.const 1, []⟩]
  equations := ((s.allConsts.zipIdx.map fun (c, i) => (⟨0, .sub (.var i) (.const c)⟩ : Equation F)) ++
    trivialEqs s.inConsts.length s.outConsts.length s.params.length).toArray
  calls := #[]
  cells := #[]
  choices := #[]

def scopedChipAfterAlias (s : FlatAssertSpec F) : ScopedChip F :=
  { s.scopedChipRaw with
    equations := ((s.allConsts.zipIdx.map fun (c, i) => (⟨0, subConstPoly i c⟩ : Equation F)) ++
      zeroEqs (s.params.length * s.outConsts.length)).toArray }

def scopedChipNorm (s : FlatAssertSpec F) : ScopedChip F :=
  { s.scopedChipRaw with
    equations := (s.allConsts.zipIdx.map fun (c, i) => (⟨0, subConstPoly i c⟩ : Equation F)).toArray }

def colLayout (s : FlatAssertSpec F) : ColumnLayout where
  columnOf := (List.range s.numVars).toArray.map some
  occupants := (List.range s.numVars).toArray.map fun i => [i]

def physChip (s : FlatAssertSpec F) : Circuit.Chip F where
  name := s.fnName
  inputs := s.inputWireVars
  output := ⟨s.resultCoreTy, (List.range' s.inConsts.length s.outConsts.length).map Aiur.Optimized.Polynomial.var⟩
  numVars := s.numVars
  constraints := s.allConsts.zipIdx.map fun (c, i) => subConstPoly i c
  sends := []
  memory := []

def erasedChip (s : FlatAssertSpec F) : Circuit.Chip F :=
  Erasure.chip ⟨[s.physChip], [], [], []⟩ s.physChip

def wires (s : FlatAssertSpec F) : List (Aiur.WireValue F) :=
  s.params.map fun p => p.2.wireVal

def outputWire (s : FlatAssertSpec F) : Aiur.WireValue F :=
  ⟨s.resultCoreTy, s.outConsts⟩

def args (s : FlatAssertSpec F) : List (Aiur.SourceValue F) :=
  s.params.map fun p => p.2.sourceVal

def resultVal (s : FlatAssertSpec F) : Aiur.Value F :=
  .tuple (s.outConsts.map .field)

def typedRootMsg (s : FlatAssertSpec F) : Circuit.Message F :=
  ⟨s.fnName, s.wires, s.outputWire⟩

def erasedRootMsg (s : FlatAssertSpec F) : Circuit.Message F :=
  Erasure.message ⟨[s.physChip], [], [], []⟩ s.typedRootMsg

/-! ### Symbolic helper proofs for `FlatAssertSpec` -/

omit [Field F] [DecidableEq F] in
private theorem mkInputWires_flatMap (off : Nat) (ps : List (String × FlatVal F)) :
    (mkInputWires off ps).flatMap WireValue.words =
      List.range' off (ps.flatMap fun p => p.2.words).length := by
  induction ps generalizing off with
  | nil => rfl
  | cons p rest ih =>
    simp only [mkInputWires, List.flatMap_cons, List.length_append, FlatVal.words_length]
    rw [ih, ← Nat.one_mul p.2.width, ← List.range'_append]
    simp

omit [Field F] [DecidableEq F] in
private theorem mkInputWires_types (off : Nat) (ps : List (String × FlatVal F)) :
    (mkInputWires off ps).map WireValue.type = ps.map fun p => p.2.coreTy := by
  induction ps generalizing off with
  | nil => rfl
  | cons p rest ih => simp [mkInputWires, ih]

omit [Field F] [DecidableEq F] in
private theorem mkInputWires_shapes (off : Nat) (ps : List (String × FlatVal F)) :
    (mkInputWires off ps).map Erasure.shape = ps.map fun p => (p.2.coreTy, p.2.width) := by
  induction ps generalizing off with
  | nil => rfl
  | cons p rest ih => simp [mkInputWires, Erasure.shape, ih]

theorem physChip_wellFormed (s : FlatAssertSpec F) : s.physChip.wellFormed = true := by
  have hlen : s.inConsts.length + s.outConsts.length = s.numVars := by
    simp [numVars, allConsts]
  simp only [Circuit.Chip.wellFormed, physChip, Bool.and_eq_true, List.all_eq_true,
    List.not_mem_nil, false_implies, implies_true, and_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x hx
    rw [inputWireVars, mkInputWires_flatMap, List.mem_range'] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    simp only [inConsts] at hlen
    have hlt : 0 + 1 * k < s.numVars := by omega
    exact decide_eq_true_eq.mpr hlt
  · intro e he
    simp only [List.mem_map, List.mem_range'] at he
    obtain ⟨w, ⟨k, hk, rfl⟩, rfl⟩ := he
    simp only [Scalar.Circuit.ArithExpr.inBounds]
    have hlt : s.inConsts.length + 1 * k < s.numVars := by omega
    exact decide_eq_true_eq.mpr hlt
  · intro e he
    simp only [List.mem_map] at he
    obtain ⟨⟨c, i⟩, hi, rfl⟩ := he
    have hlt : i < s.allConsts.length := by
      have := List.mem_zipIdx hi
      omega
    rw [subConstPoly_inBounds]
    exact decide_eq_true_eq.mpr hlt

theorem erasedChip_wellFormed (s : FlatAssertSpec F) : s.erasedChip.wellFormed = true := by
  have hwf := s.physChip_wellFormed
  simp only [Circuit.Chip.wellFormed, erasedChip, Erasure.chip, Erasure.pack, physChip,
    Bool.and_eq_true, List.all_eq_true, List.flatMap_singleton,
    List.map_nil, List.not_mem_nil, false_implies, implies_true, and_true] at hwf ⊢
  exact hwf

theorem activated_erasedChip_wellFormed (s : FlatAssertSpec F) :
    (Activation.compile s.erasedChip).wellFormed = true := by
  have hwf := s.erasedChip_wellFormed
  simp only [Circuit.Chip.wellFormed, Activation.compile, Activation.guards, erasedChip,
    Erasure.chip, Erasure.pack, physChip, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, List.flatMap_singleton, List.map_nil, List.append_nil, List.dedup_nil,
    List.not_mem_nil, false_implies, implies_true, and_true] at hwf ⊢
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x hx
    exact Nat.lt_succ_of_lt (hwf.1.1 x hx)
  · intro e he
    exact Scalar.Circuit.ArithExpr.inBounds_mono (Nat.le_succ _) (hwf.1.2 e he)
  · intro e he
    rcases List.mem_cons.mp he with rfl | hmem
    · simp [Activation.boolean, Scalar.Circuit.ArithExpr.inBounds]
    · simp only [List.mem_map] at hmem
      obtain ⟨_, ⟨⟨c, i⟩, hi, rfl⟩, rfl⟩ := hmem
      have hlt : i < s.numVars := by
        have := List.mem_zipIdx hi
        simp only [numVars]
        omega
      exact activation_subConstPoly_inBounds hlt c

omit [Field F] [DecidableEq F] in
private theorem prep_expr_literals (p : Generic.Program F) (d : Nat) (cs : List F) :
    Generic.Preparation.expression p d [] (.tuple (cs.map .literal)) =
      .ok (.tuple (cs.map .literal)) := by
  rw [Generic.Preparation.expression]
  have hmap : (cs.map Generic.Expr.literal).mapM (Generic.Preparation.expression p d []) =
      .ok (cs.map Generic.Expr.literal) := by
    induction cs with
    | nil => rfl
    | cons c rest ih =>
      simp [List.mapM_cons, Generic.Preparation.expression, ih, bind, Except.bind, pure, Except.pure]
  simp [hmap, bind, Except.bind, pure, Except.pure]

omit [Field F] [DecidableEq F] in
private theorem prep_expr_flatVal (p : Generic.Program F) (d : Nat) (v : FlatVal F) :
    Generic.Preparation.expression p d [] v.genericExpr = .ok v.genericExpr := by
  cases v with
  | scalar c => rw [FlatVal.genericExpr, Generic.Preparation.expression]; rfl
  | arr cs => exact prep_expr_literals p d cs

omit [Field F] [DecidableEq F] in
private theorem prep_expr_mkGenericBody (p : Generic.Program F) (d : Nat)
    (outConsts : List F) (ps : List (String × FlatVal F)) :
    Generic.Preparation.expression p d [] (mkGenericBody outConsts ps) =
      .ok (mkGenericBody outConsts ps) := by
  induction ps with
  | nil => exact prep_expr_literals p d outConsts
  | cons hd rest ih =>
    rcases hd with ⟨name, val⟩
    rw [mkGenericBody, Generic.Preparation.expression]
    have hpat : Generic.Preparation.pattern p (p.consts.length + 1) [] (.wildcard : Generic.Pattern F) =
        .ok .wildcard := by
      rw [Generic.Preparation.pattern]; rfl
    have hvar : Generic.Preparation.expression p d [] (.var name : Generic.Expr F) = .ok (.var name) := by
      rw [Generic.Preparation.expression]; rfl
    have hass : Generic.Preparation.expression p d []
        (.builtin (.assertEq {}) [.var name, val.genericExpr]) =
        .ok (.builtin (.assertEq {}) [.var name, val.genericExpr]) := by
      rw [Generic.Preparation.expression]
      simp [List.mapM_cons, List.mapM_nil, hvar, prep_expr_flatVal p d val, Generic.Builtin.subst,
        bind, Except.bind, pure, Except.pure]
    simp [hpat, hass, ih, bind, Except.bind, pure, Except.pure]

omit [Field F] [DecidableEq F] in
private theorem hasControl_literals (cs : List F) :
    Generic.ControlLower.hasControl (.tuple (cs.map .literal)) = false := by
  rw [Generic.ControlLower.hasControl]
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.map_cons, List.any_cons, Bool.or_eq_false_iff, id_eq]
    exact ⟨by rw [Generic.ControlLower.hasControl], ih⟩

omit [Field F] [DecidableEq F] in
private theorem hasControl_mkGenericBody (outConsts : List F) (ps : List (String × FlatVal F)) :
    Generic.ControlLower.hasControl (mkGenericBody outConsts ps) = false := by
  induction ps with
  | nil => exact hasControl_literals outConsts
  | cons hd rest ih =>
    rcases hd with ⟨name, val⟩
    rw [mkGenericBody, Generic.ControlLower.hasControl]
    have hv : Generic.ControlLower.hasControl val.genericExpr = false := by
      cases val with
      | scalar _ => rw [FlatVal.genericExpr, Generic.ControlLower.hasControl]
      | arr cs => exact hasControl_literals cs
    have hass : Generic.ControlLower.hasControl
        (.builtin (.assertEq {}) [.var name, val.genericExpr]) = false := by
      rw [Generic.ControlLower.hasControl]
      simp [Generic.ControlLower.hasControl, hv]
    simp [hass, ih]

omit [Field F] [DecidableEq F] in
private theorem lowerSafe_literals (cs : List F) :
    (Generic.Expr.tuple (cs.map .literal)).lowerSafe [] := by
  rw [Generic.Expr.lowerSafe]
  intro x hx
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
  rw [Generic.Expr.lowerSafe]; trivial

omit [Field F] [DecidableEq F] in
private theorem lowerSafe_mkGenericBody (outConsts : List F) (ps : List (String × FlatVal F)) :
    (mkGenericBody outConsts ps).lowerSafe [] := by
  induction ps with
  | nil => exact lowerSafe_literals outConsts
  | cons hd rest ih =>
    rcases hd with ⟨name, val⟩
    rw [mkGenericBody, Generic.Expr.lowerSafe]
    refine ⟨?_, ih, ?_⟩
    · rw [Generic.Expr.lowerSafe]
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · rw [Generic.Expr.lowerSafe]; trivial
      · cases val with
        | scalar _ => rw [FlatVal.genericExpr, Generic.Expr.lowerSafe]; trivial
        | arr cs => exact lowerSafe_literals cs
    · simp [Generic.PatternLowering.LetSafe, Generic.Pattern.toCore?]

omit [Field F] [DecidableEq F] in
private theorem lower_literals (cs : List F) :
    (Generic.Expr.tuple (cs.map .literal)).lower [] = .tuple (cs.map .literal) := by
  rw [Generic.Expr.lower]
  congr 1
  induction cs with
  | nil => rfl
  | cons c rest ih => simp [Generic.Expr.lower, ih]

omit [Field F] [DecidableEq F] in
private theorem lower_flatVal (v : FlatVal F) : v.genericExpr.lower [] = v.coreExpr := by
  cases v with
  | scalar _ => rw [FlatVal.genericExpr, FlatVal.coreExpr, Generic.Expr.lower]
  | arr cs => exact lower_literals cs

omit [Field F] [DecidableEq F] in
private theorem lower_mkGenericBody (outConsts : List F) (ps : List (String × FlatVal F)) :
    (mkGenericBody outConsts ps).lower [] = mkCoreBody outConsts ps := by
  induction ps with
  | nil => exact lower_literals outConsts
  | cons hd rest ih =>
    rcases hd with ⟨name, val⟩
    rw [mkGenericBody, Generic.Expr.lower, mkCoreBody, mkCoreAssert]
    simp only [Generic.PatternLowering.lowerLet, Generic.Pattern.toCore?, Generic.Expr.lower,
      List.map_cons, List.map_nil, lower_flatVal, ih, Generic.BuiltinLowering.expression]

omit [Field F] [DecidableEq F] in
private theorem inferType_literals (prog : Aiur.Program F) (caller : String)
    (locals : List (String × Aiur.Ty)) (cs : List F) :
    Aiur.inferType prog caller locals (.tuple (cs.map .literal)) =
      .ok (.tuple (List.replicate cs.length .field)) := by
  rw [Aiur.inferType]
  have hts : Aiur.inferTypes prog caller locals (cs.map .literal) =
      .ok (List.replicate cs.length .field) := by
    induction cs with
    | nil => rw [List.map_nil, Aiur.inferTypes.eq_def]; rfl
    | cons c rest ih =>
      rw [List.map_cons, Aiur.inferTypes.eq_def]
      simp [Aiur.inferType, ih, List.replicate_succ, bind, Except.bind, pure, Except.pure]
  simp [hts, bind, Except.bind, pure, Except.pure]

omit [Field F] [DecidableEq F] in
private theorem inferType_flatVal (prog : Aiur.Program F) (caller : String)
    (locals : List (String × Aiur.Ty)) (v : FlatVal F) :
    Aiur.inferType prog caller locals v.coreExpr = .ok v.coreTy := by
  cases v with
  | scalar _ => rw [FlatVal.coreExpr, FlatVal.coreTy, Aiur.inferType]; rfl
  | arr cs => exact inferType_literals prog caller locals cs

omit [Field F] [DecidableEq F] in
private theorem inferType_mkCoreAssert (prog : Aiur.Program F) (hEnums : prog.enums = [])
    (caller : String) (locals : List (String × Aiur.Ty)) (name : String) (val : FlatVal F)
    (hlook : locals.find? (·.1 == name) = some (name, val.coreTy)) :
    Aiur.inferType prog caller locals (mkCoreAssert name val) = .ok (.tuple []) := by
  have hvar : Aiur.inferType prog caller locals (.var name) = .ok val.coreTy := by
    rw [Aiur.inferType]; simp [hlook, pure, Except.pure]
  have hpair : Aiur.inferType prog caller locals (.tuple [.var name, val.coreExpr]) =
      .ok (.tuple [val.coreTy, val.coreTy]) := by
    rw [Aiur.inferType.eq_def]
    have hts : Aiur.inferTypes prog caller locals [.var name, val.coreExpr] =
        .ok [val.coreTy, val.coreTy] := by
      rw [Aiur.inferTypes.eq_def]; dsimp only
      rw [hvar]; simp only [bind, Except.bind]
      rw [Aiur.inferTypes.eq_def]; dsimp only
      rw [inferType_flatVal]; simp only [bind, Except.bind]
      rw [Aiur.inferTypes.eq_def]; rfl
    simp [hts, bind, Except.bind, pure, Except.pure]
  have hfd : Aiur.findDuplicate ["$assertLeft", "$assertRight"] [] = none := by decide
  have hpat : Aiur.checkPattern prog.enums caller
      (.tuple [.bind "$assertLeft", .bind "$assertRight"] : Aiur.Pattern F) (.tuple [val.coreTy, val.coreTy]) =
      .ok [("$assertLeft", val.coreTy), ("$assertRight", val.coreTy)] := by
    unfold Aiur.checkPattern
    have hpt : Aiur.patternTypes prog.enums caller
        (.tuple [.bind "$assertLeft", .bind "$assertRight"] : Aiur.Pattern F) (.tuple [val.coreTy, val.coreTy]) =
        .ok [("$assertLeft", val.coreTy), ("$assertRight", val.coreTy)] := by
      rw [Aiur.patternTypes.eq_def]; dsimp only
      simp only [List.length_cons, List.length_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      rw [Aiur.patternTypesList.eq_def]; dsimp only
      rw [Aiur.patternTypes.eq_def]; dsimp only
      simp only [bind, Except.bind, pure, Except.pure]
      rw [Aiur.patternTypesList.eq_def]; dsimp only
      rw [Aiur.patternTypes.eq_def]; dsimp only
      simp only [bind, Except.bind, pure, Except.pure]
      rw [Aiur.patternTypesList.eq_def]; rfl
    rw [hpt]
    simp [hfd, bind, Except.bind, pure, Except.pure]
  have hne : ("$assertLeft" == "$assertRight") = false := by decide
  let locals' : List (String × Aiur.Ty) := ("$assertLeft", val.coreTy) :: ("$assertRight", val.coreTy) :: locals
  have hbody : Aiur.inferType prog caller locals'
      (.assertEq {} (.var "$assertLeft") (.var "$assertRight")) = .ok (.tuple []) := by
    rw [Aiur.inferType.eq_def]; dsimp only
    have hl : Aiur.inferType prog caller locals' (.var "$assertLeft") = .ok val.coreTy := by
      rw [Aiur.inferType.eq_def]; simp [locals', pure, Except.pure]
    have hr : Aiur.inferType prog caller locals' (.var "$assertRight") = .ok val.coreTy := by
      rw [Aiur.inferType.eq_def]; simp [locals', hne, pure, Except.pure]
    simp [hl, hr, Aiur.requireType, hEnums, val.coreTy_pointerFree,
      bind, Except.bind, pure, Except.pure]
  rw [mkCoreAssert, Aiur.inferType.eq_def]; dsimp only
  simp only [hpair, hpat, bind, Except.bind, List.cons_append, List.nil_append]
  exact hbody

omit [Field F] [DecidableEq F] in
private theorem inferType_mkCoreBody (prog : Aiur.Program F) (hEnums : prog.enums = [])
    (caller : String) (locals : List (String × Aiur.Ty)) (outConsts : List F)
    (ps : List (String × FlatVal F))
    (hMem : ∀ p ∈ ps, locals.find? (·.1 == p.1) = some (p.1, p.2.coreTy)) :
    Aiur.inferType prog caller locals (mkCoreBody outConsts ps) =
      .ok (.tuple (List.replicate outConsts.length .field)) := by
  induction ps with
  | nil => exact inferType_literals prog caller locals outConsts
  | cons hd rest ih =>
    rcases hd with ⟨name, val⟩
    have hlook := hMem (name, val) List.mem_cons_self
    dsimp only at hlook
    have hrest := ih (fun p hp => hMem p (List.mem_cons_of_mem _ hp))
    have hass := inferType_mkCoreAssert prog hEnums caller locals name val hlook
    have hpat : Aiur.checkPattern prog.enums caller (.wildcard : Aiur.Pattern F) (.tuple []) = .ok [] := by
      simp [Aiur.checkPattern, Aiur.patternTypes, Aiur.findDuplicate, bind, Except.bind,
        pure, Except.pure]
    rw [mkCoreBody, Aiur.inferType.eq_def]; dsimp only
    simp [hass, hpat, hrest, bind, Except.bind]

omit [Field F] [DecidableEq F] in
private theorem engine_inScope_literals (names : List String) (kt : Aiur.Ty → Bool) (cs : List F) :
    Generic.Engine.inScope names kt (.tuple (cs.map .literal)) = true := by
  rw [Generic.Engine.inScope]
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true, id_eq]
    exact ⟨by rw [Generic.Engine.inScope], ih⟩

omit [Field F] [DecidableEq F] in
private theorem engine_inScope_mkCoreAssert (names : List String) (kt : Aiur.Ty → Bool)
    (name : String) (val : FlatVal F) :
    Generic.Engine.inScope names kt (mkCoreAssert name val) = true := by
  have hv : Generic.Engine.inScope names kt val.coreExpr = true := by
    cases val with
    | scalar _ => rw [FlatVal.coreExpr, Generic.Engine.inScope]
    | arr cs => exact engine_inScope_literals names kt cs
  rw [mkCoreAssert, Generic.Engine.inScope]
  have hpair : Generic.Engine.inScope names kt (.tuple [.var name, val.coreExpr]) = true := by
    rw [Generic.Engine.inScope]
    simp [Generic.Engine.inScope, hv]
  have hass : Generic.Engine.inScope names kt
      (.assertEq {} (.var "$assertLeft") (.var "$assertRight") : Aiur.Expr F) = true := by
    rw [Generic.Engine.inScope]
    simp [Generic.Engine.inScope]
  simp [hpair, hass]

omit [Field F] [DecidableEq F] in
private theorem engine_inScope_mkCoreBody (names : List String) (kt : Aiur.Ty → Bool)
    (outConsts : List F) (ps : List (String × FlatVal F)) :
    Generic.Engine.inScope names kt (mkCoreBody outConsts ps) = true := by
  induction ps with
  | nil => exact engine_inScope_literals names kt outConsts
  | cons hd rest ih =>
    rcases hd with ⟨name, val⟩
    rw [mkCoreBody, Generic.Engine.inScope]
    simp [engine_inScope_mkCoreAssert, ih]

omit [Field F] [DecidableEq F] in
private theorem source_inScope_literals (names : List String) (kt : Aiur.Ty → Bool) (cs : List F) :
    Generic.SourceSemantics.inScope names kt [] (.tuple (cs.map .literal)) = true := by
  rw [Generic.SourceSemantics.inScope]
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true, id_eq]
    exact ⟨by rw [Generic.SourceSemantics.inScope], ih⟩

omit [Field F] [DecidableEq F] in
private theorem source_inScope_mkGenericBody (names : List String) (kt : Aiur.Ty → Bool)
    (outConsts : List F) (ps : List (String × FlatVal F)) :
    Generic.SourceSemantics.inScope names kt [] (mkGenericBody outConsts ps) = true := by
  induction ps with
  | nil => exact source_inScope_literals names kt outConsts
  | cons hd rest ih =>
    rcases hd with ⟨name, val⟩
    rw [mkGenericBody, Generic.SourceSemantics.inScope]
    have hv : Generic.SourceSemantics.inScope names kt [] val.genericExpr = true := by
      cases val with
      | scalar _ => rw [FlatVal.genericExpr, Generic.SourceSemantics.inScope]
      | arr cs => exact source_inScope_literals names kt cs
    have hass : Generic.SourceSemantics.inScope names kt []
        (.builtin (.assertEq {}) [.var name, val.genericExpr]) = true := by
      rw [Generic.SourceSemantics.inScope]
      simp [Generic.SourceSemantics.inScope, hv]
    simp [hass, ih]

omit [Field F] [DecidableEq F] in
private theorem checkLowerTypes_literals (prog : Aiur.Program F)
    (locals : List (String × Aiur.Ty)) (cs : List F) :
    (Generic.Expr.tuple (cs.map .literal)).checkLowerTypes prog [] locals =
      some (.tuple (List.replicate cs.length .field)) := by
  rw [Generic.Expr.checkLowerTypes, lower_literals, inferType_literals, engine_inScope_literals]
  have hmap : (cs.map Generic.Expr.literal).mapM (Generic.Expr.checkLowerTypes prog [] locals) =
      some (List.replicate cs.length .field) := by
    induction cs with
    | nil => rfl
    | cons c rest ih =>
      simp only [List.map_cons, List.mapM_cons]
      have hc : (Generic.Expr.literal c).checkLowerTypes prog [] locals = some .field := by
        rw [Generic.Expr.checkLowerTypes]
        simp [Generic.Expr.lower, Aiur.inferType, Generic.Engine.inScope, Except.toOption,
          bind, Option.bind, pure, Except.pure]
      simp [hc, ih, List.replicate_succ, bind, Option.bind, pure]
  simp [hmap, Except.toOption, bind, Option.bind]

omit [Field F] [DecidableEq F] in
private theorem checkLowerTypes_mkGenericBody (prog : Aiur.Program F) (hEnums : prog.enums = [])
    (locals : List (String × Aiur.Ty)) (outConsts : List F) (ps : List (String × FlatVal F))
    (hMem : ∀ p ∈ ps, locals.find? (·.1 == p.1) = some (p.1, p.2.coreTy)) :
    (mkGenericBody outConsts ps).checkLowerTypes prog [] locals =
      some (.tuple (List.replicate outConsts.length .field)) := by
  induction ps with
  | nil => exact checkLowerTypes_literals prog locals outConsts
  | cons hd rest ih =>
    rcases hd with ⟨name, val⟩
    have hlook := hMem (name, val) List.mem_cons_self
    dsimp only at hlook
    have hrest := ih (fun p hp => hMem p (List.mem_cons_of_mem _ hp))
    have hvar : (Generic.Expr.var name).checkLowerTypes prog [] locals = some val.coreTy := by
      rw [Generic.Expr.checkLowerTypes]
      simp [Generic.Expr.lower, Aiur.inferType, hlook, Generic.Engine.inScope, Except.toOption,
        bind, Option.bind, pure, Except.pure]
    have hval : val.genericExpr.checkLowerTypes prog [] locals = some val.coreTy := by
      cases val with
      | scalar _ =>
        rw [FlatVal.genericExpr, FlatVal.coreTy, Generic.Expr.checkLowerTypes]
        simp [Generic.Expr.lower, Aiur.inferType, Generic.Engine.inScope, Except.toOption,
          bind, Option.bind, pure, Except.pure]
      | arr cs => exact checkLowerTypes_literals prog locals cs
    have hass : (Generic.Expr.builtin (.assertEq {}) [.var name, val.genericExpr]).checkLowerTypes
        prog [] locals = some (.tuple []) := by
      rw [Generic.Expr.checkLowerTypes]
      have hlow : (Generic.Expr.builtin (.assertEq {}) [.var name, val.genericExpr]).lower [] =
          mkCoreAssert name val := by
        rw [Generic.Expr.lower]
        simp [Generic.Expr.lower, lower_flatVal, Generic.BuiltinLowering.expression, mkCoreAssert]
      rw [hlow, inferType_mkCoreAssert prog hEnums "$lower" locals name val hlook,
        engine_inScope_mkCoreAssert]
      simp [hvar, hval, Except.toOption, bind, Option.bind, pure]
    rw [mkGenericBody, Generic.Expr.checkLowerTypes]
    have hlow : (Generic.Expr.letValue .wildcard (.builtin (.assertEq {}) [.var name, val.genericExpr])
        (mkGenericBody outConsts rest)).lower [] = mkCoreBody outConsts ((name, val) :: rest) :=
      lower_mkGenericBody outConsts ((name, val) :: rest)
    rw [hlow, inferType_mkCoreBody prog hEnums "$lower" locals outConsts ((name, val) :: rest) hMem,
      engine_inScope_mkCoreBody]
    have hpat : Generic.Pattern.lowerBindingTypes prog.enums [] (.wildcard : Generic.Pattern F) (.tuple []) = some [] := by
      simp [Generic.Pattern.lowerBindingTypes, Generic.Consts.dependencies,
        Generic.PatternLowering.planTree, Generic.PatternLowering.PlanTree.bindTypes, pure, StateT.pure]
    simp only [hass, hpat, List.nil_append, hrest, Except.toOption, bind, Option.bind]
    rfl

omit [Field F] [DecidableEq F] in
private theorem findDuplicate_none_find {α : Type} (xs : List (String × α))
    (hdup : Aiur.findDuplicate (xs.map Prod.fst) [] = none) :
    ∀ p ∈ xs, xs.find? (·.1 == p.1) = some p := by
  have hnodup : (xs.map Prod.fst).Nodup := by
    have aux : ∀ (ns seen : List String), Aiur.findDuplicate ns seen = none →
        ns.Nodup ∧ ∀ x ∈ ns, x ∉ seen := by
      intro ns
      induction ns with
      | nil => intro seen _; exact ⟨List.nodup_nil, by simp⟩
      | cons a ns ih =>
        intro seen h
        simp only [Aiur.findDuplicate] at h
        split at h
        · cases h
        · rename_i hnot
          obtain ⟨hn, hs⟩ := ih (a :: seen) h
          refine ⟨List.nodup_cons.mpr ⟨fun ha => hs a ha (by simp), hn⟩, fun y hy => ?_⟩
          rcases List.mem_cons.mp hy with rfl | hmem
          · simpa using hnot
          · intro hys; exact hs y hmem (by simp [hys])
    exact (aux _ [] hdup).1
  clear hdup
  induction xs with
  | nil => intro _ h; cases h
  | cons a rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hmem
    · simp
    · have hne : (a.1 == p.1) = false := by
        simp only [beq_eq_false_iff_ne]
        intro heq
        exact hnodup.1 (List.mem_map.mpr ⟨p, hmem, heq.symm⟩)
      simp [hne, ih hnodup.2 p hmem]

omit [Field F] in
theorem coreProgram_typecheck (s : FlatAssertSpec F)
    (hNodup : Aiur.findDuplicate (s.params.map Prod.fst) [] = none) :
    Aiur.typecheck s.coreProgram = .ok () := by
  have hFind : ∀ p ∈ s.params,
      (s.params.map fun x => (x.1, x.2.coreTy)).find? (·.1 == p.1) = some (p.1, p.2.coreTy) := by
    intro p hp
    have hdup' : Aiur.findDuplicate ((s.params.map fun x => (x.1, x.2.coreTy)).map Prod.fst) [] = none := by
      simpa [List.map_map, Function.comp_def] using hNodup
    exact findDuplicate_none_find _ hdup' (p.1, p.2.coreTy) (List.mem_map.mpr ⟨p, hp, rfl⟩)
  have hParamsCheck : ∀ ps : List (String × FlatVal F),
      (forIn (m := Except Aiur.CheckError) (ps.map fun x => (x.1, x.2.coreTy)) PUnit.unit
        fun x _ => do
          let _ ← (x.2.checkNames []).mapError Aiur.CheckError.invalidDeclarations
          pure (.yield PUnit.unit)) = .ok PUnit.unit := by
    intro ps
    induction ps with
    | nil => rfl
    | cons hd rest ih =>
      simp only [List.map_cons, List.forIn_cons, FlatVal.coreTy_checkNames, Except.mapError,
        bind, Except.bind, pure, Except.pure]
      exact ih
  have hResCheck : s.resultCoreTy.checkNames [] = .ok () :=
    FlatVal.coreTy_checkNames (.arr s.outConsts)
  have hFn : Aiur.checkFunction s.coreProgram s.coreFn = .ok () := by
    unfold Aiur.checkFunction
    have hdup' : Aiur.findDuplicate (s.coreFn.params.map Prod.fst) [] = none := by
      simpa [coreFn, List.map_map, Function.comp_def] using hNodup
    have hinf := inferType_mkCoreBody s.coreProgram rfl s.fnName s.coreFn.params s.outConsts s.params hFind
    simp only [coreProgram, coreFn] at hinf hdup' ⊢
    rw [hParamsCheck s.params]
    simp only [bind, Except.bind, pure, Except.pure, Except.mapError]
    rw [hResCheck]
    simp only
    rw [hdup']
    simp only
    rw [hinf]
    simp [resultCoreTy, Aiur.requireType]
  unfold Aiur.typecheck
  simp only [coreProgram] at hFn
  simp only [coreProgram, Aiur.checkDeclarations, Aiur.duplicateName, Aiur.findDuplicate,
    Aiur.checkTables, Except.mapError, List.map_cons, List.map_nil, List.append_nil,
    List.not_mem_nil, ↓reduceIte, List.forIn_cons,
    List.forIn_nil, bind, Except.bind, pure, Except.pure, hFn]

omit [Field F] [DecidableEq F] in
theorem checkEntry_coreProgram (s : FlatAssertSpec F) :
    Aiur.checkEntry s.coreProgram s.fnName = .ok () := by
  rw [Aiur.checkEntry_ok]
  refine ⟨⟨s.coreFn.params, s.coreFn.result⟩, ?_, ?_⟩
  · simp [coreProgram, coreFn, Aiur.Program.findSignature?, Aiur.Program.findFunction?]
  · intro ty hty
    simp only [coreFn, List.map_map, Function.comp_def, List.mem_map] at hty
    obtain ⟨p, _, rfl⟩ := hty
    exact p.2.coreTy_pointerFree

omit [Field F] in
theorem checkEntry_source (s : FlatAssertSpec F) :
    s.source.checkEntry s.fnName = .ok () := by
  have hpf : (s.genericFn.params.map Prod.snd).forM
      (Generic.checkPointerFree s.genericProgram s!"entrypoint '{s.fnName}'" 1024 []) = .ok () := by
    have hmapP : s.genericFn.params.map Prod.snd = s.params.map fun p => p.2.genericTy := by
      simp [genericFn, List.map_map, Function.comp_def]
    rw [hmapP]
    induction s.params with
    | nil => rfl
    | cons hd rest ih =>
      have h1 : Generic.checkPointerFree s.genericProgram s!"entrypoint '{s.fnName}'" 1024 [] hd.2.genericTy = .ok () := by
        cases hd.2 with
        | scalar _ => rw [FlatVal.genericTy, Generic.checkPointerFree]; rfl
        | arr cs =>
          rw [FlatVal.genericTy, Generic.checkPointerFree]
          have h1023 : Generic.checkPointerFree s.genericProgram s!"entrypoint '{s.fnName}'" 1023 [] .field = .ok () := rfl
          induction cs with
          | nil => rfl
          | cons _ _ ihc =>
            simp only [List.length_cons, List.replicate_succ, List.forM, h1023, ihc,
              bind, Except.bind]
      simp only [List.map_cons, List.forM, h1, ih, bind, Except.bind]
  have hnames : ((s.genericFn.params.map fun (n, t) => (n, t.toCore)).map Prod.snd).flatMap
      Generic.coreTypeNames = [] := by
    have hmap : (s.genericFn.params.map fun (n, t) => (n, t.toCore)).map Prod.snd =
        s.params.map fun p => p.2.coreTy := by
      simp [genericFn, List.map_map, Function.comp_def, FlatVal.genericTy_toCore]
    rw [hmap]
    induction s.params with
    | nil => rfl
    | cons hd rest ih =>
      have h1 : Generic.coreTypeNames hd.2.coreTy = [] := by
        cases hd.2 with
        | scalar _ => simp [FlatVal.coreTy, Generic.coreTypeNames]
        | arr cs =>
          simp only [FlatVal.coreTy, Generic.coreTypeNames]
          induction cs with
          | nil => rfl
          | cons _ _ ihc => simp [List.replicate_succ, Generic.coreTypeNames, ihc]
      simp [List.flatMap_cons, h1, ih]
  have hcoll : Generic.collectEnums s.genericProgram [] 1024 [] [] = .ok [] := by
    rw [Generic.collectEnums]; rfl
  let fcore : Aiur.Function F := {
    name := s.fnName
    params := s.genericFn.params.map fun (n, t) => (n, t.toCore)
    result := s.genericFn.result.toCore
    body := .tuple [] }
  have hce : Aiur.checkEntry ({ functions := [fcore], enums := [] } : Aiur.Program F) s.fnName = .ok () := by
    rw [Aiur.checkEntry_ok]
    refine ⟨⟨fcore.params, fcore.result⟩, ?_, ?_⟩
    · simp [fcore, Aiur.Program.findSignature?, Aiur.Program.findFunction?]
    · intro ty hty
      simp only [fcore, genericFn, List.map_map, Function.comp_def, List.mem_map] at hty
      obtain ⟨p, _, rfl⟩ := hty
      rw [FlatVal.genericTy_toCore]
      exact p.2.coreTy_pointerFree
  have hfind : s.genericProgram.findFunction? s.fnName = some s.genericFn := by
    simp [genericProgram, Generic.Program.findFunction?, genericFn]
  unfold Generic.Source.checkEntry
  change (do
    let some (fn0 : Generic.Function F) := s.genericProgram.findFunction? s.fnName | throw s!"unknown entrypoint '{s.fnName}'"
    if fn0.isInline then throw s!"inline function '{s.fnName}' cannot be an entrypoint"
    if !fn0.typeParams.isEmpty then throw s!"entrypoint '{s.fnName}' must be non-generic"
    (fn0.params.map Prod.snd).forM (Generic.checkPointerFree s.genericProgram s!"entrypoint '{s.fnName}'" 1024 [])
    let fn1 : Aiur.Function F := {
      name := s.fnName, params := fn0.params.map fun (n, (t : Generic.Ty)) => (n, t.toCore)
      result := fn0.result.toCore, body := .tuple [] }
    let enums ← Generic.collectEnums s.genericProgram [] 1024 [] ((fn1.params.map Prod.snd).flatMap Generic.coreTypeNames)
    (Aiur.checkEntry ({ functions := [fn1], enums } : Aiur.Program F) s.fnName).mapError (fun e => reprStr e)) = .ok ()
  rw [hfind]
  simp only [bind, Except.bind]
  have hisInl : s.genericFn.isInline = false := rfl
  have htp : s.genericFn.typeParams.isEmpty = true := rfl
  rw [hisInl, htp]
  simp only [Bool.false_eq_true, Bool.not_true, ↓reduceIte, hpf, hnames, hcoll]
  change (Aiur.checkEntry ({ functions := [fcore], enums := [] } : Aiur.Program F) s.fnName).mapError (fun e => reprStr e) = .ok ()
  rw [hce]; rfl

omit [Field F] in
theorem compilerFunction_eq (s : FlatAssertSpec F)
    (hSym : Generic.Instance.ofSymbol s.fnName = .ok ⟨s.fnName, []⟩) :
    s.source.compilerFunction? s.fnName = some s.coreFn := by
  have hfind : s.genericProgram.findFunction? s.fnName = some s.genericFn := by
    simp [genericProgram, Generic.Program.findFunction?, genericFn]
  have harg : Generic.arguments s.genericFn.typeParams [] = .ok [] := rfl
  have hprep : Generic.Preparation.expression s.genericProgram (s.genericProgram.consts.length + 1) [] s.genericFn.body =
      .ok (mkGenericBody s.outConsts s.params) :=
    prep_expr_mkGenericBody s.genericProgram (s.genericProgram.consts.length + 1) s.outConsts s.params
  have hctrl : Generic.ControlLower.function (mkGenericBody s.outConsts s.params)
      (s.genericFn.params.map Prod.fst) = .ok (mkGenericBody s.outConsts s.params) := by
    unfold Generic.ControlLower.function
    simp [hasControl_mkGenericBody, pure, Except.pure]
  have hsafe : decide ((mkGenericBody s.outConsts s.params).lowerSafe []) = true :=
    decide_eq_true (lowerSafe_mkGenericBody s.outConsts s.params)
  have hsym' : Generic.Instance.symbol ⟨s.fnName, []⟩ = s.fnName := rfl
  have hparams : (s.genericFn.params.map fun (n, t) => (n, (t.subst []).toCore)) = s.coreFn.params := by
    simp [genericFn, coreFn, List.map_map, Function.comp_def,       FlatVal.genericTy_toCore]
  have hres : (s.genericFn.result.subst []).toCore = s.coreFn.result := by
    change ((FlatVal.arr s.outConsts).genericTy.subst []).toCore = s.resultCoreTy
    rw [FlatVal.genericTy_subst_nil, FlatVal.genericTy_toCore]; rfl
  unfold Generic.Source.compilerFunction? Generic.Preparation.function
  simp only [source, bind, Except.bind, pure, Except.pure, Except.toOption]
  rw [hSym]; dsimp only
  rw [hfind]; dsimp only
  rw [harg]; dsimp only
  rw [hprep]; dsimp only
  rw [hctrl]; dsimp only
  simp only [hsafe, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hsym', hparams, hres,
    lower_mkGenericBody]
  rfl

def specialized (s : FlatAssertSpec F)
    (hSym : Generic.Instance.ofSymbol s.fnName = .ok ⟨s.fnName, []⟩)
    (hNodup : Aiur.findDuplicate (s.params.map Prod.fst) [] = none) :
    Generic.Specialized s.source [s.fnName] where
  program := s.coreProgram
  valid := by
    have htc := s.coreProgram_typecheck hNodup
    have hcomp := s.compilerFunction_eq hSym
    refine ⟨htc, rfl, rfl, ?_, fun _ h => by simp [coreProgram] at h,
      by simp [Generic.closedEnums, coreProgram], ?_, ?_⟩
    · intro n hn
      simp only [Generic.callableNames, coreProgram, coreFn, List.map_cons, List.map_nil,
        List.append_nil, List.mem_singleton] at hn
      subst hn
      rw [hcomp]
      simp [coreProgram, Aiur.Program.findFunction?, coreFn]
    · intro f0 hf0
      simp only [coreProgram, List.mem_singleton] at hf0
      subst hf0
      refine ⟨?_, engine_inScope_mkCoreBody _ _ _ _⟩
      intro param hp
      simp only [coreFn, List.mem_map] at hp
      obtain ⟨p, _, rfl⟩ := hp
      exact p.2.coreTy_known
    · intro n hn
      simp only [List.mem_singleton] at hn
      subst hn
      exact ⟨by simp [Generic.callableNames, coreProgram, coreFn], s.checkEntry_source,
        s.checkEntry_coreProgram⟩
  sourceClosed := by
    intro n hn
    simp only [Generic.callableNames, coreProgram, coreFn, List.map_cons, List.map_nil,
      List.append_nil, List.mem_singleton] at hn
    subst hn
    have harg : Generic.arguments [] [] = .ok [] := rfl
    simp [source, genericProgram, Generic.Program.sourceFunction?, hSym, Generic.Program.findFunction?,
      genericFn, harg, bind, Option.bind, pure, Except.toOption, Option.all,
      source_inScope_mkGenericBody]
  loweringReady := by
    intro n hn
    simp only [Generic.callableNames, coreProgram, coreFn, List.map_cons, List.map_nil,
      List.append_nil, List.mem_singleton] at hn
    subst hn
    have harg : Generic.arguments [] [] = .ok [] := rfl
    rw [s.compilerFunction_eq hSym]
    simp [source, genericProgram, Generic.Program.sourceFunction?, hSym, Generic.Program.findFunction?,
      genericFn, harg, bind, Option.bind, pure, Except.toOption]
  typedLowering := by
    intro n hn
    simp only [Generic.callableNames, coreProgram, coreFn, List.map_cons, List.map_nil,
      List.append_nil, List.mem_singleton] at hn
    subst hn
    have hfind : s.genericProgram.findFunction? s.fnName = some s.genericFn := by
      simp [genericProgram, Generic.Program.findFunction?, genericFn]
    have harg : Generic.arguments s.genericFn.typeParams [] = .ok [] := rfl
    have hFind : ∀ p ∈ s.params,
        (s.params.map fun x => (x.1, x.2.coreTy)).find? (·.1 == p.1) = some (p.1, p.2.coreTy) := by
      intro p hp
      have hdup' : Aiur.findDuplicate ((s.params.map fun x => (x.1, x.2.coreTy)).map Prod.fst) [] = none := by
        simpa [List.map_map, Function.comp_def] using hNodup
      exact findDuplicate_none_find _ hdup' (p.1, p.2.coreTy) (List.mem_map.mpr ⟨p, hp, rfl⟩)
    have hpar : (s.genericFn.params.map fun (n, t) => (n, (t.subst []).toCore)) =
        s.params.map fun x => (x.1, x.2.coreTy) := by
      simp [genericFn, List.map_map, Function.comp_def,         FlatVal.genericTy_toCore]
    have hsf : s.source.program.sourceFunction? s.fnName =
        some ⟨[], s.params.map fun x => (x.1, x.2.coreTy), mkGenericBody s.outConsts s.params⟩ := by
      change (do
        let key ← (Generic.Instance.ofSymbol s.fnName).toOption
        let fn0 ← s.genericProgram.findFunction? key.name
        let types ← (Generic.arguments fn0.typeParams key.types).toOption
        return ({ types, params := fn0.params.map fun (n, (t : Generic.Ty)) => (n, (t.subst types).toCore), body := fn0.body } : Generic.SourceFunction F)) = _
      rw [hSym]; simp only [Except.toOption, bind, Option.bind]
      rw [hfind]; simp only
      rw [harg]; simp only [pure, hpar]; rfl
    have hprep := prep_expr_mkGenericBody s.genericProgram (s.genericProgram.consts.length + 1) s.outConsts s.params
    have hctrl : Generic.ControlLower.function (mkGenericBody s.outConsts s.params)
        ((s.params.map fun x => (x.1, x.2.coreTy)).map Prod.fst) = .ok (mkGenericBody s.outConsts s.params) := by
      unfold Generic.ControlLower.function
      simp [hasControl_mkGenericBody, pure, Except.pure]
    have hchk := checkLowerTypes_mkGenericBody s.coreProgram rfl (s.params.map fun x => (x.1, x.2.coreTy))
      s.outConsts s.params hFind
    rw [hsf]
    change (match Generic.Preparation.expression s.genericProgram (s.genericProgram.consts.length + 1) []
        (mkGenericBody s.outConsts s.params) with
      | .error _ => false
      | .ok prepared => match Generic.ControlLower.function prepared
          ((s.params.map fun x => (x.1, x.2.coreTy)).map Prod.fst) with
        | .error _ => false
        | .ok body => (body.checkLowerTypes s.coreProgram [] (s.params.map fun x => (x.1, x.2.coreTy))).isSome) = true
    rw [hprep]; dsimp only
    rw [hctrl]; dsimp only
    rw [hchk]
    rfl

omit [Field F] [DecidableEq F] in
private theorem tree_source_literals (cs : List F) :
    (Inlining.Tree.tuple (cs.map .literal)).source = .tuple (cs.map .literal) := by
  rw [Inlining.Tree.source]
  congr 1
  induction cs with
  | nil => rfl
  | cons c rest ih => simp [Inlining.Tree.source, ih]

omit [Field F] [DecidableEq F] in
private theorem tree_target_literals (cs : List F) :
    (Inlining.Tree.tuple (cs.map .literal)).target = .tuple (cs.map .literal) := by
  rw [Inlining.Tree.target]
  congr 1
  induction cs with
  | nil => rfl
  | cons c rest ih => simp [Inlining.Tree.target, ih]

omit [Field F] [DecidableEq F] in
private theorem tree_source_mkTreeAssert (name : String) (val : FlatVal F) :
    (mkTreeAssert name val).source = mkCoreAssert name val := by
  have hv : val.treeExpr.source = val.coreExpr := by
    cases val with
    | scalar _ => rw [FlatVal.treeExpr, FlatVal.coreExpr, Inlining.Tree.source]
    | arr cs => exact tree_source_literals cs
  rw [mkTreeAssert, mkCoreAssert, Inlining.Tree.source]
  simp [Inlining.Tree.source, hv]

omit [Field F] [DecidableEq F] in
private theorem tree_target_mkTreeAssert (name : String) (val : FlatVal F) :
    (mkTreeAssert name val).target = mkCoreAssert name val := by
  have hv : val.treeExpr.target = val.coreExpr := by
    cases val with
    | scalar _ => rw [FlatVal.treeExpr, FlatVal.coreExpr, Inlining.Tree.target]
    | arr cs => exact tree_target_literals cs
  rw [mkTreeAssert, mkCoreAssert, Inlining.Tree.target]
  simp [Inlining.Tree.target, hv]

omit [Field F] [DecidableEq F] in
private theorem tree_source_mkTreeBody (outConsts : List F) (ps : List (String × FlatVal F)) :
    (mkTreeBody outConsts ps).source = mkCoreBody outConsts ps := by
  induction ps with
  | nil => exact tree_source_literals outConsts
  | cons hd rest ih =>
    rcases hd with ⟨name, val⟩
    rw [mkTreeBody, mkCoreBody, Inlining.Tree.source, tree_source_mkTreeAssert, ih]

omit [Field F] [DecidableEq F] in
private theorem tree_target_mkTreeBody (outConsts : List F) (ps : List (String × FlatVal F)) :
    (mkTreeBody outConsts ps).target = mkCoreBody outConsts ps := by
  induction ps with
  | nil => exact tree_target_literals outConsts
  | cons hd rest ih =>
    rcases hd with ⟨name, val⟩
    rw [mkTreeBody, mkCoreBody, Inlining.Tree.target, tree_target_mkTreeAssert, ih]

omit [Field F] [DecidableEq F] in
private theorem tree_safe_mkTreeBody (p : Aiur.Program F) (names : List String)
    (outConsts : List F) (ps : List (String × FlatVal F)) :
    (mkTreeBody outConsts ps).Safe p names := by
  have hLits : ∀ cs : List F, (Inlining.Tree.tuple (cs.map .literal)).Safe p names := by
    intro cs
    rw [Inlining.Tree.Safe]
    intro x hx
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
    rw [Inlining.Tree.Safe]; trivial
  induction ps with
  | nil => exact hLits outConsts
  | cons hd rest ih =>
    rcases hd with ⟨name, val⟩
    rw [mkTreeBody, Inlining.Tree.Safe]
    refine ⟨?_, ih⟩
    rw [mkTreeAssert, Inlining.Tree.Safe]
    refine ⟨?_, ?_⟩
    · rw [Inlining.Tree.Safe]
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · rw [Inlining.Tree.Safe]; trivial
      · cases val with
        | scalar _ => rw [FlatVal.treeExpr, Inlining.Tree.Safe]; trivial
        | arr cs => exact hLits cs
    · rw [Inlining.Tree.Safe]
      exact ⟨by rw [Inlining.Tree.Safe]; trivial, by rw [Inlining.Tree.Safe]; trivial⟩

omit [Field F] [DecidableEq F] in
private theorem tree_checkTypes_literals (q : Aiur.Program F) (locals : List (String × Aiur.Ty))
    (cs : List F) :
    (Inlining.Tree.tuple (cs.map .literal)).checkTypes q locals =
      some (.tuple (List.replicate cs.length .field)) := by
  rw [Inlining.Tree.checkTypes, tree_target_literals, inferType_literals]
  have hmap : (cs.map Inlining.Tree.literal).mapM (Inlining.Tree.checkTypes q locals) =
      some (List.replicate cs.length .field) := by
    induction cs with
    | nil => rfl
    | cons c rest ih =>
      simp only [List.map_cons, List.mapM_cons]
      have hc : (Inlining.Tree.literal c).checkTypes q locals = some .field := by
        rw [Inlining.Tree.checkTypes]
        simp [Inlining.Tree.target, Aiur.inferType, Except.toOption, bind, Option.bind, pure, Except.pure]
      simp [hc, ih, List.replicate_succ, bind, Option.bind, pure]
  simp [hmap, Except.toOption, bind, Option.bind]

omit [Field F] [DecidableEq F] in
private theorem tree_checkTypes_mkTreeAssert (q : Aiur.Program F) (hEnums : q.enums = [])
    (locals : List (String × Aiur.Ty)) (name : String) (val : FlatVal F)
    (hlook : locals.find? (·.1 == name) = some (name, val.coreTy)) :
    (mkTreeAssert name val).checkTypes q locals = some (.tuple []) := by
  have hvar : (Inlining.Tree.var name).checkTypes q locals = some val.coreTy := by
    rw [Inlining.Tree.checkTypes]
    simp [Inlining.Tree.target, Aiur.inferType, hlook, Except.toOption, bind, Option.bind, pure, Except.pure]
  have hval : val.treeExpr.checkTypes q locals = some val.coreTy := by
    cases val with
    | scalar _ =>
      rw [FlatVal.treeExpr, FlatVal.coreTy, Inlining.Tree.checkTypes]
      simp [Inlining.Tree.target, Aiur.inferType, Except.toOption, bind, Option.bind, pure, Except.pure]
    | arr cs => exact tree_checkTypes_literals q locals cs
  have hpair : (Inlining.Tree.tuple [.var name, val.treeExpr]).checkTypes q locals =
      some (.tuple [val.coreTy, val.coreTy]) := by
    rw [Inlining.Tree.checkTypes]
    have hv : val.treeExpr.target = val.coreExpr := by
      cases val with
      | scalar _ => rw [FlatVal.treeExpr, FlatVal.coreExpr, Inlining.Tree.target]
      | arr cs => exact tree_target_literals cs
    have hinf : Aiur.inferType q "$inline" locals (.tuple [.var name, val.coreExpr]) =
        .ok (.tuple [val.coreTy, val.coreTy]) := by
      rw [Aiur.inferType.eq_def]
      have hvarI : Aiur.inferType q "$inline" locals (.var name) = .ok val.coreTy := by
        rw [Aiur.inferType]; simp [hlook, pure, Except.pure]
      have hts : Aiur.inferTypes q "$inline" locals [.var name, val.coreExpr] =
          .ok [val.coreTy, val.coreTy] := by
        rw [Aiur.inferTypes.eq_def]; dsimp only
        rw [hvarI]; simp only [bind, Except.bind]
        rw [Aiur.inferTypes.eq_def]; dsimp only
        rw [inferType_flatVal]; simp only [bind, Except.bind]
        rw [Aiur.inferTypes.eq_def]; rfl
      simp [hts, bind, Except.bind, pure, Except.pure]
    simp [Inlining.Tree.target, hv, hinf, hvar, hval, Except.toOption, bind, Option.bind, pure]
  have hfd : Aiur.findDuplicate ["$assertLeft", "$assertRight"] [] = none := by decide
  have hpat : Aiur.checkPattern q.enums "$inline"
      (.tuple [.bind "$assertLeft", .bind "$assertRight"] : Aiur.Pattern F) (.tuple [val.coreTy, val.coreTy]) =
      .ok [("$assertLeft", val.coreTy), ("$assertRight", val.coreTy)] := by
    unfold Aiur.checkPattern
    have hpt : Aiur.patternTypes q.enums "$inline"
        (.tuple [.bind "$assertLeft", .bind "$assertRight"] : Aiur.Pattern F) (.tuple [val.coreTy, val.coreTy]) =
        .ok [("$assertLeft", val.coreTy), ("$assertRight", val.coreTy)] := by
      rw [Aiur.patternTypes.eq_def]; dsimp only
      simp only [List.length_cons, List.length_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      rw [Aiur.patternTypesList.eq_def]; dsimp only
      rw [Aiur.patternTypes.eq_def]; dsimp only
      simp only [bind, Except.bind, pure, Except.pure]
      rw [Aiur.patternTypesList.eq_def]; dsimp only
      rw [Aiur.patternTypes.eq_def]; dsimp only
      simp only [bind, Except.bind, pure, Except.pure]
      rw [Aiur.patternTypesList.eq_def]; rfl
    rw [hpt]
    simp [hfd, bind, Except.bind, pure, Except.pure]
  have hne : ("$assertLeft" == "$assertRight") = false := by decide
  let locals' : List (String × Aiur.Ty) := ("$assertLeft", val.coreTy) :: ("$assertRight", val.coreTy) :: locals
  have hass : (Inlining.Tree.assertEq {} (.var "$assertLeft") (.var "$assertRight")).checkTypes q locals' =
      some (.tuple []) := by
    rw [Inlining.Tree.checkTypes]
    have hl : (Inlining.Tree.var "$assertLeft").checkTypes q locals' = some val.coreTy := by
      rw [Inlining.Tree.checkTypes]
      simp [locals', Inlining.Tree.target, Aiur.inferType, Except.toOption, bind, Option.bind, pure, Except.pure]
    have hr : (Inlining.Tree.var "$assertRight").checkTypes q locals' = some val.coreTy := by
      rw [Inlining.Tree.checkTypes]
      simp [locals', Inlining.Tree.target, Aiur.inferType, hne, Except.toOption, bind, Option.bind, pure, Except.pure]
    have hinf : Aiur.inferType q "$inline" locals'
        (.assertEq {} (.var "$assertLeft") (.var "$assertRight")) = .ok (.tuple []) := by
      rw [Aiur.inferType.eq_def]; dsimp only
      have hlI : Aiur.inferType q "$inline" locals' (.var "$assertLeft") = .ok val.coreTy := by
        rw [Aiur.inferType]; simp [locals', pure, Except.pure]
      have hrI : Aiur.inferType q "$inline" locals' (.var "$assertRight") = .ok val.coreTy := by
        rw [Aiur.inferType]; simp [locals', hne, pure, Except.pure]
      simp [hlI, hrI, Aiur.requireType, hEnums, val.coreTy_pointerFree,
        bind, Except.bind, pure, Except.pure]
    simp [Inlining.Tree.target, hinf, hl, hr, Except.toOption, bind, Option.bind]
  rw [mkTreeAssert, Inlining.Tree.checkTypes]
  rw [show (Inlining.Tree.letValue (.tuple [.bind "$assertLeft", .bind "$assertRight"])
      (.tuple [.var name, val.treeExpr]) (.assertEq {} (.var "$assertLeft") (.var "$assertRight"))).target =
      mkCoreAssert name val from tree_target_mkTreeAssert name val]
  rw [inferType_mkCoreAssert q hEnums "$inline" locals name val hlook]
  simp only [hpair, hpat, Except.toOption, bind, Option.bind, List.cons_append, List.nil_append]
  rw [hass]
  rfl

omit [Field F] [DecidableEq F] in
private theorem tree_checkTypes_mkTreeBody (q : Aiur.Program F) (hEnums : q.enums = [])
    (locals : List (String × Aiur.Ty)) (outConsts : List F) (ps : List (String × FlatVal F))
    (hMem : ∀ p ∈ ps, locals.find? (·.1 == p.1) = some (p.1, p.2.coreTy)) :
    (mkTreeBody outConsts ps).checkTypes q locals =
      some (.tuple (List.replicate outConsts.length .field)) := by
  induction ps with
  | nil => exact tree_checkTypes_literals q locals outConsts
  | cons hd rest ih =>
    rcases hd with ⟨name, val⟩
    have hlook := hMem (name, val) List.mem_cons_self
    dsimp only at hlook
    have hrest := ih (fun p hp => hMem p (List.mem_cons_of_mem _ hp))
    have hass := tree_checkTypes_mkTreeAssert q hEnums locals name val hlook
    have hpat : Aiur.checkPattern q.enums "$inline" (.wildcard : Aiur.Pattern F) (.tuple []) = .ok [] := by
      simp [Aiur.checkPattern, Aiur.patternTypes, Aiur.findDuplicate, bind, Except.bind,
        pure, Except.pure]
    rw [mkTreeBody, Inlining.Tree.checkTypes]
    have ht : (Inlining.Tree.letValue .wildcard (mkTreeAssert name val)
        (mkTreeBody outConsts rest)).target = mkCoreBody outConsts ((name, val) :: rest) :=
      tree_target_mkTreeBody outConsts ((name, val) :: rest)
    rw [ht, inferType_mkCoreBody q hEnums "$inline" locals outConsts ((name, val) :: rest) hMem]
    simp [hass, hpat, hrest, Except.toOption, bind, Option.bind]

omit [Field F] in
private theorem specialized_inlineNames_eq_nil (s : FlatAssertSpec F)
    (hSym : Generic.Instance.ofSymbol s.fnName = .ok ⟨s.fnName, []⟩)
    (hNodup : Aiur.findDuplicate (s.params.map Prod.fst) [] = none) :
    (s.specialized hSym hNodup).inlineNames = [] := by
  simp [Generic.Specialized.inlineNames, specialized, source, coreProgram, coreFn,
    genericProgram, Generic.Program.findFunction?, genericFn, hSym]

def inlinedBase (s : FlatAssertSpec F)
    (hSym : Generic.Instance.ofSymbol s.fnName = .ok ⟨s.fnName, []⟩)
    (hNodup : Aiur.findDuplicate (s.params.map Prod.fst) [] = none) :
    Inlining.Prepared (s.specialized hSym hNodup).program [] [s.fnName] := by
  have htc := s.coreProgram_typecheck hNodup
  have hFind : ∀ p ∈ s.params,
      s.coreFn.params.find? (·.1 == p.1) = some (p.1, p.2.coreTy) := by
    intro p hp
    have hdup' : Aiur.findDuplicate (s.coreFn.params.map Prod.fst) [] = none := by
      simpa [coreFn, List.map_map, Function.comp_def] using hNodup
    exact findDuplicate_none_find _ hdup' (p.1, p.2.coreTy) (List.mem_map.mpr ⟨p, hp, rfl⟩)
  let bodies : Inlining.Bodies F := [(s.fnName, mkTreeBody s.outConsts s.params)]
  have hq : bodies.program s.coreProgram [] = s.coreProgram := by
    simp only [Inlining.Bodies.program, coreProgram, List.filter_cons, List.contains_nil,
      Bool.not_false, ↓reduceIte, List.filter_nil, List.map_cons, List.map_nil,
      Inlining.Bodies.function, Inlining.Bodies.body, bodies, List.find?_cons, coreFn,
      beq_self_eq_true, Option.map_some, Option.getD_some, tree_target_mkTreeBody]
  refine ⟨bodies, htc, ?_⟩
  change bodies.Valid s.coreProgram [] [s.fnName]
  simp only [Inlining.Bodies.Valid, hq]
  refine ⟨htc, ?_, ?_⟩
  · intro f hf
    simp only [coreProgram, List.mem_singleton] at hf
    subst hf
    have hbody : bodies.body s.coreFn.name = mkTreeBody s.outConsts s.params := by
      simp [bodies, Inlining.Bodies.body, coreFn]
    rw [hbody]
    exact ⟨tree_source_mkTreeBody _ _, tree_safe_mkTreeBody _ _ _ _,
      tree_checkTypes_mkTreeBody _ rfl _ _ _ hFind,
      by rw [tree_target_mkTreeBody]; exact engine_inScope_mkCoreBody _ _ _ _⟩
  · intro n hn
    simp only [List.mem_singleton] at hn
    subst hn
    exact ⟨by simp, s.checkEntry_coreProgram⟩

def inlined (s : FlatAssertSpec F)
    (hSym : Generic.Instance.ofSymbol s.fnName = .ok ⟨s.fnName, []⟩)
    (hNodup : Aiur.findDuplicate (s.params.map Prod.fst) [] = none) :
    Inlining.Prepared (s.specialized hSym hNodup).program
      (s.specialized hSym hNodup).inlineNames [s.fnName] :=
  (s.specialized_inlineNames_eq_nil hSym hNodup).symm ▸ s.inlinedBase hSym hNodup

/-! ### Symbolic `Compiler.function` and `checkedLayOut minimalConfig` evaluation -/

omit [Field F] [DecidableEq F] in
private theorem stateT_bind_run {σ ε α β : Type} (x : StateT σ (Except ε) α)
    (f : α → StateT σ (Except ε) β) (s : σ) :
    (StateT.bind x f).run s =
      match x.run s with | .error e => .error e | .ok (a, s') => (f a).run s' := by
  unfold StateT.run StateT.bind
  cases x s <;> rfl

omit [Field F] [DecidableEq F] in
private theorem stateT_run_bind {σ ε α β : Type} (x : StateT σ (Except ε) α)
    (f : α → StateT σ (Except ε) β) (s : σ) :
    (x >>= f).run s =
      match x.run s with | .error e => .error e | .ok (a, s') => (f a).run s' :=
  stateT_bind_run x f s

omit [Field F] [DecidableEq F] in
private theorem stateT_pure_run {σ ε α : Type} (a : α) (s : σ) :
    (StateT.pure (m := Except ε) a).run s = .ok (a, s) := rfl

omit [Field F] [DecidableEq F] in
private theorem stateT_run_pure {σ ε α : Type} (a : α) (s : σ) :
    (pure a : StateT σ (Except ε) α).run s = .ok (a, s) := rfl

omit [Field F] [DecidableEq F] in
private theorem stateT_monadLift_ok {σ ε α : Type} (a : α) (s : σ) :
    (monadLift (Except.ok a : Except ε α) : StateT σ (Except ε) α).run s = .ok (a, s) := rfl

omit [Field F] [DecidableEq F] in
private theorem forIn_append_yield {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (l₁ l₂ : List α) (init : β) (f : α → β → m (ForInStep β))
    (hYield : ∀ x ∈ l₁, ∀ b, ∃ m' : m β, f x b = (· |> ForInStep.yield) <$> m') :
    forIn (l₁ ++ l₂) init f = (forIn l₁ init f >>= fun b => forIn l₂ b f) := by
  induction l₁ generalizing init with
  | nil => simp
  | cons x rest ih =>
    simp only [List.cons_append, List.forIn_cons]
    obtain ⟨m', hm'⟩ := hYield x List.mem_cons_self init
    rw [hm', map_eq_pure_bind, bind_assoc, bind_assoc, bind_assoc]
    simp only [pure_bind]
    congr 1; funext b'
    exact ih b' (fun y hy => hYield y (List.mem_cons_of_mem _ hy))

omit [Field F] [DecidableEq F] in
private theorem forIn_yield_const {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (xs : List α) (acc : β) (body : α → β → m (ForInStep β))
    (hBody : ∀ x ∈ xs, ∀ r, body x r = pure (.yield r)) :
    forIn xs acc body = pure acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.forIn_cons, hBody x List.mem_cons_self, pure_bind]
    exact ih acc (fun y hy => hBody y (List.mem_cons_of_mem _ hy))

omit [Field F] [DecidableEq F] in
private theorem forall₂_append_cons {α β : Type} {R : α → β → Prop}
    {l₁ : List α} {l₂ : List β} {a : α} {b : β}
    (h : List.Forall₂ R l₁ l₂) (hab : R a b) :
    List.Forall₂ R (l₁ ++ [a]) (l₂ ++ [b]) := by
  induction h with
  | nil => exact List.Forall₂.cons hab List.Forall₂.nil
  | cons h1 _ ih => exact List.Forall₂.cons h1 ih

omit [Field F] [DecidableEq F] in
private theorem compiler_fresh_range (role : Optimized.Role) (n : Nat) (st : Optimized.Compiler.State F)
    (hLen : st.roles.size = st.aliases.size) :
    ((List.range n).mapM fun _ => Optimized.Compiler.fresh (F := F) role).run st =
      .ok (List.range' st.roles.size n,
        { st with
          roles := st.roles ++ (List.replicate n role).toArray
          aliases := st.aliases ++ (List.replicate n none).toArray }) := by
  induction n generalizing st with
  | zero =>
    simp [StateT.run, pure, StateT.pure, Except.pure]
  | succ n ih =>
    rw [List.range_succ_eq_map, List.mapM_cons]
    have h1 : (Optimized.Compiler.fresh (F := F) role).run st =
        .ok (st.roles.size, { st with roles := st.roles.push role, aliases := st.aliases.push none }) := rfl
    have hmap : ((List.range n).map Nat.succ).mapM (fun _ => Optimized.Compiler.fresh (F := F) role) =
        (List.range n).mapM (fun _ => Optimized.Compiler.fresh (F := F) role) := by
      clear ih h1
      induction (List.range n) with
      | nil => rfl
      | cons _ _ ih' => simp [List.mapM_cons, ih']
    simp only [stateT_run_bind, h1, hmap]
    rw [ih _ (by simp [hLen])]
    simp only [stateT_pure_run, pure, Except.ok.injEq, Prod.mk.injEq, Array.size_push]
    refine ⟨by simp [List.range'_succ], ?_⟩
    congr 1 <;> apply Array.toList_inj.mp <;> simp [List.replicate_succ]

omit [Field F] [DecidableEq F] in
private theorem compiler_freshValue_flat (role : Optimized.Role) (v : FlatVal F) (st : Optimized.Compiler.State F)
    (hLen : st.roles.size = st.aliases.size) :
    (Optimized.Compiler.freshValue (F := F) [] role v.coreTy).run st =
      .ok (⟨v.coreTy, List.range' st.roles.size v.width⟩,
        { st with
          roles := st.roles ++ (List.replicate v.width role).toArray
          aliases := st.aliases ++ (List.replicate v.width none).toArray }) := by
  unfold Optimized.Compiler.freshValue Optimized.Compiler.getLayout
  rw [FlatVal.coreTy_layout]
  have hw : (match v with | .scalar _ => Aiur.Layout.field | .arr cs => .tuple (List.replicate cs.length .field)).width = v.width := by
    cases v with
    | scalar _ => simp [FlatVal.width, Aiur.Layout.width]
    | arr cs => exact FlatVal.layout_width_replicate_field cs.length
  simp only [stateT_run_bind, liftM, Except.mapError, stateT_monadLift_ok, hw]
  rw [compiler_fresh_range role v.width st hLen]
  simp only [pure, stateT_pure_run]

omit [Field F] [DecidableEq F] in
private theorem compiler_freshInputs (ps : List (String × FlatVal F)) (st : Optimized.Compiler.State F)
    (hLen : st.roles.size = st.aliases.size) :
    ((ps.map fun p => p.2.coreTy).mapM (Optimized.Compiler.freshValue (F := F) [] .input)).run st =
      .ok (mkInputWires st.roles.size ps,
        { st with
          roles := st.roles ++ (List.replicate (ps.flatMap fun p => p.2.words).length .input).toArray
          aliases := st.aliases ++ (List.replicate (ps.flatMap fun p => p.2.words).length none).toArray }) := by
  induction ps generalizing st with
  | nil => simp [mkInputWires, StateT.run, pure, StateT.pure, Except.pure]
  | cons hd rest ih =>
    rcases hd with ⟨name, val⟩
    simp only [List.map_cons, List.mapM_cons, stateT_run_bind]
    rw [compiler_freshValue_flat .input val st hLen]
    dsimp only
    rw [ih _ (by simp [hLen])]
    simp only [mkInputWires, List.flatMap_cons, List.length_append, FlatVal.words_length,
      Array.size_append, List.size_toArray, List.length_replicate,
      pure, stateT_pure_run, Except.ok.injEq, Prod.mk.injEq, true_and]
    congr 1 <;> apply Array.toList_inj.mp <;>
      simp only [Array.toList_append, List.append_assoc, ← List.replicate_add]

omit [DecidableEq F] in
private theorem compiler_validate_flat (v : FlatVal F) (ws : List (Aiur.Optimized.Polynomial F))
    (hW : ws.length = v.width) (st : Optimized.Compiler.State F) :
    (Optimized.Compiler.validateValue [] 0 ⟨v.coreTy, ws⟩).run st = .ok ((), st) := by
  unfold Optimized.Compiler.validateValue Optimized.Compiler.getLayout
  rw [FlatVal.coreTy_layout]
  simp only [stateT_run_bind, liftM, Except.mapError, stateT_monadLift_ok]
  cases v with
  | scalar _ =>
    rcases ws with _ | ⟨w, _ | _⟩ <;> simp [FlatVal.width] at hW
    rw [Optimized.Compiler.validate.eq_def]; rfl
  | arr cs =>
    rw [Optimized.Compiler.validate.eq_def]; dsimp only
    have aux : ∀ (n : Nat) (l : List (Aiur.Optimized.Polynomial F)), l.length = n →
        (Optimized.Compiler.validateList 0 (List.replicate n Aiur.Layout.field) l).run st = .ok ((), st) := by
      intro n
      induction n with
      | zero =>
        intro l hl
        cases l with
        | nil => rw [List.replicate_zero, Optimized.Compiler.validateList.eq_def]; rfl
        | cons _ _ => simp at hl
      | succ n ih =>
        intro l hl
        cases l with
        | nil => simp at hl
        | cons x xs =>
          rw [List.replicate_succ, Optimized.Compiler.validateList.eq_def]; dsimp only
          simp only [Aiur.Layout.width, List.length_cons,
            show ¬ (xs.length + 1 < 1) by omega, ↓reduceIte, List.take_succ_cons, List.take_zero,
            List.drop_succ_cons, List.drop_zero, stateT_run_bind, stateT_run_pure]
          have hv1 : (Optimized.Compiler.validate 0 Aiur.Layout.field [x]).run st = .ok ((), st) := by
            rw [Optimized.Compiler.validate.eq_def]; rfl
          rw [hv1]
          exact ih xs (by simp at hl; omega)
    exact aux cs.length ws hW

omit [DecidableEq F] in
private theorem compiler_validateParams (ps : List (String × FlatVal F)) (off : Nat) (st : Optimized.Compiler.State F) :
    (Optimized.Compiler.validateParameters [] true (mkInputWires off ps)).run st = .ok ((), st) := by
  unfold Optimized.Compiler.validateParameters
  simp only [↓reduceIte]
  have hfor : ∀ (ps : List (String × FlatVal F)) (off : Nat),
      (forIn (m := Optimized.Compiler.Build F) (mkInputWires off ps) PUnit.unit fun value _ =>
        do
          Optimized.Compiler.validateValue [] 0 (value.map Aiur.Optimized.Polynomial.var)
          return .yield PUnit.unit).run st = .ok (PUnit.unit, st) := by
    intro ps
    induction ps with
    | nil => intro _; rfl
    | cons hd rest ih =>
      intro off
      rcases hd with ⟨_, val⟩
      simp only [mkInputWires, List.forIn_cons, stateT_run_bind, WireValue.map]
      rw [compiler_validate_flat val ((List.range' off val.width).map Aiur.Optimized.Polynomial.var)
        (by simp) st]
      simp only [stateT_pure_run, pure]
      exact ih (off + val.width)
  rw [stateT_run_bind, hfor ps off]
  rfl

private theorem compiler_lowerArgs_literals (prog : Aiur.Program F) (fnName : String)
    (locals : Optimized.Compiler.Locals F) (cs : List F) (st : Optimized.Compiler.State F) :
    (Optimized.Compiler.lowerArgs prog fnName locals 0 (cs.map .literal)).run st =
      .ok (cs.map (fun c => WireValue.field (Aiur.Optimized.Polynomial.const c)), st) := by
  induction cs with
  | nil => rw [List.map_nil, Optimized.Compiler.lowerArgs]; rfl
  | cons c rest ih =>
    rw [List.map_cons, Optimized.Compiler.lowerArgs]
    have h1 : (Optimized.Compiler.lower prog fnName locals 0 (.literal c) none).run st =
        .ok (WireValue.field (.const c), st) := by
      rw [Optimized.Compiler.lower]; rfl
    simp only [stateT_run_bind, h1, ih, pure, stateT_pure_run, List.map_cons]

omit [Field F] [DecidableEq F] in
private theorem wireValue_tuple_fields (cs : List F) :
    WireValue.tuple (cs.map fun c => WireValue.field (Aiur.Optimized.Polynomial.const c)) =
      ⟨.tuple (List.replicate cs.length .field), cs.map Aiur.Optimized.Polynomial.const⟩ := by
  unfold WireValue.tuple
  congr 1
  · simp only [List.map_map, Function.comp_def, WireValue.field]
    congr 1
    induction cs with
    | nil => rfl
    | cons _ _ ih => simp [List.replicate_succ, ih]
  · simp only [List.flatMap_map, WireValue.field]
    induction cs with
    | nil => rfl
    | cons _ _ ih => simp [ih]

omit [Field F] [DecidableEq F] in
private theorem compiler_equalValue_push (xs : List Nat) (cs : List F) (ty : Aiur.Ty)
    (hLen : xs.length = cs.length) (st : Optimized.Compiler.State F) :
    (Optimized.Compiler.equalValue 0 ⟨ty, xs.map Aiur.Optimized.Polynomial.var⟩ ⟨ty, cs.map Aiur.Optimized.Polynomial.const⟩).run st =
      .ok ((), { st with
        equations := st.equations ++ ((xs.zip cs).map fun p => (⟨0, .sub (.var p.1) (.const p.2)⟩ : Equation F)).toArray }) := by
  unfold Optimized.Compiler.equalValue
  have hlen' : (xs.map (Aiur.Optimized.Polynomial.var : Nat → Aiur.Optimized.Polynomial F)).length =
      (cs.map Aiur.Optimized.Polynomial.const).length := by simp [hLen]
  simp only [ne_eq, not_true_eq_false, hlen', or_self, ↓reduceIte]
  have aux : ∀ (l : List (Nat × F)) (s0 : Optimized.Compiler.State F),
      (forIn (m := Optimized.Compiler.Build F)
        (l.map fun p => (Aiur.Optimized.Polynomial.var p.1, Aiur.Optimized.Polynomial.const p.2)) PUnit.unit
        fun p _ => do
          Optimized.Compiler.equation 0 (.sub p.1 p.2)
          return .yield PUnit.unit).run s0 =
      .ok (PUnit.unit, { s0 with equations := s0.equations ++ (l.map fun p => (⟨0, .sub (.var p.1) (.const p.2)⟩ : Equation F)).toArray }) := by
    intro l
    induction l with
    | nil => intro s0; simp [StateT.run, pure, StateT.pure, Except.pure]
    | cons p rest ih =>
      intro s0
      rcases p with ⟨i, c⟩
      simp only [List.map_cons, List.forIn_cons, stateT_run_bind]
      have h1 : (Optimized.Compiler.equation (F := F) 0 (.sub (.var i) (.const c))).run s0 =
          .ok ((), { s0 with equations := s0.equations.push ⟨0, .sub (.var i) (.const c)⟩ }) := rfl
      rw [h1]
      dsimp only
      rw [show (pure (.yield PUnit.unit) : Optimized.Compiler.Build F (ForInStep PUnit)).run _ =
          .ok (.yield PUnit.unit, _) from rfl]
      dsimp only
      rw [ih]
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and]
      congr 1
      apply Array.toList_inj.mp
      simp
  have hzip : (xs.map (Aiur.Optimized.Polynomial.var : Nat → Aiur.Optimized.Polynomial F)).zip
      (cs.map Aiur.Optimized.Polynomial.const) =
      (xs.zip cs).map fun p => (Aiur.Optimized.Polynomial.var p.1, Aiur.Optimized.Polynomial.const p.2) := by
    clear hLen hlen'
    induction xs generalizing cs with
    | nil => cases cs <;> rfl
    | cons x xs ih =>
      cases cs with
      | nil => rfl
      | cons c cs => simp only [List.map_cons, List.zip_cons_cons, ih cs]
  rw [stateT_run_bind, stateT_run_pure]; dsimp only
  rw [stateT_run_bind, hzip, aux (xs.zip cs) st]
  rfl

omit [Field F] [DecidableEq F] in
private theorem zip_range'_eq_zipIdx {α : Type} (off : Nat) (cs : List α) :
    (List.range' off cs.length).zip cs = (cs.zipIdx off).map fun (c, i) => (i, c) := by
  induction cs generalizing off with
  | nil => rfl
  | cons c rest ih => simp [List.range'_succ, List.zipIdx_cons, ih]

omit [Field F] [DecidableEq F] in
private theorem compiler_equalValue_self (xs : List Nat) (ty : Aiur.Ty) (st : Optimized.Compiler.State F) :
    (Optimized.Compiler.equalValue 0 ⟨ty, xs.map Aiur.Optimized.Polynomial.var⟩ ⟨ty, xs.map Aiur.Optimized.Polynomial.var⟩).run st =
      .ok ((), { st with
        equations := st.equations ++ (xs.map fun i => (⟨0, .sub (.var i) (.var i)⟩ : Equation F)).toArray }) := by
  unfold Optimized.Compiler.equalValue
  simp only [ne_eq, not_true_eq_false, or_self, ↓reduceIte]
  have aux : ∀ (l : List Nat) (s0 : Optimized.Compiler.State F),
      (forIn (m := Optimized.Compiler.Build F)
        ((l.map (Aiur.Optimized.Polynomial.var : Nat → Aiur.Optimized.Polynomial F)).zip
          (l.map (Aiur.Optimized.Polynomial.var : Nat → Aiur.Optimized.Polynomial F))) PUnit.unit
        fun p _ => do
          Optimized.Compiler.equation 0 (.sub p.1 p.2)
          return .yield PUnit.unit).run s0 =
      .ok (PUnit.unit, { s0 with equations := s0.equations ++ (l.map fun i => (⟨0, .sub (.var i) (.var i)⟩ : Equation F)).toArray }) := by
    intro l
    induction l with
    | nil => intro s0; simp [StateT.run, pure, StateT.pure, Except.pure]
    | cons x rest ih =>
      intro s0
      simp only [List.map_cons, List.zip_cons_cons, List.forIn_cons, stateT_run_bind]
      have h1 : (Optimized.Compiler.equation (F := F) 0 (.sub (.var x) (.var x))).run s0 =
          .ok ((), { s0 with equations := s0.equations.push ⟨0, .sub (.var x) (.var x)⟩ }) := rfl
      rw [h1]
      dsimp only
      rw [show (pure (.yield PUnit.unit) : Optimized.Compiler.Build F (ForInStep PUnit)).run _ =
          .ok (.yield PUnit.unit, _) from rfl]
      dsimp only
      rw [ih]
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and]
      congr 1
      apply Array.toList_inj.mp
      simp
  rw [stateT_run_bind, stateT_run_pure]; dsimp only
  rw [stateT_run_bind, aux xs st]
  rfl

omit [Field F] [DecidableEq F] in
private theorem trivialEqs_succ (outOff outLen count : Nat) :
    trivialEqs (F := F) outOff outLen (count + 1) =
      trivialEqs outOff outLen count ++
        ((List.range' outOff outLen).map fun i => (⟨0, .sub (.var i) (.var i)⟩ : Equation F)) := by
  unfold trivialEqs
  rw [List.replicate_succ', List.flatten_append, List.flatten_singleton]

private theorem compiler_lower_mkCoreBody (prog : Aiur.Program F) (hEnums : prog.enums = [])
    (fnName : String) (locals : Optimized.Compiler.Locals F) (outConsts : List F) (outOff : Nat)
    (ps : List (String × FlatVal F)) (off : Nat) (st : Optimized.Compiler.State F)
    (hLocals : ∀ p ∈ ps, ∀ k,
      ps.drop k = p :: ps.drop (k + 1) →
      let pOff := off + ((ps.take k).flatMap fun q => q.2.words).length
      locals.find? (·.1 == p.1) =
        some (p.1, ⟨p.2.coreTy, (List.range' pOff p.2.width).map Aiur.Optimized.Polynomial.var⟩)) :
    (Optimized.Compiler.lower prog fnName locals 0 (mkCoreBody outConsts ps)
        (some ⟨.tuple (List.replicate outConsts.length .field), List.range' outOff outConsts.length⟩)).run st =
      .ok (⟨.tuple (List.replicate outConsts.length .field), (List.range' outOff outConsts.length).map Aiur.Optimized.Polynomial.var⟩,
        { st with
          equations := st.equations ++
            (((ps.flatMap fun p => p.2.words).zipIdx off).map fun (c, i) => (⟨0, .sub (.var i) (.const c)⟩ : Equation F)).toArray ++
            ((outConsts.zipIdx outOff).map fun (c, i) => (⟨0, .sub (.var i) (.const c)⟩ : Equation F)).toArray ++
            (trivialEqs outOff outConsts.length ps.length).toArray }) := by
  induction ps generalizing off st with
  | nil =>
    rw [mkCoreBody, Optimized.Compiler.lower]
    simp only [stateT_run_bind]
    have h1 : (Optimized.Compiler.lowerArgs prog fnName locals 0 (outConsts.map .literal)).run st =
        .ok (outConsts.map (fun c => WireValue.field (Aiur.Optimized.Polynomial.const c)), st) :=
      compiler_lowerArgs_literals prog fnName locals outConsts st
    rw [h1]
    simp only [wireValue_tuple_fields, WireValue.map, stateT_run_pure]
    rw [compiler_equalValue_push (List.range' outOff outConsts.length) outConsts _ (by simp) st]
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and]
    congr 1
    apply Array.toList_inj.mp
    simp [zip_range'_eq_zipIdx, trivialEqs, List.map_map, Function.comp_def]
  | cons hd rest ih =>
    rcases hd with ⟨name, val⟩
    have hlook : locals.find? (·.1 == name) =
        some (name, ⟨val.coreTy, (List.range' off val.width).map Aiur.Optimized.Polynomial.var⟩) := by
      have h0 := hLocals (name, val) List.mem_cons_self 0 rfl
      simpa using h0
    let lhs : Optimized.Compiler.Symbolic F :=
      ⟨val.coreTy, (List.range' off val.width).map Aiur.Optimized.Polynomial.var⟩
    let rhs : Optimized.Compiler.Symbolic F :=
      ⟨val.coreTy, val.words.map Aiur.Optimized.Polynomial.const⟩
    have hValLower : (Optimized.Compiler.lower prog fnName locals 0 val.coreExpr none).run st = .ok (rhs, st) := by
      cases val with
      | scalar c => rw [FlatVal.coreExpr, Optimized.Compiler.lower]; rfl
      | arr cs =>
        rw [FlatVal.coreExpr, Optimized.Compiler.lower]
        simp only [stateT_run_bind]
        rw [compiler_lowerArgs_literals prog fnName locals cs st]
        simp only [rhs, FlatVal.coreTy, FlatVal.words, wireValue_tuple_fields, stateT_run_pure]
    have hAss : (Optimized.Compiler.lower prog fnName locals 0 (mkCoreAssert name val) none).run st =
        .ok (.tuple [], { st with
          equations := st.equations ++
            ((val.words.zipIdx off).map fun (c, i) => (⟨0, .sub (.var i) (.const c)⟩ : Equation F)).toArray }) := by
      have hvar : (Optimized.Compiler.lower prog fnName locals 0 (.var name) none).run st = .ok (lhs, st) := by
        rw [Optimized.Compiler.lower]; simp [lhs, hlook]
      have hpair : (Optimized.Compiler.lower prog fnName locals 0 (.tuple [.var name, val.coreExpr]) none).run st =
          .ok (⟨.tuple [val.coreTy, val.coreTy], lhs.words ++ rhs.words⟩, st) := by
        rw [Optimized.Compiler.lower]
        simp only [stateT_run_bind]
        have hargs : (Optimized.Compiler.lowerArgs prog fnName locals 0 [.var name, val.coreExpr]).run st =
            .ok ([lhs, rhs], st) := by
          rw [Optimized.Compiler.lowerArgs, stateT_run_bind, hvar]; dsimp only
          rw [stateT_run_bind, Optimized.Compiler.lowerArgs, stateT_run_bind, hValLower]; dsimp only
          rw [stateT_run_bind, Optimized.Compiler.lowerArgs]
          rfl
        rw [hargs]
        simp only [WireValue.tuple, lhs, rhs, stateT_run_pure, List.map_cons, List.map_nil,
          List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have hSplit : (Optimized.Compiler.splitValues (F := F) prog.enums [val.coreTy, val.coreTy] (lhs.words ++ rhs.words)).run st =
          .ok ([lhs, rhs], st) := by
        rw [hEnums]
        have hw : (match val with | .scalar _ => Aiur.Layout.field | .arr cs => .tuple (List.replicate cs.length .field)).width = val.width := by
          cases val with
          | scalar _ => simp [FlatVal.width, Aiur.Layout.width]
          | arr cs => exact FlatVal.layout_width_replicate_field cs.length
        have hlLen : lhs.words.length = val.width := by simp [lhs]
        have hrLen : rhs.words.length = val.width := by simp [rhs, FlatVal.words_length]
        have htake1 : (lhs.words ++ rhs.words).take val.width = lhs.words := by
          rw [← hlLen, List.take_left]
        have hdrop1 : (lhs.words ++ rhs.words).drop val.width = rhs.words := by
          rw [← hlLen, List.drop_left]
        have htake2 : rhs.words.take val.width = rhs.words := by
          rw [← hrLen, List.take_length]
        have hdrop2 : rhs.words.drop val.width = [] := by
          rw [← hrLen, List.drop_length]
        rw [Optimized.Compiler.splitValues.eq_def]; dsimp only
        rw [stateT_run_bind]
        unfold Optimized.Compiler.getLayout
        rw [FlatVal.coreTy_layout]
        simp only [stateT_run_bind, liftM, Except.mapError, stateT_monadLift_ok,
          hw, List.length_append, hlLen, hrLen,
          show ¬ (val.width + val.width < val.width) by omega, ↓reduceIte, htake1, hdrop1,
          stateT_run_pure]
        rw [Optimized.Compiler.splitValues.eq_def]; dsimp only
        rw [stateT_run_bind]
        unfold Optimized.Compiler.getLayout
        rw [FlatVal.coreTy_layout]
        simp only [stateT_run_bind, liftM, Except.mapError, stateT_monadLift_ok,
          hw, hrLen, Nat.lt_irrefl, ↓reduceIte, htake2, hdrop2, stateT_run_pure]
        rw [Optimized.Compiler.splitValues.eq_def]
        rfl
      have hPat : (Optimized.Compiler.pattern (F := F) prog.enums
          (.tuple [.bind "$assertLeft", .bind "$assertRight"])
          ⟨.tuple [val.coreTy, val.coreTy], lhs.words ++ rhs.words⟩).run st =
          .ok (([], [("$assertLeft", lhs), ("$assertRight", rhs)]), st) := by
        rw [Optimized.Compiler.pattern]; dsimp only
        rw [stateT_run_bind, hSplit]; dsimp only
        rw [Optimized.Compiler.patternList, stateT_run_bind, Optimized.Compiler.pattern]
        simp only [stateT_run_pure, stateT_run_bind]
        rw [Optimized.Compiler.patternList, stateT_run_bind, Optimized.Compiler.pattern]
        simp only [stateT_run_pure, stateT_run_bind]
        rw [Optimized.Compiler.patternList]
        rfl
      have hne : ("$assertLeft" == "$assertRight") = false := by decide
      let locals' : Optimized.Compiler.Locals F := ("$assertLeft", lhs) :: ("$assertRight", rhs) :: locals
      have hEqBody : (Optimized.Compiler.lower prog fnName locals' 0
          (.assertEq {} (.var "$assertLeft") (.var "$assertRight")) none).run st =
          .ok (.tuple [], { st with
            equations := st.equations ++
              ((val.words.zipIdx off).map fun (c, i) => (⟨0, .sub (.var i) (.const c)⟩ : Equation F)).toArray }) := by
        rw [Optimized.Compiler.lower]
        have hl : (Optimized.Compiler.lower prog fnName locals' 0 (.var "$assertLeft") none).run st = .ok (lhs, st) := by
          rw [Optimized.Compiler.lower]; simp [locals']
        have hr : (Optimized.Compiler.lower prog fnName locals' 0 (.var "$assertRight") none).run st = .ok (rhs, st) := by
          rw [Optimized.Compiler.lower]; simp [locals', hne]
        simp only [stateT_run_bind, hl, hr, lhs, rhs, hEnums,
          val.coreTy_pointerFree, Bool.not_true, Bool.false_eq_true, ↓reduceIte, stateT_run_pure]
        rw [compiler_equalValue_push (List.range' off val.width) val.words val.coreTy
          (by simp [FlatVal.words_length]) st]
        simp only [← FlatVal.words_length, zip_range'_eq_zipIdx, List.map_map, Function.comp_def
          ]
      rw [mkCoreAssert, Optimized.Compiler.lower]
      simp only [stateT_run_bind, hpair, hPat, List.forIn_nil,
        stateT_run_pure, List.cons_append, List.nil_append]
      rw [show (("$assertLeft", lhs) :: ("$assertRight", rhs) :: locals) = locals' from rfl, hEqBody]
    rw [mkCoreBody, Optimized.Compiler.lower]
    simp only [stateT_run_bind, hAss]
    have hpat : (Optimized.Compiler.pattern prog.enums .wildcard (.tuple [])).run
        { st with equations := st.equations ++ ((val.words.zipIdx off).map fun (c, i) => (⟨0, .sub (.var i) (.const c)⟩ : Equation F)).toArray } =
        .ok (([], []), { st with equations := st.equations ++ ((val.words.zipIdx off).map fun (c, i) => (⟨0, .sub (.var i) (.const c)⟩ : Equation F)).toArray }) := by
      rw [Optimized.Compiler.pattern]; rfl
    rw [hpat]
    simp only [List.nil_append, List.forIn_nil, stateT_run_pure]
    have hRestLocals : ∀ p ∈ rest, ∀ k,
        rest.drop k = p :: rest.drop (k + 1) →
        let pOff := (off + val.width) + ((rest.take k).flatMap fun q => q.2.words).length
        locals.find? (·.1 == p.1) =
          some (p.1, ⟨p.2.coreTy, (List.range' pOff p.2.width).map Aiur.Optimized.Polynomial.var⟩) := by
      intro p hp k hdrop
      have h' := hLocals p (List.mem_cons_of_mem _ hp) (k + 1) (by simpa using hdrop)
      simpa [List.take_succ_cons, List.flatMap_cons, List.length_append, FlatVal.words_length,
        Nat.add_assoc] using h'
    rw [ih (off + val.width) _ hRestLocals]
    simp only [WireValue.map]
    rw [compiler_equalValue_self (List.range' outOff outConsts.length) _]
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and]
    congr 1
    apply Array.toList_inj.mp
    simp only [Array.toList_append, List.flatMap_cons, List.zipIdx_append,
      FlatVal.words_length, List.map_append, List.length_cons, trivialEqs_succ, List.append_assoc]

omit [Field F] [DecidableEq F] in
private theorem zip_names_mkInputWires (off : Nat) (ps : List (String × FlatVal F))
    (hNodup : Aiur.findDuplicate (ps.map Prod.fst) [] = none) :
    ∀ p ∈ ps, ∀ k,
      ps.drop k = p :: ps.drop (k + 1) →
      let pOff := off + ((ps.take k).flatMap fun q => q.2.words).length
      ((ps.map Prod.fst).zip ((mkInputWires off ps).map
          (WireValue.map (Aiur.Optimized.Polynomial.var : Nat → Aiur.Optimized.Polynomial F)))).find?
        (·.1 == p.1) =
        some (p.1, ⟨p.2.coreTy, (List.range' pOff p.2.width).map Aiur.Optimized.Polynomial.var⟩) := by
  have hnod : (ps.map Prod.fst).Nodup := by
    have aux : ∀ (ns seen : List String), Aiur.findDuplicate ns seen = none →
        ns.Nodup ∧ ∀ x ∈ ns, x ∉ seen := by
      intro ns
      induction ns with
      | nil => intro seen _; exact ⟨List.nodup_nil, by simp⟩
      | cons a ns ih =>
        intro seen h
        simp only [Aiur.findDuplicate] at h
        split at h
        · cases h
        · rename_i hnot
          obtain ⟨hn, hs⟩ := ih (a :: seen) h
          refine ⟨List.nodup_cons.mpr ⟨fun ha => hs a ha (by simp), hn⟩, fun y hy => ?_⟩
          rcases List.mem_cons.mp hy with rfl | hmem
          · simpa using hnot
          · intro hys; exact hs y hmem (by simp [hys])
    exact (aux _ [] hNodup).1
  clear hNodup
  induction ps generalizing off with
  | nil => intro _ h; cases h
  | cons hd rest ih =>
    rcases hd with ⟨name, val⟩
    simp only [List.map_cons, List.nodup_cons] at hnod
    intro p hp k hdrop
    cases k with
    | zero =>
      simp only [List.drop_zero, List.cons.injEq] at hdrop
      obtain ⟨rfl, _⟩ := hdrop
      simp [mkInputWires, WireValue.map]
    | succ k' =>
      simp only [List.drop_succ_cons] at hdrop
      have hp' : p ∈ rest := List.mem_of_mem_drop (hdrop ▸ List.mem_cons_self)
      have hne : (name == p.1) = false := by
        simp only [beq_eq_false_iff_ne]
        intro heq
        exact hnod.1 (List.mem_map.mpr ⟨p, hp', heq.symm⟩)
      simp only [mkInputWires, List.map_cons, List.zip_cons_cons, List.find?_cons, hne,
        List.take_succ_cons, List.flatMap_cons, List.length_append, FlatVal.words_length]
      have hrec := ih (off + val.width) hnod.2 p hp' k' hdrop
      simpa [Nat.add_assoc] using hrec

theorem compiler_function_eq (s : FlatAssertSpec F)
    (hNodup : Aiur.findDuplicate (s.params.map Prod.fst) [] = none) :
    Optimized.Compiler.function s.coreProgram minimalConfig s.coreFn true = .ok s.scopedChipRaw := by
  unfold Optimized.Compiler.function
  have hEn : s.coreProgram.enums = [] := rfl
  have hMapSnd : s.coreFn.params.map Prod.snd = s.params.map fun p => p.2.coreTy := by
    simp [coreFn, List.map_map, Function.comp_def]
  have hMapFst : s.coreFn.params.map Prod.fst = s.params.map Prod.fst := by
    simp [coreFn, List.map_map, Function.comp_def]
  simp only [hEn, hMapSnd, hMapFst, stateT_run_bind]
  rw [compiler_freshInputs s.params _ rfl]
  simp only [Array.size_empty]
  rw [show s.coreFn.result = (FlatVal.arr s.outConsts).coreTy from rfl]
  rw [compiler_freshValue_flat .output (.arr s.outConsts) _ (by simp)]
  simp only [Array.size_append, List.size_toArray, List.length_replicate, FlatVal.width]
  rw [compiler_validateParams s.params 0 _]
  dsimp only
  have hLoc := zip_names_mkInputWires 0 s.params hNodup
  rw [show s.coreFn.body = mkCoreBody s.outConsts s.params from rfl]
  rw [show (s.params.flatMap fun p => p.2.words).length = s.inConsts.length from rfl]
  simp only [List.length_nil, Nat.zero_add, FlatVal.coreTy]
  rw [compiler_lower_mkCoreBody s.coreProgram rfl s.coreFn.name _ s.outConsts s.inConsts.length s.params 0 _ hLoc]
  simp only [stateT_pure_run, bind, Except.bind, pure, Except.pure, Except.ok.injEq]
  unfold scopedChipRaw inputWireVars outputWireVars numVars allConsts inConsts
  congr 1
  · apply Array.toList_inj.mp
    simp only [Array.toList_append, List.nil_append]
  · apply Array.toList_inj.mp
    simp only [Array.toList_append, List.nil_append,
      Array.toList_replicate, List.length_append, List.replicate_add]
  · apply Array.toList_inj.mp
    simp only [Array.toList_append, List.nil_append,
      List.zipIdx_append, List.map_append, List.append_assoc, Nat.zero_add]

private theorem resolveAliasValues_eq (s : FlatAssertSpec F) :
    resolveAliasValues s.scopedChipRaw = .ok ((List.range s.numVars).toArray.map Aiur.Optimized.Polynomial.var) := by
  unfold resolveAliasValues
  have hSz : s.scopedChipRaw.roles.size = s.numVars := by
    simp [scopedChipRaw, numVars, allConsts]
  rw [hSz]
  have hNone : ∀ x ∈ (List.range s.numVars).reverse, s.scopedChipRaw.aliases[x]?.getD none = none := by
    intro x _
    simp only [scopedChipRaw]
    by_cases hx : x < s.numVars
    · simp [hx]
    · rw [Array.getElem?_eq_none (by simp; omega)]; rfl
  dsimp only
  simp only [pure_bind]
  rw [forIn_yield_const (m := Except String) (List.range s.numVars).reverse _ _ (fun x hx r => by
    simp [hNone x hx])]
  rfl

omit [Field F] [DecidableEq F] in
private theorem replacement_range_var (n : Nat) (id : Nat) :
    Degree.replacement ((List.range n).toArray.map Aiur.Optimized.Polynomial.var : Array (Aiur.Optimized.Polynomial F)) id = .var id := by
  unfold Degree.replacement
  by_cases h : id < n
  · simp [h]
  · rw [Array.getElem?_eq_none (by simp; omega)]; rfl

private theorem scopedChipRaw_subst_var (s : FlatAssertSpec F) :
    s.scopedChipRaw.substitute (Degree.replacement ((List.range s.numVars).toArray.map Aiur.Optimized.Polynomial.var)) =
      s.scopedChipAfterAlias := by
  have hrep : Degree.replacement ((List.range s.numVars).toArray.map Aiur.Optimized.Polynomial.var : Array (Aiur.Optimized.Polynomial F)) =
      Aiur.Optimized.Polynomial.var := funext (replacement_range_var s.numVars)
  rw [hrep]
  unfold ScopedChip.substitute scopedChipAfterAlias
  dsimp only
  have hScope : (s.scopedChipRaw.scopes.map fun scope =>
      { scope with activation := (scope.activation.subst Aiur.Optimized.Polynomial.var).simplify }) =
      s.scopedChipRaw.scopes := by
    simp [scopedChipRaw, Aiur.Optimized.Polynomial.subst, Aiur.Optimized.Polynomial.simplify]
  have hEq : (s.scopedChipRaw.equations.map fun eq =>
      { eq with polynomial := (eq.polynomial.subst Aiur.Optimized.Polynomial.var).simplify }) =
      ((s.allConsts.zipIdx.map fun (c, i) => (⟨0, subConstPoly i c⟩ : Equation F)) ++
        zeroEqs (s.params.length * s.outConsts.length)).toArray := by
    apply Array.toList_inj.mp
    simp only [scopedChipRaw, Array.toList_map, List.map_append,
      List.map_map, Function.comp_def]
    refine congrArg₂ (· ++ ·) ?_ ?_
    · apply List.map_congr_left
      rintro ⟨c, i⟩ _
      simp [Aiur.Optimized.Polynomial.subst, simplify_sub_var_const]
    · unfold trivialEqs zeroEqs
      rw [List.map_flatten, List.map_replicate, List.map_map]
      have h1 : (((List.range' s.inConsts.length s.outConsts.length).map
          (fun x => ({ scope := 0, polynomial := (Aiur.Optimized.Polynomial.subst Aiur.Optimized.Polynomial.var (.sub (.var x) (.var x))).simplify } : Equation F)))) =
          List.replicate s.outConsts.length (⟨0, .const 0⟩ : Equation F) := by
        apply List.ext_getElem (by simp)
        intro k hk1 hk2
        simp [Aiur.Optimized.Polynomial.subst, Aiur.Optimized.Polynomial.simplify, beq_var_self]
      simp only [Function.comp_def]
      rw [h1, List.flatten_replicate_replicate]
  rw [hScope, hEq]
  simp [scopedChipRaw]

private theorem degree_reduce_subConstPoly (v : Nat) (c : F) (st : Degree.State F) :
    (Degree.reduce 0 3 (subConstPoly v c)).run st = .ok (subConstPoly v c, st) := by
  by_cases hc : c = 0
  · subst hc; simp [subConstPoly, Degree.reduce]
  · simp [subConstPoly, hc, Degree.reduce, stateT_bind_run,
      stateT_pure_run, simplify_sub_var_const, bind, pure]

private theorem degree_boundState_eq (s : FlatAssertSpec F) :
    Degree.boundState minimalConfig s.scopedChipAfterAlias = .ok ⟨s.scopedChipNorm, []⟩ := by
  unfold Degree.boundState
  simp only [minimalConfig, show ¬ (3 < 3) by omega, ↓reduceIte, scopedChipAfterAlias,
    scopedChipRaw, ← Array.forIn_toList, List.forIn_cons, List.forIn_nil,
    Aiur.Optimized.Polynomial.degree, Scalar.Circuit.ArithExpr.degree, show ¬ (0 > 1) by omega,
    stateT_run_bind]
  have hZeroBeq : ((Aiur.Optimized.Polynomial.const 0 : Aiur.Optimized.Polynomial F) == .const 0) = true := by
    change ((0 : F) == 0) = true
    exact beq_self_eq_true (0 : F)
  have hForEqs : ∀ (body : Equation F → PUnit → StateT (Degree.State F) (Except String) (ForInStep PUnit))
      (l : List (F × Nat)) (st : Degree.State F),
      st.chip.scopes = #[⟨.const 1, []⟩] →
      (∀ (c : F) (i : Nat) (st' : Degree.State F), st'.chip.scopes = #[⟨.const 1, []⟩] →
        (body ⟨0, subConstPoly i c⟩ PUnit.unit).run st' =
          Except.ok (ForInStep.yield PUnit.unit,
            { st' with chip := { st'.chip with equations := st'.chip.equations.push ⟨0, subConstPoly i c⟩ } })) →
      (forIn (m := StateT (Degree.State F) (Except String))
        (l.map fun p => (⟨0, subConstPoly p.2 p.1⟩ : Equation F)) PUnit.unit body).run st =
      Except.ok (PUnit.unit, { st with chip := { st.chip with
        equations := st.chip.equations ++ (l.map fun p => (⟨0, subConstPoly p.2 p.1⟩ : Equation F)).toArray } }) := by
    intro body l
    induction l with
    | nil => intro st _ _; simp
    | cons hd rest ih =>
      intro st hsc hstep
      rcases hd with ⟨c, i⟩
      simp only [List.map_cons, List.forIn_cons, stateT_run_bind]
      rw [hstep c i st hsc]
      dsimp only
      rw [ih { st with chip := { st.chip with equations := st.chip.equations.push ⟨0, subConstPoly i c⟩ } } hsc hstep]
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and]
      congr 1; congr 1; apply Array.toList_inj.mp; simp
  have hForZeroEqs : ∀ (body : Equation F → PUnit → StateT (Degree.State F) (Except String) (ForInStep PUnit))
      (k : Nat) (st : Degree.State F),
      (∀ (st' : Degree.State F), (body ⟨0, .const 0⟩ PUnit.unit).run st' = Except.ok (ForInStep.yield PUnit.unit, st')) →
      (forIn (m := StateT (Degree.State F) (Except String)) (zeroEqs (F := F) k) PUnit.unit body).run st =
        Except.ok (PUnit.unit, st) := by
    intro body k
    induction k with
    | zero => intro st _; rfl
    | succ k ih =>
      intro st hstep
      simp only [zeroEqs, List.replicate_succ, List.forIn_cons, stateT_run_bind]
      rw [hstep st]
      exact ih st hstep
  have hScopeGet : ∀ n : Nat,
      (#[({ activation := Aiur.Optimized.Polynomial.const 1, path := [] } : Scope F)])[n]? =
        if n < 1 then some ⟨.const 1, []⟩ else none := by
    intro n
    cases n with
    | zero => rfl
    | succ m =>
      rw [Array.getElem?_eq_none (by simp)]
      simp
  simp only [hScopeGet, pure_bind]
  rw [forIn_append_yield (m := StateT (Degree.State F) (Except String)) _ _ _ _ (fun eq heq _ => by
    obtain ⟨⟨c, i⟩, _, rfl⟩ := List.mem_map.mp heq
    refine ⟨do
      let expr ← Degree.reduce 0 (3 - Circuit.ArithExpr.degree (⟨.const 1, []⟩ : Scope F).activation) (subConstPoly i c)
      Degree.emit 0 expr, ?_⟩
    simp only [show (0 : Nat) < 1 by omega, ↓reduceIte, map_eq_pure_bind, bind_assoc])]
  rw [stateT_run_bind]
  rw [hForEqs _ s.allConsts.zipIdx _ rfl (fun c i st' _ => by
    simp only [show (0 : Nat) < 1 by omega, ↓reduceIte, stateT_run_bind]
    rw [show (3 - Circuit.ArithExpr.degree (⟨.const 1, []⟩ : Scope F).activation) = 3 from rfl,
      degree_reduce_subConstPoly]
    dsimp only
    have hemit : (Degree.emit (F := F) 0 (subConstPoly i c)).run st' =
        Except.ok ((), { st' with chip := { st'.chip with equations := st'.chip.equations.push ⟨0, subConstPoly i c⟩ } }) := by
      unfold Degree.emit
      simp only [simplify_subConstPoly, subConstPoly_beq_zero, Bool.false_eq_true, ↓reduceIte,
        stateT_run_bind, stateT_run_pure]
      rfl
    rw [hemit]
    rfl)]
  dsimp only
  rw [hForZeroEqs _ (s.params.length * s.outConsts.length) _ (fun st' => by
    simp only [show (0 : Nat) < 1 by omega, ↓reduceIte, stateT_run_bind]
    rw [show (3 - Circuit.ArithExpr.degree (⟨.const 1, []⟩ : Scope F).activation) = 3 from rfl]
    simp only [Degree.reduce, Degree.emit, Aiur.Optimized.Polynomial.simplify, hZeroBeq,
      ↓reduceIte, stateT_run_pure])]
  simp only [Array.mapM_empty,     modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.run, StateT.pure,
    bind, Except.bind, pure, Except.pure, Except.ok.injEq, scopedChipNorm, scopedChipRaw]
  congr 1
  congr 1
  apply Array.toList_inj.mp
  simp

private theorem allocateColumns_eq (s : FlatAssertSpec F) :
    allocateColumns minimalConfig s.scopedChipNorm = s.colLayout := by
  have hSz : s.scopedChipNorm.roles.size = s.numVars := by
    simp [scopedChipNorm, scopedChipRaw, numVars, allConsts]
  have hAlias : ∀ id : Nat, s.scopedChipNorm.aliases[id]?.getD none = none := by
    intro id
    simp only [scopedChipNorm, scopedChipRaw]
    by_cases h : id < s.numVars
    · simp [h]
    · rw [Array.getElem?_eq_none (by simp; omega)]; rfl
  have hNotAux : ∀ id (hid : id < s.numVars),
      s.scopedChipNorm.roles[id]? = some (if id < s.inConsts.length then Optimized.Role.input else Optimized.Role.output) := by
    intro id hid
    simp only [scopedChipNorm, scopedChipRaw, numVars, allConsts, List.length_append] at hid ⊢
    rw [List.getElem?_toArray, List.getElem?_append]
    by_cases h : id < s.inConsts.length
    · simp [h]
    · have h2 : id - s.inConsts.length < s.outConsts.length := by omega
      simp [h, h2]
  unfold allocateColumns
  simp only [hSz, Id.run, pure]
  -- Loop 1 populates `columnOf[0..k-1] = some i` and `occupants = [[0], ..., [k-1]]`
  have hLoop1 : ∀ k (hk : k ≤ s.numVars),
      (forIn (m := Id) (List.range k)
        (⟨Array.replicate s.numVars none, #[]⟩ : ColumnLayout) fun id layout =>
        if (s.scopedChipNorm.aliases[id]?.getD none).isNone then
          match s.scopedChipNorm.roles[id]? with
          | some (Optimized.Role.auxiliary _) => ForInStep.yield layout
          | some _ =>
            ForInStep.yield {
              columnOf := layout.columnOf.set! id (some layout.occupants.size)
              occupants := layout.occupants.push [id] }
          | none => ForInStep.yield layout
        else ForInStep.yield layout) =
      ⟨((List.range k).map some ++ List.replicate (s.numVars - k) none).toArray,
       (List.range k).toArray.map fun i => [i]⟩ := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [List.range_zero, List.forIn_nil, pure]
      congr 1
      apply Array.toList_inj.mp; simp
    | succ k ih =>
      intro hk
      rw [List.range_succ, forIn_append_yield (m := Id) _ _ _ _ (fun (id : Nat) _ layout => by
        by_cases ha : (s.scopedChipNorm.aliases[id]?.getD none).isNone
        · simp only [ha, ↓reduceIte]
          cases s.scopedChipNorm.roles[id]? with
          | none => exact ⟨layout, rfl⟩
          | some r => cases r <;> exact ⟨_, rfl⟩
        · simp only [ha, Bool.false_eq_true, ↓reduceIte]; exact ⟨layout, rfl⟩)]
      simp only [bind]
      rw [ih (by omega)]
      simp only [List.forIn_cons, List.forIn_nil, hAlias, Option.isNone_none,
        ↓reduceIte, hNotAux k (by omega), bind, pure]
      by_cases hlt : k < s.inConsts.length <;>
      · simp only [hlt, ↓reduceIte]
        congr 1
        · apply Array.toList_inj.mp
          simp only [Array.size_map, List.size_toArray, List.length_range, Array.set!_eq_setIfInBounds,
            Array.toList_setIfInBounds, List.map_append,
            List.map_singleton]
          rw [show s.numVars - k = (s.numVars - (k + 1)) + 1 by omega, List.replicate_succ,
            List.set_append]
          simp [List.append_assoc]
        · apply Array.toList_inj.mp
          simp []
  have h1 := hLoop1 s.numVars le_rfl
  simp only [Nat.sub_self, List.replicate_zero, List.append_nil] at h1
  -- Rewrite loop 1 and loop 2
  have h2 : ∀ (xs : List Nat) (_hxs : ∀ id ∈ xs, id < s.numVars) (acc : ColumnLayout) (live : Std.HashSet Witness),
      (forIn (m := Id) xs acc fun id layout =>
        match s.scopedChipNorm.roles[id]? with
        | some (Optimized.Role.auxiliary _) =>
          if !live.contains id then ForInStep.yield layout
          else
            if (if minimalConfig.shareAuxiliaries then
                layout.occupants.toList.findIdx (fun occupants => occupants.all (s.scopedChipNorm.canShare id))
                else layout.occupants.size) < layout.occupants.size then
              ForInStep.yield {
                columnOf := layout.columnOf.set! id (some (if minimalConfig.shareAuxiliaries then
                  layout.occupants.toList.findIdx (fun occupants => occupants.all (s.scopedChipNorm.canShare id))
                  else layout.occupants.size))
                occupants := layout.occupants.modify (if minimalConfig.shareAuxiliaries then
                  layout.occupants.toList.findIdx (fun occupants => occupants.all (s.scopedChipNorm.canShare id))
                  else layout.occupants.size) (id :: ·) }
            else
              ForInStep.yield {
                columnOf := layout.columnOf.set! id (some layout.occupants.size)
                occupants := layout.occupants.push [id] }
        | _ => ForInStep.yield layout) = acc := by
    intro xs
    induction xs with
    | nil => intro _ acc _; rfl
    | cons x rest ih =>
      intro hxs acc live
      have hx := hNotAux x (hxs x List.mem_cons_self)
      simp only [List.forIn_cons, hx, bind, pure]
      by_cases hlt : x < s.inConsts.length
      · simp only [hlt, ↓reduceIte]
        exact ih (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) acc live
      · simp only [hlt, ↓reduceIte]
        exact ih (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) acc live
  simp only [bind]
  erw [h1]
  erw [h2 (List.range s.numVars) (fun _ h => List.mem_range.mp h)]
  unfold colLayout
  congr 1
  apply Array.toList_inj.mp
  simp

omit [Field F] [DecidableEq F] in
private theorem colLayout_column (s : FlatAssertSpec F) {i : Nat} (hi : i < s.numVars) :
    s.colLayout.column i = i := by
  simp [ColumnLayout.column, colLayout, hi]

private theorem emitChip_eq (s : FlatAssertSpec F) :
    emitChip s.scopedChipNorm s.colLayout = s.physChip := by
  have hlen : s.inConsts.length + s.outConsts.length = s.numVars := by
    simp [numVars, allConsts]
  have hInp : s.scopedChipNorm.inputs.map (WireValue.map s.colLayout.column) = s.inputWireVars := by
    change s.inputWireVars.map (WireValue.map s.colLayout.column) = s.inputWireVars
    have aux : ∀ (off : Nat) (ps : List (String × FlatVal F)),
        off + (ps.flatMap fun p => p.2.words).length ≤ s.numVars →
        (mkInputWires off ps).map (WireValue.map s.colLayout.column) = mkInputWires off ps := by
      intro off ps
      induction ps generalizing off with
      | nil => intro _; rfl
      | cons hd rest ih =>
        intro hle
        rcases hd with ⟨_, val⟩
        simp only [mkInputWires, List.map_cons, WireValue.map, List.cons.injEq]
        refine ⟨?_, ih (off + val.width) (by
          simp only [List.flatMap_cons, List.length_append, FlatVal.words_length] at hle; omega)⟩
        congr 1
        conv_rhs => rw [← List.map_id (List.range' off val.width)]
        apply List.map_congr_left
        intro x hx
        rw [List.mem_range'] at hx
        obtain ⟨k, hk, rfl⟩ := hx
        exact colLayout_column s (by
          simp only [List.flatMap_cons, List.length_append, FlatVal.words_length] at hle; omega)
    exact aux 0 s.params (by simp only [inConsts] at hlen; omega)
  have hOut : s.scopedChipNorm.output.map
        ((Aiur.Optimized.Polynomial.var : Nat → Aiur.Optimized.Polynomial F) ∘ s.colLayout.column) =
      ⟨s.resultCoreTy, (List.range' s.inConsts.length s.outConsts.length).map
        (Aiur.Optimized.Polynomial.var : Nat → Aiur.Optimized.Polynomial F)⟩ := by
    simp only [scopedChipNorm, scopedChipRaw, outputWireVars, WireValue.map]
    congr 1
    apply List.map_congr_left
    intro x hx
    rw [List.mem_range'] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    simp only [Nat.one_mul, Function.comp_apply]
    rw [colLayout_column s (i := s.inConsts.length + k) (by omega)]
  have hCon : s.scopedChipNorm.equations.toList.filterMap (fun eq =>
      let polynomial := Aiur.Optimized.Polynomial.simplify (.mul (s.colLayout.expression (s.scopedChipNorm.activation eq.scope))
        (s.colLayout.expression eq.polynomial))
      if polynomial == .const 0 then none else some polynomial) =
      s.allConsts.zipIdx.map fun (c, i) => subConstPoly i c := by
    simp only [scopedChipNorm, List.toList_toArray]
    have hmap : ∀ (l : List (F × Nat)), (∀ p ∈ l, p.2 < s.numVars) →
        (l.map fun (c, i) => (⟨0, subConstPoly i c⟩ : Equation F)).filterMap (fun eq =>
          let polynomial := Aiur.Optimized.Polynomial.simplify (.mul (s.colLayout.expression (s.scopedChipNorm.activation eq.scope))
            (s.colLayout.expression eq.polynomial))
          if polynomial == .const 0 then none else some polynomial) =
        l.map fun (c, i) => subConstPoly i c := by
      intro l
      induction l with
      | nil => intro _; rfl
      | cons hd rest ih =>
        intro hl
        rcases hd with ⟨c, i⟩
        have hi := hl (c, i) List.mem_cons_self
        have hact : s.colLayout.expression (s.scopedChipNorm.activation 0) = .const 1 := by
          simp [ColumnLayout.expression, ScopedChip.activation, scopedChipNorm, scopedChipRaw,
            Aiur.Optimized.Polynomial.subst, Aiur.Optimized.Polynomial.simplify]
        have hexpr : s.colLayout.expression (subConstPoly i c) = subConstPoly i c := by
          by_cases hc : c = 0
          · simp [ColumnLayout.expression, subConstPoly, hc, Aiur.Optimized.Polynomial.subst,
              colLayout_column s hi, Aiur.Optimized.Polynomial.simplify]
          · simp [ColumnLayout.expression, subConstPoly, hc, Aiur.Optimized.Polynomial.subst,
              colLayout_column s hi, simplify_sub_var_const]
        simp only [List.map_cons, List.filterMap_cons, hact, hexpr,
          simplify_mul_one_subConstPoly, subConstPoly_beq_zero, Bool.false_eq_true, ↓reduceIte,
          ih (fun p hp => hl p (List.mem_cons_of_mem _ hp))]
    exact hmap _ (fun p hp => by have := List.mem_zipIdx hp; simp only [numVars]; omega)
  unfold emitChip
  simp only [Id.run, pure, hInp, hOut, hCon]
  simp only [scopedChipNorm, scopedChipRaw, colLayout, physChip, Array.size_map, List.size_toArray,
    List.length_range, Array.toList_empty, List.map_nil]

private theorem physChip_degree_bounds (s : FlatAssertSpec F) :
    s.physChip.stats.maxConstraintDegree ≤ 3 ∧
    s.physChip.stats.maxLookupDegree ≤ 1 ∧
    s.physChip.maxLookupGuardDegree ≤ 1 := by
  have hfold : ∀ (l : List (ArithExpr F)) (acc : Nat), acc ≤ 1 → (∀ e ∈ l, e.degree ≤ 1) →
      l.foldl (fun largest expr => max largest expr.degree) acc ≤ 1 := by
    intro l
    induction l with
    | nil => intro acc ha _; exact ha
    | cons e rest ih =>
      intro acc ha hall
      exact ih (max acc e.degree) (Nat.max_le.mpr ⟨ha, hall e List.mem_cons_self⟩)
        (fun x hx => hall x (List.mem_cons_of_mem _ hx))
  have hCon : Circuit.ArithExpr.maxDegree s.physChip.constraints ≤ 1 := by
    apply hfold _ 0 (by omega)
    intro e he
    simp only [physChip, List.mem_map] at he
    obtain ⟨⟨c, i⟩, _, rfl⟩ := he
    exact le_of_eq (subConstPoly_degree i c)
  have hOut : Circuit.ArithExpr.maxDegree s.physChip.output.words ≤ 1 := by
    apply hfold _ 0 (by omega)
    intro e he
    simp only [physChip, List.mem_map] at he
    obtain ⟨w, _, rfl⟩ := he
    simp [Circuit.ArithExpr.degree, Scalar.Circuit.ArithExpr.degree]
  refine ⟨by simpa [Circuit.Chip.stats] using Nat.le_trans hCon (by decide), ?_, ?_⟩
  · simp only [Circuit.Chip.stats, physChip, List.map_nil, List.foldl_nil, Nat.max_zero] at hOut ⊢
    by_cases h : (List.flatMap WireValue.words s.inputWireVars).isEmpty = true
    · simp only [h, ↓reduceIte]; omega
    · simp only [h, Bool.false_eq_true, ↓reduceIte]; omega
  · simp [Circuit.Chip.maxLookupGuardDegree, physChip, Circuit.ArithExpr.maxDegree]

private theorem degreeChecked_eq {src : ScopedChip F} {a b : Degree.Checked src}
    (h : a.chip = b.chip) : a = b := by
  cases a; cases b; cases h; rfl

private theorem layOut_minimalConfig_eq (s : FlatAssertSpec F) :
    layOut minimalConfig s.scopedChipRaw = .ok ⟨s.scopedChipNorm, s.colLayout, s.physChip⟩ := by
  unfold layOut checkedLayOut
  have hAliasCert : Alias.Certificate s.scopedChipRaw
      ((List.range s.numVars).toArray.map Aiur.Optimized.Polynomial.var) := by
    have hSz : s.scopedChipRaw.roles.size = s.numVars := by
      simp [scopedChipRaw, numVars, allConsts]
    refine ⟨by simp [hSz], ?_, ?_⟩
    · intro id _; exact replacement_range_var s.numVars id
    · intro id _; exact Or.inl (replacement_range_var s.numVars id)
  have hAlias : Alias.checkedResolve s.scopedChipRaw =
      .ok ⟨s.scopedChipAfterAlias, scopedChipRaw_subst_var s ▸ hAliasCert.equivalent, rfl, rfl, rfl⟩ := by
    unfold Alias.checkedResolve
    simp only [resolveAliasValues_eq, bind, Except.bind, pure, Except.pure, hAliasCert, ↓reduceDIte]
    congr 1
    exact degreeChecked_eq (scopedChipRaw_subst_var s)
  have hDegCert : Degree.Certificate s.scopedChipAfterAlias s.scopedChipNorm []
      (Degree.expand s.scopedChipNorm.roles.size ([] : List (Degree.Definition F))) := by
    have hSz : s.scopedChipNorm.roles.size = s.numVars := by
      simp [scopedChipNorm, scopedChipRaw, numVars, allConsts]
    have hExp : Degree.expand s.scopedChipNorm.roles.size ([] : List (Degree.Definition F)) =
        (List.range s.numVars).toArray.map Aiur.Optimized.Polynomial.var := by
      simp [Degree.expand, hSz]
    have hRep : ∀ id, Degree.replacement (Degree.expand s.scopedChipNorm.roles.size ([] : List (Degree.Definition F))) id = .var id := by
      intro id; rw [hExp]; exact replacement_range_var s.numVars id
    have hSubVar : ∀ p : Aiur.Optimized.Polynomial F,
        p.subst (Degree.replacement (Degree.expand s.scopedChipNorm.roles.size ([] : List (Degree.Definition F)))) = p := by
      intro p
      have hf : Degree.replacement (Degree.expand s.scopedChipNorm.roles.size ([] : List (Degree.Definition F))) = Aiur.Optimized.Polynomial.var :=
        funext hRep
      rw [hf]
      induction p with
      | const _ => rfl
      | var _ => rfl
      | add a b iha ihb => simp [Aiur.Optimized.Polynomial.subst, iha, ihb]
      | sub a b iha ihb => simp [Aiur.Optimized.Polynomial.subst, iha, ihb]
      | mul a b iha ihb => simp [Aiur.Optimized.Polynomial.subst, iha, ihb]
    have hBase : s.scopedChipAfterAlias.roles.size = s.numVars := by
      simp [scopedChipAfterAlias, scopedChipRaw, numVars, allConsts]
    refine ⟨rfl, rfl, rfl, rfl, fun id _ => hRep id, ?_, ?_, (fun _ h => nomatch h), ?_, ?_,
      rfl, (fun _ h => nomatch h), rfl, (fun _ h => nomatch h)⟩
    · intro id hid
      rw [hBase]
      simp only [scopedChipAfterAlias, scopedChipRaw, List.mem_append] at hid
      rcases hid with hin | hout
      · rw [inputWireVars, mkInputWires_flatMap, List.mem_range'] at hin
        obtain ⟨k, hk, rfl⟩ := hin
        simp only [numVars, allConsts, inConsts, List.length_append] at hk ⊢
        exact (by omega : 0 + 1 * k < (List.flatMap (fun p => p.2.words) s.params).length + s.outConsts.length)
      · simp only [outputWireVars, List.mem_range'] at hout
        obtain ⟨k, hk, rfl⟩ := hout
        simp only [numVars, allConsts, List.length_append]
        exact (by omega : s.inConsts.length + 1 * k < s.inConsts.length + s.outConsts.length)
    · intro sc hsc id hid
      simp [scopedChipAfterAlias, scopedChipRaw] at hsc hid
      obtain ⟨rfl⟩ := hsc
      simp [Aiur.Optimized.Polynomial.vars] at hid
    · intro eq heq
      simp only [scopedChipAfterAlias, List.toList_toArray, List.mem_append] at heq
      rcases heq with h1 | h2
      · right
        obtain ⟨⟨c, i⟩, hi, rfl⟩ := List.mem_map.mp h1
        have hlt : i < s.numVars := by have := List.mem_zipIdx hi; simp only [numVars]; omega
        refine ⟨⟨0, subConstPoly i c⟩, ?_, rfl, ?_, ?_⟩
        · simp only [scopedChipNorm, List.toList_toArray]
          exact List.mem_map.mpr ⟨(c, i), hi, rfl⟩
        · intro id hid
          rw [subConstPoly_vars] at hid
          simp only [List.mem_singleton] at hid
          subst hid; exact Or.inl (by rw [hBase]; exact hlt)
        · rw [hSubVar]; rfl
      · left
        have heq0 : eq = ⟨0, .const 0⟩ := List.eq_of_mem_replicate h2
        rw [heq0]; rfl
    · intro eq heq
      right
      refine ⟨eq, ?_, rfl, ?_⟩
      · simp only [scopedChipNorm, scopedChipAfterAlias, List.toList_toArray] at heq ⊢
        exact List.mem_append_left _ heq
      · rw [hSubVar]; rfl
  have hDeg : Degree.checkedBound minimalConfig s.scopedChipAfterAlias =
      .ok ⟨s.scopedChipNorm, hDegCert.equivalent, rfl, rfl, rfl⟩ := by
    unfold Degree.checkedBound Degree.certify
    simp only [degree_boundState_eq, bind, Except.bind, pure, Except.pure, hDegCert, ↓reduceDIte]
  have hWellScoped : s.scopedChipNorm.wellScoped = true := by
    have hNotAux : ∀ id (hid : id < s.numVars),
        s.scopedChipNorm.roles[id]? = some (if id < s.inConsts.length then Optimized.Role.input else Optimized.Role.output) := by
      intro id hid
      simp only [scopedChipNorm, scopedChipRaw, numVars, allConsts, List.length_append] at hid ⊢
      rw [List.getElem?_toArray, List.getElem?_append]
      by_cases h : id < s.inConsts.length
      · simp [h]
      · have h2 : id - s.inConsts.length < s.outConsts.length := by omega
        simp [h, h2]
    unfold ScopedChip.wellScoped
    simp only [Bool.and_eq_true, Array.all_eq_true_iff_forall_mem, scopedChipNorm, scopedChipRaw]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · intro sc hsc
      simp only [List.mem_toArray, List.mem_singleton] at hsc
      subst hsc
      simp [Aiur.Optimized.Polynomial.vars]
    · intro eq heq
      rw [List.mem_toArray] at heq
      obtain ⟨⟨c, i⟩, hi, rfl⟩ := List.mem_map.mp heq
      have hlt : i < s.numVars := by have := List.mem_zipIdx hi; simp only [numVars]; omega
      unfold ScopedChip.owns
      simp only [subConstPoly_vars, List.all_cons, List.all_nil, Bool.and_true]
      have hr := hNotAux i hlt
      simp only [scopedChipNorm, scopedChipRaw] at hr
      rw [hr]
      split_ifs <;> rfl
    · intro c hc; simp at hc
    · intro c hc; simp at hc
  have hAllocCert : Allocation.Certificate s.scopedChipNorm s.colLayout := by
    have hCtrl : Control.Certificate s.scopedChipNorm := by
      refine ⟨rfl, (fun _ h => nomatch h), ?_⟩
      intro id hid
      simp only [scopedChipNorm, scopedChipRaw, List.size_toArray, List.length_singleton,
        List.range_one, List.mem_singleton] at hid
      subst hid
      simp [Control.ParentChecked, scopedChipNorm, scopedChipRaw]
    have hOccLt : ∀ site ∈ Allocation.occurrences s.scopedChipNorm, site.1 < s.numVars := by
      intro site hsite
      simp only [Allocation.occurrences, Allocation.sites, scopedChipNorm, scopedChipRaw,
        List.toList_toArray, List.flatMap_nil, List.append_nil,
        List.mem_append, List.mem_map, List.mem_flatMap] at hsite
      rcases hsite with (⟨x, hx, rfl⟩ | ⟨sc, hsc, hx⟩) | ⟨eq, heq, hx⟩
      · rcases hx with ⟨w, hw, hxw⟩ | hout
        · have hin : x ∈ s.inputWireVars.flatMap WireValue.words := List.mem_flatMap.mpr ⟨w, hw, hxw⟩
          rw [inputWireVars, mkInputWires_flatMap, List.mem_range'] at hin
          obtain ⟨k, hk, rfl⟩ := hin
          dsimp only
          simp only [numVars, allConsts, inConsts, List.length_append] at hk ⊢
          exact (by omega : 0 + 1 * k < (List.flatMap (fun p => p.2.words) s.params).length + s.outConsts.length)
        · simp only [outputWireVars, List.mem_range'] at hout
          obtain ⟨k, hk, rfl⟩ := hout
          dsimp only
          simp only [numVars, allConsts, List.length_append]
          exact (by omega : s.inConsts.length + 1 * k < s.inConsts.length + s.outConsts.length)
      · simp only [List.mem_singleton] at hsc; subst hsc
        simp only [show Aiur.Optimized.Polynomial.vars (.const 1 : Aiur.Optimized.Polynomial F) = [] from rfl,
          List.not_mem_nil, false_and, exists_false] at hx
      · obtain ⟨⟨c, i⟩, hi, rfl⟩ := heq
        obtain ⟨x, hx', rfl⟩ := hx
        rw [subConstPoly_vars, List.mem_singleton] at hx'
        subst hx'
        dsimp only
        simpa [numVars] using (List.mem_zipIdx hi).2.1
    have hOccOwn : ∀ site ∈ Allocation.occurrences s.scopedChipNorm, Allocation.Owned s.scopedChipNorm site := by
      intro site hsite
      have hlt : (site.1 : Nat) < s.numVars := hOccLt site hsite
      unfold Allocation.Owned
      have hr : s.scopedChipNorm.roles[site.1]? =
          some (if site.1 < s.inConsts.length then Optimized.Role.input else Optimized.Role.output) := by
        simp only [scopedChipNorm, scopedChipRaw, numVars, allConsts, List.length_append] at hlt ⊢
        rw [List.getElem?_toArray, List.getElem?_append]
        by_cases h : site.1 < s.inConsts.length
        · simp [h]
        · have h2 : (site.1 : Nat) - s.inConsts.length < s.outConsts.length :=
            Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt h) hlt
          simp [h, h2]
      rw [hr]
      split_ifs <;> trivial
    refine ⟨hCtrl, ?_, ?_⟩
    · intro site hsite
      have hlt := hOccLt site hsite
      refine ⟨?_, hOccOwn site hsite⟩
      rw [colLayout_column s hlt]
      simp [colLayout, hlt]
    · intro i hi j hj hcol
      have hilt : i < s.numVars := by
        have hm := List.mem_eraseDups.mp hi
        obtain ⟨site, hsite, rfl⟩ := List.mem_map.mp hm
        exact hOccLt site hsite
      have hjlt : j < s.numVars := by
        have hm := List.mem_eraseDups.mp hj
        obtain ⟨site, hsite, rfl⟩ := List.mem_map.mp hm
        exact hOccLt site hsite
      rw [colLayout_column s hilt, colLayout_column s hjlt] at hcol
      exact Or.inl hcol
  have hwf := s.physChip_wellFormed
  have hdeg := s.physChip_degree_bounds
  have hLook : LookupMerging.run minimalConfig s.scopedChipNorm s.colLayout =
      Propagation.Checked.identity (emitChip s.scopedChipNorm s.colLayout) := by
    unfold LookupMerging.run
    simp [minimalConfig]
  have hps : minimalConfig.propagateScopes = false := rfl
  have hpv : minimalConfig.propagateValues = false := rfl
  have hml : minimalConfig.mergeLookups = false := rfl
  have hmd : minimalConfig.maxDegree = 3 := rfl
  have hPropIdChip : (Propagation.Checked.identity (emitChip s.scopedChipNorm s.colLayout)).chip =
      emitChip s.scopedChipNorm s.colLayout := rfl
  have hDeg' : ∃ d : Degree.Checked
      (if minimalConfig.simplifyConstraints = true then
          ConstraintElimination.run (ScopedPropagation.identity s.scopedChipAfterAlias).chip
        else ScopedPropagation.identity (ScopedPropagation.identity s.scopedChipAfterAlias).chip).chip,
      Degree.checkedBound minimalConfig
        (if minimalConfig.simplifyConstraints = true then
            ConstraintElimination.run (ScopedPropagation.identity s.scopedChipAfterAlias).chip
          else ScopedPropagation.identity (ScopedPropagation.identity s.scopedChipAfterAlias).chip).chip = .ok d ∧
      d.chip = s.scopedChipNorm :=
    ⟨_, hDeg, rfl⟩
  obtain ⟨dg, hdg, hdgChip⟩ := hDeg'
  have hFinalChip :
      (Propagation.Checked.identity
        (LookupMerging.run minimalConfig dg.chip (allocateColumns minimalConfig dg.chip)).chip).chip =
      s.physChip := by
    rw [hdgChip, allocateColumns_eq, hLook, hPropIdChip, emitChip_eq]; rfl
  have hDegFalse :
      (decide (s.physChip.stats.maxConstraintDegree > 3) ||
       decide (s.physChip.stats.maxLookupDegree > 1) ||
       decide (s.physChip.maxLookupGuardDegree > 1)) = false := by
    have h1 := hdeg.1; have h2 := hdeg.2.1; have h3 := hdeg.2.2
    simp [show ¬ (s.physChip.stats.maxConstraintDegree > 3) by omega,
      show ¬ (s.physChip.stats.maxLookupDegree > 1) by omega,
      show ¬ (s.physChip.maxLookupGuardDegree > 1) by omega]
  simp only [hAlias, hps, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure]
  rw [hdg]
  simp only [hdgChip, hpv, hml, hmd, hWellScoped, allocateColumns_eq,
    emitChip_eq, hAllocCert, hFinalChip, hwf, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    ↓reduceDIte, hDegFalse, Except.map]

omit [Field F] [DecidableEq F] in
private theorem chip_rename_self (chip : Circuit.Chip F) :
    chip.rename (Dedup.rename [(chip.name, chip.name)]) = chip := by
  cases chip with
  | mk name inputs output numVars constraints sends memory =>
    have hren : Dedup.rename [(name, name)] name = name := by simp [Dedup.rename]
    simp only [Circuit.Chip.rename, hren]
    congr 1
    induction sends with
    | nil => rfl
    | cons sd rest ih =>
      simp only [List.map_cons, List.cons.injEq]
      refine ⟨?_, ih⟩
      cases sd with
      | mk channel args result enable =>
        simp only [Circuit.Send.mk.injEq, and_true]
        by_cases h : channel = name
        · simp [Dedup.rename, h]
        · have hne : (name == channel) = false := beq_false_of_ne (Ne.symm h)
          simp [Dedup.rename, hne]

omit [DecidableEq F] in
private theorem dedup_identity_cert (sys : Circuit.System F) (chip : Circuit.Chip F)
    (hSys : sys = ⟨[chip], [], [], []⟩) (hWf : chip.wellFormed = true) :
    Dedup.Certificate sys sys (Dedup.identity sys).representatives [chip.name] := by
  subst hSys
  refine ⟨?_, ?_, ?_, rfl, (fun _ h => nomatch h), rfl, ?_, ?_, ?_⟩
  · intro p hp
    simp only [Dedup.identity, List.map_cons, List.map_nil, List.mem_singleton] at hp
    subst hp; simp [Circuit.System.findChip?]
  · intro c hc
    simp only [List.mem_singleton] at hc
    rw [hc]
    have hren : Dedup.rename [(chip.name, chip.name)] chip.name = chip.name := by
      simp [Dedup.rename]
    simp [Dedup.identity, hren, chip_rename_self, Circuit.System.findChip?]
  · intro c hc
    simp only [List.mem_singleton] at hc
    rw [hc]; simp [Circuit.System.findChip?]
  · simp [Circuit.checkChips, hWf, bind, Except.bind, pure, Except.pure]
  · simp [Circuit.checkChips, hWf, bind, Except.bind, pure, Except.pure]
  · intro e he
    simp only [List.mem_singleton] at he
    subst he; simp [Dedup.identity, Dedup.rename]

def artifact (s : FlatAssertSpec F) : Optimized.Artifact F where
  config := minimalConfig
  entries := [s.fnName]
  layouts := [⟨s.scopedChipNorm, s.colLayout, s.physChip⟩]
  system := ⟨[s.physChip], [], [], []⟩
  representatives := [(s.fnName, s.fnName)]
  unmerged := ⟨[s.physChip], [], [], []⟩
  deduplication := dedup_identity_cert ⟨[s.physChip], [], [], []⟩ s.physChip rfl s.physChip_wellFormed
  degreeBound := by
    intro chip hchip
    simp only [List.mem_singleton] at hchip
    subst hchip
    have h := s.physChip_degree_bounds
    exact ⟨h.1, Nat.le_trans h.2.1 (by decide : 1 ≤ 2), h.2.2⟩

theorem compile_eq (s : FlatAssertSpec F)
    (hNodup : Aiur.findDuplicate (s.params.map Prod.fst) [] = none) :
    Optimized.compile s.coreProgram [s.fnName] minimalConfig = .ok s.artifact := by
  rw [Optimized.compile, parMapM_eq_mapM]
  have htc := s.coreProgram_typecheck hNodup
  have hce := s.checkEntry_coreProgram
  have hfn := s.compiler_function_eq hNodup
  have hlo := s.layOut_minimalConfig_eq
  let initSys : Circuit.System F :=
    ⟨([({ logical := s.scopedChipNorm, layout := s.colLayout, chip := s.physChip } : Optimized.LaidOutChip F)]).map (·.chip),
      s.coreProgram.enums, s.coreProgram.tables, s.coreProgram.maps⟩
  have hded : Dedup.certify initSys [s.fnName] (Dedup.identity initSys) =
      .ok { toResult := Dedup.identity initSys,
            certificate := dedup_identity_cert initSys s.physChip rfl s.physChip_wellFormed } := by
    unfold Dedup.certify
    have hcert : Dedup.Certificate initSys (Dedup.identity initSys).system
        (Dedup.identity initSys).representatives [s.fnName] :=
      dedup_identity_cert initSys s.physChip rfl s.physChip_wellFormed
    simp only [hcert, ↓reduceDIte]
  have hcc : Circuit.checkChips [] [s.physChip] = .ok () := by
    simp [Circuit.checkChips, s.physChip_wellFormed, bind, Except.bind, pure, Except.pure]
  have hdb : ([s.physChip].all fun chip =>
      decide (chip.stats.maxConstraintDegree ≤ 3 ∧ chip.stats.maxLookupDegree ≤ 2 ∧
        chip.maxLookupGuardDegree ≤ 1)) = true := by
    have h := s.physChip_degree_bounds
    simp [h.1, Nat.le_trans h.2.1 (by decide : 1 ≤ 2), h.2.2]
  have hfind : s.coreProgram.findFunction? s.fnName = some s.coreFn := by
    simp [coreProgram, Aiur.Program.findFunction?, coreFn]
  have hCfgD : minimalConfig.maxDegree = 3 ∧ minimalConfig.deduplicate = false := ⟨rfl, rfl⟩
  have hForIn : ∀ (α : Type) (xs : List α) (_ : xs = [])
      (f : α → PUnit → Except String (ForInStep PUnit)),
      forIn (m := Except String) xs PUnit.unit f = Except.ok PUnit.unit := by
    rintro _ _ rfl _; rfl
  have hFns : s.coreProgram.functions = [s.coreFn] := rfl
  have hCoreName : s.coreFn.name = s.fnName := rfl
  simp only [hCfgD.1, hCfgD.2, show ¬ (3 < 3) by omega, ↓reduceIte, htc, Except.mapError,
    List.forIn_cons, List.forIn_nil, hfind, Option.isNone_some, Bool.false_eq_true, hce,
    hFns, List.mapM_cons, List.mapM_nil,
    List.contains_cons, hCoreName, beq_self_eq_true, Bool.true_or, hfn, hlo,
    bind, Except.bind, pure, Except.pure]
  rw [hForIn _ s.coreProgram.enums rfl]
  dsimp only
  dsimp only [initSys] at hded
  rw [hded]
  simp only [Dedup.identity, List.map_cons, List.map_nil, hcc, hdb, ↓reduceDIte]
  rfl

omit [Field F] in
private theorem inlined_program_cast {p : Aiur.Program F} {ns : List String} {es : List String}
    (h : ns = []) (x : Inlining.Prepared p [] es) :
    (h.symm ▸ x : Inlining.Prepared p ns es).program = x.program := by
  cases h; rfl

omit [Field F] in
private theorem inlined_program_eq (s : FlatAssertSpec F)
    (hSym : Generic.Instance.ofSymbol s.fnName = .ok ⟨s.fnName, []⟩)
    (hNodup : Aiur.findDuplicate (s.params.map Prod.fst) [] = none) :
    (s.inlined hSym hNodup).program = s.coreProgram := by
  unfold inlined
  rw [inlined_program_cast (s.specialized_inlineNames_eq_nil hSym hNodup)]
  simp [inlinedBase, Inlining.Prepared.program, Inlining.Bodies.program, specialized, coreProgram,
    Inlining.Bodies.function, Inlining.Bodies.body, coreFn, tree_target_mkTreeBody]

def compiled (s : FlatAssertSpec F)
    (hSym : Generic.Instance.ofSymbol s.fnName = .ok ⟨s.fnName, []⟩)
    (hNodup : Aiur.findDuplicate (s.params.map Prod.fst) [] = none) :
    GenericArtifact (s.specialized hSym hNodup) where
  inlined := s.inlined hSym hNodup
  artifact := s.artifact
  config := minimalConfig
  compiled := by
    rw [s.inlined_program_eq hSym hNodup]
    exact s.compile_eq hNodup

def prepared (s : FlatAssertSpec F)
    (hSym : Generic.Instance.ofSymbol s.fnName = .ok ⟨s.fnName, []⟩)
    (hNodup : Aiur.findDuplicate (s.params.map Prod.fst) [] = none) :
    Physical.Prepared (s.compiled hSym hNodup).artifact where
  compatible := by
    refine ⟨?_, ?_⟩
    · intro c hc call hcall
      simp only [compiled, artifact, List.mem_singleton] at hc
      subst hc; cases hcall
    · intro c hc l hl
      simp only [compiled, artifact, List.mem_singleton] at hc
      subst hc; cases hl
  merged :=
    { toResult := Dedup.identity ⟨[s.erasedChip], [], [], []⟩
      certificate := dedup_identity_cert ⟨[s.erasedChip], [], [], []⟩ s.erasedChip rfl s.erasedChip_wellFormed }
  faithful := by
    intro chip hchip
    simp only [Dedup.identity, List.mem_singleton] at hchip
    subst hchip
    have hren : Dedup.rename [(s.fnName, s.fnName)] s.fnName = s.fnName := by
      simp [Dedup.rename]
    simp [compiled, artifact, Erasure.system, erasedChip, Circuit.System.findChip?,
      Circuit.Chip.rename, Dedup.identity, physChip, Erasure.chip, hren]
  mapShaped := ⟨(fun _ h => nomatch h), (fun _ _ _ _ _ h => nomatch h)⟩

theorem depthSystem_eq (s : FlatAssertSpec F)
    (hSym : Generic.Instance.ofSymbol s.fnName = .ok ⟨s.fnName, []⟩)
    (hNodup : Aiur.findDuplicate (s.params.map Prod.fst) [] = none) :
    Depth.system trivialDepthCfg (s.prepared hSym hNodup).system = ⟨[s.erasedChip], [], [], []⟩ := by
  simp [Depth.system, Depth.compileChip, Depth.Config.plan, Depth.ChipPlan.base,
    Depth.nextColumn, Depth.mainSends, Depth.rangeSends, trivialDepthCfg, prepared,
    Physical.Prepared.system, Dedup.identity, erasedChip, Erasure.chip, physChip]

theorem certified (s : FlatAssertSpec F)
    (hSym : Generic.Instance.ofSymbol s.fnName = .ok ⟨s.fnName, []⟩)
    (hNodup : Aiur.findDuplicate (s.params.map Prod.fst) [] = none) :
    Physical.Prepared.DepthCertified (s.compiled hSym hNodup) (s.prepared hSym hNodup) trivialDepthCfg := by
  refine ⟨?_, [], ?_⟩
  · simp [Depth.Structural.certify, Depth.fresh, Depth.Structural.chipOK, Depth.Config.names,
      Depth.Config.plan, trivialDepthCfg, prepared, Physical.Prepared.system, Dedup.identity,
      s.erasedChip_wellFormed, show s.erasedChip.sends = [] from rfl]
  · rw [show (s.compiled hSym hNodup).inlined.program = s.coreProgram from s.inlined_program_eq hSym hNodup]
    simp [Depth.Structural.check, trivialDepthCfg, coreProgram]

def plan (s : FlatAssertSpec F)
    (hSym : Generic.Instance.ofSymbol s.fnName = .ok ⟨s.fnName, []⟩)
    (hNodup : Aiur.findDuplicate (s.params.map Prod.fst) [] = none) :
    Grouping.Plan (Depth.system trivialDepthCfg (s.prepared hSym hNodup).system) (fun _ => .ok 0) where
  singles := [s.erasedChip]
  groups := []
  certificate := by
    rw [s.depthSystem_eq hSym hNodup]
    refine ⟨?_, (fun _ h => nomatch h), ?_⟩
    · intro c hc
      simp only [List.mem_singleton] at hc; subst hc
      simp [Circuit.System.findChip?]
    · intro c hc
      exact Or.inl hc

theorem activated (s : FlatAssertSpec F)
    (hSym : Generic.Instance.ofSymbol s.fnName = .ok ⟨s.fnName, []⟩)
    (hNodup : Aiur.findDuplicate (s.params.map Prod.fst) [] = none) :
    (s.plan hSym hNodup).WellFormedActivation := by
  intro c hc
  simp only [plan, List.mem_singleton] at hc
  subst hc
  exact ⟨s.erasedChip_wellFormed, s.activated_erasedChip_wellFormed⟩

theorem signed (s : FlatAssertSpec F)
    (hSym : Generic.Instance.ofSymbol s.fnName = .ok ⟨s.fnName, []⟩)
    (hNodup : Aiur.findDuplicate (s.params.map Prod.fst) [] = none) :
    Erasure.Signed (s.compiled hSym hNodup).system s.typedRootMsg := by
  intro chip hfind
  simp only [compiled, GenericArtifact.system, artifact, Circuit.System.findChip?,
    List.find?_cons, typedRootMsg, physChip, beq_self_eq_true, Option.some.injEq] at hfind
  subst hfind
  unfold Erasure.messageShape Erasure.signature
  simp only [typedRootMsg, wires, outputWire, inputWireVars, List.map_map,
    Function.comp_def, Erasure.shape, FlatVal.wireVal, FlatVal.words_length, mkInputWires_shapes,
    Prod.mk.injEq, true_and]
  simp

theorem rooted (s : FlatAssertSpec F)
    (hSym : Generic.Instance.ofSymbol s.fnName = .ok ⟨s.fnName, []⟩)
    (hNodup : Aiur.findDuplicate (s.params.map Prod.fst) [] = none) :
    Depth.erase trivialDepthCfg s.erasedRootMsg =
      Erasure.message (s.compiled hSym hNodup).system s.typedRootMsg := by
  simp [Depth.erase, Depth.Config.recursive, Depth.Config.plan, trivialDepthCfg,
    erasedRootMsg, compiled, GenericArtifact.system, artifact]

theorem outside (s : FlatAssertSpec F) :
    s.erasedRootMsg.channel ∉ trivialDepthCfg.names := by
  simp [Depth.Config.names, trivialDepthCfg]

theorem arguments (s : FlatAssertSpec F)
    (hSym : Generic.Instance.ofSymbol s.fnName = .ok ⟨s.fnName, []⟩)
    (hNodup : Aiur.findDuplicate (s.params.map Prod.fst) [] = none) :
    DecodesValues (s.specialized hSym hNodup).program.enums s.wires (entryValues s.args) := by
  simp only [specialized, coreProgram, wires, args, Aiur.entryValues, List.map_map, Function.comp_def]
  induction s.params with
  | nil => exact List.Forall₂.nil
  | cons p rest ih =>
    exact List.Forall₂.cons (by dsimp only; rw [p.2.mapAddress_sourceVal]; exact p.2.wireVal_decode) ih

theorem decoded (s : FlatAssertSpec F)
    (hSym : Generic.Instance.ofSymbol s.fnName = .ok ⟨s.fnName, []⟩)
    (hNodup : Aiur.findDuplicate (s.params.map Prod.fst) [] = none) :
    s.outputWire.decode (s.specialized hSym hNodup).program.enums = some s.resultVal := by
  exact (FlatVal.arr s.outConsts).wireVal_decode

theorem chanIds_singleton (s : FlatAssertSpec F)
    (hSym : Generic.Instance.ofSymbol s.fnName = .ok ⟨s.fnName, []⟩)
    (hNodup : Aiur.findDuplicate (s.params.map Prod.fst) [] = none) :
    ∀ x ∈ Bridge.channels (Depth.system trivialDepthCfg (s.prepared hSym hNodup).system)
        (s.plan hSym hNodup).singles s.erasedRootMsg, x = s.fnName := by
  intro x hx
  have hdyn : Erasure.dynamic (⟨[s.physChip], [], [], []⟩ : Circuit.System F) s.fnName = true := by
    simp [Erasure.dynamic, Circuit.System.findChip?, physChip]
  simp only [Bridge.channels, plan] at hx
  rw [s.depthSystem_eq hSym hNodup] at hx
  simp only [erasedRootMsg, Erasure.message, Erasure.flatten] at hx
  simp only [erasedChip, Erasure.chip, physChip, typedRootMsg,
    Circuit.System.mapClaims, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl | rfl
  · rfl
  · split_ifs with h <;> simp [h]

/-- Symbolic trace assignment satisfying `Bridge.lower (fun _ => 0) s.erasedChip`:
`0..numVars-1` carry `s.allConsts`, `numVars` carries `sel = 1`, `numVars + 1` carries `mult = 1`. -/
def mainTrace (s : FlatAssertSpec F) : Nat → Nat → Scalar.Circuit.Var → F :=
  fun _ _ v => (s.allConsts ++ [1, 1]).getD v 0

theorem lower_holds_mainTrace (s : FlatAssertSpec F) :
    (Bridge.lower (fun _ => 0) s.erasedChip).Holds
      ((WideStage.unitAirs (fun _ => 0) [((s.erasedChip, none), 1)]).headD (defaultAirF F) |>.assign
        (s.mainTrace 0) 0) := by
  intro c hc
  set a := ((WideStage.unitAirs (fun _ => 0) [((s.erasedChip, none), 1)]).headD (defaultAirF F)).assign
    (s.mainTrace 0) 0
  have ha : ∀ v < s.numVars + 2, a v = (s.allConsts ++ [1, 1]).getD v 0 := by
    intro v hv
    simp [a, WideStage.Air.assign, WideStage.unitAirs, WideStage.unitAir, Bridge.unitCircuit,
      Bridge.lower, erasedChip, Erasure.chip, physChip, hv, mainTrace]
  have hsel : a s.numVars = 1 := by
    rw [ha s.numVars (by omega)]
    simp [List.getD_eq_getElem?_getD, numVars]
  have hmult : a (s.numVars + 1) = 1 := by
    rw [ha (s.numVars + 1) (by omega)]
    simp [List.getD_eq_getElem?_getD, numVars]
  simp only [Bridge.lower, Activation.compile, Activation.guards, erasedChip, Erasure.chip,
    physChip, List.map_nil, List.append_nil, List.dedup_nil, List.cons_append] at hc
  rcases List.mem_cons.mp hc with rfl | hrest
  · simp [Activation.boolean, Scalar.Circuit.ArithExpr.denote, hsel]
  · rcases List.mem_append.mp hrest with hmid | hlast
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmid
      obtain ⟨⟨val, i⟩, hi, rfl⟩ := List.mem_map.mp he
      have hlt : i < s.numVars := by have := List.mem_zipIdx hi; simp only [numVars]; omega
      have hget : s.allConsts[i]? = some val := by
        have := List.mem_zipIdx_iff_getElem?.mp hi
        simpa using this
      dsimp only
      have hact : Scalar.Circuit.ArithExpr.denote a (Activation.polynomial s.numVars (subConstPoly i val)) =
          Scalar.Circuit.ArithExpr.denote a (subConstPoly i val) :=
        Activation.polynomial_active s.numVars (subConstPoly i val) a hsel
      have hsub : Scalar.Circuit.ArithExpr.denote a (subConstPoly i val) = a i - val :=
        subConstPoly_denote i val a
      rw [hact, hsub, ha i (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, hget]
    · simp only [List.mem_singleton] at hlast
      subst hlast
      simp [Scalar.Circuit.ArithExpr.denote, hsel, hmult]

theorem lower_receive_tuple_mainTrace (s : FlatAssertSpec F) :
    ((Bridge.lower (fun _ => 0) s.erasedChip).lookups.map fun l =>
      (l.tuple (((WideStage.unitAirs (fun _ => 0) [((s.erasedChip, none), 1)]).headD (defaultAirF F)).assign
        (s.mainTrace 0) 0),
       l.multiplicity.denote (((WideStage.unitAirs (fun _ => 0) [((s.erasedChip, none), 1)]).headD (defaultAirF F)).assign
        (s.mainTrace 0) 0))) =
    [(Bridge.encode (fun _ => 0) s.erasedRootMsg, (-1 : F))] := by
  set a := ((WideStage.unitAirs (fun _ => 0) [((s.erasedChip, none), 1)]).headD (defaultAirF F)).assign
    (s.mainTrace 0) 0
  have ha : ∀ v < s.numVars + 2, a v = (s.allConsts ++ [1, 1]).getD v 0 := by
    intro v hv
    simp [a, WideStage.Air.assign, WideStage.unitAirs, WideStage.unitAir, Bridge.unitCircuit,
      Bridge.lower, erasedChip, Erasure.chip, physChip, hv, mainTrace]
  have hmult : a (s.numVars + 1) = 1 := by
    rw [ha (s.numVars + 1) (by omega)]
    simp [List.getD_eq_getElem?_getD, numVars]
  have hmapRange : ∀ off len (hle : off + len ≤ s.allConsts.length),
      (List.range' off len).map a = (s.allConsts.drop off).take len := by
    intro off len hle
    apply List.ext_getElem (by simp; omega)
    intro k hk1 hk2
    have hk : k < len := by simpa using hk1
    simp only [List.getElem_map, List.getElem_range', Nat.one_mul, List.getElem_take, List.getElem_drop]
    rw [ha (off + k) (by simp only [numVars]; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show off + k < s.allConsts.length by omega),
      List.getElem?_eq_getElem (show off + k < s.allConsts.length by omega)]
  have hin : (List.range' 0 s.inConsts.length).map a = s.inConsts := by
    rw [hmapRange 0 s.inConsts.length (by simp [allConsts])]
    simp [allConsts]
  have hout : (List.range' s.inConsts.length s.outConsts.length).map a = s.outConsts := by
    rw [hmapRange s.inConsts.length s.outConsts.length (by simp [allConsts])]
    simp [allConsts]
  have hdyn : Erasure.dynamic (⟨[s.physChip], [], [], []⟩ : Circuit.System F) s.fnName = true := by
    simp [Erasure.dynamic, Circuit.System.findChip?, physChip]
  simp only [Bridge.lower, Activation.compile, erasedChip, Erasure.chip, physChip,
    List.map_nil, List.append_nil, List.map_cons, List.cons.injEq, and_true, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · simp only [Bridge.receiveLookup, Tiling.Lookup.tuple, Bridge.encode, erasedRootMsg,
      Erasure.message, Erasure.flatten, Erasure.pack, typedRootMsg, wires, outputWire,
      hdyn, ↓reduceIte, Scalar.Circuit.ArithExpr.denote, List.map_cons, List.map_append,
      List.map_map, Function.comp_def, List.flatMap_singleton, inputWireVars, mkInputWires_flatMap,
      List.cons.injEq, true_and]
    have hw : (s.params.map fun p => p.2.wireVal).flatMap WireValue.words = s.inConsts := by
      simp [inConsts, List.flatMap_map, FlatVal.wireVal]
    change (List.range' 0 s.inConsts.length).map a ++ (List.range' s.inConsts.length s.outConsts.length).map a =
      (s.params.map fun p => p.2.wireVal).flatMap WireValue.words ++ s.outConsts
    rw [hw, hin, hout]
  · simp [Bridge.receiveLookup, Scalar.Circuit.ArithExpr.denote, hmult]

theorem encode_erasedRootMsg (s : FlatAssertSpec F) :
    Bridge.encode (fun _ => 0) s.erasedRootMsg =
      (CALL : F) :: (0 : F) :: s.allConsts := by
  have hdyn : Erasure.dynamic (⟨[s.physChip], [], [], []⟩ : Circuit.System F) s.fnName = true := by
    simp [Erasure.dynamic, Circuit.System.findChip?, physChip]
  simp only [Bridge.encode, erasedRootMsg, Erasure.message, hdyn, ↓reduceIte,
    Erasure.flatten, Erasure.pack, typedRootMsg, wires, outputWire, allConsts, inConsts,
    List.flatMap_singleton, List.flatMap_map, FlatVal.wireVal, Nat.cast_zero
    ]

end FlatAssertSpec

/-! ## 5. Stage 1 (`CompressWrap`) & Stage 2 (`CompressGL`) Polymorphic Builders -/

/-- Polymorphic `FlatAssertSpec` for `CompressWrap::verify_root` (Stage 1, Goldilocks)
or `CompressGL::verify_root` (Stage 2, BN254): asserts `reserved == [0; 8]` and `stmt == targetWords`. -/
def mkVerifyRootSpec (F : Type) [Field F] (entryName : String) (targetWords : List Nat) :
    FlatAssertSpec F where
  fnName := entryName
  params := [
    ("reserved", .arr (List.replicate 8 0)),
    ("stmt", .arr (targetWords.map fun w => (w : F)))
  ]
  outConsts := []

private theorem verifyRootSpec_eval_inv {p : Nat} [NeZero p] [Fact (Nat.Prime p)]
    (hp : 2 ^ 32 < p) (entryName : String)
    (hSym : Generic.Instance.ofSymbol entryName = .ok ⟨entryName, []⟩)
    {targetWords : List Nat} (htCanon : CanonicalU32Digest8 targetWords)
    {stmtWords : List Nat} {value heap} (hsCanon : CanonicalU32Digest8 stmtWords)
    (hEv : Generic.SourceSemantics.EvalFn (mkVerifyRootSpec (ZMod p) entryName targetWords).source.world
      entryName [zeroArray8SourceValue (ZMod p), u32Array8SourceValue (ZMod p) stmtWords] [] value heap) :
    stmtWords = targetWords := by
  have hprep : (mkVerifyRootSpec (ZMod p) entryName targetWords).source.world.prepare entryName
      [zeroArray8SourceValue (ZMod p), u32Array8SourceValue (ZMod p) stmtWords] =
      .ok ([],
        [("reserved", zeroArray8SourceValue (ZMod p)),
         ("stmt", u32Array8SourceValue (ZMod p) stmtWords)],
        (.letValue .wildcard
          (.builtin (.assertEq {}) [.var "reserved", .tuple ((List.replicate 8 (0 : ZMod p)).map .literal)]) <|
         .letValue .wildcard
          (.builtin (.assertEq {}) [.var "stmt", .tuple ((targetWords.map fun w => (w : ZMod p)).map .literal)]) <|
         .tuple [])) := by
    have hs8 : stmtWords.length = 8 := hsCanon.1
    have ht8 : targetWords.length = 8 := htCanon.1
    rcases stmtWords with _ | ⟨s0, _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, _ | ⟨s4, _ | ⟨s5, _ | ⟨s6, _ | ⟨s7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      simp at hs8
    simp [Generic.Source.world, Generic.sourceWorld, Generic.Program.sourceFunction?,
      Generic.Program.findFunction?, FlatAssertSpec.source, FlatAssertSpec.genericProgram,
      FlatAssertSpec.genericFn, FlatAssertSpec.mkGenericBody, mkVerifyRootSpec, FlatVal.genericTy,
      FlatVal.genericExpr, Generic.SourceFunction.prepare, hSym, ht8, Generic.Ty.toCore,
      Generic.Ty.subst, zeroArray8SourceValue, u32Array8SourceValue, Generic.wellFormed,
      Aiur.Value.type, Generic.arguments, bind, Option.bind, Except.bind, pure, Except.pure,
      Except.toOption]
  cases hEv with
  | intro hpr hbody =>
    rw [hprep] at hpr
    injection hpr with hpr
    simp only [Prod.mk.injEq] at hpr
    obtain ⟨rfl, rfl, rfl⟩ := hpr
    obtain ⟨_, hbody2⟩ := evalExpr_letAssertEq_var_tuple hbody
    obtain ⟨hlook, _⟩ := evalExpr_letAssertEq_var_tuple hbody2
    have hne : ("reserved" == "stmt") = false := by decide
    simp only [List.find?_cons, hne, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq, true_and,
      u32Array8SourceValue, Aiur.Value.tuple.injEq, List.map_map, Function.comp_def] at hlook
    exact u32Words_eq_of_field_tuple_eq hp hsCanon.2 htCanon.2 hlook
  | returned hpr hexit =>
    rw [hprep] at hpr
    injection hpr with hpr
    simp only [Prod.mk.injEq] at hpr
    obtain ⟨rfl, rfl, rfl⟩ := hpr
    have h1 := evalExit_letAssertEq_var_tuple hexit
    have h2 := evalExit_letAssertEq_var_tuple h1
    exact False.elim (evalExit_tuple_literals_false (cs := []) h2)

/-- Stage 1 (`CompressWrap`) symbolic `FlatAssertSpec` on `toyRootWords`. -/
def toyWrapSpec : FlatAssertSpec _root_.MultiStark.F :=
  mkVerifyRootSpec _root_.MultiStark.F compressWrapEntry toyRootWords

theorem toyWrapSpec_sym : Generic.Instance.ofSymbol toyWrapSpec.fnName = .ok ⟨toyWrapSpec.fnName, []⟩ := by
  rfl

theorem toyWrapSpec_nodup : Aiur.findDuplicate (toyWrapSpec.params.map Prod.fst) [] = none := by
  decide

def toyWrapWitness :
    GoldilocksWideStageWitness toyWrapSpec.source [compressWrapEntry] compressWrapEntry
      (compressWrapArgs toyRootWords) where
  specialized := toyWrapSpec.specialized toyWrapSpec_sym toyWrapSpec_nodup
  compiled := toyWrapSpec.compiled toyWrapSpec_sym toyWrapSpec_nodup
  prepared := toyWrapSpec.prepared toyWrapSpec_sym toyWrapSpec_nodup
  cfg := trivialDepthCfg
  certified := toyWrapSpec.certified toyWrapSpec_sym toyWrapSpec_nodup
  id := fun _ => .ok 0
  plan := toyWrapSpec.plan toyWrapSpec_sym toyWrapSpec_nodup
  activated := toyWrapSpec.activated toyWrapSpec_sym toyWrapSpec_nodup
  entry := by simp
  result := toyWrapSpec.resultVal
  wires := toyWrapSpec.wires
  output := toyWrapSpec.outputWire
  signed := toyWrapSpec.signed toyWrapSpec_sym toyWrapSpec_nodup
  root := toyWrapSpec.erasedRootMsg
  rooted := toyWrapSpec.rooted toyWrapSpec_sym toyWrapSpec_nodup
  outside := toyWrapSpec.outside
  entryPlain := rfl
  arguments := by
    have h := toyWrapSpec.arguments toyWrapSpec_sym toyWrapSpec_nodup
    simpa [toyWrapSpec, mkVerifyRootSpec, FlatAssertSpec.args, FlatVal.sourceVal,
      compressWrapArgs, zeroArray8SourceValue, u32Array8SourceValue] using h
  decoded := toyWrapSpec.decoded toyWrapSpec_sym toyWrapSpec_nodup
  idOf := fun _ => 0
  units := [((toyWrapSpec.erasedChip, none), 1)]
  chipsIn := by intro u hu; simp only [List.mem_singleton] at hu; subst hu; simp [FlatAssertSpec.plan]
  unrolled := by intro u hu; simp only [List.mem_singleton] at hu; subst hu; rfl
  capacity := by simp [WideStage.unitCapRows, Bridge.unitBodies]
  mapCap := fun _ => 0
  roms := []
  widths := List.nodup_nil
  bound := 100
  romCaps := fun _ h => absurd h List.not_mem_nil
  hbound := by decide
  tags := by decide
  lookups := by
    simp [WideStage.unitCapLookups, FlatAssertSpec.erasedChip, Erasure.chip, FlatAssertSpec.physChip]
  hbits := by decide
  chanIds := by
    intro x hx y hy _
    rw [toyWrapSpec.chanIds_singleton toyWrapSpec_sym toyWrapSpec_nodup x hx,
      toyWrapSpec.chanIds_singleton toyWrapSpec_sym toyWrapSpec_nodup y hy]
  chanBound := fun _ _ => by decide
  enablesOk := by
    intro c hc
    simp only [FlatAssertSpec.plan, List.mem_singleton] at hc
    subst hc
    simp [Bridge.checkEnables, Activation.compile, FlatAssertSpec.erasedChip, Erasure.chip,
      FlatAssertSpec.physChip]
  mainU := toyWrapSpec.mainTrace
  mainM := fun _ _ _ => 0
  mainR := fun _ _ _ => 0
  holds := by
    intro x hx r hr
    simp only [WideStage.unitAirs, List.map_cons, List.map_nil, List.zipIdx_singleton,
      List.mem_singleton] at hx
    subst hx
    have hr0 : r = 0 := by simp [WideStage.unitAir] at hr; omega
    subst hr0
    simpa [WideStage.unitAirs, WideStage.unitAir, Bridge.unitCircuit] using toyWrapSpec.lower_holds_mainTrace
  balanced := by
    have hM : WideStage.stageLedger (WideStage.mapAirs
        ((Depth.system trivialDepthCfg (toyWrapSpec.prepared toyWrapSpec_sym toyWrapSpec_nodup).system).mapClaims.map
          (Bridge.encode fun _ => 0)) (fun _ => 0)) (fun _ _ _ => 0) = 0 := by
      rw [toyWrapSpec.depthSystem_eq toyWrapSpec_sym toyWrapSpec_nodup]
      simp [Circuit.System.mapClaims, WideStage.mapAirs, WideStage.mapLengths, WideStage.stageLedger]
    have hR : WideStage.stageLedger (WideStage.romAirs (F := _root_.MultiStark.F) []) (fun _ _ _ => 0) = 0 := rfl
    have hU : WideStage.stageLedger (WideStage.unitAirs (fun _ => 0) [((toyWrapSpec.erasedChip, none), 1)])
        toyWrapSpec.mainTrace = Finsupp.single (Bridge.encode (fun _ => 0) toyWrapSpec.erasedRootMsg) (-1) := by
      simp only [WideStage.stageLedger, WideStage.unitAirs, WideStage.unitAir, List.map_cons,
        List.map_nil, List.zipIdx_singleton, List.sum_cons, List.sum_nil, add_zero,
        WideStage.Air.ledger, List.range_one, Tiling.Circuit.rowLedger]
      have h1 : ∀ (ls : List (Tiling.Lookup _root_.MultiStark.F)) (a : Nat → _root_.MultiStark.F),
          (ls.map (fun l => l.entry a)).sum =
            ((ls.map fun l => (l.tuple a, l.multiplicity.denote a)).map
              fun p => Finsupp.single p.1 p.2).sum := by
        intro ls a; simp [Tiling.Lookup.entry, List.map_map, Function.comp_def]
      rw [h1]
      have hlook := toyWrapSpec.lower_receive_tuple_mainTrace
      simp only [WideStage.unitAirs, WideStage.unitAir, List.map_cons, List.map_nil,
        List.headD_cons] at hlook
      simpa [Bridge.unitCircuit] using congrArg (fun l => (l.map fun p => Finsupp.single p.1 p.2).sum) hlook
    rw [hM, hR, hU, add_zero, add_zero, ← Finsupp.single_add]
    simp

/-- Stage 2 (`CompressGL`) polymorphic `FlatAssertSpec` over `BN254Fr`. -/
def mkToyGlSpec (targetWords : List Nat) : FlatAssertSpec BN254Fr :=
  mkVerifyRootSpec BN254Fr MultiStark.CompressGL.entry targetWords

theorem mkToyGlSpec_sym (targetWords : List Nat) :
    Generic.Instance.ofSymbol (mkToyGlSpec targetWords).fnName = .ok ⟨(mkToyGlSpec targetWords).fnName, []⟩ := by
  change Generic.Instance.ofSymbol MultiStark.CompressGL.entry = .ok ⟨MultiStark.CompressGL.entry, []⟩
  rfl

theorem mkToyGlSpec_nodup (targetWords : List Nat) :
    Aiur.findDuplicate ((mkToyGlSpec targetWords).params.map Prod.fst) [] = none := by
  simp only [mkToyGlSpec, mkVerifyRootSpec, List.map_cons, List.map_nil]
  decide

/-- Polymorphic Stage 2 (`CompressGL`) `Bn254GroupedWideStageWitness` for ANY 8-word digest! -/
def mkToyGlWitness (targetWords : List Nat) :
    Bn254GroupedWideStageWitness (mkToyGlSpec targetWords).source [MultiStark.CompressGL.entry]
      MultiStark.CompressGL.entry (compressGLArgs BN254Fr targetWords) where
  specialized := (mkToyGlSpec targetWords).specialized (mkToyGlSpec_sym _) (mkToyGlSpec_nodup _)
  compiled := (mkToyGlSpec targetWords).compiled (mkToyGlSpec_sym _) (mkToyGlSpec_nodup _)
  prepared := (mkToyGlSpec targetWords).prepared (mkToyGlSpec_sym _) (mkToyGlSpec_nodup _)
  cfg := trivialDepthCfg
  certified := (mkToyGlSpec targetWords).certified (mkToyGlSpec_sym _) (mkToyGlSpec_nodup _)
  id := fun _ => .ok 0
  plan := (mkToyGlSpec targetWords).plan (mkToyGlSpec_sym _) (mkToyGlSpec_nodup _)
  activated := (mkToyGlSpec targetWords).activated (mkToyGlSpec_sym _) (mkToyGlSpec_nodup _)
  entry := by simp
  result := (mkToyGlSpec targetWords).resultVal
  wires := (mkToyGlSpec targetWords).wires
  output := (mkToyGlSpec targetWords).outputWire
  signed := (mkToyGlSpec targetWords).signed (mkToyGlSpec_sym _) (mkToyGlSpec_nodup _)
  root := (mkToyGlSpec targetWords).erasedRootMsg
  rooted := (mkToyGlSpec targetWords).rooted (mkToyGlSpec_sym _) (mkToyGlSpec_nodup _)
  outside := (mkToyGlSpec targetWords).outside
  entryPlain := rfl
  arguments := by
    have h := (mkToyGlSpec targetWords).arguments (mkToyGlSpec_sym _) (mkToyGlSpec_nodup _)
    simpa [mkToyGlSpec, mkVerifyRootSpec, FlatAssertSpec.args, FlatVal.sourceVal,
      compressGLArgs, zeroArray8SourceValue, u32Array8SourceValue] using h
  decoded := (mkToyGlSpec targetWords).decoded (mkToyGlSpec_sym _) (mkToyGlSpec_nodup _)
  idOf := fun _ => 0
  idOk := fun _ _ h => (Except.ok.inj h).symm
  names := by simp [circuitNames, FlatAssertSpec.plan]
  units := [(((mkToyGlSpec targetWords).erasedChip, none), 1)]
  chipsIn := by intro u hu; simp only [List.mem_singleton] at hu; subst hu; simp [FlatAssertSpec.plan]
  unrolled := by intro u hu; simp only [List.mem_singleton] at hu; subst hu; rfl
  groups := []
  groupsIn := fun _ h => absurd h List.not_mem_nil
  capacity := by simp [WideStage.unitCapRows, Bridge.unitBodies]
  mapCap := fun _ => 0
  roms := []
  widths := List.nodup_nil
  bound := 100
  romCaps := fun _ h => absurd h List.not_mem_nil
  romWidths := fun _ h => absurd h List.not_mem_nil
  hbound := by decide
  tags := by decide
  lookups := by
    simp [WideStage.unitCapLookups, FlatAssertSpec.erasedChip, Erasure.chip, FlatAssertSpec.physChip]
  hbits := by decide
  chanIds := by
    intro x hx y hy _
    have hall : allChips ((mkToyGlSpec targetWords).plan (mkToyGlSpec_sym _) (mkToyGlSpec_nodup _)) =
        ((mkToyGlSpec targetWords).plan (mkToyGlSpec_sym _) (mkToyGlSpec_nodup _)).singles := by
      simp [allChips, FlatAssertSpec.plan]
    rw [hall] at hx hy
    rw [(mkToyGlSpec targetWords).chanIds_singleton (mkToyGlSpec_sym _) (mkToyGlSpec_nodup _) x hx,
      (mkToyGlSpec targetWords).chanIds_singleton (mkToyGlSpec_sym _) (mkToyGlSpec_nodup _) y hy]
  chanBound := fun _ _ => by decide
  enablesOk := by
    intro c hc
    simp only [allChips, FlatAssertSpec.plan, List.flatMap_nil, List.append_nil, List.mem_singleton] at hc
    subst hc
    simp [Bridge.checkEnables, Activation.compile, FlatAssertSpec.erasedChip, Erasure.chip,
      FlatAssertSpec.physChip]
  memWidth := by
    intro c hc m hm
    simp only [allChips, FlatAssertSpec.plan, List.flatMap_nil, List.append_nil, List.mem_singleton] at hc
    subst hc
    simp [FlatAssertSpec.erasedChip, Erasure.chip, FlatAssertSpec.physChip] at hm
  mainU := (mkToyGlSpec targetWords).mainTrace
  mainG := fun _ _ _ => 0
  mainM := fun _ _ _ => 0
  mainR := fun _ _ _ => 0
  holds := by
    intro x hx r hr
    simp only [WideStage.unitAirs, List.map_cons, List.map_nil, List.zipIdx_singleton,
      List.mem_singleton] at hx
    subst hx
    have hr0 : r = 0 := by simp [WideStage.unitAir] at hr; omega
    subst hr0
    simpa [WideStage.unitAirs, WideStage.unitAir, Bridge.unitCircuit] using (mkToyGlSpec targetWords).lower_holds_mainTrace
  holdsG := fun _ h => absurd h List.not_mem_nil
  balanced := by
    have hG : WideStage.stageLedger (groupAirs ([] : List (Grouping.Packed BN254Fr (fun _ => .ok 0) × Nat)))
        (fun _ _ _ => 0) = 0 := rfl
    have hM : WideStage.stageLedger (WideStage.mapAirs
        ((Depth.system trivialDepthCfg
          ((mkToyGlSpec targetWords).prepared (mkToyGlSpec_sym _) (mkToyGlSpec_nodup _)).system).mapClaims.map
          (Bridge.encode fun _ => 0)) (fun _ => 0)) (fun _ _ _ => 0) = 0 := by
      rw [(mkToyGlSpec targetWords).depthSystem_eq (mkToyGlSpec_sym _) (mkToyGlSpec_nodup _)]
      simp [Circuit.System.mapClaims, WideStage.mapAirs, WideStage.mapLengths, WideStage.stageLedger]
    have hR : WideStage.stageLedger (WideStage.romAirs (F := BN254Fr) []) (fun _ _ _ => 0) = 0 := rfl
    have hU : WideStage.stageLedger (WideStage.unitAirs (fun _ => 0)
          [(((mkToyGlSpec targetWords).erasedChip, none), 1)])
        (mkToyGlSpec targetWords).mainTrace =
        Finsupp.single (Bridge.encode (fun _ => 0) (mkToyGlSpec targetWords).erasedRootMsg) (-1) := by
      simp only [WideStage.stageLedger, WideStage.unitAirs, WideStage.unitAir, List.map_cons,
        List.map_nil, List.zipIdx_singleton, List.sum_cons, List.sum_nil, add_zero,
        WideStage.Air.ledger, List.range_one, Tiling.Circuit.rowLedger]
      have h1 : ∀ (ls : List (Tiling.Lookup BN254Fr)) (a : Nat → BN254Fr),
          (ls.map (fun l => l.entry a)).sum =
            ((ls.map fun l => (l.tuple a, l.multiplicity.denote a)).map
              fun p => Finsupp.single p.1 p.2).sum := by
        intro ls a; simp [Tiling.Lookup.entry, List.map_map, Function.comp_def]
      rw [h1]
      have hlook := (mkToyGlSpec targetWords).lower_receive_tuple_mainTrace
      simp only [WideStage.unitAirs, WideStage.unitAir, List.map_cons, List.map_nil,
        List.headD_cons] at hlook
      simpa [Bridge.unitCircuit] using congrArg (fun l => (l.map fun p => Finsupp.single p.1 p.2).sum) hlook
    rw [hG, hM, hR, hU, add_zero, add_zero, add_zero, ← Finsupp.single_add]
    simp

/-! ## 6. Stage 3 (`CompressNarrowFixed`) Polymorphic BN254 Periodic Sharded Witness -/

/-- Polymorphic Stage 3 (`CompressNarrowFixed::step_v1`) `FlatAssertSpec`:
17 inputs (`policy[0..7], stage=1, stmt[0..7]`) and 4 outputs (`toyPrevAccWords = [1, -1, 0, 0]`). -/
def mkToyNarrowSpec (policyWords targetWords : List Nat) : FlatAssertSpec BN254Fr where
  fnName := compressNarrowFixedEntry
  params := [
    ("policy", .arr (policyWords.map fun w => (w : BN254Fr))),
    ("stage", .scalar 1),
    ("stmt", .arr (targetWords.map fun w => (w : BN254Fr)))
  ]
  outConsts := toyPrevAccWords

theorem mkToyNarrowSpec_sym (policyWords targetWords : List Nat) :
    Generic.Instance.ofSymbol (mkToyNarrowSpec policyWords targetWords).fnName =
      .ok ⟨(mkToyNarrowSpec policyWords targetWords).fnName, []⟩ := by
  change Generic.Instance.ofSymbol compressNarrowFixedEntry = .ok ⟨compressNarrowFixedEntry, []⟩
  rfl

theorem mkToyNarrowSpec_nodup (policyWords targetWords : List Nat) :
    Aiur.findDuplicate ((mkToyNarrowSpec policyWords targetWords).params.map Prod.fst) [] = none := by
  simp only [mkToyNarrowSpec, List.map_cons, List.map_nil]
  decide

private theorem toyNarrowSpec_eval_inv {policyTarget stmtTarget : List Nat}
    (hpCanon : CanonicalU32Digest8 policyTarget) (htCanon : CanonicalU32Digest8 stmtTarget)
    {policyWords stmtWords : List Nat} {value heap}
    (hPol : CanonicalU32Digest8 policyWords) (hStmt : CanonicalU32Digest8 stmtWords)
    (hEv : Generic.SourceSemantics.EvalFn (mkToyNarrowSpec policyTarget stmtTarget).source.world
      compressNarrowFixedEntry
      (compressNarrowArgs BN254Fr policyWords 1 stmtWords) [] value heap) :
    policyWords = policyTarget ∧ stmtWords = stmtTarget ∧
    value = .tuple (toyPrevAccWords.map Aiur.Value.field) := by
  have hprep : (mkToyNarrowSpec policyTarget stmtTarget).source.world.prepare compressNarrowFixedEntry
      (compressNarrowArgs BN254Fr policyWords 1 stmtWords) =
      .ok ([],
        [("policy", u32Array8SourceValue BN254Fr policyWords),
         ("stage", .field (1 : BN254Fr)),
         ("stmt", u32Array8SourceValue BN254Fr stmtWords)],
        (.letValue .wildcard
          (.builtin (.assertEq {}) [.var "policy", .tuple ((policyTarget.map fun w => (w : BN254Fr)).map .literal)]) <|
         .letValue .wildcard
          (.builtin (.assertEq {}) [.var "stage", .literal (1 : BN254Fr)]) <|
         .letValue .wildcard
          (.builtin (.assertEq {}) [.var "stmt", .tuple ((stmtTarget.map fun w => (w : BN254Fr)).map .literal)]) <|
         .tuple (toyPrevAccWords.map .literal))) := by
    have hp8 : policyWords.length = 8 := hPol.1
    have hs8 : stmtWords.length = 8 := hStmt.1
    have hpt8 : policyTarget.length = 8 := hpCanon.1
    have hst8 : stmtTarget.length = 8 := htCanon.1
    rcases policyWords with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | ⟨p4, _ | ⟨p5, _ | ⟨p6, _ | ⟨p7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      simp at hp8
    rcases stmtWords with _ | ⟨s0, _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, _ | ⟨s4, _ | ⟨s5, _ | ⟨s6, _ | ⟨s7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      simp at hs8
    have hSym : Generic.Instance.ofSymbol compressNarrowFixedEntry = .ok ⟨compressNarrowFixedEntry, []⟩ :=
      mkToyNarrowSpec_sym policyTarget stmtTarget
    simp [Generic.Source.world, Generic.sourceWorld, Generic.Program.sourceFunction?,
      Generic.Program.findFunction?, FlatAssertSpec.source, FlatAssertSpec.genericProgram,
      FlatAssertSpec.genericFn, FlatAssertSpec.mkGenericBody, mkToyNarrowSpec, FlatVal.genericTy,
      FlatVal.genericExpr, Generic.SourceFunction.prepare, hSym, hpt8, hst8,
      Generic.Ty.toCore, Generic.Ty.subst, compressNarrowArgs, u32Array8SourceValue,
      Generic.wellFormed, Aiur.Value.type, Generic.arguments, bind, Option.bind, Except.bind,
      pure, Except.pure, Except.toOption]
  cases hEv with
  | intro hpr hbody =>
    rw [hprep] at hpr
    injection hpr with hpr
    simp only [Prod.mk.injEq] at hpr
    obtain ⟨rfl, rfl, rfl⟩ := hpr
    obtain ⟨hlookP, hbody2⟩ := evalExpr_letAssertEq_var_tuple hbody
    obtain ⟨_, hbody3⟩ := evalExpr_letAssertEq_var_literal hbody2
    obtain ⟨hlookS, hbody4⟩ := evalExpr_letAssertEq_var_tuple hbody3
    obtain ⟨hval, _⟩ := evalExpr_tuple_literals hbody4
    have hne1 : ("policy" == "stmt") = false := by decide
    have hne2 : ("stage" == "stmt") = false := by decide
    simp only [List.find?_cons, hne1, hne2, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq,
      true_and, u32Array8SourceValue, Aiur.Value.tuple.injEq, List.map_map, Function.comp_def] at hlookP hlookS
    exact ⟨u32Words_eq_of_field_tuple_eq (p := bn254FrModulus) (by decide) hPol.2 hpCanon.2 hlookP,
      u32Words_eq_of_field_tuple_eq (p := bn254FrModulus) (by decide) hStmt.2 htCanon.2 hlookS, hval⟩
  | returned hpr hexit =>
    rw [hprep] at hpr
    injection hpr with hpr
    simp only [Prod.mk.injEq] at hpr
    obtain ⟨rfl, rfl, rfl⟩ := hpr
    have h1 := evalExit_letAssertEq_var_tuple hexit
    have h2 := evalExit_letAssertEq_var_literal h1
    have h3 := evalExit_letAssertEq_var_tuple h2
    exact False.elim (evalExit_tuple_literals_false h3)

/-- Single-lane `Row2.gate` of width `24` (6 lanes: lane 0 holds `lane`, lanes 1..5 empty). -/
def mkNarrowGateRow2 (lane : Lane BN254Fr) (role : Tiling.Role) : Row2 BN254Fr :=
  .gate (.gate lane :: List.replicate 5 .empty) [⟨0, 1, role⟩]

/-- Width-24 unchunked `Periodic.Template2 BN254Fr` for ANY 21-word `allConsts : List BN254Fr`
(`allConsts.length = 21`, slots `0..20` data, `21` sel, `22` mult, 24 rows total). -/
def mkToyNarrowTemplate2 (allConsts : List BN254Fr) : Template2 BN254Fr :=
  let slots : List (SlotDef BN254Fr) := (List.range 23).map SlotDef.column
  -- Row 0: sel * (sel - 1) = 0  (col 21)
  let rBool := mkNarrowGateRow2 { (Lane.zero : Lane BN254Fr) with qm := 1, q0 := -1, c0 := some 21, c1 := some 21 } (.root 0)
  -- Rows 1..21: var i - c_i * sel = 0  (cols i, 21)
  let rData := (List.range 21).map fun i =>
    let c := allConsts.getD i 0
    mkNarrowGateRow2 { (Lane.zero : Lane BN254Fr) with q0 := 1, q1 := -c, c0 := some i, c1 := some 21 } (.root (i + 1))
  -- Row 22: (1 - sel) * mult = mult - sel * mult = 0  (cols 21, 22)
  let rMult := mkNarrowGateRow2 { (Lane.zero : Lane BN254Fr) with qm := -1, q1 := 1, c0 := some 21, c1 := some 22 } (.root 22)
  -- Row 23: unchunked receive message (mult = 22, payload = 0..20)
  let msg : Periodic.Message BN254Fr := (-1, (CALL : BN254Fr), 0, messageCells 24 22 (List.range 21))
  { width := 24
    slots := slots
    messages := [msg]
    rows := [rBool] ++ rData ++ [rMult, .message 0 false]
    virtual := []
    booleans := [] }

/-- Concrete dummy template (`allConsts = 0`) sharing the exact same shadow/cell/slot structure! -/
def toyNarrowTemplate2Dummy : Template2 BN254Fr :=
  mkToyNarrowTemplate2 (List.replicate 21 0)

def mkToyNarrowSharded (s : FlatAssertSpec BN254Fr) : Periodic.Sharded BN254Fr :=
  let C := Bridge.unitCircuit (fun _ => 0) (s.erasedChip, none)
  let T := mkToyNarrowTemplate2 s.allConsts
  { width := 24
    shards := [⟨[C], [T], [1]⟩]
    buses := [(((CALL : BN254Fr), 0), (1, false))] }

def toyNarrowMain (allConsts : List BN254Fr) : Nat → Nat → Nat → BN254Fr :=
  let slotVals : List BN254Fr := allConsts ++ [1, 1]
  fun _ p j =>
    match toyNarrowTemplate2Dummy.rows[p]? with
    | some row =>
      match (toyNarrowTemplate2Dummy.rowCells row)[j]? with
      | some (some s) => slotVals.getD s 0
      | _ => 0
    | none => 0

private theorem template2_rowCells_eq_of_fields {F : Type} [Zero F]
    {t1 t2 : Template2 F}
    (hw : t1.width = t2.width) (hs : t1.slots = t2.slots)
    (hm : t1.messages = t2.messages) (hv : t1.virtual = t2.virtual)
    (r : Row2 F) : t1.rowCells r = t2.rowCells r := by
  have hpm : ∀ m, t1.physMult m = t2.physMult m := by
    intro m; unfold Template2.physMult; rw [hm, hs, hv]
  have hmsg : ∀ m, t1.msgCells m = t2.msgCells m := by
    intro m; unfold Template2.msgCells; rw [hm]
  cases r with
  | gate lanes spans =>
    simp only [Template2.rowCells]
    apply List.flatMap_congr
    intro lu _
    cases lu with
    | empty => rfl
    | gate _ => rfl
    | message m => simp only [Template2.laneCells, hpm m, hmsg m]
  | message m key =>
    simp only [Template2.rowCells, hw, hpm m, hmsg m]

private theorem mkToyNarrowTemplate2_rowCells (allConsts : List BN254Fr) (p : Nat) :
    ((mkToyNarrowTemplate2 allConsts).rows.map (mkToyNarrowTemplate2 allConsts).rowCells)[p]? =
      (toyNarrowTemplate2Dummy.rows.map toyNarrowTemplate2Dummy.rowCells)[p]? := by
  have hrc : ∀ r, (mkToyNarrowTemplate2 allConsts).rowCells r = toyNarrowTemplate2Dummy.rowCells r :=
    template2_rowCells_eq_of_fields rfl rfl rfl rfl
  have hrows : ∀ (xs : List BN254Fr),
      (mkToyNarrowTemplate2 xs).rows.map toyNarrowTemplate2Dummy.rowCells =
      [toyNarrowTemplate2Dummy.rowCells (mkNarrowGateRow2
          { (Lane.zero : Lane BN254Fr) with qm := 1, q0 := -1, c0 := some 21, c1 := some 21 } (.root 0))] ++
        (List.range 21).map (fun i =>
          [some i, some 21, none, none] ++ List.replicate 20 none) ++
        [toyNarrowTemplate2Dummy.rowCells (mkNarrowGateRow2
          { (Lane.zero : Lane BN254Fr) with qm := -1, q1 := 1, c0 := some 21, c1 := some 22 } (.root 22)),
         toyNarrowTemplate2Dummy.rowCells (.message 0 false)] := by
    intro xs
    unfold mkToyNarrowTemplate2
    dsimp only
    simp only [List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def]
    refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) rfl ?_) rfl
    apply List.map_congr_left
    intro i _
    simp [mkNarrowGateRow2, Template2.rowCells, Template2.laneCells, Lane.cells, Lane.zero]
  have hall : (mkToyNarrowTemplate2 allConsts).rows.map (mkToyNarrowTemplate2 allConsts).rowCells =
      toyNarrowTemplate2Dummy.rows.map toyNarrowTemplate2Dummy.rowCells := by
    rw [List.map_congr_left (fun r _ => hrc r), hrows allConsts]
    exact (hrows (List.replicate 21 0)).symm
  rw [hall]

private theorem mkToyNarrowTemplate2_shadow (allConsts : List BN254Fr) :
    (mkToyNarrowTemplate2 allConsts).shadow = toyNarrowTemplate2Dummy.shadow := by
  unfold Template2.shadow
  have hall : (mkToyNarrowTemplate2 allConsts).rows.map (mkToyNarrowTemplate2 allConsts).rowCells =
      toyNarrowTemplate2Dummy.rows.map toyNarrowTemplate2Dummy.rowCells := by
    apply List.ext_getElem
    · simp [mkToyNarrowTemplate2, toyNarrowTemplate2Dummy]
    · intro p hp1 hp2
      have h := mkToyNarrowTemplate2_rowCells allConsts p
      simp only [List.getElem?_eq_getElem hp1, List.getElem?_eq_getElem hp2, Option.some.injEq] at h
      exact h
  have hrows : (mkToyNarrowTemplate2 allConsts).rows.map (fun r => Row.message (0 : BN254Fr) 0 0 ((mkToyNarrowTemplate2 allConsts).rowCells r)) =
      toyNarrowTemplate2Dummy.rows.map (fun r => Row.message (0 : BN254Fr) 0 0 (toyNarrowTemplate2Dummy.rowCells r)) := by
    have h1 := congrArg (List.map (Row.message (0 : BN254Fr) 0 0)) hall
    simpa [List.map_map, Function.comp_def] using h1
  simp only [mkToyNarrowTemplate2, toyNarrowTemplate2Dummy] at hrows ⊢
  exact congrArg (Template.mk (F := BN254Fr) 24 ((List.range 23).map SlotDef.column)) hrows

def toyNarrowShadow : Tiling.System BN254Fr :=
  (⟨[], [toyNarrowTemplate2Dummy], [1]⟩ : Periodic.Layout BN254Fr).shadow 24

private theorem toyNarrowShadow_eq (s : FlatAssertSpec BN254Fr) :
    let sh := ((mkToyNarrowSharded s).layout 0).shadow 24
    sh.places = toyNarrowShadow.places ∧
    sh.keys = toyNarrowShadow.keys ∧
    sh.bound = toyNarrowShadow.bound ∧
    (∀ f i, sh.instId f i = toyNarrowShadow.instId f i) ∧
    (∀ p j, sh.labelAt p j = toyNarrowShadow.labelAt p j) ∧
    (∀ p j, sh.multAt p j = toyNarrowShadow.multAt p j) := by
  have hT : [mkToyNarrowTemplate2 s.allConsts].map Template2.shadow =
      [toyNarrowTemplate2Dummy].map Template2.shadow := by
    simp [mkToyNarrowTemplate2_shadow]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [toyNarrowShadow, mkToyNarrowSharded, Periodic.Sharded.layout, Periodic.Layout.shadow,
      System.places, System.enumerate, System.rowCount, System.cap, hT]
  · simp [toyNarrowShadow, mkToyNarrowSharded, Periodic.Sharded.layout, Periodic.Layout.shadow,
      System.keys, System.enumerate, System.slotCount, System.cap, hT]
  · simp [toyNarrowShadow, mkToyNarrowSharded, Periodic.Sharded.layout, Periodic.Layout.shadow,
      System.bound, System.keys, System.places, System.enumerate, System.slotCount,
      System.rowCount, System.cap, hT]
  · intro f i
    simp only [toyNarrowShadow, mkToyNarrowSharded, Periodic.Sharded.layout, Periodic.Layout.shadow,
      System.instId]
    congr 1
  · intro p j
    simp [toyNarrowShadow, mkToyNarrowSharded, Periodic.Sharded.layout, Periodic.Layout.shadow,
      System.labelAt, System.copyKey, System.label, System.places, System.keys, System.enumerate,
      System.rowCount, System.slotCount, System.cap, hT]
  · intro p j
    simp [toyNarrowShadow, mkToyNarrowSharded, Periodic.Sharded.layout, Periodic.Layout.shadow,
      System.multAt, System.places, System.enumerate, System.rowCount, System.cap, hT]

private theorem arithExpr_denote_inBounds_congr {F : Type} [Field F] {n : Nat}
    {e : Scalar.Circuit.ArithExpr F} (hb : e.inBounds n = true)
    {a b : Nat → F} (hab : ∀ v < n, a v = b v) :
    e.denote a = e.denote b := by
  induction e with
  | const c => rfl
  | var v =>
    simp only [Scalar.Circuit.ArithExpr.inBounds, decide_eq_true_eq] at hb
    exact hab v hb
  | add x y ihx ihy =>
    simp only [Scalar.Circuit.ArithExpr.inBounds, Bool.and_eq_true] at hb
    simp [Scalar.Circuit.ArithExpr.denote, ihx hb.1, ihy hb.2]
  | sub x y ihx ihy =>
    simp only [Scalar.Circuit.ArithExpr.inBounds, Bool.and_eq_true] at hb
    simp [Scalar.Circuit.ArithExpr.denote, ihx hb.1, ihy hb.2]
  | mul x y ihx ihy =>
    simp only [Scalar.Circuit.ArithExpr.inBounds, Bool.and_eq_true] at hb
    simp [Scalar.Circuit.ArithExpr.denote, ihx hb.1, ihy hb.2]

private theorem mkToyNarrowSharded_check (policyWords targetWords : List Nat)
    (hp8 : policyWords.length = 8) (ht8 : targetWords.length = 8) :
    (mkToyNarrowSharded (mkToyNarrowSpec policyWords targetWords)).check = true := by
  set s := mkToyNarrowSpec policyWords targetWords
  have hallLen : s.allConsts.length = 21 := by
    simp [s, FlatAssertSpec.allConsts, FlatAssertSpec.inConsts, mkToyNarrowSpec, FlatVal.words,
      toyPrevAccWords, hp8, ht8]
  set C := Bridge.unitCircuit (fun _ => 0) (s.erasedChip, none)
  set T := mkToyNarrowTemplate2 s.allConsts
  have hNumVars : s.numVars = 21 := hallLen
  have hCWidth : C.width = 23 := by
    simp [C, Bridge.unitCircuit, Bridge.lower, FlatAssertSpec.erasedChip, Erasure.chip,
      FlatAssertSpec.physChip, hNumVars]
  have hCLookups : C.lookups =
      [⟨.sub (.const 0) (.var 22),
        .const (CALL : BN254Fr) :: .const 0 :: (List.range 21).map .var⟩] := by
    have hInLen : s.inConsts.length = 17 := by
      simp [s, FlatAssertSpec.inConsts, mkToyNarrowSpec, FlatVal.words, hp8, ht8]
    have hOutLen : s.outConsts.length = 4 := rfl
    simp only [C, Bridge.unitCircuit, Bridge.lower, Activation.compile, Bridge.receiveLookup,
      FlatAssertSpec.erasedChip, Erasure.chip, Erasure.pack, FlatAssertSpec.physChip,
      FlatAssertSpec.inputWireVars, FlatAssertSpec.mkInputWires_flatMap, hNumVars,
      List.map_nil, List.append_nil, List.flatMap_singleton, List.cons.injEq, and_true]
    congr 1; congr 1; congr 1
    change ((List.range' 0 s.inConsts.length).map (Scalar.Circuit.ArithExpr.var : Nat → Scalar.Circuit.ArithExpr BN254Fr) ++
      (List.range' s.inConsts.length s.outConsts.length).map Scalar.Circuit.ArithExpr.var) =
      (List.range 21).map Scalar.Circuit.ArithExpr.var
    rw [← List.map_append, hInLen, hOutLen]
    rfl
  have hCConstraints : C.constraints =
      Activation.boolean 21 ::
      ((List.range 21).map fun i => Activation.polynomial 21 (subConstPoly i (s.allConsts.getD i 0))) ++
      [.mul (.sub (.const 1) (.var 21)) (.var 22)] := by
    have hzip : s.allConsts.zipIdx.map (fun (c, i) => Activation.polynomial 21 (subConstPoly i c)) =
        (List.range 21).map (fun i => Activation.polynomial 21 (subConstPoly i (s.allConsts.getD i 0))) := by
      apply List.ext_getElem (by simp [hallLen])
      intro k hk1 hk2
      have hk : k < 21 := by simpa using hk2
      have hk' : k < s.allConsts.length := hallLen ▸ hk
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']
    simp [C, Bridge.unitCircuit, Bridge.lower, Activation.compile, Activation.guards,
      FlatAssertSpec.erasedChip, Erasure.chip, FlatAssertSpec.physChip, hNumVars,
      List.map_map, Function.comp_def, hzip]
  have hMeaning : ∀ v < 23, T.logical.meaning v = Tiling.Poly.var v := by
    intro v hv
    exact Template.meaning_column T.logical (by simp [T, Template2.logical, mkToyNarrowTemplate2, hv])
  have hWide : ∀ v < 23, T.logical.wideSlot v = true := by
    intro v hv
    simp [Template.wideSlot, T, Template2.logical, mkToyNarrowTemplate2, hv]
  have hWide22 : T.logical.wideSlot 22 = true := hWide 22 (by omega)
  have hPins : T.pins = [] := by
    simp only [Template2.pins, T, mkToyNarrowTemplate2]; decide
  have hVirtR : T.virtualRows = [] := rfl
  have hBoolR : T.boolRows = [] := rfl
  have hMsgR : T.messageRows = [Row.message (-1) (CALL : BN254Fr) 0 (messageCells 24 22 (List.range 21))] := rfl
  have hTW : T.width = 24 := rfl
  have hTLW : T.logical.width = 24 := rfl
  have hLogRows : T.logical.rows =
      Row.gate (spanLanes 24 (.gate { (Lane.zero : Lane BN254Fr) with qm := 1, q0 := -1, c0 := some 21, c1 := some 21 } :: List.replicate 5 .empty) ⟨0, 1, .root 0⟩) true [.root 0] ::
      ((List.range 21).map fun i =>
        Row.gate (spanLanes 24 (.gate { (Lane.zero : Lane BN254Fr) with q0 := 1, q1 := -(s.allConsts.getD i 0), c0 := some i, c1 := some 21 } :: List.replicate 5 .empty) ⟨0, 1, .root (i + 1)⟩) true [.root (i + 1)]) ++
      [Row.gate (spanLanes 24 (.gate { (Lane.zero : Lane BN254Fr) with qm := -1, q1 := 1, c0 := some 21, c1 := some 22 } :: List.replicate 5 .empty) ⟨0, 1, .root 22⟩) true [.root 22],
       Row.message (-1) (CALL : BN254Fr) 0 (messageCells 24 22 (List.range 21))] := by
    have hfm : ∀ {α β : Type} (f : α → β) (l : List α), l.flatMap (fun a => [f a]) = l.map f := by
      intro α β f l; induction l with | nil => rfl | cons _ _ ih => simp [ih]
    simp only [Template2.logical, hPins, hVirtR, hBoolR, hMsgR]
    simp [T, mkToyNarrowTemplate2, mkNarrowGateRow2, Row2.logical, List.flatMap_map, hfm]
  have hMsgs : T.logical.messages = [(-1, (CALL : BN254Fr), 0, messageCells 24 22 (List.range 21))] := by
    rw [Template.messages, hLogRows]
    simp [List.filterMap_append, List.filterMap_map]
  have hMsgCheck : T.logical.checkUnchunked C = true := by
    unfold Template.checkUnchunked
    rw [hMsgs, hCLookups]
    simp only [List.length_singleton, beq_self_eq_true, List.zip_cons_cons, List.zip_nil_right,
      List.all_cons, List.all_nil, Bool.true_and, Bool.and_true]
    have hM22 : Tiling.Poly.Identical (Tiling.Poly.scale (-1) (T.logical.meaning 22))
        (Tiling.Poly.ofExpr (.sub (.const 0) (.var 22))) = true := by
      rw [hMeaning 22 (by omega)]; decide
    have hCells : messageCells 24 22 (List.range 21) =
        some 22 :: (List.range 21).map some ++ List.replicate 2 none := rfl
    have hPairs : allPairs (fun s expr => T.logical.wideSlot s && Tiling.Poly.Identical (T.logical.meaning s) (Tiling.Poly.ofExpr expr))
        (List.range 21) ((List.range 21).map .var) = true := by
      rw [allPairs_iff]
      have aux : ∀ n ≤ 21, List.Forall₂
          (fun s expr => (T.logical.wideSlot s && Tiling.Poly.Identical (T.logical.meaning s) (Tiling.Poly.ofExpr expr)) = true)
          (List.range n) ((List.range n).map .var) := by
        intro n
        induction n with
        | zero => intro _; exact List.Forall₂.nil
        | succ n ih =>
          intro hn
          rw [List.range_succ, List.map_append, List.map_singleton]
          refine FlatAssertSpec.forall₂_append_cons (ih (by omega)) ?_
          rw [hMeaning n (by omega)]
          simp [hWide n (by omega), Tiling.Poly.Identical, Tiling.Poly.ofExpr]
      exact aux 21 le_rfl
    have hTake : (((List.range 21).map some ++ List.replicate 2 none).take 21).filterMap id = List.range 21 := by
      decide
    rw [hCells]
    simp only [List.cons_append, Template.checkMessage, hTLW, List.length_map, List.length_range,
      hTake, hWide22, hM22, hPairs, show 21 + 1 ≤ 24 by omega, decide_true,
      Bool.and_true]
    clear * -
    decide
  -- Check `T.logical.check C = true` symbolically!
  have hCheckT : T.logical.check C = true := by
    have hRelCheck : T.logical.relations.all (T.logical.checkRelation C) = true := by
      rw [List.all_eq_true]
      intro rel hrel
      rw [Template.relations, hLogRows] at hrel
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.flatMap_map,
        List.append_nil, List.mem_append, List.mem_flatMap, List.mem_range] at hrel
      rcases hrel with (h0 | ⟨i, hi, hri⟩) | (h22 | hmsg)
      · -- Row 0: `sel * (sel - 1)`
        have h0' : rel = (.root 0, [([21, 21], (1 : BN254Fr)), ([21], -1), ([21], 0),
            ([], 0), ([], 0), ([], 0), ([], 0), ([], 0), ([], 0)]) := by
          simpa [spanLanes, Row.relations, Lane.poly, Lane.zero, LaneUse.lane,
            cellPoly, Mono.insert, lanes] using h0
        subst h0'
        have hget0 : C.constraints[0]? = some (Activation.boolean 21) := by
          rw [hCConstraints]; rfl
        simp only [Template.checkRelation, hget0, Bool.and_eq_true]
        refine ⟨by simp [Template.widePoly, hWide 21 (by omega)], ?_⟩
        have hsub : Tiling.Poly.subst T.logical.meaning
            [([21, 21], (1 : BN254Fr)), ([21], -1), ([21], 0), ([], 0), ([], 0), ([], 0), ([], 0), ([], 0), ([], 0)] =
            Tiling.Poly.subst (fun v => Tiling.Poly.var v)
            [([21, 21], (1 : BN254Fr)), ([21], -1), ([21], 0), ([], 0), ([], 0), ([], 0), ([], 0), ([], 0), ([], 0)] := by
          simp [Tiling.Poly.subst, Tiling.Poly.substMono, hMeaning 21 (by omega)]
        rw [hsub]
        decide
      · -- Rows 1..21: `var i - c_i * sel`
        have hi21 : i < 21 := hi
        set c := s.allConsts.getD i 0
        have hri' : rel = (.root (i + 1), [([i, 21], (0 : BN254Fr)), ([i], 1), ([21], -c),
            ([], 0), ([], 0), ([], 0), ([], 0), ([], 0), ([], 0)]) := by
          simpa [spanLanes, Row.relations, Lane.poly, Lane.zero, LaneUse.lane,
            cellPoly, Mono.insert, lanes, hi21, show i ≤ 21 by omega, c] using hri
        subst hri'
        have hget : C.constraints[i + 1]? = some (Activation.polynomial 21 (subConstPoly i c)) := by
          rw [hCConstraints, List.cons_append, List.getElem?_cons_succ,
            List.getElem?_append_left (by simp; omega)]
          simp [hi21, c]
        simp only [Template.checkRelation, hget, Bool.and_eq_true]
        refine ⟨by simp [Template.widePoly, hWide i (by omega), hWide 21 (by omega)], ?_⟩
        unfold Tiling.Poly.Identical
        have hsub : Tiling.Poly.subst T.logical.meaning
            [([i, 21], (0 : BN254Fr)), ([i], 1), ([21], -c), ([], 0), ([], 0), ([], 0), ([], 0), ([], 0), ([], 0)] =
            [([i, 21], (0 : BN254Fr)), ([i], 1), ([21], -c), ([], 0), ([], 0), ([], 0), ([], 0), ([], 0), ([], 0)] := by
          simp [Tiling.Poly.subst, Tiling.Poly.substMono, Tiling.Poly.mul, Tiling.Poly.scale,
            Tiling.Poly.const, Tiling.Poly.var, Tiling.Mono.mul, Tiling.Mono.insert,
            hMeaning i (by omega), hMeaning 21 (by omega)]
          omega
        have hnorm : Tiling.Poly.norm
            [([i, 21], (0 : BN254Fr)), ([i], 1), ([21], -c), ([], 0), ([], 0), ([], 0), ([], 0), ([], 0), ([], 0)] =
            Tiling.Poly.norm [([i], (1 : BN254Fr)), ([21], -c)] := by
          have h1 : Tiling.Poly.norm [([i], (1 : BN254Fr)), ([21], -c)] =
              if c = 0 then [([i], 1)] else [([i], 1), ([21], -c)] :=
            poly_norm_linear_pair hi21 c
          change Tiling.Poly.insertTerm ([i, 21], (0 : BN254Fr))
            (Tiling.Poly.norm [([i], (1 : BN254Fr)), ([21], -c)]) =
            Tiling.Poly.norm [([i], (1 : BN254Fr)), ([21], -c)]
          rw [h1]
          by_cases hc : c = 0
          · simp [hc, Tiling.Poly.insertTerm, Tiling.Mono.lt]
          · simp [hc, Tiling.Poly.insertTerm, Tiling.Mono.lt]
        rw [hsub, hnorm, poly_norm_linear_pair hi21 c, poly_norm_activation_subConstPoly hi21 c]
        exact beq_self_eq_true _
      · -- Row 22: `(1 - sel) * mult`
        have h22' : rel = (.root 22, [([21, 22], (-1 : BN254Fr)), ([21], 0), ([22], 1),
            ([], 0), ([], 0), ([], 0), ([], 0), ([], 0), ([], 0)]) := by
          simpa [spanLanes, Row.relations, Lane.poly, Lane.zero, LaneUse.lane,
            cellPoly, Mono.insert, lanes] using h22
        subst h22'
        have hget : C.constraints[22]? = some (.mul (.sub (.const 1) (.var 21)) (.var 22)) := by
          rw [hCConstraints]
          simp
        simp only [Template.checkRelation, hget, Bool.and_eq_true]
        refine ⟨by simp [Template.widePoly, hWide 21 (by omega), hWide 22 (by omega)], ?_⟩
        have hsub : Tiling.Poly.subst T.logical.meaning
            [([21, 22], (-1 : BN254Fr)), ([21], 0), ([22], 1), ([], 0), ([], 0), ([], 0), ([], 0), ([], 0), ([], 0)] =
            Tiling.Poly.subst (fun v => Tiling.Poly.var v)
            [([21, 22], (-1 : BN254Fr)), ([21], 0), ([22], 1), ([], 0), ([], 0), ([], 0), ([], 0), ([], 0), ([], 0)] := by
          simp [Tiling.Poly.subst, Tiling.Poly.substMono, hMeaning 21 (by omega), hMeaning 22 (by omega)]
        rw [hsub]
        decide
      · simp [Row.relations] at hmsg
    have hConCheck : C.constraints.zipIdx.all (fun (c, j) => T.logical.checkConstraint j c) = true := by
      rw [List.all_eq_true]
      rintro ⟨c, j⟩ hj
      have hlenC : C.constraints.length = 23 := by rw [hCConstraints]; simp
      have hjLt : j < 23 := by
        have := (List.mem_zipIdx hj).2.1
        omega
      have hRelIn : ∃ rel ∈ T.logical.relations, rel.1 = .root j := by
        rw [Template.relations, hLogRows]
        simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.flatMap_map,
          List.append_nil, List.mem_append, List.mem_flatMap, List.mem_range]
        by_cases hj0 : j = 0
        · subst hj0
          simp [Row.relations]
        · by_cases hj22 : j = 22
          · subst hj22
            simp [Row.relations]
          · simp [Row.relations]
            left; right
            refine ⟨j - 1, by omega, by omega⟩
      unfold Template.checkConstraint
      rw [Bool.or_eq_true]
      right
      rw [List.any_eq_true]
      obtain ⟨rel, hmem, hrole⟩ := hRelIn
      exact ⟨rel, hmem, by simp [hrole]⟩
    have hRowsWf : T.logical.rows.all (Row.wellFormed 24) = true := by
      rw [List.all_eq_true]
      intro r hr
      rw [hLogRows] at hr
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map,
        List.mem_range, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | ⟨i, _, rfl⟩ | rfl | rfl
      · decide
      · simp [Row.wellFormed, spanLanes, Lane.wellFormed, Lane.zero, LaneUse.lane, lanes]
      · decide
      · decide
    have hCellsWf : T.logical.rows.all (fun row => row.cells.all fun cell => cell.all (· < T.logical.slots.length)) = true := by
      have hSLen : T.logical.slots.length = 23 := rfl
      rw [hSLen, List.all_eq_true]
      intro r hr
      rw [hLogRows] at hr
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map,
        List.mem_range, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | ⟨i, hi, rfl⟩ | rfl | rfl
      · decide
      · simp [Row.cells, spanLanes, Lane.cells, Lane.zero, LaneUse.lane,
          lanes, show i < 23 by omega]
      · decide
      · decide
    have hSlotsWf : T.logical.slots.zipIdx.all (fun p => T.logical.checkSlot p.2 p.1) = true := by
      rw [List.all_eq_true]
      rintro ⟨sl, idx⟩ hmem
      have hget := List.mem_zipIdx_iff_getElem?.mp hmem
      have hlt : idx < 23 := by
        have := (List.mem_zipIdx hmem).2.1
        simpa [T, Template2.logical, mkToyNarrowTemplate2] using this
      simp only [T, Template2.logical, mkToyNarrowTemplate2,         List.getElem?_map, List.getElem?_range hlt, Option.map_some, Option.some.injEq] at hget
      subst hget
      simp only [Template.checkSlot, Template.colSlot, T, Template2.logical, mkToyNarrowTemplate2]
      interval_cases idx <;> decide
    unfold Template.check
    simp only [hTLW, hRowsWf, hCellsWf, hSlotsWf, hRelCheck, hConCheck, hMsgCheck, Bool.true_or,
      Bool.and_true]
    decide
  -- Check `T.logical.checkGroups C = true` (1 unchunked message = identical to `hMsgCheck`)
  have hCheckGroups : T.logical.checkGroups C = true := by
    have hUnch := hMsgCheck
    have hSplit1 : Template.splitGroups 24 [(-1, (CALL : BN254Fr), 0, messageCells 24 22 (List.range 21))]
        [⟨.sub (.const 0) (.var 22), .const (CALL : BN254Fr) :: .const 0 :: (List.range 21).map .var⟩] =
        [[(-1, (CALL : BN254Fr), 0, messageCells 24 22 (List.range 21))]] := rfl
    unfold Template.checkGroups
    rw [hTLW, hMsgs, hCLookups, hSplit1]
    simp only [List.flatten_singleton, beq_self_eq_true, Bool.true_and, allPairs, List.zipIdx_singleton,
            Bool.and_true, Template.checkGroup]
    unfold Template.checkUnchunked at hUnch
    rw [hMsgs, hCLookups] at hUnch
    simpa only [List.length_singleton, beq_self_eq_true, List.zip_cons_cons, List.zip_nil_right,
      List.all_cons, List.all_nil, Bool.true_and, Bool.and_true] using hUnch
  -- Check `T.checkPhysical`, `T.checkVirtual`, `T.checkBool` (independent of `allConsts`!)
  have hPhys : T.checkPhysical [(((CALL : BN254Fr), 0), (1, false))] = true := by
    have hCells : T.rows.all (fun r => (T.rowCells r).all fun c => c.all fun s =>
        s < T.slots.length && T.slots[s]? != some .invocation) = true := by
      have hdum : toyNarrowTemplate2Dummy.rows.all (fun r => (toyNarrowTemplate2Dummy.rowCells r).all fun c =>
          c.all fun s => s < toyNarrowTemplate2Dummy.slots.length &&
            toyNarrowTemplate2Dummy.slots[s]? != some .invocation) = true := by decide
      rw [List.all_eq_true] at hdum ⊢
      intro r hr
      have ⟨p, hp, hrEq⟩ := List.mem_iff_getElem.mp hr
      have hrc := mkToyNarrowTemplate2_rowCells s.allConsts p
      have hp' : p < toyNarrowTemplate2Dummy.rows.length := by
        simpa [T, mkToyNarrowTemplate2, toyNarrowTemplate2Dummy] using hp
      have hp'' : p < (mkToyNarrowTemplate2 s.allConsts).rows.length := hp
      simp only [List.getElem?_map, List.getElem?_eq_getElem hp'', List.getElem?_eq_getElem hp',
        Option.map_some, Option.some.injEq] at hrc
      change ((mkToyNarrowTemplate2 s.allConsts).rowCells r).all _ = true
      have hrEq' : (mkToyNarrowTemplate2 s.allConsts).rows[p] = r := hrEq
      rw [← hrEq', hrc]
      exact hdum _ (List.getElem_mem hp')
    have hRows : T.rows.all (T.checkRow [(((CALL : BN254Fr), 0), (1, false))]) = true := by
      rw [List.all_eq_true]
      intro r hr
      simp only [T, mkToyNarrowTemplate2, List.cons_append, List.nil_append, List.mem_cons,
        List.mem_append, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | ⟨i, _, rfl⟩ | rfl | rfl
      · simp [Template2.checkRow, T, mkToyNarrowTemplate2, mkNarrowGateRow2,
          Template2.checkSpan, lanes, Lane.zero]
      · simp [Template2.checkRow, T, mkToyNarrowTemplate2, mkNarrowGateRow2,
          Template2.checkSpan, lanes, Lane.zero]
      · simp [Template2.checkRow, T, mkToyNarrowTemplate2, mkNarrowGateRow2,
          Template2.checkSpan, lanes, Lane.zero]
      · simp [Template2.checkRow, Template2.rowMessageOk, T,
          mkToyNarrowTemplate2]
    have hRefs : T.refs = [0] := by
      simp [T, Template2.refs, mkToyNarrowTemplate2, List.flatMap_append, List.flatMap_cons,
        List.flatMap_map, mkNarrowGateRow2, Row2.refs]
    have hMLen : T.messages.length = 1 := rfl
    unfold Template2.checkPhysical
    simp only [hCells, hRows, hRefs, hMLen, Bool.true_and]
    decide
  have hVirt : T.checkVirtual = true := by
    unfold Template2.checkVirtual
    simp [T, mkToyNarrowTemplate2, List.all_eq_true, messageCells]
  have hBool : T.checkBool = true := by
    simp [Template2.checkBool, T, mkToyNarrowTemplate2]
  -- Assemble `Sharded.check = true` without exposing free vars to `decide`
  have hMsgs' : (mkToyNarrowTemplate2 s.allConsts).logical.messages =
      [(-1, (CALL : BN254Fr), 0, messageCells 24 22 (List.range 21))] := hMsgs
  have hCLookups' : (Bridge.unitCircuit (fun _ => 0) (s.erasedChip, none)).lookups =
      [⟨.sub (.const 0) (.var 22),
        .const (CALL : BN254Fr) :: .const 0 :: (List.range 21).map .var⟩] := hCLookups
  have hTLW' : (mkToyNarrowTemplate2 s.allConsts).logical.width = 24 := hTLW
  have hTW' : (mkToyNarrowTemplate2 s.allConsts).width = 24 := hTW
  have hCheckT' : (mkToyNarrowTemplate2 s.allConsts).logical.check
      (Bridge.unitCircuit (fun _ => 0) (s.erasedChip, none)) = true := hCheckT
  have hCheckGroups' : (mkToyNarrowTemplate2 s.allConsts).logical.checkGroups
      (Bridge.unitCircuit (fun _ => 0) (s.erasedChip, none)) = true := hCheckGroups
  have hPhys' : (mkToyNarrowTemplate2 s.allConsts).checkPhysical [(((CALL : BN254Fr), 0), (1, false))] = true := hPhys
  have hVirt' : (mkToyNarrowTemplate2 s.allConsts).checkVirtual = true := hVirt
  have hBool' : (mkToyNarrowTemplate2 s.allConsts).checkBool = true := hBool
  have hSysKeyed : (mkToyNarrowSharded s).system.checkKeyed = true := by
    have hGroups : System.groups (mkToyNarrowTemplate2 s.allConsts).logical
        (Bridge.unitCircuit (fun _ => 0) (s.erasedChip, none)) =
        [[(-1, (CALL : BN254Fr), 0, messageCells 24 22 (List.range 21))]] := by
      unfold System.groups
      rw [hTLW', hMsgs', hCLookups']
      rfl
    have hRomAddr : System.romAddress (Bridge.unitCircuit (fun _ => 0) (s.erasedChip, none)) = none := by
      unfold System.romAddress
      rw [hCLookups']
      rfl
    have hArities : (mkToyNarrowSharded s).system.arities =
        [(((CALL : BN254Fr), 0), 21)] := by
      simp only [System.arities, Periodic.Sharded.system, mkToyNarrowSharded, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil, hMsgs']
      decide
    have hRoles : (mkToyNarrowSharded s).system.roles =
        [(((CALL : BN254Fr), 0), (0, none))] := by
      simp only [System.roles, Periodic.Sharded.system, mkToyNarrowSharded, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil, List.zip_cons_cons,
        List.zip_nil_right, hGroups]
      rfl
    have hRomRec : (mkToyNarrowSharded s).system.romReceivers = [] := by
      simp only [System.romReceivers, Periodic.Sharded.system, mkToyNarrowSharded, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil, List.zip_cons_cons,
        List.zip_nil_right, List.zipIdx_singleton, List.filterMap_cons, List.filterMap_nil,
        hGroups, hRomAddr]
    unfold System.checkKeyed
    rw [hArities, hRoles, hRomRec]
    simp only [Periodic.Sharded.system, mkToyNarrowSharded,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil,
      List.length_singleton, beq_self_eq_true, List.zip_cons_cons, List.zip_nil_right,
      List.all_cons, List.all_nil, Bool.and_true, hTLW', hCheckT', hCheckGroups']
    decide
  unfold Periodic.Sharded.check
  rw [hSysKeyed]
  simp only [Bool.true_and, mkToyNarrowSharded, List.all_cons, List.all_nil,
    List.length_singleton, beq_self_eq_true, Bool.and_true, hTW', hPhys', hVirt', hBool']
  simp []

private theorem mkToyNarrowSharded_rows (policyWords targetWords : List Nat)
    (hp8 : policyWords.length = 8) (ht8 : targetWords.length = 8) :
    let s := mkToyNarrowSpec policyWords targetWords
    let S := mkToyNarrowSharded s
    ∀ p < 24, Scalar.Circuit.Satisfies (S.circuit 0).constraints
      (S.assign 0 (toyNarrowMain s.allConsts 0) p) := by
  intro s S p hp
  have hallLen : s.allConsts.length = 21 := by
    simp [s, FlatAssertSpec.allConsts, FlatAssertSpec.inConsts, mkToyNarrowSpec, FlatVal.words,
      toyPrevAccWords, hp8, ht8]
  set T := mkToyNarrowTemplate2 s.allConsts
  obtain ⟨hShPlaces, _, _, hShInstId, hShLab, hShMult⟩ := toyNarrowShadow_eq s
  have hPlaces : ((S.layout 0).shadow 24).places =
      (List.range 24).map fun r => (0, 0, r) := by
    rw [hShPlaces]; decide
  have hC0 : S.circuit 0 = Periodic.narrowCircuit 24 0 0 := by
    simp [S, Periodic.Sharded.circuit, Periodic.Sharded.labelOffset, Periodic.Sharded.idOffset,
      Periodic.Sharded.base, System.instId, mkToyNarrowSharded]
  rw [hC0]
  set a := S.assign 0 (toyNarrowMain s.allConsts 0) p
  set row := T.rows.getD p (.message 0 false)
  have hFixed : ∀ c, a (24 + c) =
      ((fixedRow 24 row.gateCoef row.flag (row.laneMsg T S.buses) (row.rowMsg T S.buses 0)
        (toyNarrowShadow.labelAt p) (toyNarrowShadow.multAt p))[c]?).getD 0 := by
    intro c
    have hp' : ((S.layout 0).shadow 24).places[p]? = some (0, 0, p) := by
      rw [hPlaces]; simp [hp]
    have hTp : T.rows[p]? = some row := by
      have hpT : p < T.rows.length := by simp [T, mkToyNarrowTemplate2, hp]
      simp [row, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpT]
    have hid : (((S.layout 0).shadow 24).instId 0 0 : BN254Fr) = 0 := by
      rw [hShInstId]; decide
    have hLfun : ((S.layout 0).shadow 24).labelAt p = toyNarrowShadow.labelAt p := funext (hShLab p)
    have hMfun : ((S.layout 0).shadow 24).multAt p = toyNarrowShadow.multAt p := funext (hShMult p)
    have hSw : S.width = 24 := rfl
    have hLt : (S.layout 0).templates[0]? = some T := rfl
    change (if 24 + c < S.width then _ else S.fixedAt (S.layout 0) p (24 + c - S.width)) = _
    simp only [hSw, Nat.not_lt.mpr (Nat.le_add_right 24 c), ↓reduceIte, Nat.add_sub_cancel_left]
    unfold Periodic.Sharded.fixedAt
    simp only [hSw, hp', hLt, hTp, hid, hLfun, hMfun]
  have hGate : ∀ l < 6, ∀ m < 6, a (24 + Periodic.gateCol l m) = row.gateCoef l m := by
    intro l hl m hm
    rw [hFixed, Periodic.fixedRow_gate 24 _ _ _ _ _ _ (by simpa [lanes] using hl) hm]
    rfl
  have hFlag : ∀ l l', l ≤ l' → l' < 6 → a (24 + Periodic.flagCol 24 l l') = row.flag l l' := by
    intro l l' hle hl'
    rw [hFixed, Periodic.fixedRow_flag 24 _ _ _ _ _ _ hle (by simpa [lanes] using hl')]
    rfl
  have hMain : ∀ (j : Nat), j < 24 → a j = toyNarrowMain s.allConsts 0 p j := by
    intro j hj
    change (if j < S.width then toyNarrowMain s.allConsts 0 p j else _) = _
    simp [show S.width = 24 from rfl, hj]
  -- Helper: any single-lane gate row `mkNarrowGateRow2 lane role` satisfies all 6 `spanConstraint`s
  -- as soon as `lane.qm * a 0 * a 1 + (lane.q0 * a 0 + lane.q1 * a 1 + lane.q2 * a 2 + lane.q3 * a 3 + lane.qc) = 0`!
  have hSingleLane : ∀ (lane : Lane BN254Fr) (role : Tiling.Role),
      row = mkNarrowGateRow2 lane role →
      lane.qm * a 0 * a 1 + (lane.q0 * a 0 + lane.q1 * a 1 + lane.q2 * a 2 + lane.q3 * a 3 + lane.qc) = 0 →
      Scalar.Circuit.Satisfies (Periodic.narrowCircuit (F := BN254Fr) 24 0 0).constraints a := by
    intro lane role hrow heq e he
    simp only [Periodic.narrowCircuit, lanes, List.mem_map, List.mem_range] at he
    obtain ⟨l, hl, rfl⟩ := he
    rw [Periodic.spanConstraint_denote]
    by_cases hl0 : l = 0
    · subst hl0
      have hgm : a (24 + Periodic.gateCol 0 0) = lane.qm := by
        rw [hGate 0 (by omega) 0 (by omega), hrow]; rfl
      have hf0 : a (24 + Periodic.flagCol 24 0 0) = 1 := by
        rw [hFlag 0 0 (by omega) (by omega), hrow]; rfl
      have hfnz : ∀ l' ∈ [1, 2, 3, 4, 5], a (24 + Periodic.flagCol 24 0 l') = 0 := by
        intro l' hl'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'
        rcases hl' with rfl | rfl | rfl | rfl | rfl <;>
          (rw [hFlag 0 _ (by omega) (by omega), hrow]; rfl)
      have hlin0 : Periodic.lin 24 0 a =
          lane.q0 * a 0 + lane.q1 * a 1 + lane.q2 * a 2 + lane.q3 * a 3 + lane.qc := by
        unfold Periodic.lin
        rw [hGate 0 (by omega) 1 (by omega), hGate 0 (by omega) 2 (by omega),
          hGate 0 (by omega) 3 (by omega), hGate 0 (by omega) 4 (by omega),
          hGate 0 (by omega) 5 (by omega), hrow]
        rfl
      have hrg : List.range' 0 (lanes 24 - 0) = [0, 1, 2, 3, 4, 5] := rfl
      rw [hrg, hgm]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        hf0, hfnz 1 (by simp), hfnz 2 (by simp), hfnz 3 (by simp), hfnz 4 (by simp),
        hfnz 5 (by simp), one_mul, zero_mul, hlin0]
      exact heq
    · have hgm : a (24 + Periodic.gateCol l 0) = 0 := by
        rw [hGate l hl 0 (by omega), hrow]
        interval_cases l <;> first | exact absurd rfl hl0 | rfl
      have hfl : ∀ l' ∈ List.range' l (lanes 24 - l), a (24 + Periodic.flagCol 24 l l') = 0 := by
        intro l' hl'
        rw [List.mem_range'_1] at hl'
        have hl'6 : l' < 6 := by simp [lanes] at hl'; omega
        rw [hFlag l l' (by omega) hl'6, hrow]
        have hne : (0 == l) = false := beq_false_of_ne (Ne.symm hl0)
        simp [mkNarrowGateRow2, Row2.flag, hne]
      rw [hgm, zero_mul, zero_mul, zero_add]
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hx
      rw [hfl l' hl', zero_mul]
  -- Split on `p = 0`, `p = 22`, `p = 23`, and `1 ≤ p ≤ 21`
  by_cases hp0 : p = 0
  · subst hp0
    have hRow0 : row = mkNarrowGateRow2 { (Lane.zero : Lane BN254Fr) with qm := 1, q0 := -1, c0 := some 21, c1 := some 21 } (.root 0) := rfl
    have ha0 : a 0 = 1 := by
      rw [hMain 0 (by omega)]
      simp [toyNarrowMain, toyNarrowTemplate2Dummy, mkToyNarrowTemplate2, mkNarrowGateRow2,
        Template2.rowCells, Template2.laneCells, Lane.cells, Lane.zero, List.getD_eq_getElem?_getD,
        hallLen]
    have ha1 : a 1 = 1 := by
      rw [hMain 1 (by omega)]
      simp [toyNarrowMain, toyNarrowTemplate2Dummy, mkToyNarrowTemplate2, mkNarrowGateRow2,
        Template2.rowCells, Template2.laneCells, Lane.cells, Lane.zero, List.getD_eq_getElem?_getD,
        hallLen]
    exact hSingleLane _ _ hRow0 (by simp [Lane.zero, ha0, ha1])
  · by_cases hp22 : p = 22
    · subst hp22
      have hRow22 : row = mkNarrowGateRow2 { (Lane.zero : Lane BN254Fr) with qm := -1, q1 := 1, c0 := some 21, c1 := some 22 } (.root 22) := by
        simp [row, T, mkToyNarrowTemplate2, List.getD_eq_getElem?_getD]
      have ha0 : a 0 = 1 := by
        rw [hMain 0 (by omega)]
        simp [toyNarrowMain, toyNarrowTemplate2Dummy, mkToyNarrowTemplate2, mkNarrowGateRow2,
          Template2.rowCells, Template2.laneCells, Lane.cells, Lane.zero, List.getD_eq_getElem?_getD,
          hallLen]
      have ha1 : a 1 = 1 := by
        rw [hMain 1 (by omega)]
        simp [toyNarrowMain, toyNarrowTemplate2Dummy, mkToyNarrowTemplate2, mkNarrowGateRow2,
          Template2.rowCells, Template2.laneCells, Lane.cells, Lane.zero, List.getD_eq_getElem?_getD,
          hallLen]
      exact hSingleLane _ _ hRow22 (by simp [Lane.zero, ha0, ha1])
    · by_cases hp23 : p = 23
      · subst hp23
        have hRow23 : row = .message 0 false := by
          simp [row, T, mkToyNarrowTemplate2, List.getD_eq_getElem?_getD]
        intro e he
        simp only [Periodic.narrowCircuit, lanes, List.mem_map, List.mem_range] at he
        obtain ⟨l, hl, rfl⟩ := he
        rw [Periodic.spanConstraint_denote, hGate l hl 0 (by omega), hRow23]
        simp only [Row2.gateCoef, Bool.false_eq_true, false_and, ↓reduceIte, zero_mul, zero_add]
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hx
        rw [List.mem_range'_1] at hl'
        have hl'6 : l' < 6 := by simp [lanes] at hl'; omega
        rw [hFlag l l' (by omega) hl'6, hRow23]
        simp [Row2.flag]
      · -- Rows `p = i + 1` for `0 ≤ i < 21`
        set i := p - 1
        have hi21 : i < 21 := by omega
        set c := s.allConsts.getD i 0
        have hpEq : p = i + 1 := by omega
        have hRowP : row =
            mkNarrowGateRow2 { (Lane.zero : Lane BN254Fr) with q0 := 1, q1 := -c, c0 := some i, c1 := some 21 } (.root p) := by
          simp only [row, hpEq, T, mkToyNarrowTemplate2, List.getD_eq_getElem?_getD,
            List.cons_append, List.nil_append, List.getElem?_cons_succ]
          rw [List.getElem?_append_left (by simp; omega)]
          simp [hi21, c]
        have ha0 : a 0 = c := by
          rw [hMain 0 (by omega)]
          simp only [toyNarrowMain, hpEq, toyNarrowTemplate2Dummy, mkToyNarrowTemplate2,
            List.cons_append, List.nil_append, List.getElem?_cons_succ]
          rw [List.getElem?_append_left (by simp; omega)]
          simp [mkNarrowGateRow2, Template2.rowCells, Template2.laneCells, Lane.cells, Lane.zero,
            hi21, List.getD_eq_getElem?_getD, List.getElem?_append_left (hallLen ▸ hi21), c]
        have ha1 : a 1 = 1 := by
          rw [hMain 1 (by omega)]
          simp only [toyNarrowMain, hpEq, toyNarrowTemplate2Dummy, mkToyNarrowTemplate2,
            List.cons_append, List.nil_append, List.getElem?_cons_succ]
          rw [List.getElem?_append_left (by simp; omega)]
          simp [mkNarrowGateRow2, Template2.rowCells, Template2.laneCells, Lane.cells, Lane.zero,
            hi21, List.getD_eq_getElem?_getD, hallLen]
        exact hSingleLane _ _ hRowP (by simp [Lane.zero, ha0, ha1])

/-- Symbolic copy + message ledger balance for `mkToyNarrowSharded` for ANY 21-word `allConsts`! -/
private theorem mkToyNarrowSharded_balanced (policyWords targetWords : List Nat)
    (hp8 : policyWords.length = 8) (ht8 : targetWords.length = 8) :
    let s := mkToyNarrowSpec policyWords targetWords
    let S := mkToyNarrowSharded s
    Finsupp.mapDomain trimZeros
      (S.ledger (fun _ => 24) (toyNarrowMain s.allConsts) +
        Periodic.compactLedger S [] (fun _ => 0) (fun _ _ _ => 0) +
        S.padded2 (Part.request S.width (Bridge.encode (fun _ => 0) s.erasedRootMsg))) = 0 := by
  intro s S
  have hallLen : s.allConsts.length = 21 := by
    simp [s, FlatAssertSpec.allConsts, FlatAssertSpec.inConsts, mkToyNarrowSpec, FlatVal.words,
      toyPrevAccWords, hp8, ht8]
  have hT : Periodic.compactLedger S [] (fun _ => 0) (fun _ _ _ => 0) = 0 := by
    simp [Periodic.compactLedger]
  rw [hT, add_zero]
  set T := mkToyNarrowTemplate2 s.allConsts
  obtain ⟨hShPlaces, _, _, hShInstId, hShLab, hShMult⟩ := toyNarrowShadow_eq s
  suffices hZero : S.ledger (fun _ => 24) (toyNarrowMain s.allConsts) +
      S.padded2 (Part.request S.width (Bridge.encode (fun _ => 0) s.erasedRootMsg)) = 0 by
    rw [hZero, Finsupp.mapDomain_zero]
  have hC0 : S.circuit 0 = Periodic.narrowCircuit 24 0 0 := by
    simp [S, Periodic.Sharded.circuit, Periodic.Sharded.labelOffset, Periodic.Sharded.idOffset,
      Periodic.Sharded.base, System.instId, mkToyNarrowSharded]
  -- Compute `S.padded2 (Part.request ...)` symbolically
  have hReqEnc : S.padded2 (Part.request S.width (Bridge.encode (fun _ => 0) s.erasedRootMsg)) =
      Finsupp.single ((1 : BN254Fr) :: s.allConsts ++ [0, 0]) 1 := by
    rw [s.encode_erasedRootMsg]
    have hNoChunk : (Part.request 24 ((CALL : BN254Fr) :: (0 : BN254Fr) :: s.allConsts)).chunks = [] := by
      simp [Part.request, hallLen]
    have hNarrow : (Part.request 24 ((CALL : BN254Fr) :: (0 : BN254Fr) :: s.allConsts)).narrow =
        Finsupp.single ((CALL : BN254Fr) :: (0 : BN254Fr) :: s.allConsts) 1 := by
      simp [Part.narrow, Part.wide, Part.tuple, Part.request, hallLen]
    simp [Periodic.Sharded.padded2, S, mkToyNarrowSharded, hNarrow, Finsupp.mapDomain_single,
      Periodic.Sharded.encode2, hallLen]
  -- Concrete shadow invariants (proved once by `decide`)
  have hSlotLab : ∀ p < 24, ∀ j < 24, ∀ sl,
      (toyNarrowTemplate2Dummy.rows[p]?.bind fun r => (toyNarrowTemplate2Dummy.rowCells r)[j]?).join = some sl →
      toyNarrowShadow.labelAt p j = ((sl + 1 : Nat) : BN254Fr) ∧ sl < 23 := by
    have hall : (List.range 24).all (fun p => (List.range 24).all fun j =>
        match (toyNarrowTemplate2Dummy.rows[p]?.bind fun r => (toyNarrowTemplate2Dummy.rowCells r)[j]?).join with
        | some sl => (toyNarrowShadow.labelAt p j == ((sl + 1 : Nat) : BN254Fr)) && decide (sl < 23)
        | none => true) = true := by decide
    intro p hp j hj sl hcell
    have h1 := List.all_eq_true.mp hall p (List.mem_range.mpr hp)
    have h2 := List.all_eq_true.mp h1 j (List.mem_range.mpr hj)
    rw [hcell] at h2
    simpa [Bool.and_eq_true] using h2
  have hNoneMult0 : ∀ p < 24, ∀ j < 24,
      (toyNarrowTemplate2Dummy.rows[p]?.bind fun r => (toyNarrowTemplate2Dummy.rowCells r)[j]?).join = none →
      toyNarrowShadow.multAt p j = 0 := by
    have hall : (List.range 24).all (fun p => (List.range 24).all fun j =>
        match (toyNarrowTemplate2Dummy.rows[p]?.bind fun r => (toyNarrowTemplate2Dummy.rowCells r)[j]?).join with
        | none => toyNarrowShadow.multAt p j == 0
        | some _ => true) = true := by decide
    intro p hp j hj hnone
    have h1 := List.all_eq_true.mp hall p (List.mem_range.mpr hp)
    have h2 := List.all_eq_true.mp h1 j (List.mem_range.mpr hj)
    rw [hnone] at h2
    simpa using h2
  -- Pure algebraic proof of copy-multiplicity balance for every `sl < 23` via `System.multAt_placed`
  -- (ZERO `decide` on `Template.occurrences`, ZERO `maxRecDepth`!).
  have hSlotMultSum : ∀ sl < 23,
      (∑ p ∈ Finset.range 24, ∑ j ∈ Finset.range 24,
        if (toyNarrowTemplate2Dummy.rows[p]?.bind fun r => (toyNarrowTemplate2Dummy.rowCells r)[j]?).join == some sl
        then toyNarrowShadow.multAt p j else 0) = 0 := by
    set Tsh := toyNarrowTemplate2Dummy.shadow
    have hCellEq : ∀ p j, Tsh.cell p j =
        (toyNarrowTemplate2Dummy.rows[p]?.bind fun r => (toyNarrowTemplate2Dummy.rowCells r)[j]?).join := by
      intro p j
      simp only [Tsh, Template.cell, Template2.shadow, List.getElem?_map]
      cases toyNarrowTemplate2Dummy.rows[p]? with
      | none => rfl
      | some r =>
        simp only [Option.map_some, Option.bind_some, Row.cells]
        cases (toyNarrowTemplate2Dummy.rowCells r)[j]? <;> rfl
    have hPlaces : ∀ p < 24, toyNarrowShadow.places[p]? = some (0, 0, p) := by
      have hpL : toyNarrowShadow.places = (List.range 24).map fun r => (0, 0, r) := by decide
      intro p hp; rw [hpL]; simp [hp]
    have hT0 : toyNarrowShadow.templates[0]? = some Tsh := rfl
    have hRowsLen : Tsh.rows.length = 24 := rfl
    have hWidth : Tsh.width = 24 := rfl
    intro sl hsl
    have hWit : ∃ p < 24, ∃ j < 24, Tsh.cell p j = some sl := by
      by_cases h21 : sl = 21
      · subst h21; exact ⟨0, by decide, 0, by decide, by decide⟩
      · by_cases h22 : sl = 22
        · subst h22; exact ⟨23, by decide, 0, by decide, by decide⟩
        · have hsl21 : sl < 21 := by omega
          refine ⟨23, by decide, sl + 1, by omega, ?_⟩
          clear * - hsl21
          interval_cases sl <;> decide
    obtain ⟨p₀, hp₀, j₀, hj₀, hcell₀⟩ := hWit
    obtain ⟨ra, ja, hanc⟩ := Template.anchor_exists (hRowsLen ▸ hp₀) (hWidth ▸ hj₀) hcell₀
    obtain ⟨hra, hja, hacell⟩ := Template.anchor_spec hanc
    set S_sl := (Finset.range 24 ×ˢ Finset.range 24).filter fun e => Tsh.cell e.1 e.2 = some sl
    have hOcc : Tsh.occurrences sl = S_sl.card := by
      simp [Template.occurrences, hRowsLen, hWidth, S_sl]
    have hMemA : (ra, ja) ∈ S_sl := by
      simp only [S_sl, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨hRowsLen ▸ hra, hWidth ▸ hja⟩, hacell⟩
    have hStep1 :
        (∑ p ∈ Finset.range 24, ∑ j ∈ Finset.range 24,
          if (toyNarrowTemplate2Dummy.rows[p]?.bind fun r => (toyNarrowTemplate2Dummy.rowCells r)[j]?).join == some sl
          then toyNarrowShadow.multAt p j else 0) =
        ∑ e ∈ S_sl, toyNarrowShadow.multAt e.1 e.2 := by
      rw [← Finset.sum_product']
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e _
      rw [← hCellEq e.1 e.2]
      by_cases hc : Tsh.cell e.1 e.2 = some sl
      · simp [hc]
      · simp [hc]
    rw [hStep1]
    have hEach : ∀ e ∈ S_sl, toyNarrowShadow.multAt e.1 e.2 =
        if e = (ra, ja) then (S_sl.card : BN254Fr) - 1 else -1 := by
      intro e he
      simp only [S_sl, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at he
      rw [System.multAt_placed (hPlaces e.1 he.1.1) hT0 he.2, hanc, hOcc]
      have heq : (some (ra, ja) = some (e.1, e.2)) ↔ (e = (ra, ja)) := by
        rcases e with ⟨p, j⟩
        simp [Option.some.injEq, Prod.mk.injEq, eq_comm]
      by_cases h : e = (ra, ja)
      · simp [heq.mpr h, h]
      · have hne : ¬ (some (ra, ja) = some (e.1, e.2)) := fun h' => h (heq.mp h')
        simp [hne, h]
    rw [Finset.sum_congr rfl hEach]
    rw [← Finset.add_sum_erase S_sl _ hMemA]
    simp only [↓reduceIte]
    have hErase : ∑ e ∈ S_sl.erase (ra, ja), (if e = (ra, ja) then (S_sl.card : BN254Fr) - 1 else -1) =
        ∑ _e ∈ S_sl.erase (ra, ja), (-1 : BN254Fr) := by
      apply Finset.sum_congr rfl
      intro e he
      simp [Finset.ne_of_mem_erase he]
    rw [hErase, Finset.sum_const, Finset.card_erase_of_mem hMemA, nsmul_eq_mul,
      Nat.cast_sub (Finset.card_pos.mpr ⟨_, hMemA⟩), Nat.cast_one]
    ring
  set slotVals : List BN254Fr := s.allConsts ++ [1, 1]
  -- Compute each row's ledger cleanly via `Periodic.{rowMessage,laneMessage,copyLookup}_entry`!
  have hRowLed : ∀ p < 24,
      (Periodic.narrowCircuit 24 0 0).rowLedger (S.assign 0 (toyNarrowMain s.allConsts 0) p) =
        (∑ j ∈ Finset.range 24, ∑ sl ∈ Finset.range 23,
          Finsupp.single [((Periodic.copyKey (sl + 1) : Nat) : BN254Fr), slotVals.getD sl 0]
            (if (toyNarrowTemplate2Dummy.rows[p]?.bind fun r => (toyNarrowTemplate2Dummy.rowCells r)[j]?).join == some sl
             then toyNarrowShadow.multAt p j else 0)) +
        (if p = 23 then Finsupp.single ((1 : BN254Fr) :: s.allConsts ++ [0, 0]) (-1) else 0) := by
    intro p hp
    set a := S.assign 0 (toyNarrowMain s.allConsts 0) p
    set row := T.rows.getD p (.message 0 false)
    have hFixed : ∀ c, a (24 + c) =
        ((fixedRow 24 row.gateCoef row.flag (row.laneMsg T S.buses) (row.rowMsg T S.buses 0)
          (toyNarrowShadow.labelAt p) (toyNarrowShadow.multAt p))[c]?).getD 0 := by
      intro c
      have hPlaces : ((S.layout 0).shadow 24).places = (List.range 24).map fun r => (0, 0, r) := by
        rw [hShPlaces]; decide
      have hp' : ((S.layout 0).shadow 24).places[p]? = some (0, 0, p) := by rw [hPlaces]; simp [hp]
      have hTp : T.rows[p]? = some row := by
        have hpT : p < T.rows.length := by simp [T, mkToyNarrowTemplate2, hp]
        simp [row, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpT]
      have hid : (((S.layout 0).shadow 24).instId 0 0 : BN254Fr) = 0 := by rw [hShInstId]; decide
      have hLfun : ((S.layout 0).shadow 24).labelAt p = toyNarrowShadow.labelAt p := funext (hShLab p)
      have hMfun : ((S.layout 0).shadow 24).multAt p = toyNarrowShadow.multAt p := funext (hShMult p)
      have hSw : S.width = 24 := rfl
      have hLt : (S.layout 0).templates[0]? = some T := rfl
      change (if 24 + c < S.width then _ else S.fixedAt (S.layout 0) p (24 + c - S.width)) = _
      simp only [hSw, Nat.not_lt.mpr (Nat.le_add_right 24 c), ↓reduceIte, Nat.add_sub_cancel_left]
      unfold Periodic.Sharded.fixedAt
      simp only [hSw, hp', hLt, hTp, hid, hLfun, hMfun]
    have hRowShape : (p = 23 ∧ row = .message 0 false) ∨
        (p ≠ 23 ∧ ∃ lane role, row = mkNarrowGateRow2 lane role) := by
      by_cases hp23 : p = 23
      · left; exact ⟨hp23, by subst hp23; simp [row, T, mkToyNarrowTemplate2, List.getD_eq_getElem?_getD]⟩
      · right; refine ⟨hp23, ?_⟩
        by_cases hp0 : p = 0
        · subst hp0; exact ⟨_, _, rfl⟩
        · by_cases hp22 : p = 22
          · subst hp22
            exact ⟨{ (Lane.zero : Lane BN254Fr) with qm := -1, q1 := 1, c0 := some 21, c1 := some 22 }, .root 22,
              by simp [row, T, mkToyNarrowTemplate2, List.getD_eq_getElem?_getD]⟩
          · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp0
            have hi : k < 21 := by omega
            refine ⟨{ (Lane.zero : Lane BN254Fr) with
                q0 := 1, q1 := -(s.allConsts.getD k 0),
                c0 := some k, c1 := some 21 }, .root (k + 1), ?_⟩
            simp only [row, T, mkToyNarrowTemplate2,
              List.getD_eq_getElem?_getD, List.cons_append, List.nil_append, List.getElem?_cons_succ]
            rw [List.getElem?_append_left (by simp; omega)]
            simp [hi]
    -- 1. All 6 lane messages have multiplicity 0
    have hLMs : ((List.range (lanes 24)).map fun l => (Periodic.laneMessage (F := BN254Fr) 24 l).entry a).sum = 0 := by
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
      have hl6 : l < 6 := by simp [lanes] at hl; exact hl
      have hlm1 : a (24 + Periodic.laneMsgCol 24 l 1) = row.laneMsg T S.buses l 1 := by
        rw [hFixed, Periodic.fixedRow_laneMsg 24 _ _ _ _ _ _ (by simpa [lanes] using hl6) (by decide)]; rfl
      have hlm2 : a (24 + Periodic.laneMsgCol 24 l 2) = row.laneMsg T S.buses l 2 := by
        rw [hFixed, Periodic.fixedRow_laneMsg 24 _ _ _ _ _ _ (by simpa [lanes] using hl6) (by decide)]; rfl
      rw [Periodic.laneMessage_entry, hlm1, hlm2]
      have h0 : row.laneMsg T S.buses l 1 = 0 ∧ row.laneMsg T S.buses l 2 = 0 := by
        rcases hRowShape with ⟨_, hEq⟩ | ⟨_, lane, role, hEq⟩
        · rw [hEq]; exact ⟨rfl, rfl⟩
        · rw [hEq]; interval_cases l <;> exact ⟨rfl, rfl⟩
      simp [h0.1, h0.2]
    -- 2. Row message is `single (1 :: s.allConsts ++ [0, 0]) (-1)` at `p = 23`, else `0`
    have hRM : (Periodic.rowMessage (F := BN254Fr) 24 0).entry a =
        if p = 23 then Finsupp.single ((1 : BN254Fr) :: s.allConsts ++ [0, 0]) (-1) else 0 := by
      rw [Periodic.rowMessage_entry]
      have hrm : ∀ k < 5, a (24 + Periodic.rowMsgCol 24 k) = row.rowMsg T S.buses 0 k := by
        intro k hk
        rw [hFixed, Periodic.fixedRow_rowMsg 24 _ _ _ _ _ _ hk]
        rfl
      rcases hRowShape with ⟨hp23, hEq⟩ | ⟨hp23, lane, role, hEq⟩
      · simp only [hp23, ↓reduceIte]
        have hrm23 : ∀ k < 5, row.rowMsg T S.buses 0 k = ([1, 0, -1, 0, 0] : List BN254Fr).getD k 0 := by
          intro k hk
          rw [hEq]
          interval_cases k <;>
            simp [Row2.rowMsg, T, mkToyNarrowTemplate2, S, mkToyNarrowSharded, Template2.physMult,
              codeOf, messageCells]
        have h23 : ∀ (j : Nat), j < 24 → a j =
            if j = 0 then 1 else if j - 1 < 21 then s.allConsts.getD (j - 1) 0 else 0 := by
          intro j hj
          change (if j < S.width then toyNarrowMain s.allConsts 0 p j else _) = _
          simp only [show S.width = 24 from rfl, hj, ↓reduceIte, hp23]
          interval_cases j <;>
            simp [toyNarrowMain, toyNarrowTemplate2Dummy, mkToyNarrowTemplate2, Template2.rowCells,
              Template2.physMult, Template2.msgCells, messageCells, List.getD_eq_getElem?_getD,
              hallLen]
        have htail : a 1 :: (List.range 22).map (fun j => a (j + 2)) = s.allConsts ++ [0, 0] := by
          apply List.ext_getElem (by simp [hallLen])
          intro k hk1 hk2
          have hk23 : k < 23 := by simpa [hallLen] using hk2
          cases k with
          | zero =>
            have h0lt : 0 < s.allConsts.length := by omega
            simp only [List.getElem_cons_zero, h23 1 (by omega), show ¬ (1 = 0) by omega,
              show 1 - 1 < 21 by omega, ↓reduceIte, Nat.sub_self, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem h0lt, Option.getD_some, List.getElem_append_left h0lt]
          | succ k' =>
            simp only [List.getElem_cons_succ, List.getElem_map, List.getElem_range]
            rw [h23 (k' + 2) (by omega)]
            by_cases hk21 : k' + 1 < 21
            · have hk' : k' + 1 < s.allConsts.length := hallLen ▸ hk21
              simp [hk21, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk',
                List.getElem_append_left hk']
            · have hk2' : k' = 20 ∨ k' = 21 := by omega
              rcases hk2' with rfl | rfl
              · simp [List.getElem_append_right (by omega : s.allConsts.length ≤ 21), hallLen]
              · simp [List.getElem_append_right (by omega : s.allConsts.length ≤ 22), hallLen]
        rw [hrm 0 (by omega), hrm 1 (by omega), hrm 2 (by omega), hrm 3 (by omega), hrm 4 (by omega),
          hrm23 0 (by omega), hrm23 1 (by omega), hrm23 2 (by omega), hrm23 3 (by omega), hrm23 4 (by omega),
          h23 0 (by omega)]
        have hM : (0 : BN254Fr) + (-1 : BN254Fr) * 1 = -1 := by ring
        have hK1 : a 1 + (0 : BN254Fr) + 0 * ((0 : Nat) : BN254Fr) = a 1 := by ring
        simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, ↓reduceIte, show (24 - 2 : Nat) = 22 from rfl]
        rw [hM, hK1]
        exact congrArg (fun l => Finsupp.single ((1 : BN254Fr) :: l) (-1)) htail
      · simp only [hp23, ↓reduceIte]
        rw [hrm 1 (by omega), hrm 2 (by omega), hEq]
        simp [Row2.rowMsg, mkNarrowGateRow2]
    -- 3. Copy lookups
    have hCopies : ((List.range 24).map fun j => (Periodic.copyLookup (F := BN254Fr) 24 0 j).entry a).sum =
        ∑ j ∈ Finset.range 24, ∑ sl ∈ Finset.range 23,
          Finsupp.single [((Periodic.copyKey (sl + 1) : Nat) : BN254Fr), slotVals.getD sl 0]
            (if (toyNarrowTemplate2Dummy.rows[p]?.bind fun r => (toyNarrowTemplate2Dummy.rowCells r)[j]?).join == some sl
             then toyNarrowShadow.multAt p j else 0) := by
      rw [list_sum_map_range]
      apply Finset.sum_congr rfl
      intro j hj
      have hj24 := Finset.mem_range.mp hj
      have hlab : a (24 + Periodic.labelCol 24 j) = toyNarrowShadow.labelAt p j := by
        rw [hFixed, Periodic.fixedRow_label 24 _ _ _ _ _ _ hj24]; rfl
      have hmult : a (24 + Periodic.multCol 24 j) = toyNarrowShadow.multAt p j := by
        rw [hFixed, Periodic.fixedRow_mult 24 _ _ _ _ _ _ hj24]; rfl
      have hVal : a j =
          match (toyNarrowTemplate2Dummy.rows[p]?.bind fun r => (toyNarrowTemplate2Dummy.rowCells r)[j]?).join with
          | some sl => slotVals.getD sl 0
          | none => 0 := by
        change (if j < S.width then toyNarrowMain s.allConsts 0 p j else _) = _
        simp only [show S.width = 24 from rfl, hj24, ↓reduceIte, toyNarrowMain, slotVals]
        cases h1 : toyNarrowTemplate2Dummy.rows[p]? with
        | none => rfl
        | some r =>
          simp only [Option.bind_some]
          cases h2 : (toyNarrowTemplate2Dummy.rowCells r)[j]? with
          | none => simp []
          | some o => cases o <;> simp []
      cases hcell : (toyNarrowTemplate2Dummy.rows[p]?.bind fun r => (toyNarrowTemplate2Dummy.rowCells r)[j]?).join with
      | none =>
        have hm0 := hNoneMult0 p hp j hj24 hcell
        simp only [Tiling.Lookup.entry, Periodic.copyLookup, Scalar.Circuit.ArithExpr.denote,
          Periodic.fx, hmult, hm0, Finsupp.single_zero]
        symm
        apply Finset.sum_eq_zero
        intro sl _; simp
      | some sl =>
        obtain ⟨hslLab, hsl23⟩ := hSlotLab p hp j hj24 sl hcell
        rw [Periodic.copyLookup_entry 24 0 j a (sl + 1) (by rw [hlab, hslLab]), hmult, hVal, hcell]
        symm
        rw [Finset.sum_eq_single sl]
        · simp
        · intro sl' _ hne
          have hbeq : (some sl == some sl') = false := beq_false_of_ne (fun h => hne (Option.some.inj h).symm)
          simp [hbeq]
        · intro hnot; exact absurd (Finset.mem_range.mpr hsl23) hnot
    simp only [Tiling.Circuit.rowLedger, Periodic.narrowCircuit, List.map_cons, List.sum_cons,
      List.map_append, List.sum_append, List.map_map, Function.comp_def, hRM, hLMs, hCopies,
      zero_add, add_comm]
  -- Sum over `p ∈ range 24`, cancel row 23's message with `hReqEnc`, and swap copy sum over `sl ∈ range 23`!
  have hSlen : S.shards.length = 1 := rfl
  rw [Periodic.Sharded.ledger, hSlen, Finset.range_one, Finset.sum_singleton, hC0]
  rw [Finset.sum_congr rfl (fun p hp => hRowLed p (Finset.mem_range.mp hp))]
  rw [Finset.sum_add_distrib, add_assoc]
  simp only [Finset.sum_ite_eq', Finset.mem_range, show 23 < 24 by omega, ↓reduceIte,
    hReqEnc, ← Finsupp.single_add, neg_add_cancel, Finsupp.single_zero, add_zero]
  have hSwap :
      (∑ p ∈ Finset.range 24, ∑ j ∈ Finset.range 24, ∑ sl ∈ Finset.range 23,
        Finsupp.single [((Periodic.copyKey (sl + 1) : Nat) : BN254Fr), slotVals.getD sl 0]
          (if (toyNarrowTemplate2Dummy.rows[p]?.bind fun r => (toyNarrowTemplate2Dummy.rowCells r)[j]?).join == some sl
           then toyNarrowShadow.multAt p j else 0)) =
      ∑ sl ∈ Finset.range 23,
        Finsupp.single [((Periodic.copyKey (sl + 1) : Nat) : BN254Fr), slotVals.getD sl 0]
          (∑ p ∈ Finset.range 24, ∑ j ∈ Finset.range 24,
            if (toyNarrowTemplate2Dummy.rows[p]?.bind fun r => (toyNarrowTemplate2Dummy.rowCells r)[j]?).join == some sl
            then toyNarrowShadow.multAt p j else 0) := by
    calc
      (∑ p ∈ Finset.range 24, ∑ j ∈ Finset.range 24, ∑ sl ∈ Finset.range 23,
          Finsupp.single [((Periodic.copyKey (sl + 1) : Nat) : BN254Fr), slotVals.getD sl 0]
            (if (toyNarrowTemplate2Dummy.rows[p]?.bind fun r => (toyNarrowTemplate2Dummy.rowCells r)[j]?).join == some sl
             then toyNarrowShadow.multAt p j else 0))
        = ∑ p ∈ Finset.range 24, ∑ sl ∈ Finset.range 23, ∑ j ∈ Finset.range 24,
            Finsupp.single [((Periodic.copyKey (sl + 1) : Nat) : BN254Fr), slotVals.getD sl 0]
              (if (toyNarrowTemplate2Dummy.rows[p]?.bind fun r => (toyNarrowTemplate2Dummy.rowCells r)[j]?).join == some sl
               then toyNarrowShadow.multAt p j else 0) := by
          apply Finset.sum_congr rfl; intro p _; rw [Finset.sum_comm]
      _ = ∑ sl ∈ Finset.range 23, ∑ p ∈ Finset.range 24, ∑ j ∈ Finset.range 24,
            Finsupp.single [((Periodic.copyKey (sl + 1) : Nat) : BN254Fr), slotVals.getD sl 0]
              (if (toyNarrowTemplate2Dummy.rows[p]?.bind fun r => (toyNarrowTemplate2Dummy.rowCells r)[j]?).join == some sl
               then toyNarrowShadow.multAt p j else 0) := by
          rw [Finset.sum_comm]
      _ = ∑ sl ∈ Finset.range 23,
            Finsupp.single [((Periodic.copyKey (sl + 1) : Nat) : BN254Fr), slotVals.getD sl 0]
              (∑ p ∈ Finset.range 24, ∑ j ∈ Finset.range 24,
                if (toyNarrowTemplate2Dummy.rows[p]?.bind fun r => (toyNarrowTemplate2Dummy.rowCells r)[j]?).join == some sl
                then toyNarrowShadow.multAt p j else 0) := by
          apply Finset.sum_congr rfl
          intro sl _
          set k := [((Periodic.copyKey (sl + 1) : Nat) : BN254Fr), slotVals.getD sl 0]
          change ∑ p ∈ Finset.range 24, ∑ j ∈ Finset.range 24,
            Finsupp.singleAddHom k _ = Finsupp.singleAddHom k _
          simp only [map_sum]
  rw [hSwap]
  apply Finset.sum_eq_zero
  intro sl hsl
  rw [hSlotMultSum sl (Finset.mem_range.mp hsl), Finsupp.single_zero]

/-- Polymorphic Stage 3 (`CompressNarrowFixed`) `NarrowCompactStageWitness BN254Fr` for ANY
8-word `policyWords` and `targetWords`! -/
def mkToyNarrowWitness (policyWords targetWords : List Nat)
    (hp8 : policyWords.length = 8) (ht8 : targetWords.length = 8) :
    NarrowCompactStageWitness BN254Fr (mkToyNarrowSpec policyWords targetWords).source
      [compressNarrowFixedEntry] compressNarrowFixedEntry
      (compressNarrowArgs BN254Fr policyWords 1 targetWords) :=
  let s := mkToyNarrowSpec policyWords targetWords
  let hSym := mkToyNarrowSpec_sym policyWords targetWords
  let hNod := mkToyNarrowSpec_nodup policyWords targetWords
  let S := mkToyNarrowSharded s
  have hallLen : s.allConsts.length = 21 := by
    simp [s, FlatAssertSpec.allConsts, FlatAssertSpec.inConsts, mkToyNarrowSpec, FlatVal.words,
      toyPrevAccWords, hp8, ht8]
  have hSh := toyNarrowShadow_eq s
  { specialized := s.specialized hSym hNod
    compiled := s.compiled hSym hNod
    prepared := s.prepared hSym hNod
    cfg := trivialDepthCfg
    certified := s.certified hSym hNod
    hbits := by decide
    id := fun _ => .ok 0
    plan := s.plan hSym hNod
    activated := s.activated hSym hNod
    entry := by simp
    result := s.resultVal
    wires := s.wires
    output := s.outputWire
    signed := s.signed hSym hNod
    root := s.erasedRootMsg
    rooted := s.rooted hSym hNod
    outside := s.outside
    entryPlain := rfl
    arguments := by
      have h := s.arguments hSym hNod
      simpa [s, mkToyNarrowSpec, FlatAssertSpec.args, FlatVal.sourceVal,
        compressNarrowArgs, u32Array8SourceValue] using h
    decoded := s.decoded hSym hNod
    idOf := fun _ => 0
    S := S
    ok := mkToyNarrowSharded_check policyWords targetWords hp8 ht8
    units := [(s.erasedChip, none)]
    chipsIn := by intro u hu; simp only [List.mem_singleton] at hu; subst hu; simp [FlatAssertSpec.plan]
    unrolled := by intro u hu; simp only [List.mem_singleton] at hu; subst hu; rfl
    wide := [Bridge.unitCircuit (fun _ => 0) (s.erasedChip, none)]
    groups := [[[0]]]
    circuits := by
      simp only [S, Periodic.Sharded.system, mkToyNarrowSharded, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.zipWith_cons_cons, List.zipWith_nil_left,
        List.cons.injEq, and_true]
      simp [Tiling.Circuit.mergeBy, Tiling.Circuit.multSum, Tiling.Circuit.lookupAt,
        Bridge.unitCircuit, Bridge.lower, Activation.compile, FlatAssertSpec.erasedChip,
        Erasure.chip, FlatAssertSpec.physChip]
    wideEq := rfl
    lenG := rfl
    merged := by
      intro j hw _
      have hj : j = 0 := by simp at hw; omega
      subst hj
      have hId : ∀ xs : List (Scalar.Circuit.ArithExpr BN254Fr), Tiling.argsIdentical xs xs = true := by
        intro xs
        unfold Tiling.argsIdentical
        simp only [beq_self_eq_true, Bool.true_and, List.all_eq_true]
        intro p hp
        have hEq : p.1 = p.2 := by
          induction xs with
          | nil => simp at hp
          | cons a rest ih =>
            simp only [List.zip_cons_cons, List.mem_cons] at hp
            rcases hp with rfl | h'
            · rfl
            · exact ih h'
        rw [hEq]
        simp [Tiling.Poly.Identical]
      simp only [List.getElem_cons_zero, Tiling.Circuit.checkMerge, List.flatten_singleton,
        List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self,
        decide_true, Bool.true_and, List.all_cons, List.all_nil, Bool.and_true, List.isEmpty_cons,
        Bool.not_false, List.headD_cons, hId, Bool.true_and]
      have hLen1 : (Bridge.unitCircuit (fun _ => 0) (s.erasedChip, none)).lookups.length = 1 := by
        simp [Bridge.unitCircuit, Bridge.lower, Activation.compile, FlatAssertSpec.erasedChip,
          Erasure.chip, FlatAssertSpec.physChip]
      simp [hLen1]
    ν := ZMod.val
    tables := []
    tablesOk := by simp [Periodic.checkTables, fastNodup, ascending]
    mapsIn := fun _ h => absurd h List.not_mem_nil
    capacity := by
      simp [Bridge.capacityRowsU, Bridge.unitBodies, System.cap, S, Periodic.Sharded.system,
        mkToyNarrowSharded]
    bound := 10000
    small := Aiur.Tiling.smallCast_zmod bn254FrModulus (by decide)
    tags := by decide
    codesBound := by
      intro e he
      simp only [S, mkToyNarrowSharded, List.mem_singleton] at he
      subst he; decide
    labels := by
      have hLT : S.labelTotal = toyNarrowShadow.keys.length + 1 := by
        have hK : (((mkToyNarrowSharded s).layout 0).shadow 24).keys = toyNarrowShadow.keys := hSh.2.1
        simpa [Periodic.Sharded.labelTotal, Periodic.Sharded.labelOffset, Periodic.Sharded.shadow,
          S, mkToyNarrowSharded, Periodic.Sharded.layout] using congrArg List.length hK
      rw [hLT]; decide
    shadowBound := by
      intro k hk
      have hk0 : k = 0 := by simp [S, mkToyNarrowSharded] at hk; omega
      subst hk0
      change ((S.layout 0).shadow 24).bound ≤ 10000
      have hB : ((S.layout 0).shadow 24).bound = toyNarrowShadow.bound := hSh.2.2.1
      rw [hB]; decide
    lookups := by
      simp [Bridge.capacityLookupsU, Bridge.unitBodies, System.cap, S, Periodic.Sharded.system,
        mkToyNarrowSharded, FlatAssertSpec.erasedChip, Erasure.chip, FlatAssertSpec.physChip]
    idsBound := by
      simp [System.instances, System.cap, S, Periodic.Sharded.system, mkToyNarrowSharded]
    parts := by
      have hEnum : (S.system.enumerate S.system.lookupCount).length = 1 := by
        simp [System.enumerate, System.cap, System.lookupCount, S, Periodic.Sharded.system,
          mkToyNarrowSharded, Bridge.unitCircuit, Bridge.lower, Activation.compile,
          FlatAssertSpec.erasedChip, Erasure.chip, FlatAssertSpec.physChip]
      simp [hEnum]
    characteristic := DepthBridge.bn254_characteristic_24
    req := by
      have hEnc := s.encode_erasedRootMsg
      have hPins : (mkToyNarrowTemplate2 s.allConsts).pins = [] := by
        simp only [Template2.pins, mkToyNarrowTemplate2]; decide
      have hfm : ∀ {α β : Type} (f : α → β) (l : List α), l.flatMap (fun a => [f a]) = l.map f := by
        intro α β f l; induction l with | nil => rfl | cons _ _ ih => simp [ih]
      have hMsgs : (mkToyNarrowTemplate2 s.allConsts).logical.messages =
          [(-1, (CALL : BN254Fr), 0, messageCells 24 22 (List.range 21))] := by
        simp only [Template.messages, Template2.logical, hPins]
        simp [mkToyNarrowTemplate2, mkNarrowGateRow2, Template2.virtualRows, Template2.boolRows,
          Template2.messageRows, Row2.logical, List.flatMap_map, hfm, List.filterMap_append,
          List.filterMap_map]
      have hTLW : (mkToyNarrowTemplate2 s.allConsts).logical.width = 24 := rfl
      have hCLook : (Bridge.unitCircuit (fun _ => 0) (s.erasedChip, none)).lookups =
          [⟨.sub (.const 0) (.var 22),
            .const (CALL : BN254Fr) :: .const 0 :: (List.range 21).map .var⟩] := by
        have hInLen : s.inConsts.length = 17 := by
          simp [s, FlatAssertSpec.inConsts, mkToyNarrowSpec, FlatVal.words, hp8, ht8]
        simp only [Bridge.unitCircuit, Bridge.lower, Activation.compile, Bridge.receiveLookup,
          FlatAssertSpec.erasedChip, Erasure.chip, Erasure.pack, FlatAssertSpec.physChip,
          FlatAssertSpec.inputWireVars, FlatAssertSpec.mkInputWires_flatMap, FlatAssertSpec.numVars,
          hallLen, List.map_nil, List.append_nil, List.flatMap_singleton, List.cons.injEq, and_true]
        congr 1; congr 1; congr 1
        change ((List.range' 0 s.inConsts.length).map (Scalar.Circuit.ArithExpr.var : Nat → Scalar.Circuit.ArithExpr BN254Fr) ++
          (List.range' s.inConsts.length 4).map Scalar.Circuit.ArithExpr.var) =
          (List.range 21).map Scalar.Circuit.ArithExpr.var
        rw [← List.map_append, hInLen]
        rfl
      rw [hEnc]
      simp [Part.request, Part.checkRequest, Part.tuple, hallLen, S, Periodic.Sharded.system,
        mkToyNarrowSharded, System.arityAt, System.arities, System.roleOf, System.roles,
        System.groups, hMsgs, hCLook, hTLW]
      clear * -
      decide
    req2 := by
      rw [s.encode_erasedRootMsg]
      simp [Periodic.Sharded.checkRequest2, Periodic.Sharded.rowKeys, Part.request, hallLen,
        S, mkToyNarrowSharded]
    chanIds := by
      intro x hx y hy _
      rw [s.chanIds_singleton hSym hNod x hx, s.chanIds_singleton hSym hNod y hy]
    chanBound := fun _ _ => by decide
    enablesOk := by
      intro c hc
      simp only [FlatAssertSpec.plan, List.mem_singleton] at hc
      subst hc
      simp [Bridge.checkEnables, Activation.compile, FlatAssertSpec.erasedChip, Erasure.chip,
        FlatAssertSpec.physChip]
    H := fun _ => 24
    main := toyNarrowMain s.allConsts
    HT := fun _ => 0
    mainT := fun _ _ _ => 0
    tall := by
      intro k hk
      have hk0 : k = 0 := by simp [S, mkToyNarrowSharded] at hk; omega
      subst hk0
      change ((S.layout 0).shadow 24).places.length ≤ 24
      have hP : ((S.layout 0).shadow 24).places.length = toyNarrowShadow.places.length :=
        congrArg List.length hSh.1
      rw [hP]; decide
    tallT := fun _ _ h => by simp at h
    rows := by
      intro k hk p hp
      have hk0 : k = 0 := by simp [S, mkToyNarrowSharded] at hk; omega
      subst hk0
      exact mkToyNarrowSharded_rows policyWords targetWords hp8 ht8 p hp
    balanced := mkToyNarrowSharded_balanced policyWords targetWords hp8 ht8 }

/-! ## 7. Stage 4 (`CompressFinalNarrow`) Polymorphic BN254 PLONK Shared-Map Witness -/

/-- Polymorphic Stage 4 (`CompressFinalNarrow::verify_accumulator_v1`) `FlatAssertSpec`:
2 inputs (`low, high`) and 18 outputs (`bn254AffineZeroPairWords`). -/
def mkToyFinalSpec (lowVal highVal : Nat) : FlatAssertSpec BN254Fr where
  fnName := compressFinalNarrowEntry
  params := [
    ("low", .scalar (lowVal : BN254Fr)),
    ("high", .scalar (highVal : BN254Fr))
  ]
  outConsts := bn254AffineZeroPairWords

theorem mkToyFinalSpec_sym (lowVal highVal : Nat) :
    Generic.Instance.ofSymbol (mkToyFinalSpec lowVal highVal).fnName =
      .ok ⟨(mkToyFinalSpec lowVal highVal).fnName, []⟩ := by
  change Generic.Instance.ofSymbol compressFinalNarrowEntry = .ok ⟨compressFinalNarrowEntry, []⟩
  rfl

theorem mkToyFinalSpec_nodup (lowVal highVal : Nat) :
    Aiur.findDuplicate ((mkToyFinalSpec lowVal highVal).params.map Prod.fst) [] = none := by
  simp only [mkToyFinalSpec, List.map_cons, List.map_nil]
  decide

private theorem toyFinalSpec_eval_inv {targetLow targetHigh : Nat}
    (hLowLt : targetLow < 2 ^ 128) (hHighLt : targetHigh < 2 ^ 128)
    {low high : Nat} {value heap}
    (hLow : low < 2 ^ 128) (hHigh : high < 2 ^ 128)
    (hEv : Generic.SourceSemantics.EvalFn (mkToyFinalSpec targetLow targetHigh).source.world
      compressFinalNarrowEntry (compressFinalArgs BN254Fr low high) [] value heap) :
    low = targetLow ∧ high = targetHigh ∧
    value = .tuple (bn254AffineZeroPairWords.map Aiur.Value.field) := by
  have hprep : (mkToyFinalSpec targetLow targetHigh).source.world.prepare compressFinalNarrowEntry
      (compressFinalArgs BN254Fr low high) =
      .ok ([],
        [("low", .field (low : BN254Fr)), ("high", .field (high : BN254Fr))],
        (.letValue .wildcard
          (.builtin (.assertEq {}) [.var "low", .literal (targetLow : BN254Fr)]) <|
         .letValue .wildcard
          (.builtin (.assertEq {}) [.var "high", .literal (targetHigh : BN254Fr)]) <|
         .tuple (bn254AffineZeroPairWords.map .literal))) := by
    have hSym : Generic.Instance.ofSymbol compressFinalNarrowEntry = .ok ⟨compressFinalNarrowEntry, []⟩ :=
      mkToyFinalSpec_sym targetLow targetHigh
    simp [Generic.Source.world, Generic.sourceWorld, Generic.Program.sourceFunction?,
      Generic.Program.findFunction?, FlatAssertSpec.source, FlatAssertSpec.genericProgram,
      FlatAssertSpec.genericFn, FlatAssertSpec.mkGenericBody, mkToyFinalSpec, FlatVal.genericTy,
      FlatVal.genericExpr, Generic.SourceFunction.prepare, hSym, Generic.Ty.toCore,
      Generic.Ty.subst, compressFinalArgs, Generic.wellFormed, Aiur.Value.type, Generic.arguments,
      bind, Option.bind, Except.bind, pure, Except.pure, Except.toOption, bn254AffineZeroPairWords]
  cases hEv with
  | intro hpr hbody =>
    rw [hprep] at hpr
    injection hpr with hpr
    simp only [Prod.mk.injEq] at hpr
    obtain ⟨rfl, rfl, rfl⟩ := hpr
    obtain ⟨hlookL, hbody2⟩ := evalExpr_letAssertEq_var_literal hbody
    obtain ⟨hlookH, hbody3⟩ := evalExpr_letAssertEq_var_literal hbody2
    obtain ⟨hval, _⟩ := evalExpr_tuple_literals hbody3
    have hne : ("low" == "high") = false := by decide
    simp only [List.find?_cons, hne, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq, true_and,
      Aiur.Value.field.injEq] at hlookL hlookH
    obtain ⟨eL, eH⟩ := limbs_embed_bn254_injective hLow hHigh hLowLt hHighLt hlookL hlookH
    exact ⟨eL, eH, hval⟩
  | returned hpr hexit =>
    rw [hprep] at hpr
    injection hpr with hpr
    simp only [Prod.mk.injEq] at hpr
    obtain ⟨rfl, rfl, rfl⟩ := hpr
    have h1 := evalExit_letAssertEq_var_literal hexit
    have h2 := evalExit_letAssertEq_var_literal h1
    exact False.elim (evalExit_tuple_literals_false h2)

/-- Global pool computing powers `γ^2 .. γ^22` (`pool 2 .. pool 22`), 100% total and concrete. -/
def toyPlonkPool : Lower.Pool BN254Fr where
  gates := ((List.range 21).map fun i =>
    let e := i + 2
    let prev := if e == 2 then Lower.gammaRef else Lower.pool (e - 1)
    { a := prev, b := Lower.gammaRef, c := Lower.pool e,
      L := 0, R := 0, O := -1, M := 1, C := 0, tag := .pool }).toArray
  next := 23

/-- Reference of `γ^e` in `toyPlonkPool` (`1 ≤ e ≤ 22`). -/
def toyPoolPow (e : Nat) : Lower.Ref :=
  if e == 1 then Lower.gammaRef else Lower.pool e

/-- 22 single-gate constraint `LGate`s for our Stage 4 chip (`width = 22`, `sel = 20`, `mult = 21`). -/
def toyFinalConstraintGates (lowVal highVal : Nat) : Array (Lower.LGate BN254Fr) :=
  let gBool : Lower.LGate BN254Fr :=
    { a := 160, b := 160, c := 160, L := -1, R := 0, O := 0, M := 1, C := 0, tag := .constraint, root := some 0 }
  let gLow : Lower.LGate BN254Fr :=
    { a := 0, b := 160, c := 0, L := 1, R := -(lowVal : BN254Fr), O := 0, M := 0, C := 0, tag := .constraint, root := some 1 }
  let gHigh : Lower.LGate BN254Fr :=
    { a := 8, b := 160, c := 8, L := 1, R := -(highVal : BN254Fr), O := 0, M := 0, C := 0, tag := .constraint, root := some 2 }
  let gOuts : List (Lower.LGate BN254Fr) :=
    bn254AffineZeroPairWords.zipIdx.map fun (v, k) =>
      { a := 8 * (2 + k), b := 160, c := 8 * (2 + k), L := 1, R := -v, O := 0, M := 0, C := 0,
        tag := .constraint, root := some (3 + k) }
  let gMult : Lower.LGate BN254Fr :=
    { a := 160, b := 168, c := 168, L := 0, R := 1, O := 0, M := -1, C := 0, tag := .constraint, root := some 21 }
  ([gBool, gLow, gHigh] ++ gOuts ++ [gMult]).toArray

/-- Total builder for a 22-arg lookup's fingerprint + `q` + running-sum `LGate`s (100% concrete!). -/
def buildFpLookupGates (args : List (Scalar.Circuit.ArithExpr BN254Fr))
    (multNegVar? : Option Nat) :
    Array (Lower.LGate BN254Fr) × Array (Lower.LGate BN254Fr) × Lower.Ref × Lower.Ref := Id.run do
  let n := args.length
  let mut defs : Array (Lower.LGate BN254Fr) := #[]
  let mut nextLoc : Nat := 0
  let allocLoc (k : Nat) : Lower.Ref := Lower.loc k
  let acc0 := allocLoc nextLoc
  nextLoc := nextLoc + 1
  defs := defs.push
    { a := Lower.betaRef, b := toyPoolPow n, c := acc0,
      L := 1, R := (n : BN254Fr), O := -1, M := 0, C := 0, tag := .fingerprint }
  let mut acc := acc0
  for (arg, i) in args.zipIdx do
    let e := expOf n i
    match arg with
    | .const c =>
      if c != 0 then
        let r := allocLoc nextLoc
        nextLoc := nextLoc + 1
        if e == 0 then
          defs := defs.push
            { a := acc, b := acc, c := r,
              L := 1, R := 0, O := -1, M := 0, C := c, tag := .fingerprint }
        else
          defs := defs.push
            { a := acc, b := toyPoolPow e, c := r,
              L := 1, R := c, O := -1, M := 0, C := 0, tag := .fingerprint }
        acc := r
    | .var v =>
      let cellRef := 8 * v
      if e == 0 then
        let r := allocLoc nextLoc
        nextLoc := nextLoc + 1
        defs := defs.push
          { a := acc, b := cellRef, c := r,
            L := 1, R := 1, O := -1, M := 0, C := 0, tag := .fingerprint }
        acc := r
      else
        let p := allocLoc nextLoc
        nextLoc := nextLoc + 1
        defs := defs.push
          { a := cellRef, b := toyPoolPow e, c := p,
            L := 0, R := 0, O := -1, M := 1, C := 0, tag := .fingerprint }
        let r := allocLoc nextLoc
        nextLoc := nextLoc + 1
        defs := defs.push
          { a := acc, b := p, c := r,
            L := 1, R := 1, O := -1, M := 0, C := 0, tag := .fingerprint }
        acc := r
    | _ => pure ()
  let qRef := allocLoc nextLoc
  nextLoc := nextLoc + 1
  let sOut := allocLoc nextLoc
  let qg : Lower.LGate BN254Fr := match multNegVar? with
    | some mv =>
      { a := qRef, b := acc, c := 8 * mv,
        L := 0, R := 0, O := 1, M := 1, C := 0, tag := .logup, msg := some 0 }
    | none =>
      { a := qRef, b := acc, c := qRef,
        L := 0, R := 0, O := 0, M := 1, C := -1, tag := .logup, msg := some 0 }
  let sg : Lower.LGate BN254Fr :=
    { a := Lower.sumIn, b := qRef, c := sOut,
      L := 1, R := 1, O := -1, M := 0, C := 0, tag := .logup, msg := some 0 }
  (defs, #[qg, sg], qRef, sOut)

/-- 100% CONCRETE lookup args for row `(0, 0)` and row `(1, 0)` (completely independent of `lowVal, highVal`!). -/
def toyFinalLookupArgs : List (Scalar.Circuit.ArithExpr BN254Fr) :=
  .const (CALL : BN254Fr) :: .const 0 :: (List.range 20).map .var

def toyFinalLook0 := buildFpLookupGates toyFinalLookupArgs (some 21)
def toyFinalLook1 := buildFpLookupGates toyFinalLookupArgs none

/-- Put `look0` gates FIRST (`0..42`) and `constraintGates` LAST (`43..64`) so `rowPool` at every
message-certificate index (`0..42` and `65..85`) is **100% independent of `lowVal, highVal`**! -/
def toyFinalRowGates (lowVal highVal : Nat) : Nat × Nat → Array (Lower.LGate BN254Fr)
  | (0, 0) => toyFinalLook0.1 ++ toyFinalLook0.2.1 ++ toyFinalConstraintGates lowVal highVal
  | (1, 0) => toyFinalLook1.1 ++ toyFinalLook1.2.1
  | _ => #[]

def toyFinalRowFin : Nat × Nat → Lower.Ref
  | (0, 0) => toyFinalLook0.2.2.2
  | (1, 0) => toyFinalLook1.2.2.2
  | _ => Lower.sumIn

/-- Lightweight concrete dummy `Air` for row `(0, 0)` with identical width (`22`), fixed (`0`),
and lookup (`toyFinalLookupArgs`), avoiding `FlatAssertSpec` unfolding inside kernel `decide`. -/
def toyFinalAir0Dummy : WideStage.Air BN254Fr where
  circuit := ⟨22, 0, [], [⟨.sub (.const 0) (.var 21), toyFinalLookupArgs⟩]⟩
  rows := 1
  fixed := fun _ _ => 0

/-- Pure-`List` `AirIn.MsgCert` builder (ZERO `Std.HashMap` so kernel reduction is instant!). -/
def buildToyMsgCert (defs roots : Array (Lower.LGate BN254Fr)) (idx : Array Nat)
    (col : Lower.Ref → Option Nat) (qRef sIn sOut : Lower.Ref) : AirIn.MsgCert BN254Fr := Id.run do
  let mut slotOf : List (Lower.Ref × Nat) := []
  let mut slots : List (SlotDef BN254Fr) := []
  let mut sr : List Lower.Ref := []
  for g in (defs ++ roots).toList do
    for r in [g.a, g.b, g.c] do
      if let some c := col r then
        if (slotOf.lookup r).isNone then
          slotOf := slotOf ++ [(r, slots.length)]
          slots := slots ++ [.column c]
          sr := sr ++ [r]
  let mut rows : List (Tiling.Row BN254Fr) := []
  for g in defs.toList do
    let sa := (slotOf.lookup g.a).getD 0
    let sb := (slotOf.lookup g.b).getD 0
    let s := slots.length
    slotOf := slotOf ++ [(g.c, s)]
    let terms : List (Term BN254Fr) :=
      (if g.L == 0 then [] else [.linear g.L sa]) ++
      (if g.R == 0 then [] else [.linear g.R sb]) ++
      (if g.M == 0 then [] else [.product g.M sa sb])
    slots := slots ++ [.sum terms g.C]
    sr := sr ++ [g.c]
    rows := rows ++ [.gate [⟨g.M, g.L, g.R, -1, 0, g.C, some sa, some sb, some s, none, 0⟩] false [.defines s]]
  for (g, j) in roots.toList.zipIdx do
    let sa := (slotOf.lookup g.a).getD 0
    let sb := (slotOf.lookup g.b).getD 0
    let sc := (slotOf.lookup g.c).getD 0
    rows := rows ++ [.gate [⟨g.M, g.L, g.R, g.O, 0, g.C, some sa, some sb, some sc, none, 0⟩] false [.root j]]
  { T := { width := 4, slots := slots, rows := rows }
    sr := sr.toArray
    idx := idx
    count := false
    qRef := qRef
    sIn := sIn
    sOut := sOut }

/-- 100% concrete `AirIn.MsgCert` for row `(0, 0)` (at offset 0, total rowLen 65). -/
def toyFinalMsgCert0Val : AirIn.MsgCert BN254Fr :=
  let defsAll := toyPlonkPool.gates ++ toyFinalLook0.1
  let rowLen := toyFinalLook0.1.size + toyFinalLook0.2.1.size + 22
  let poolIdxs := (List.range toyPlonkPool.gates.size).map (· + rowLen)
  let defIdxs := List.range toyFinalLook0.1.size
  let rootIdxs := (List.range toyFinalLook0.2.1.size).map (· + toyFinalLook0.1.size)
  let idx := (poolIdxs ++ defIdxs ++ rootIdxs).toArray
  let col := AirIn.msgCol toyFinalAir0Dummy toyFinalLook0.2.2.1 Lower.sumIn toyFinalLook0.2.2.2
  buildToyMsgCert defsAll toyFinalLook0.2.1 idx col toyFinalLook0.2.2.1 Lower.sumIn toyFinalLook0.2.2.2

def toyFinalMsgCert0 : Except String (Option (AirIn.MsgCert BN254Fr)) := .ok (some toyFinalMsgCert0Val)

/-- 100% concrete `AirIn.MsgCert` for row `(1, 0)` (at offset 0, total rowLen 43). -/
def toyFinalMsgCert1Val : AirIn.MsgCert BN254Fr :=
  let defsAll := toyPlonkPool.gates ++ toyFinalLook1.1
  let rowLen := toyFinalLook1.1.size + toyFinalLook1.2.1.size
  let poolIdxs := (List.range toyPlonkPool.gates.size).map (· + rowLen)
  let defIdxs := List.range toyFinalLook1.1.size
  let rootIdxs := (List.range toyFinalLook1.2.1.size).map (· + toyFinalLook1.1.size)
  let idx := (poolIdxs ++ defIdxs ++ rootIdxs).toArray
  let col := AirIn.msgCol (rootAir (0 : BN254Fr) 20) toyFinalLook1.2.2.1 Lower.sumIn toyFinalLook1.2.2.2
  buildToyMsgCert defsAll toyFinalLook1.2.1 idx col toyFinalLook1.2.2.1 Lower.sumIn toyFinalLook1.2.2.2

def toyFinalMsgCert1 : Except String (Option (AirIn.MsgCert BN254Fr)) := .ok (some toyFinalMsgCert1Val)

/-- Concrete layout shared by BOTH two-layer and single-layer Stage 4 witnesses:
- Row `(1, 0)` cells: wires `0..19` (`0..1` = public inputs `(stmtLow, stmtHigh)`, `2..19` = 18 affine outputs!)
- Row `(0, 0)` cells: wires `20..41` (`20..39` = data, `40` = sel, `41` = mult)
- Pool wires: `50..72` (`50` = γ, `51` = β, `52..72` = γ²..γ²²)
- Local wires: row `(0, 0)` at `100..142`, row `(1, 0)` at `200..242`
- `init` = `300`, `sumIn (1, 0)` = `100 + sOut0 / 4` = `142`, `last` = `242`, `spare` = `309`, `nWires = 310`. -/
def toyFinalLayout : Aiur.Plonk.Layout where
  cellBase := fun t => if t == 0 then 20 else 0
  rowWidth := fun t => if t == 0 then 22 else 20
  poolBase := 50
  locBase := fun i => if i.1 == 0 then 100 else 200
  sumIn := fun i => if i.1 == 0 then 300 else 100 + toyFinalLook0.2.2.2 / 4
  spare := 309

/-- Affine coefficients `(c0, cLow, cHigh)` for Stage 4 wire values at ANY `(lowVal, highVal)`
with `γ = 0, β = 1 - lowVal`. -/
def toyFinalWLin (wire : Nat) : BN254Fr × BN254Fr × BN254Fr :=
  -- Row (1, 0) cells: wires 0..19
  if wire = 0 then (0, 1, 0)
  else if wire = 1 then (0, 0, 1)
  else if wire < 20 then (bn254AffineZeroPairWords.getD (wire - 2) 0, 0, 0)
  -- Row (0, 0) cells: wires 20..41
  else if wire = 20 then (0, 1, 0)
  else if wire = 21 then (0, 0, 1)
  else if wire < 40 then (bn254AffineZeroPairWords.getD (wire - 22) 0, 0, 0)
  else if wire = 40 then (1, 0, 0)
  else if wire = 41 then (1, 0, 0)
  -- Pool: wire 50 = γ = 0, wire 51 = β = 1 - lowF, wires 52..72 = γ^e = 0
  else if wire = 51 then (1, -1, 0)
  -- Row (0, 0) locals: wires 100..142
  else if wire = 100 then (1, -1, 0)
  else if wire = 101 then (1, -1, 0)
  else if wire = 102 then (1, 0, 0)
  else if 103 ≤ wire ∧ wire ≤ 140 then (if wire % 2 = 0 then 1 else 0, 0, 0)
  else if wire = 141 then (-1, 0, 0)
  else if wire = 142 then (-1, 0, 0)
  -- Row (1, 0) locals: wires 200..242
  else if wire = 200 then (1, -1, 0)
  else if wire = 201 then (1, -1, 0)
  else if wire = 202 then (1, 0, 0)
  else if 203 ≤ wire ∧ wire ≤ 240 then (if wire % 2 = 0 then 1 else 0, 0, 0)
  else if wire = 241 then (1, 0, 0)
  else (0, 0, 0)

/-- Closed-form satisfying wire assignment `Nat → BN254Fr` for Stage 4 at ANY `(lowVal, highVal)`
with `γ = 0, β = 1 - lowVal` (ZERO `Std.HashMap` loops, 100% symbolic!). -/
def toyFinalW (lowVal highVal : Nat) (wire : Nat) : BN254Fr :=
  let c := toyFinalWLin wire
  c.1 + c.2.1 * (lowVal : BN254Fr) + c.2.2 * (highVal : BN254Fr)

private theorem toyFinalW_eq_lin (lowVal highVal wire : Nat) :
    toyFinalW lowVal highVal wire =
      (toyFinalWLin wire).1 + (toyFinalWLin wire).2.1 * (lowVal : BN254Fr) +
        (toyFinalWLin wire).2.2 * (highVal : BN254Fr) := rfl

def gateHoldsLinB (g : Gate BN254Fr) : Bool :=
  let a := toyFinalWLin g.a
  let b := toyFinalWLin g.b
  let c := toyFinalWLin g.c
  (g.qL * a.1 + g.qR * b.1 + g.qO * c.1 + g.qM * a.1 * b.1 + g.qC == 0) &&
  (g.qL * a.2.1 + g.qR * b.2.1 + g.qO * c.2.1 + g.qM * (a.1 * b.2.1 + a.2.1 * b.1) == 0) &&
  (g.qL * a.2.2 + g.qR * b.2.2 + g.qO * c.2.2 + g.qM * (a.1 * b.2.2 + a.2.2 * b.1) == 0) &&
  (g.qM * a.2.1 * b.2.1 == 0) &&
  (g.qM * (a.2.1 * b.2.2 + a.2.2 * b.2.1) == 0) &&
  (g.qM * a.2.2 * b.2.2 == 0)

private theorem gateHolds_of_gateHoldsLinB (lowVal highVal : Nat) (g : Gate BN254Fr)
    (h : gateHoldsLinB g = true) : g.Holds (toyFinalW lowVal highVal) := by
  unfold gateHoldsLinB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨⟨h1, hL⟩, hH⟩, hLL⟩, hLH⟩, hHH⟩
  unfold Gate.Holds
  rw [toyFinalW_eq_lin, toyFinalW_eq_lin, toyFinalW_eq_lin]
  set lowF : BN254Fr := (lowVal : BN254Fr)
  set highF : BN254Fr := (highVal : BN254Fr)
  linear_combination
    h1 + lowF * hL + highF * hH + lowF ^ 2 * hLL + (lowF * highF) * hLH + highF ^ 2 * hHH

/-- 18 linear output-pinning gates constraining wires `2..19` to `bn254AffineZeroPairWords`. -/
def toyOutputPinGates : List (Gate BN254Fr) :=
  bn254AffineZeroPairWords.zipIdx.map fun (v, j) =>
    ⟨2 + j, 2 + j, 2 + j, 1, 0, 0, 0, -v⟩

/-- Any wire assignment satisfying `toyOutputPinGates` maps wires `2..19` to
`bn254AffineZeroPairWords`. -/
theorem outputWires_eq_of_pinGates {w : Nat → BN254Fr}
    (h : ∀ g ∈ toyOutputPinGates, g.Holds w) :
    (List.range' 2 18).map w = bn254AffineZeroPairWords := by
  have h1 : ∀ j (hj : j < 18), w (2 + j) = bn254AffineZeroPairWords.getD j 0 := by
    intro j hj
    have hlen : bn254AffineZeroPairWords.length = 18 := rfl
    have hj' : j < bn254AffineZeroPairWords.length := hlen ▸ hj
    have hmem : (bn254AffineZeroPairWords[j], j) ∈ bn254AffineZeroPairWords.zipIdx :=
      List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [List.getElem?_eq_getElem hj'])
    have hg := h _ (List.mem_map.mpr ⟨_, hmem, rfl⟩)
    simp only [Gate.Holds, one_mul, zero_mul, add_zero] at hg
    have heq : w (2 + j) = bn254AffineZeroPairWords[j] := by linear_combination hg
    rw [heq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some]
  apply List.ext_getElem
  · simp [bn254AffineZeroPairWords, bn254AffineInfinityWords]
  · intro j hj1 hj2
    have hj18 : j < 18 := by simpa using hj1
    simp only [List.getElem_map, List.getElem_range', Nat.one_mul]
    rw [h1 j hj18, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj2, Option.getD_some]

private theorem poly_norm_ofExpr_normExpr_linear {i : Nat} (hi : i < 20) (c : BN254Fr) :
    Tiling.Poly.norm (Tiling.Poly.ofExpr (AirIn.normExpr (Activation.polynomial 20 (subConstPoly i c)))) =
      if c = 0 then [([i], (1 : BN254Fr))] else [([i], 1), ([20], -c)] := by
  unfold AirIn.normExpr
  rw [poly_norm_activation_subConstPoly hi c]
  by_cases hc : c = 0
  · simp [hc, Aiur.Plonk.Poly.toExpr, Aiur.Plonk.monoExpr, Tiling.Poly.ofExpr, Tiling.Poly.add,
      Tiling.Poly.mul, Tiling.Poly.const, Tiling.Poly.var, Tiling.Mono.mul, Tiling.Mono.insert,
      Tiling.Poly.norm, Tiling.Poly.insertTerm]
  · have hEq : Tiling.Poly.ofExpr (Aiur.Plonk.Poly.toExpr [([i], (1 : BN254Fr)), ([20], -c)]) =
        [([i], (1 : BN254Fr)), ([20], -c), ([], 0)] := by
      simp [Aiur.Plonk.Poly.toExpr, Aiur.Plonk.monoExpr, Tiling.Poly.ofExpr, Tiling.Poly.add,
        Tiling.Poly.mul, Tiling.Poly.const, Tiling.Poly.var, Tiling.Mono.mul, Tiling.Mono.insert]
    simp only [hc, ↓reduceIte, hEq]
    have h0 : Tiling.Poly.norm [([i], (1 : BN254Fr)), ([20], -c), ([], 0)] =
        Tiling.Poly.norm [([i], (1 : BN254Fr)), ([20], -c)] := rfl
    rw [h0, poly_norm_linear_pair hi c]
    simp [hc]

/-- Symbolic constraint-certificate lemma for any linear constraint `var i - c * var 20` (`i < 20`). -/
private theorem linearConstraintCert_ok {i : Nat} (hi : i < 20) (c : BN254Fr)
    {gs : List (Lower.LGate BN254Fr)}
    (hgMem :
      ({ a := 8 * i, b := 160, c := 8 * i, L := 1, R := -c, O := 0, M := 0, C := 0,
         tag := .constraint, root := some (i + 1) } : Lower.LGate BN254Fr) ∈ gs) :
    let T : Template BN254Fr := {
      width := 4
      slots := [.column i, .column 20]
      rows := [.gate [⟨0, 1, -c, 0, 0, 0, some 0, some 1, some 0, none, 0⟩] false [.root 0]]
    }
    let sr : Nat → Lower.Ref := fun | 0 => 8 * i | _ => 160
    let Cj : Tiling.Circuit BN254Fr := ⟨22, 0, [AirIn.normExpr (Activation.polynomial 20 (subConstPoly i c))], []⟩
    T.check Cj = true ∧ coversVars T 22 Cj = true ∧ realisedB T sr gs = true ∧ colsB T sr = true := by
  intro T sr Cj
  have hne : i ≠ 20 := Nat.ne_of_lt hi
  have hM0 : T.meaning 0 = Tiling.Poly.var i := Template.meaning_column T rfl
  have hM1 : T.meaning 1 = Tiling.Poly.var 20 := Template.meaning_column T rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `T.check Cj = true`
    have hRel : T.relations = [(.root 0, [([0, 1], (0 : BN254Fr)), ([0], 1), ([1], -c), ([0], 0), ([], 0)])] := by
      simp [T, Template.relations, Row.relations, Lane.poly, cellPoly, Tiling.Mono.insert]
    have hCheckRel : T.checkRelation Cj (.root 0, [([0, 1], (0 : BN254Fr)), ([0], 1), ([1], -c), ([0], 0), ([], 0)]) = true := by
      simp only [Template.checkRelation, Cj, List.getElem?_cons_zero, Bool.and_eq_true]
      refine ⟨by simp [Template.widePoly, Template.wideSlot, T], ?_⟩
      unfold Tiling.Poly.Identical
      have hsub : Tiling.Poly.subst T.meaning [([0, 1], (0 : BN254Fr)), ([0], 1), ([1], -c), ([0], 0), ([], 0)] =
          [([i, 20], (0 : BN254Fr)), ([i], 1), ([20], -c), ([i], 0), ([], 0)] := by
        simp [Tiling.Poly.subst, Tiling.Poly.substMono, Tiling.Poly.mul, Tiling.Poly.scale,
          Tiling.Poly.const, Tiling.Poly.var, Tiling.Mono.mul, Tiling.Mono.insert,
          show ¬ (20 ≤ i) by omega, hM0, hM1]
      have hnorm : Tiling.Poly.norm [([i, 20], (0 : BN254Fr)), ([i], 1), ([20], -c), ([i], 0), ([], 0)] =
          Tiling.Poly.norm [([i], (1 : BN254Fr)), ([20], -c)] := by
        have h1 : Tiling.Poly.norm [([i], (1 : BN254Fr)), ([20], -c)] =
            if c = 0 then [([i], 1)] else [([i], 1), ([20], -c)] :=
          poly_norm_linear_pair hi c
        change Tiling.Poly.insertTerm ([i, 20], 0)
          (Tiling.Poly.insertTerm ([i], 1) (Tiling.Poly.insertTerm ([20], -c) [])) =
          Tiling.Poly.norm [([i], (1 : BN254Fr)), ([20], -c)]
        change Tiling.Poly.insertTerm ([i, 20], 0)
          (Tiling.Poly.norm [([i], (1 : BN254Fr)), ([20], -c)]) =
          Tiling.Poly.norm [([i], (1 : BN254Fr)), ([20], -c)]
        rw [h1]
        by_cases hc : c = 0
        · simp [hc, Tiling.Poly.insertTerm, Tiling.Mono.lt]
        · simp [hc, Tiling.Poly.insertTerm, Tiling.Mono.lt]
      rw [hsub, hnorm, poly_norm_linear_pair hi c, poly_norm_ofExpr_normExpr_linear hi c]
      exact beq_self_eq_true _
    have hCol0 : T.colSlot i = some 0 := by simp [Template.colSlot, T, List.findIdx?_cons]
    have hCol1 : T.colSlot 20 = some 1 := by
      have hneq : (SlotDef.column (F := BN254Fr) i == SlotDef.column 20) = false := by
        simp [hne]
      simp [Template.colSlot, T, List.findIdx?_cons, hneq]
    unfold Template.check
    simp [T, Cj, Row.wellFormed, Lane.wellFormed, Row.cells, Lane.cells, Template.checkSlot,
      hCol0, hCol1, hRel, hCheckRel, Template.checkConstraint, Template.checkUnchunked,
      Template.messages]
  · -- `coversVars T 22 Cj = true`
    unfold coversVars
    have hCol0 : T.colSlot i = some 0 := by simp [Template.colSlot, T, List.findIdx?_cons]
    have hCol1 : T.colSlot 20 = some 1 := by
      have hneq : (SlotDef.column (F := BN254Fr) i == SlotDef.column 20) = false := by
        simp [hne]
      simp [Template.colSlot, T, List.findIdx?_cons, hneq]
    simp only [Cj, List.all_cons, List.all_nil, Bool.and_true, poly_norm_ofExpr_normExpr_linear hi c]
    by_cases hc : c = 0
    · simp [hc, hCol0, show i < 22 by omega]
    · simp [hc, hCol0, hCol1, show i < 22 by omega]
  · -- `realisedB T sr gs = true`
    unfold realisedB rowMatches
    simp only [T, List.all_cons, List.all_nil, Bool.and_true, List.any_eq_true]
    refine ⟨_, hgMem, ?_⟩
    simp [sr, laneMatches]
  · -- `colsB T sr = true`
    simp [colsB, T, sr]
    rw [show 8 * i = (2 * i) * 4 by omega, Nat.mul_mod_left]

/-! ### Structurally-recursive (`WellFounded.fix`-free) `Template.check` / `AirIn.certSomeOk` Helper

`Template.meaning` and `Template.expandAbove` use well-founded recursion (`WellFounded.fix`),
which blows up inside kernel `decide` when a template chains 60+ `.sum` slots. The helper
`certSomeOkFast` replaces `Template.meaning` by fuel-indexed structural recursion `meaningFuel`
and short-circuits `Template.expandAbove s t` to `Poly.var t` whenever every slot index in a
`.defines s` relation satisfies `t ≤ s`. -/

def meaningFuel {F : Type} [CommRing F] (T : Template F) : Nat → Nat → Tiling.Poly F
  | 0, _ => []
  | fuel + 1, s =>
    match T.slots[s]? with
    | some (.column c) => Tiling.Poly.var c
    | some (.sum terms k) =>
        Tiling.Poly.const k ++
          Aiur.Tiling.substTerms (fun u => if _h : u < s then meaningFuel T fuel u else []) terms
    | _ => []

private theorem template_meaning_eq_fuel {F : Type} [CommRing F] (T : Template F) :
    ∀ (fuel s : Nat), s < fuel → T.meaning s = meaningFuel T fuel s
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, s, h => by
    rw [Template.meaning, meaningFuel]
    cases T.slots[s]? with
    | none => rfl
    | some d =>
      cases d with
      | column c => rfl
      | sum terms k =>
        dsimp only
        congr 1
        unfold Aiur.Tiling.substTerms
        apply List.flatMap_congr
        intro t _
        cases t with
        | linear a u =>
          simp only [Aiur.Tiling.Term.subst]
          split_ifs with hu
          · rw [template_meaning_eq_fuel T fuel u (by omega)]
          · rfl
        | product a u v =>
          simp only [Aiur.Tiling.Term.subst]
          split_ifs with hu hv
          · rw [template_meaning_eq_fuel T fuel u (by omega),
                template_meaning_eq_fuel T fuel v (by omega)]
          · rw [template_meaning_eq_fuel T fuel u (by omega)]
          · rw [template_meaning_eq_fuel T fuel v (by omega)]
          · rfl
      | invocation => rfl
      | key _ => rfl

private theorem expandAbove_eq_var_of_le {F : Type} [CommRing F] (T : Template F) {s t : Nat}
    (hle : t ≤ s) : T.expandAbove s t = Tiling.Poly.var t := by
  rw [Template.expandAbove]
  cases T.slots[t]? with
  | none => rfl
  | some d =>
    cases d with
    | sum terms k => simp [Nat.not_lt.mpr hle]
    | _ => rfl

private theorem poly_substMono_congr {F : Type} [CommRing F] {f g : Nat → Tiling.Poly F}
    {m : Tiling.Mono} (h : ∀ u ∈ m, f u = g u) :
    Tiling.Poly.substMono f m = Tiling.Poly.substMono g m := by
  induction m with
  | nil => rfl
  | cons u us ih =>
    change (f u).mul (Tiling.Poly.substMono f us) = (g u).mul (Tiling.Poly.substMono g us)
    rw [h u List.mem_cons_self, ih (fun v hv => h v (List.mem_cons_of_mem _ hv))]

private theorem poly_subst_congr {F : Type} [CommRing F] {f g : Nat → Tiling.Poly F}
    {p : Tiling.Poly F} (h : ∀ t ∈ p, ∀ u ∈ t.1, f u = g u) :
    Tiling.Poly.subst f p = Tiling.Poly.subst g p := by
  unfold Tiling.Poly.subst
  apply List.flatMap_congr
  intro t ht
  rw [poly_substMono_congr (h t ht)]

def checkRelationFast {F : Type} [CommRing F] [DecidableEq F]
    (T : Template F) (circuit : Tiling.Circuit F) : Tiling.Role × Tiling.Poly F → Bool
  | (.pad, p) => (Tiling.Poly.norm p).isEmpty
  | (.defines s, p) =>
      p.all (fun t => t.1.all (· ≤ s)) &&
      match T.slots[s]? with
      | some (.sum terms k) =>
          Tiling.Poly.Identical (Tiling.Poly.subst Tiling.Poly.var p) (Aiur.Tiling.defPoly s terms k)
      | _ => false
  | (.root j, p) =>
      match circuit.constraints[j]? with
      | some constraint =>
          p.all (fun t => t.1.all (· < T.slots.length)) &&
          T.widePoly p &&
          Tiling.Poly.Identical (Tiling.Poly.subst (meaningFuel T T.slots.length) p)
            (Tiling.Poly.ofExpr constraint)
      | none => false
  | (.pin s, p) =>
      T.slots[s]? == some .invocation &&
        Tiling.Poly.Identical p (Tiling.Poly.sub (Tiling.Poly.var s) (Tiling.Poly.var T.idVar))
  | (.boolean _, _) => true

private theorem checkRelation_of_fast {F : Type} [CommRing F] [DecidableEq F]
    (T : Template F) (circuit : Tiling.Circuit F) (rel : Tiling.Role × Tiling.Poly F)
    (h : checkRelationFast T circuit rel = true) :
    T.checkRelation circuit rel = true := by
  rcases rel with ⟨role, p⟩
  cases role with
  | pad => exact h
  | pin s => exact h
  | boolean s => exact h
  | defines s =>
    simp only [checkRelationFast, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨hle, hmatch⟩
    unfold Template.checkRelation
    have hsub : Tiling.Poly.subst (T.expandAbove s) p = Tiling.Poly.subst Tiling.Poly.var p :=
      poly_subst_congr (fun t ht u hu => expandAbove_eq_var_of_le T (hle t ht u hu))
    cases hs : T.slots[s]? with
    | none => simp [hs] at hmatch
    | some d =>
      cases d with
      | sum terms k => simpa [hs, hsub] using hmatch
      | _ => simp [hs] at hmatch
  | root j =>
    unfold checkRelationFast at h
    unfold Template.checkRelation
    cases hc : circuit.constraints[j]? with
    | none => simp [hc] at h
    | some constraint =>
      simp only [hc, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨⟨hlt, hwide⟩, hid⟩
      have hsub : Tiling.Poly.subst T.meaning p = Tiling.Poly.subst (meaningFuel T T.slots.length) p :=
        poly_subst_congr (fun t ht u hu => template_meaning_eq_fuel T T.slots.length u (hlt t ht u hu))
      simp only [hc, hwide, hsub, hid, Bool.true_and]

def templateCheckFast {F : Type} [CommRing F] [DecidableEq F]
    (T : Template F) (circuit : Tiling.Circuit F) : Bool :=
  4 ≤ T.width && T.width % 4 == 0 &&
    T.rows.all (Row.wellFormed T.width) &&
    T.rows.all (fun row => row.cells.all fun cell => cell.all (· < T.slots.length)) &&
    T.slots.zipIdx.all (fun (d, s) => T.checkSlot s d) &&
    T.relations.all (checkRelationFast T circuit) &&
    circuit.constraints.zipIdx.all (fun (p, j) => T.checkConstraint j p) &&
    (T.messages.isEmpty && circuit.lookups.isEmpty)

private theorem template_check_of_fast {F : Type} [CommRing F] [DecidableEq F]
    {T : Template F} {circuit : Tiling.Circuit F}
    (h : templateCheckFast T circuit = true) :
    T.check circuit = true := by
  unfold templateCheckFast at h
  unfold Template.check
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h ⊢
  rcases h with ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8m, h8l⟩
  refine ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, ?_⟩, h7⟩, Or.inl ?_⟩
  · rw [List.all_eq_true] at h6 ⊢
    exact fun rel hrel => checkRelation_of_fast T circuit rel (h6 rel hrel)
  · have hm : T.messages = [] := List.isEmpty_iff.mp h8m
    have hl : circuit.lookups = [] := List.isEmpty_iff.mp h8l
    simp [Template.checkUnchunked, hm, hl]

def certSomeOkFast (a : WideStage.Air BN254Fr) (r k : Nat) (G : Nat → Option (Lower.LGate BN254Fr))
    (c : AirIn.MsgCert BN254Fr) : Bool :=
  let sr (s : Nat) : Lower.Ref := c.sr.getD s 0
  templateCheckFast c.T (AirIn.msgCircuit a r k c.count) &&
    coversVars c.T (a.circuit.width + 6) (AirIn.msgCircuit a r k c.count) &&
    realisedIdx c.T sr c.idx G && AirIn.msgColsB a c.T sr c.qRef c.sIn c.sOut

private theorem certSomeOk_of_fast {a : WideStage.Air BN254Fr} {r k : Nat}
    {G : Nat → Option (Lower.LGate BN254Fr)} {c : AirIn.MsgCert BN254Fr}
    (h : certSomeOkFast a r k G c = true) :
    AirIn.certSomeOk a r k G c = true := by
  unfold certSomeOkFast at h
  unfold AirIn.certSomeOk
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨⟨⟨template_check_of_fast h.1.1.1, h.1.1.2⟩, h.1.2⟩, h.2⟩

def mkToyFinalAirs (lowVal highVal : Nat) : List (WideStage.Air BN254Fr) :=
  WideStage.unitAirs (fun _ => 0) [(((mkToyFinalSpec lowVal highVal).erasedChip, none), 1)]

abbrev mkToyFinalAllAirs (lowVal highVal : Nat) : List (WideStage.Air BN254Fr) :=
  mkToyFinalAirs lowVal highVal ++ [rootAir 0 20]

private theorem mkToyFinal_air0_constraints (lowVal highVal : Nat) :
    (airAt (mkToyFinalAllAirs lowVal highVal) 0).circuit.constraints =
      Activation.boolean 20 ::
      ([subConstPoly 0 (lowVal : BN254Fr), subConstPoly 1 (highVal : BN254Fr)] ++
        bn254AffineZeroPairWords.zipIdx.map fun (p : BN254Fr × Nat) => subConstPoly (2 + p.2) p.1).map
        (Activation.polynomial 20) ++
      [.mul (.sub (.const 1) (.var 20)) (.var 21)] := by
  have hAir0 : (airAt (mkToyFinalAllAirs lowVal highVal) 0).circuit =
      Bridge.lower (fun _ => 0) (mkToyFinalSpec lowVal highVal).erasedChip := by
    simp [airAt, mkToyFinalAllAirs, mkToyFinalAirs, WideStage.unitAirs, WideStage.unitAir,
      Bridge.unitCircuit]
  rw [hAir0]
  simp [Bridge.lower, Activation.compile, Activation.guards, FlatAssertSpec.erasedChip,
    Erasure.chip, FlatAssertSpec.physChip, FlatAssertSpec.numVars, FlatAssertSpec.allConsts,
    FlatAssertSpec.inConsts, mkToyFinalSpec, FlatVal.words, bn254AffineZeroPairWords,
    bn254AffineInfinityWords]

set_option maxRecDepth 4096 in
private theorem toyFinalCert0_ok :
    AirIn.certSomeOk toyFinalAir0Dummy 0 0
      (AirIn.rowPool (toyFinalRowGates 0 0 (0, 0)) toyPlonkPool.gates)
      toyFinalMsgCert0Val = true :=
  certSomeOk_of_fast (by decide)

set_option maxRecDepth 4096 in
private theorem toyFinalCert1_ok :
    AirIn.certSomeOk (rootAir (0 : BN254Fr) 20) 0 0
      (AirIn.rowPool (toyFinalLook1.1 ++ toyFinalLook1.2.1) toyPlonkPool.gates)
      toyFinalMsgCert1Val = true :=
  certSomeOk_of_fast (by decide)

def mkToyFinalCert (lowVal highVal : Nat) :
    DepthBridge.PlonkStageCert (mkToyFinalAllAirs lowVal highVal) toyPlonkPool where
  rowGates := toyFinalRowGates lowVal highVal
  rowFin := toyFinalRowFin
  poolClosedOk := by
    unfold poolClosed
    simp only [toyPlonkPool, Array.all_eq_true_iff_forall_mem, List.mem_toArray, List.mem_map,
      List.mem_range]
    rintro g ⟨i, _, rfl⟩
    by_cases hi0 : i = 0 <;> simp [hi0, Lower.gammaRef, Lower.pool]
  constraintCerts := by
    intro i hi j hj
    have hInst : Plonk.instances (mkToyFinalAllAirs lowVal highVal) = [(0, 0), (1, 0)] := by
      simp [Plonk.instances, mkToyFinalAllAirs, mkToyFinalAirs, WideStage.unitAirs, WideStage.unitAir, rootAir]
    rw [hInst] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · -- Row (0, 0): 22 constraints (`0`: bool, `1`: low, `2`: high, `3..20`: affineZero, `21`: mult)
      set s := mkToyFinalSpec lowVal highVal
      have hNumVars : s.numVars = 20 := rfl
      have hAir0 : (airAt (mkToyFinalAllAirs lowVal highVal) 0).circuit =
          Bridge.lower (fun _ => 0) s.erasedChip := by
        simp [airAt, mkToyFinalAllAirs, mkToyFinalAirs, WideStage.unitAirs, WideStage.unitAir,
          Bridge.unitCircuit, s]
      have hCons := mkToyFinal_air0_constraints lowVal highVal
      have hWidth : (airAt (mkToyFinalAllAirs lowVal highVal) 0).circuit.width = 22 := by
        rw [hAir0]
        simp [Bridge.lower, FlatAssertSpec.erasedChip, Erasure.chip, FlatAssertSpec.physChip, hNumVars]
      have hFixed0 : (airAt (mkToyFinalAllAirs lowVal highVal) 0).fixed = fun _ _ => 0 := by
        simp [airAt, mkToyFinalAllAirs, mkToyFinalAirs, WideStage.unitAirs, WideStage.unitAir]
      have hRowCon : ∀ k < 22,
          AirIn.rowConstraint (airAt (mkToyFinalAllAirs lowVal highVal) 0) 0 k =
            ⟨22, 0, [AirIn.normExpr ((airAt (mkToyFinalAllAirs lowVal highVal) 0).circuit.constraints.getD k (.const 0))], []⟩ := by
        intro k hk
        unfold AirIn.rowConstraint
        have hInB : ((airAt (mkToyFinalAllAirs lowVal highVal) 0).circuit.constraints.getD k (.const 0)).inBounds 22 = true := by
          have hwf := s.activated_erasedChip_wellFormed
          simp only [Circuit.Chip.wellFormed, Bool.and_eq_true, List.all_eq_true] at hwf
          have hlen : (airAt (mkToyFinalAllAirs lowVal highVal) 0).circuit.constraints.length = 22 := by
            rw [hCons]; simp [bn254AffineZeroPairWords, bn254AffineInfinityWords]
          have hmem : (airAt (mkToyFinalAllAirs lowVal highVal) 0).circuit.constraints.getD k (.const 0) ∈
              (airAt (mkToyFinalAllAirs lowVal highVal) 0).circuit.constraints := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen ▸ hk)]
            exact List.getElem_mem _
          rw [hAir0] at hmem
          simp only [Bridge.lower, List.mem_append, List.mem_singleton] at hmem
          rcases hmem with h1 | h2
          · rw [hAir0]; simp only [Bridge.lower]
            exact Scalar.Circuit.ArithExpr.inBounds_mono
              (by simp [Activation.compile, FlatAssertSpec.erasedChip, Erasure.chip,
                FlatAssertSpec.physChip, hNumVars])
              (hwf.1.1.2 _ h1)
          · rw [hAir0]; simp only [Bridge.lower]; rw [h2]
            simp [Scalar.Circuit.ArithExpr.inBounds, FlatAssertSpec.erasedChip, Erasure.chip,
              FlatAssertSpec.physChip, hNumVars]
        have hFix := AirIn.fixRow_of_inBounds (airAt (mkToyFinalAllAirs lowVal highVal) 0) 0
          ((airAt (mkToyFinalAllAirs lowVal highVal) 0).circuit.constraints.getD k (.const 0)) (hWidth ▸ hInB)
        rw [hFix]
        simp only [hWidth]
      have hj22 : j < 22 := by
        rw [hCons] at hj; simp [bn254AffineZeroPairWords, bn254AffineInfinityWords] at hj; exact hj
      have hFilt : ((toyFinalRowGates lowVal highVal (0, 0)).filter (·.tag == .constraint)).toList =
          (toyFinalConstraintGates lowVal highVal).toList := by
        have hLook0NoCon : (toyFinalLook0.1 ++ toyFinalLook0.2.1).filter (·.tag == .constraint) = #[] := by decide
        have hConAll : (toyFinalConstraintGates lowVal highVal).filter (·.tag == .constraint) =
            toyFinalConstraintGates lowVal highVal := by
          have hTagEq : (Lower.Tag.constraint == Lower.Tag.constraint) = true := rfl
          apply Array.toList_inj.mp
          rw [Array.toList_filter]
          simp only [toyFinalConstraintGates, List.toList_toArray, List.filter_cons, List.filter_nil,
            List.filter_append, List.filter_map, Function.comp_def, hTagEq, ↓reduceIte, List.filter_true]
        simp only [toyFinalRowGates, Array.toList_filter, Array.toList_append, List.filter_append]
        have h1 : (toyFinalLook0.1.toList ++ toyFinalLook0.2.1.toList).filter (·.tag == .constraint) = [] := by
          have := congrArg Array.toList hLook0NoCon
          simpa using this
        have h2 : (toyFinalConstraintGates lowVal highVal).toList.filter (·.tag == .constraint) =
            (toyFinalConstraintGates lowVal highVal).toList := by
          rw [← Array.toList_filter, hConAll]
        rw [← List.filter_append, h1, h2, List.nil_append]
      dsimp only
      rw [hRowCon j hj22, hWidth, hFilt]
      -- Dispatch on `j = 0`, `1 ≤ j ≤ 20`, `j = 21`!
      by_cases hj0 : j = 0
      · subst hj0
        have hget : (airAt (mkToyFinalAllAirs lowVal highVal) 0).circuit.constraints.getD 0 (.const 0) =
            Activation.boolean 20 := by rw [hCons]; rfl
        rw [hget]
        refine ⟨
          { width := 4, slots := [.column 20],
            rows := [.gate [⟨1, -1, 0, 0, 0, 0, some 0, some 0, some 0, none, 0⟩] false [.root 0]] },
          fun _ => 160,
          template_check_of_fast (by clear * -; decide),
          by clear * -; decide, ?_, by clear * -; decide⟩
        unfold realisedB rowMatches
        simp only [List.all_cons, List.all_nil, Bool.and_true, List.any_eq_true]
        refine ⟨({ a := 160, b := 160, c := 160, L := -1, R := 0, O := 0, M := 1, C := 0,
                   tag := .constraint, root := some 0 } : Lower.LGate BN254Fr),
          by simp [toyFinalConstraintGates], by decide⟩
      · by_cases hj21 : j = 21
        · subst hj21
          have hget : (airAt (mkToyFinalAllAirs lowVal highVal) 0).circuit.constraints.getD 21 (.const 0) =
              .mul (.sub (.const 1) (.var 20)) (.var 21) := by
            rw [hCons]; simp [bn254AffineZeroPairWords, bn254AffineInfinityWords]
          rw [hget]
          refine ⟨
            { width := 4, slots := [.column 20, .column 21],
              rows := [.gate [⟨-1, 0, 1, 0, 0, 0, some 0, some 1, some 1, none, 0⟩] false [.root 0]] },
            fun | 0 => 160 | _ => 168,
            template_check_of_fast (by clear * -; decide),
            by clear * -; decide, ?_, by clear * -; decide⟩
          unfold realisedB rowMatches
          simp only [List.all_cons, List.all_nil, Bool.and_true, List.any_eq_true]
          refine ⟨({ a := 160, b := 168, c := 168, L := 0, R := 1, O := 0, M := -1, C := 0,
                     tag := .constraint, root := some 21 } : Lower.LGate BN254Fr),
            by simp [toyFinalConstraintGates], by decide⟩
        · -- `j = i + 1` with `i < 20`!
          set idx := j - 1
          have hidx20 : idx < 20 := by omega
          have hjEq : j = idx + 1 := by omega
          have hget : (airAt (mkToyFinalAllAirs lowVal highVal) 0).circuit.constraints.getD j (.const 0) =
              Activation.polynomial 20 (subConstPoly idx (s.allConsts.getD idx 0)) := by
            rw [hCons, hjEq]
            interval_cases idx <;>
              simp [s, mkToyFinalSpec, FlatAssertSpec.allConsts, FlatAssertSpec.inConsts,
                FlatVal.words, bn254AffineZeroPairWords, bn254AffineInfinityWords]
          have hgMem :
              ({ a := 8 * idx, b := 160, c := 8 * idx, L := 1, R := -(s.allConsts.getD idx 0),
                 O := 0, M := 0, C := 0, tag := .constraint, root := some (idx + 1) } : Lower.LGate BN254Fr) ∈
              (toyFinalConstraintGates lowVal highVal).toList := by
            interval_cases idx <;>
              simp [s, mkToyFinalSpec, FlatAssertSpec.allConsts, FlatAssertSpec.inConsts,
                FlatVal.words, bn254AffineZeroPairWords, bn254AffineInfinityWords,
                toyFinalConstraintGates]
          rw [hget]
          exact ⟨_, _, linearConstraintCert_ok hidx20 (s.allConsts.getD idx 0) hgMem⟩
    · -- Row (1, 0): 0 constraints
      have h0 : (airAt (mkToyFinalAllAirs lowVal highVal) 1).circuit.constraints.length = 0 := by
        simp [airAt, mkToyFinalAllAirs, mkToyFinalAirs, WideStage.unitAirs, WideStage.unitAir, rootAir]
      dsimp only at hj
      omega
  msgCerts := fun i _ => if i == (0, 0) then toyFinalMsgCert0 else toyFinalMsgCert1
  chainOk := by
    intro i hi
    have hInst : Plonk.instances (mkToyFinalAllAirs lowVal highVal) = [(0, 0), (1, 0)] := by
      simp [Plonk.instances, mkToyFinalAllAirs, mkToyFinalAirs, WideStage.unitAirs, WideStage.unitAir, rootAir]
    rw [hInst] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · -- Row (0, 0): reduce to concrete `toyFinalAir0Dummy` + `toyFinalRowGates 0 0 (0, 0)`!
      have hLookEq : (airAt (mkToyFinalAllAirs lowVal highVal) 0).circuit.lookups =
          toyFinalAir0Dummy.circuit.lookups := by
        simp [airAt, mkToyFinalAllAirs, mkToyFinalAirs, toyFinalAir0Dummy, toyFinalLookupArgs,
          WideStage.unitAirs, WideStage.unitAir, Bridge.unitCircuit, Bridge.lower,
          Activation.compile, Bridge.receiveLookup, FlatAssertSpec.erasedChip, Erasure.chip,
          Erasure.pack, FlatAssertSpec.physChip, FlatAssertSpec.inputWireVars,
          FlatAssertSpec.mkInputWires, FlatAssertSpec.numVars, FlatAssertSpec.allConsts,
          FlatAssertSpec.inConsts, mkToyFinalSpec, FlatVal.words, FlatVal.width,
          bn254AffineZeroPairWords, bn254AffineInfinityWords]
        rfl
      have hWEq : (airAt (mkToyFinalAllAirs lowVal highVal) 0).circuit.width = toyFinalAir0Dummy.circuit.width := by
        simp [airAt, mkToyFinalAllAirs, mkToyFinalAirs, toyFinalAir0Dummy, WideStage.unitAirs,
          WideStage.unitAir, Bridge.unitCircuit, Bridge.lower, FlatAssertSpec.erasedChip, Erasure.chip,
          FlatAssertSpec.physChip, FlatAssertSpec.numVars, FlatAssertSpec.allConsts,
          FlatAssertSpec.inConsts, mkToyFinalSpec, FlatVal.words, bn254AffineZeroPairWords,
          bn254AffineInfinityWords]
      have hFEq : (airAt (mkToyFinalAllAirs lowVal highVal) 0).fixed = toyFinalAir0Dummy.fixed := by
        simp [airAt, mkToyFinalAllAirs, mkToyFinalAirs, toyFinalAir0Dummy, WideStage.unitAirs, WideStage.unitAir]
      have hPoolAgree : ∀ k, k < 43 ∨ 65 ≤ k →
          AirIn.rowPool (toyFinalRowGates lowVal highVal (0, 0)) toyPlonkPool.gates k =
            AirIn.rowPool (toyFinalRowGates 0 0 (0, 0)) toyPlonkPool.gates k := by
        intro k hk
        have hSz1 : (toyFinalRowGates lowVal highVal (0, 0)).size = 65 := by
          simp [toyFinalRowGates, toyFinalConstraintGates, bn254AffineZeroPairWords,
            bn254AffineInfinityWords, show toyFinalLook0.1.size = 41 by decide,
            show toyFinalLook0.2.1.size = 2 by decide]
        have hSz2 : (toyFinalRowGates 0 0 (0, 0)).size = 65 := by decide
        have hSzL : (toyFinalLook0.1 ++ toyFinalLook0.2.1).size = 43 := by decide
        unfold AirIn.rowPool
        rw [hSz1, hSz2]
        rcases hk with hlt | hge
        · simp only [show k < 65 by omega, ↓reduceIte, toyFinalRowGates,
            Array.getElem?_append_left (show k < (toyFinalLook0.1 ++ toyFinalLook0.2.1).size by omega)]
        · simp only [show ¬ k < 65 by omega, ↓reduceIte]
      have hcIdx : ∀ j < toyFinalMsgCert0Val.T.rows.length,
          toyFinalMsgCert0Val.idx.getD j 0 < 43 ∨ 65 ≤ toyFinalMsgCert0Val.idx.getD j 0 := by
        have hAll : (List.range toyFinalMsgCert0Val.T.rows.length).all
            (fun j => decide (toyFinalMsgCert0Val.idx.getD j 0 < 43 ∨
              65 ≤ toyFinalMsgCert0Val.idx.getD j 0)) = true := by clear * -; decide
        intro j hj
        exact of_decide_eq_true (List.all_eq_true.mp hAll j (List.mem_range.mpr hj))
      have hRealEq : realisedIdx toyFinalMsgCert0Val.T (fun s => toyFinalMsgCert0Val.sr.getD s 0)
            toyFinalMsgCert0Val.idx
            (AirIn.rowPool (toyFinalRowGates lowVal highVal (0, 0)) toyPlonkPool.gates) =
          realisedIdx toyFinalMsgCert0Val.T (fun s => toyFinalMsgCert0Val.sr.getD s 0)
            toyFinalMsgCert0Val.idx
            (AirIn.rowPool (toyFinalRowGates 0 0 (0, 0)) toyPlonkPool.gates) := by
        unfold realisedIdx
        have hallEq : ∀ {α : Type} (l : List α) (p q : α → Bool),
            (∀ x ∈ l, p x = q x) → l.all p = l.all q := by
          intro α l p q h
          induction l with
          | nil => rfl
          | cons a as ih =>
            simp only [List.all_cons, h a List.mem_cons_self,
              ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
        apply hallEq
        rintro ⟨row, j⟩ hj
        have hjLt : j < toyFinalMsgCert0Val.T.rows.length := by
          have hget := List.mem_zipIdx_iff_getElem?.mp hj
          exact (List.getElem?_eq_some_iff.mp (by simpa using hget)).1
        cases row with
        | gate ls isMsg roles =>
          cases ls with
          | nil => rfl
          | cons lane rest =>
            cases rest with
            | nil =>
              cases isMsg with
              | false =>
                dsimp only
                rw [hPoolAgree _ (hcIdx j hjLt)]
              | true => rfl
            | cons _ _ => rfl
        | message _ _ _ _ => rfl
      have hFixEq : AirIn.fixRow (airAt (mkToyFinalAllAirs lowVal highVal) 0) 0 =
          AirIn.fixRow toyFinalAir0Dummy 0 := by
        funext e
        induction e with
        | const _ => rfl
        | var v => simp [AirIn.fixRow, hWEq, hFEq]
        | add _ _ ih1 ih2 => simp [AirIn.fixRow, ih1, ih2]
        | sub _ _ ih1 ih2 => simp [AirIn.fixRow, ih1, ih2]
        | mul _ _ ih1 ih2 => simp [AirIn.fixRow, ih1, ih2]
      have hMsgCir : AirIn.msgCircuit (airAt (mkToyFinalAllAirs lowVal highVal) 0) 0 0 toyFinalMsgCert0Val.count =
          AirIn.msgCircuit toyFinalAir0Dummy 0 0 toyFinalMsgCert0Val.count := by
        unfold AirIn.msgCircuit AirIn.qConstraint AirIn.sumConstraint AirIn.countConstraint
          AirIn.multExpr AirIn.argExprs AirIn.lookupAt AirIn.gammaCol AirIn.betaCol
          AirIn.qCol AirIn.sInCol AirIn.sOutCol
        simp only [hLookEq, hWEq, hFixEq]
      have hColsEq : AirIn.msgColsB (airAt (mkToyFinalAllAirs lowVal highVal) 0) toyFinalMsgCert0Val.T
            (fun s => toyFinalMsgCert0Val.sr.getD s 0) toyFinalMsgCert0Val.qRef
            toyFinalMsgCert0Val.sIn toyFinalMsgCert0Val.sOut =
          AirIn.msgColsB toyFinalAir0Dummy toyFinalMsgCert0Val.T
            (fun s => toyFinalMsgCert0Val.sr.getD s 0) toyFinalMsgCert0Val.qRef
            toyFinalMsgCert0Val.sIn toyFinalMsgCert0Val.sOut := by
        unfold AirIn.msgColsB AirIn.gammaCol AirIn.betaCol AirIn.qCol AirIn.sInCol
          AirIn.sOutCol AirIn.spareCol
        simp [hWEq]
      have hCert0Ok := toyFinalCert0_ok
      have hLen1 : (airAt (mkToyFinalAllAirs lowVal highVal) 0).circuit.lookups.length = 1 := by
        rw [hLookEq]; decide
      rw [hLen1, List.range_one]
      simp only [beq_self_eq_true, ↓reduceIte, AirIn.chainOk, toyFinalMsgCert0, AirIn.certSomeOk,
        hMsgCir, hWEq, hRealEq, hColsEq]
      simp only [AirIn.certSomeOk] at hCert0Ok
      rw [hCert0Ok]
      rfl
    · -- Row (1, 0): 100% concrete via `toyFinalCert1_ok`!
      have hAir1 : airAt (mkToyFinalAllAirs lowVal highVal) 1 = rootAir (0 : BN254Fr) 20 := by
        simp [airAt, mkToyFinalAllAirs, mkToyFinalAirs, WideStage.unitAirs, WideStage.unitAir]
      rw [hAir1]
      have hCert1Ok : AirIn.certSomeOk (rootAir (0 : BN254Fr) 20) 0 0
          (AirIn.rowPool (toyFinalRowGates lowVal highVal (1, 0)) toyPlonkPool.gates)
          toyFinalMsgCert1Val = true := toyFinalCert1_ok
      have hLen1 : (rootAir (0 : BN254Fr) 20).circuit.lookups.length = 1 := rfl
      rw [hLen1, List.range_one]
      simp only [show ((1, 0) == (0, 0)) = false by decide, Bool.false_eq_true, ↓reduceIte,
        AirIn.chainOk, toyFinalMsgCert1, hCert1Ok]
      rfl

def mkToyFinalWiring (lowVal highVal : Nat) :
    DepthBridge.PlonkStageWiring (mkToyFinalAllAirs lowVal highVal) toyPlonkPool
      (mkToyFinalCert lowVal highVal).rowFin where
  wireOf := toyFinalLayout.wireOf
  cellWire := toyFinalLayout.cellWire
  poolWire := toyFinalLayout.poolWire
  init := 300
  last := 200 + toyFinalLook1.2.2.2 / 4
  cell_eq := fun i x hx => by simp [Aiur.Plonk.Layout.wireOf, hx]
  pool_eq := fun i x hx => by simp [Aiur.Plonk.Layout.wireOf, hx]
  linked := by
    have hInst : Plonk.instances (mkToyFinalAllAirs lowVal highVal) = [(0, 0), (1, 0)] := by
      simp [Plonk.instances, mkToyFinalAllAirs, mkToyFinalAirs, WideStage.unitAirs, WideStage.unitAir, rootAir]
    rw [hInst]
    dsimp only [mkToyFinalCert]
    exact linked_of_linkedB (by clear * -; decide)

def mkToyFinalEmitScs (lowVal highVal : Nat) : Aiur.Plonk.Scs BN254Fr :=
  DepthBridge.emitCertifiedScs (mkToyFinalAllAirs lowVal highVal) toyPlonkPool
    (mkToyFinalCert lowVal highVal).rowGates (mkToyFinalCert lowVal highVal).rowFin
    (mkToyFinalWiring lowVal highVal) 310 2 [0, 1]

/-- Symbolic gate-satisfaction proof for ALL gates of `mkToyFinalEmitScs lowVal highVal`! -/
private theorem toyFinalEmitScs_sat (lowVal highVal : Nat) :
    (mkToyFinalEmitScs lowVal highVal).Satisfied (toyFinalW lowVal highVal)
      [(lowVal : BN254Fr), (highVal : BN254Fr)] (fun _ => 0) := by
  have hInst : Plonk.instances (mkToyFinalAllAirs lowVal highVal) = [(0, 0), (1, 0)] := by
    simp [Plonk.instances, mkToyFinalAllAirs, mkToyFinalAirs, WideStage.unitAirs, WideStage.unitAir, rootAir]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi _
    have hi2 : i = 0 ∨ i = 1 := by simp at hi; omega
    rcases hi2 with rfl | rfl <;> simp [toyFinalW, toyFinalWLin]
  · simp [mkToyFinalEmitScs, DepthBridge.emitCertifiedScs, mkToyFinalWiring, toyFinalLayout,
      Lower.gammaRef, Lower.pool, Aiur.Plonk.Layout.poolWire, toyFinalW, toyFinalWLin]
  · intro g hg
    simp only [mkToyFinalEmitScs, DepthBridge.emitCertifiedScs, DepthBridge.emitCertifiedGates,
      hInst, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, List.mem_map] at hg
    rcases hg with ((rfl | rfl) | ⟨pg, hpg, rfl⟩) | (⟨rg, hrg, rfl⟩ | ⟨rg, hrg, rfl⟩)
    · -- `last = 242` gate: `w 242 = 0`
      have hlast : (mkToyFinalWiring lowVal highVal).last = 242 := by
        simp only [mkToyFinalWiring]; decide
      simp [Gate.Holds, hlast, toyFinalW, toyFinalWLin]
    · -- `init = 300` gate: `w 300 = 0`
      simp [Gate.Holds, mkToyFinalWiring, toyFinalW, toyFinalWLin]
    · -- Global pool gates: `γ = 0`, all `γ^e = 0`, `0 * 0 - 0 = 0`
      have hP : ∀ pg' ∈ toyPlonkPool.gates.toList,
          (pg'.inst toyFinalLayout.poolWire).a ∈ List.range' 50 23 ∧
          (pg'.inst toyFinalLayout.poolWire).b = 50 ∧
          (pg'.inst toyFinalLayout.poolWire).c ∈ List.range' 52 21 ∧
          pg'.L = 0 ∧ pg'.R = 0 ∧ pg'.O = -1 ∧ pg'.M = 1 ∧ pg'.C = 0 := by decide
      obtain ⟨_, hb, hc, hL, hR, hO, hM, hC⟩ := hP pg hpg
      have hWLinPool : ∀ w, 52 ≤ w → w < 73 → toyFinalWLin w = (0, 0, 0) := by
        intro w h1 h2
        unfold toyFinalWLin
        simp only [show ¬ (w = 0) by omega, show ¬ (w = 1) by omega, show ¬ (w < 20) by omega,
          show ¬ (w = 20) by omega, show ¬ (w = 21) by omega, show ¬ (w < 40) by omega,
          show ¬ (w = 40) by omega, show ¬ (w = 41) by omega, show ¬ (w = 51) by omega,
          show ¬ (w = 100) by omega, show ¬ (w = 101) by omega, show ¬ (w = 102) by omega,
          show ¬ (103 ≤ w ∧ w ≤ 140) by omega, show ¬ (w = 141) by omega, show ¬ (w = 142) by omega,
          show ¬ (w = 200) by omega, show ¬ (w = 201) by omega, show ¬ (w = 202) by omega,
          show ¬ (203 ≤ w ∧ w ≤ 240) by omega, show ¬ (w = 241) by omega, ↓reduceIte]
      have hwc : toyFinalW lowVal highVal (pg.inst toyFinalLayout.poolWire).c = 0 := by
        rw [List.mem_range'] at hc; obtain ⟨k, hk, heq⟩ := hc
        rw [heq, one_mul]; simp [toyFinalW, hWLinPool (52 + k) (by omega) (by omega)]
      have hwb : toyFinalW lowVal highVal (pg.inst toyFinalLayout.poolWire).b = 0 := by
        rw [hb]; simp [toyFinalW, toyFinalWLin]
      simp only [Lower.LGate.inst] at hwb hwc
      simp [Gate.Holds, Lower.LGate.inst, mkToyFinalWiring, hL, hR, hO, hM, hC, hwb, hwc]
    · -- Row (0, 0) gates: `toyFinalLook0` (43 concrete gates) ++ `toyFinalConstraintGates` (22 gates)
      simp only [mkToyFinalCert, toyFinalRowGates, Array.toList_append, List.mem_append] at hrg
      rcases hrg with hlook | hcon
      · -- 43 concrete lookup gates instantiated at row `(0, 0)` checked symbolically via `gateHoldsLinB`!
        have hAll0 : ((toyFinalLook0.1 ++ toyFinalLook0.2.1).toList.map
            (·.inst (toyFinalLayout.wireOf (0, 0)))).all gateHoldsLinB = true := by decide
        have hMem : rg.inst ((mkToyFinalWiring lowVal highVal).wireOf (0, 0)) ∈
            ((toyFinalLook0.1 ++ toyFinalLook0.2.1).toList.map
              (·.inst (toyFinalLayout.wireOf (0, 0)))) :=
          List.mem_map.mpr ⟨rg, by simpa using hlook, rfl⟩
        exact gateHolds_of_gateHoldsLinB lowVal highVal _ (List.all_eq_true.mp hAll0 _ hMem)
      · -- 22 constraint gates
        simp only [toyFinalConstraintGates, List.toList_toArray, List.cons_append,
          List.nil_append, List.mem_cons, List.mem_append, List.mem_map,           List.not_mem_nil, or_false] at hcon
        rcases hcon with rfl | rfl | rfl | ⟨⟨v, k⟩, hvk, rfl⟩ | rfl
        · simp [Gate.Holds, Lower.LGate.inst, mkToyFinalWiring, toyFinalLayout, Aiur.Plonk.Layout.wireOf,
            Aiur.Plonk.Layout.cellWire, toyFinalW, toyFinalWLin]
        · simp [Gate.Holds, Lower.LGate.inst, mkToyFinalWiring, toyFinalLayout, Aiur.Plonk.Layout.wireOf,
            Aiur.Plonk.Layout.cellWire, toyFinalW, toyFinalWLin]
        · simp [Gate.Holds, Lower.LGate.inst, mkToyFinalWiring, toyFinalLayout, Aiur.Plonk.Layout.wireOf,
            Aiur.Plonk.Layout.cellWire, toyFinalW, toyFinalWLin]
        · have hk18 : k < 18 := by
            have := List.mem_zipIdx hvk
            simp [bn254AffineZeroPairWords, bn254AffineInfinityWords] at this; omega
          have hvEq : bn254AffineZeroPairWords.getD k 0 = v := by
            have := List.mem_zipIdx_iff_getElem?.mp hvk
            simp [List.getD_eq_getElem?_getD, this]
          have hW : toyFinalW lowVal highVal (20 + (2 + k)) = v := by
            simp only [toyFinalW, toyFinalWLin, show ¬ (20 + (2 + k) = 0) by omega,
              show ¬ (20 + (2 + k) = 1) by omega, show ¬ (20 + (2 + k) < 20) by omega,
              show ¬ (20 + (2 + k) = 20) by omega, show ¬ (20 + (2 + k) = 21) by omega,
              show 20 + (2 + k) < 40 by omega, ↓reduceIte, show 20 + (2 + k) - 22 = k by omega,
              hvEq, zero_mul, add_zero]
          have h40 : toyFinalW lowVal highVal 40 = 1 := by simp [toyFinalW, toyFinalWLin]
          have hDiv : (8 * (2 + k)) % 4 = 0 ∧ (8 * (2 + k)) / 8 = 2 + k := ⟨by omega, by omega⟩
          simp [Gate.Holds, Lower.LGate.inst, mkToyFinalWiring, toyFinalLayout, Aiur.Plonk.Layout.wireOf,
            Aiur.Plonk.Layout.cellWire, hDiv.1, hDiv.2, hW, h40]
        · simp [Gate.Holds, Lower.LGate.inst, mkToyFinalWiring, toyFinalLayout, Aiur.Plonk.Layout.wireOf,
            Aiur.Plonk.Layout.cellWire, toyFinalW, toyFinalWLin]
    · -- Row (1, 0) gates: `toyFinalLook1` (43 concrete gates)
      simp only [mkToyFinalCert, toyFinalRowGates] at hrg
      have hAll1 : ((toyFinalLook1.1 ++ toyFinalLook1.2.1).toList.map
          (·.inst (toyFinalLayout.wireOf (1, 0)))).all gateHoldsLinB = true := by decide
      have hMem : rg.inst ((mkToyFinalWiring lowVal highVal).wireOf (1, 0)) ∈
          ((toyFinalLook1.1 ++ toyFinalLook1.2.1).toList.map
            (·.inst (toyFinalLayout.wireOf (1, 0)))) :=
        List.mem_map.mpr ⟨rg, hrg, rfl⟩
      exact gateHolds_of_gateHoldsLinB lowVal highVal _ (List.all_eq_true.mp hAll1 _ hMem)

/-- Symbolic `fp 0 (1 - lowVal)` evaluation on any 22-word tuple starting `[CALL, 0, lowVal, ...]`:
equals `(1 - lowVal) + lowVal = 1 ≠ 0`! -/
private theorem fp_zero_gamma_eq_one (lowVal : BN254Fr) (rest : List BN254Fr)
    (hLen : rest.length = 19) :
    fp 0 (1 - lowVal) ((CALL : BN254Fr) :: (0 : BN254Fr) :: lowVal :: rest) = 1 := by
  unfold fp
  have huLen : ((CALL : BN254Fr) :: (0 : BN254Fr) :: lowVal :: rest).length = 22 := by simp [hLen]
  rw [huLen]
  simp only [List.zipIdx_cons, List.map_cons, List.sum_cons,     show expOf 22 0 = 20 by decide, show expOf 22 1 = 21 by decide, show expOf 22 2 = 0 by decide,
    zero_pow (by decide : 22 ≠ 0), zero_pow (by decide : 20 ≠ 0), zero_pow (by decide : 21 ≠ 0),
    pow_zero, mul_zero, mul_one, add_zero, zero_add]
  have hRest : ((rest.zipIdx 3).map fun p => p.1 * (0 : BN254Fr) ^ expOf 22 p.2).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨⟨v, i⟩, hi, rfl⟩ := List.mem_map.mp hx
    have hmem := List.mem_zipIdx hi
    have hi1 : 3 ≤ i := hmem.1
    have hi2 : i < 22 := by omega
    have hexp : expOf 22 i ≠ 0 := by
      simp only [expOf, show ¬ (22 < 3) by decide, ↓reduceIte]
      omega
    simp [zero_pow hexp]
  rw [hRest]
  ring

/-- Polymorphic Stage 4 (`CompressFinalNarrow`) `PlonkSharedTerminalWitness` for ANY `(lowVal, highVal)`! -/
def mkToyFinalWitness (lowVal highVal : Nat) :
    PlonkSharedTerminalWitness (mkToyFinalSpec lowVal highVal).source [compressFinalNarrowEntry]
      compressFinalNarrowEntry (compressFinalArgs BN254Fr lowVal highVal) :=
  let s := mkToyFinalSpec lowVal highVal
  let hSym := mkToyFinalSpec_sym lowVal highVal
  let hNod := mkToyFinalSpec_nodup lowVal highVal
  { specialized := s.specialized hSym hNod
    compiled := s.compiled hSym hNod
    prepared := s.prepared hSym hNod
    cfg := trivialDepthCfg
    certified := s.certified hSym hNod
    hbits := by decide
    id := fun _ => .ok 0
    plan := s.plan hSym hNod
    activated := s.activated hSym hNod
    entry := by simp
    result := s.resultVal
    wires := s.wires
    output := s.outputWire
    signed := s.signed hSym hNod
    root := s.erasedRootMsg
    rooted := s.rooted hSym hNod
    outside := s.outside
    entryPlain := rfl
    arguments := by
      have h := s.arguments hSym hNod
      simpa [s, mkToyFinalSpec, FlatAssertSpec.args, FlatVal.sourceVal, compressFinalArgs] using h
    decoded := s.decoded hSym hNod
    idOf := fun _ => 0
    idOk := fun _ _ h => (Except.ok.inj h).symm
    names := by simp [circuitNames, FlatAssertSpec.plan]
    units := [((s.erasedChip, none), 1)]
    chipsIn := by intro u hu; simp only [List.mem_singleton] at hu; subst hu; simp [FlatAssertSpec.plan]
    unrolled := by intro u hu; simp only [List.mem_singleton] at hu; subst hu; rfl
    capacity := by simp [WideStage.unitCapRows, Bridge.unitBodies]
    shared := []
    sharedOk := fun _ h => absurd h List.not_mem_nil
    roms := []
    widths := List.nodup_nil
    bound := 100
    romCaps := fun _ h => absurd h List.not_mem_nil
    romWidths := fun _ h => absurd h List.not_mem_nil
    small := Aiur.Tiling.smallCast_zmod bn254FrModulus (by decide)
    tags := by decide
    lookups := by
      simp [WideStage.unitCapLookups, FlatAssertSpec.erasedChip, Erasure.chip, FlatAssertSpec.physChip]
    chanIds := by
      intro x hx y hy _
      have hall : allChips (s.plan hSym hNod) = (s.plan hSym hNod).singles := by
        simp [allChips, FlatAssertSpec.plan]
      rw [hall] at hx hy
      rw [s.chanIds_singleton hSym hNod x hx, s.chanIds_singleton hSym hNod y hy]
    chanBound := fun _ _ => by decide
    enablesOk := by
      intro c hc
      simp only [allChips, FlatAssertSpec.plan, List.flatMap_nil, List.append_nil, List.mem_singleton] at hc
      subst hc
      simp [Bridge.checkEnables, Activation.compile, FlatAssertSpec.erasedChip, Erasure.chip,
        FlatAssertSpec.physChip]
    memWidth := by
      intro c hc m hm
      simp only [allChips, FlatAssertSpec.plan, List.flatMap_nil, List.append_nil, List.mem_singleton] at hc
      subst hc
      simp [FlatAssertSpec.erasedChip, Erasure.chip, FlatAssertSpec.physChip] at hm
    airs := mkToyFinalAirs lowVal highVal
    hairs := by simp [mkToyFinalAirs, WideStage.romAirs, s]
    k := 0
    n := 20
    P := toyPlonkPool
    cert := mkToyFinalCert lowVal highVal
    W := mkToyFinalWiring lowVal highVal
    nWires := 310
    publics := 2
    committed := [0, 1]
    w := toyFinalW lowVal highVal
    pub := [(lowVal : BN254Fr), (highVal : BN254Fr)]
    H := fun _ => 0
    sat := toyFinalEmitScs_sat lowVal highVal
    entryId := rfl
    statement := by
      have hEnc : (Bridge.encode (fun _ => 0) s.erasedRootMsg).drop 2 =
          (lowVal : BN254Fr) :: (highVal : BN254Fr) :: bn254AffineZeroPairWords := by
        rw [s.encode_erasedRootMsg]
        rfl
      rw [hEnc]
      have hLen : (mkToyFinalAirs lowVal highVal).length = 1 := rfl
      rw [hLen]
      apply List.ext_getElem (by simp [bn254AffineZeroPairWords, bn254AffineInfinityWords])
      intro k hk1 hk2
      have hk20 : k < 20 := by simpa using hk1
      simp only [List.getElem_map, List.getElem_range, DepthBridge.PlonkStageWiring.main,
        mkToyFinalWiring, toyFinalLayout, Aiur.Plonk.Layout.cellWire]
      interval_cases k <;> simp [toyFinalW, toyFinalWLin, bn254AffineZeroPairWords, bn254AffineInfinityWords]
    good := by
      have hEnc : Bridge.encode (fun _ => 0) s.erasedRootMsg =
          (CALL : BN254Fr) :: (0 : BN254Fr) :: (lowVal : BN254Fr) :: (highVal : BN254Fr) ::
            bn254AffineZeroPairWords := by
        rw [s.encode_erasedRootMsg]
        rfl
      have hMain0 : ∀ v < 22, (mkToyFinalWiring lowVal highVal).main (toyFinalW lowVal highVal) 0 0 v =
          s.mainTrace 0 0 v := by
        intro v hv
        simp only [DepthBridge.PlonkStageWiring.main, mkToyFinalWiring, toyFinalLayout,
          Aiur.Plonk.Layout.cellWire, FlatAssertSpec.mainTrace, FlatAssertSpec.allConsts,
          FlatAssertSpec.inConsts, s, mkToyFinalSpec, FlatVal.words]
        interval_cases v <;> simp [toyFinalW, toyFinalWLin, bn254AffineZeroPairWords, bn254AffineInfinityWords]
      have hMain1 : (List.range 20).map ((mkToyFinalWiring lowVal highVal).main (toyFinalW lowVal highVal) 1 0) =
          (lowVal : BN254Fr) :: (highVal : BN254Fr) :: bn254AffineZeroPairWords := by
        apply List.ext_getElem (by simp [bn254AffineZeroPairWords, bn254AffineInfinityWords])
        intro k hk1 hk2
        have hk20 : k < 20 := by simpa using hk1
        simp only [List.getElem_map, List.getElem_range, DepthBridge.PlonkStageWiring.main,
          mkToyFinalWiring, toyFinalLayout, Aiur.Plonk.Layout.cellWire]
        interval_cases k <;> simp [toyFinalW, toyFinalWLin, bn254AffineZeroPairWords, bn254AffineInfinityWords]
      have hLook0Tup :
          (((mkToyFinalAirs lowVal highVal).headD (defaultAirF BN254Fr)).circuit.lookups.map fun l =>
            (l.tuple (((mkToyFinalAirs lowVal highVal).headD (defaultAirF BN254Fr)).assign
                ((mkToyFinalWiring lowVal highVal).main (toyFinalW lowVal highVal) 0) 0),
             l.multiplicity.denote (((mkToyFinalAirs lowVal highVal).headD (defaultAirF BN254Fr)).assign
                ((mkToyFinalWiring lowVal highVal).main (toyFinalW lowVal highVal) 0) 0))) =
          [(Bridge.encode (fun _ => 0) s.erasedRootMsg, (-1 : BN254Fr))] := by
        have hAssignEq : ((mkToyFinalAirs lowVal highVal).headD (defaultAirF BN254Fr)).assign
              ((mkToyFinalWiring lowVal highVal).main (toyFinalW lowVal highVal) 0) 0 =
            ((WideStage.unitAirs (fun _ => 0) [((s.erasedChip, none), 1)]).headD (defaultAirF BN254Fr)).assign
              (s.mainTrace 0) 0 := by
          funext v
          unfold WideStage.Air.assign
          have hW : ((mkToyFinalAirs lowVal highVal).headD (defaultAirF BN254Fr)).circuit.width = 22 := by
            simp [mkToyFinalAirs, WideStage.unitAirs, WideStage.unitAir, Bridge.unitCircuit, Bridge.lower,
              FlatAssertSpec.erasedChip, Erasure.chip, FlatAssertSpec.physChip, FlatAssertSpec.numVars,
              FlatAssertSpec.allConsts, FlatAssertSpec.inConsts, mkToyFinalSpec, FlatVal.words,
              bn254AffineZeroPairWords, bn254AffineInfinityWords]
          change (if v < ((mkToyFinalAirs lowVal highVal).headD (defaultAirF BN254Fr)).circuit.width then _ else 0) =
                 (if v < ((mkToyFinalAirs lowVal highVal).headD (defaultAirF BN254Fr)).circuit.width then _ else 0)
          rw [hW]
          by_cases hv : v < 22
          · simp [hv, hMain0 v hv]
          · simp [hv]
        rw [hAssignEq]
        simpa [mkToyFinalAirs, WideStage.unitAirs, WideStage.unitAir, Bridge.unitCircuit, s] using
          s.lower_receive_tuple_mainTrace
      have hLed0 : WideStage.stageLedger (mkToyFinalAllAirs lowVal highVal)
          ((mkToyFinalWiring lowVal highVal).main (toyFinalW lowVal highVal)) = 0 := by
        rw [stageLedger_append, stageLedger_root]
        have hA : WideStage.stageLedger (mkToyFinalAirs lowVal highVal)
            ((mkToyFinalWiring lowVal highVal).main (toyFinalW lowVal highVal)) =
            Finsupp.single (Bridge.encode (fun _ => 0) s.erasedRootMsg) (-1) := by
          simp only [WideStage.stageLedger, mkToyFinalAirs, WideStage.unitAirs, WideStage.unitAir,
            List.map_cons, List.map_nil, List.zipIdx_singleton, List.sum_cons, List.sum_nil, add_zero,
            WideStage.Air.ledger, List.range_one, Tiling.Circuit.rowLedger]
          have hmap : ∀ (ls : List (Tiling.Lookup BN254Fr)) (a : Nat → BN254Fr),
              (ls.map (fun l => l.entry a)).sum =
                ((ls.map fun l => (l.tuple a, l.multiplicity.denote a)).map
                  fun p => Finsupp.single p.1 p.2).sum := by
            intro ls a; simp [Tiling.Lookup.entry, List.map_map, Function.comp_def]
          rw [hmap]
          simp only [mkToyFinalAirs, WideStage.unitAirs, WideStage.unitAir, List.map_cons, List.map_nil,
            List.headD_cons] at hLook0Tup
          rw [hLook0Tup]; simp
        have hLen1 : (mkToyFinalAirs lowVal highVal).length = 1 := rfl
        rw [hA, hLen1, Nat.add_zero, hMain1, ← hEnc, ← Finsupp.single_add]
        simp
      have hγ : toyFinalW lowVal highVal ((mkToyFinalWiring lowVal highVal).poolWire Lower.gammaRef) = 0 := by
        simp [mkToyFinalWiring, toyFinalLayout, Aiur.Plonk.Layout.poolWire, Lower.gammaRef,
          Lower.pool, toyFinalW, toyFinalWLin]
      have hβ : toyFinalW lowVal highVal ((mkToyFinalWiring lowVal highVal).poolWire Lower.betaRef) =
          1 - (lowVal : BN254Fr) := by
        simp [mkToyFinalWiring, toyFinalLayout, Aiur.Plonk.Layout.poolWire, Lower.betaRef,
          Lower.pool, toyFinalW, toyFinalWLin]; ring
      refine ⟨?_, fun _ => hLed0⟩
      rw [hγ, hβ]
      intro u hu
      rcases hu with ⟨x, hx, r, hr, l, hl, rfl⟩
      have hx' : x = ((mkToyFinalAirs lowVal highVal).headD (defaultAirF BN254Fr), 0) ∨
          x = (rootAir 0 20, 1) := by
        simp only [mkToyFinalAirs, WideStage.unitAirs, List.map_cons,
          List.map_nil, List.cons_append, List.nil_append, List.zipIdx_cons, List.zipIdx_nil,
          List.mem_cons, List.not_mem_nil, or_false] at hx
        simpa [mkToyFinalAirs, WideStage.unitAirs] using hx
      rcases hx' with rfl | rfl
      · have hr0 : r = 0 := by
          simp only [mkToyFinalAirs, WideStage.unitAirs, WideStage.unitAir, List.map_cons,
            List.map_nil, List.headD_cons] at hr; omega
        subst hr0
        have hlTup : l.tuple (((mkToyFinalAirs lowVal highVal).headD (defaultAirF BN254Fr)).assign
            ((mkToyFinalWiring lowVal highVal).main (toyFinalW lowVal highVal) 0) 0) =
            Bridge.encode (fun _ => 0) s.erasedRootMsg := by
          let a0 := ((mkToyFinalAirs lowVal highVal).headD (defaultAirF BN254Fr)).assign
            ((mkToyFinalWiring lowVal highVal).main (toyFinalW lowVal highVal) 0) 0
          have hm : (l.tuple a0, l.multiplicity.denote a0) ∈
              ((mkToyFinalAirs lowVal highVal).headD (defaultAirF BN254Fr)).circuit.lookups.map
                (fun l => (l.tuple a0, l.multiplicity.denote a0)) :=
            List.mem_map.mpr ⟨l, hl, rfl⟩
          rw [hLook0Tup, List.mem_singleton] at hm
          exact congrArg Prod.fst hm
        dsimp only
        rw [hlTup, hEnc, fp_zero_gamma_eq_one _ _ rfl]
        exact one_ne_zero
      · have hr0 : r = 0 := by simp [rootAir] at hr; omega
        subst hr0
        simp only [rootAir, List.mem_singleton] at hl
        subst hl
        have htup : (⟨.const 1, .const (CALL : BN254Fr) :: .const 0 :: (List.range 20).map .var⟩ :
            Tiling.Lookup BN254Fr).tuple ((rootAir 0 20).assign
              ((mkToyFinalWiring lowVal highVal).main (toyFinalW lowVal highVal) 1) 0) =
            (CALL : BN254Fr) :: (0 : BN254Fr) :: (lowVal : BN254Fr) :: (highVal : BN254Fr) ::
              bn254AffineZeroPairWords := by
          have ha : ∀ k < 20, (rootAir 0 20).assign
              ((mkToyFinalWiring lowVal highVal).main (toyFinalW lowVal highVal) 1) 0 k =
              (mkToyFinalWiring lowVal highVal).main (toyFinalW lowVal highVal) 1 0 k := by
            intro k hk; simp [WideStage.Air.assign, rootAir, hk]
          simp only [Tiling.Lookup.tuple, Scalar.Circuit.ArithExpr.denote, List.map_cons,
            List.map_map, Function.comp_def, List.cons.injEq, true_and]
          rw [← hMain1]
          apply List.map_congr_left
          intro k hk
          exact ha k (List.mem_range.mp hk)
        dsimp only
        rw [htup, fp_zero_gamma_eq_one _ _ rfl]
        exact one_ne_zero }

/-! ## 8. Polymorphic Outer `ix-aiur-scs-v1` VK, Accepted Witness & Both Consistency Gates -/

def mkToyScs (lowVal highVal : Nat) : Aiur.Plonk.Scs BN254Fr :=
  { mkToyFinalEmitScs lowVal highVal with
    gates := (mkToyFinalEmitScs lowVal highVal).gates ++ toyOutputPinGates }

def mkToyOuterSpec (lowVal highVal : Nat) : AiurScsOuterSpec toyPairing where
  scs := mkToyScs lowVal highVal
  outputWires := List.range' 2 18
  outputWires_len := rfl
  outputWires_in_range := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hx
    simp only [mkToyScs, mkToyFinalEmitScs, DepthBridge.emitCertifiedScs]
    omega
  publics_ge_two := by simp [mkToyScs, mkToyFinalEmitScs, DepthBridge.emitCertifiedScs]
  anchors := toyAnchors
  anchorsBytes := toyAnchorsBytes
  anchorsBytes_len := rfl
  affineCodec := toyAffineCodec

def mkToyVk (lowVal highVal : Nat) (tagByte : UInt8) : AiurScsVerifyingKey toyPairing toySha256 where
  expectedSpec := mkToyOuterSpec lowVal highVal
  scsBytes := aiurScsMagic ++ [tagByte]
  pairingBytes := toyAnchorsBytes
  scsSha256Pin := toySha256 (aiurScsMagic ++ [tagByte])
  pairingSha256Pin := toySha256 toyAnchorsBytes
  scs_pin_ok := rfl
  pairing_pin_ok := rfl

def mkToyAcc (lowVal highVal : Nat) (hLow : lowVal < 2 ^ 128) (hHigh : highVal < 2 ^ 128)
    (tagByte : UInt8) : AiurScsOuterAccepted (mkToyVk lowVal highVal tagByte) lowVal highVal where
  stmtLow_lt := hLow
  stmtHigh_lt := hHigh
  provenScsBytes := aiurScsMagic ++ [tagByte]
  provenPairingBytes := toyAnchorsBytes
  provenScs_pin := rfl
  provenPairing_pin := rfl
  wireAssignment := toyFinalW lowVal highVal
  commitOracle := fun _ => 0
  scsSat := fun _ _ => by
    have hEmit := toyFinalEmitScs_sat lowVal highVal
    dsimp only [mkToyVk, mkToyOuterSpec, mkToyScs]
    refine ⟨hEmit.1, hEmit.2.1, ?_⟩
    intro g hg
    simp only [List.mem_append] at hg
    rcases hg with h1 | h2
    · exact hEmit.2.2 g h1
    · obtain ⟨⟨v, j⟩, hvj, rfl⟩ := List.mem_map.mp h2
      have hj18 : j < 18 := by
        have := List.mem_zipIdx hvj
        simp [bn254AffineZeroPairWords, bn254AffineInfinityWords] at this; omega
      have hvEq : bn254AffineZeroPairWords.getD j 0 = v := by
        have := List.mem_zipIdx_iff_getElem?.mp hvj
        simp [List.getD_eq_getElem?_getD, this]
      have hw : toyFinalW lowVal highVal (2 + j) = v := by
        simp only [toyFinalW, toyFinalWLin, show ¬ (2 + j = 0) by omega, show ¬ (2 + j = 1) by omega,
          show 2 + j < 20 by omega, ↓reduceIte, show 2 + j - 2 = j by omega, hvEq, zero_mul, add_zero]
      simp [Gate.Holds, hw]
  pairingHolds := fun _ _ => by
    dsimp only [mkToyVk, mkToyOuterSpec]
    refine ⟨0, 0, ?_, bn254DeferredVal_zero toyPairing toyAnchors⟩
    have hmap : (List.range' 2 18).map (toyFinalW lowVal highVal) = bn254AffineZeroPairWords := by
      apply List.ext_getElem (by simp [bn254AffineZeroPairWords, bn254AffineInfinityWords])
      intro j hj1 hj2
      have hj18 : j < 18 := by simpa using hj1
      simp only [List.getElem_map, List.getElem_range', Nat.one_mul, toyFinalW, toyFinalWLin,
        show ¬ (2 + j = 0) by omega, show ¬ (2 + j = 1) by omega,
        show 2 + j < 20 by omega, ↓reduceIte, show 2 + j - 2 = j by omega,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj2, Option.getD_some,
        zero_mul, add_zero]
    rw [hmap]
    exact decodeBn254AffinePairWords_zeroPair toyAffineCodec

-- Mode 1: Deployed Two-Layer `StatementPolicy.twoLayerWrap`
def toyTwoVk := mkToyVk toyTwoLimbs.1 toyTwoLimbs.2 0x01
def toyTwoAcc := mkToyAcc toyTwoLimbs.1 toyTwoLimbs.2 toyTwoLimbs_lt.1 toyTwoLimbs_lt.2 0x01

def toyTwoGaps :
    Bn254AiurCompressionTcbGaps toySha256 (toyManifest (aiurScsMagic ++ [0x01]))
      (.twoLayerWrap toyWrapPolicy) toyRootClaimsBytes toyFinalCfg toyFinalHeaders
      toyPairing toyTwoVk toyPackedCodec toyTwoLimbs.1 toyTwoLimbs.2
      toyWrapSpec.source [compressWrapEntry]
      (mkToyGlSpec toyGlWords).source [MultiStark.CompressGL.entry]
      (mkToyNarrowSpec toyPolicyWords toyGlWords).source [compressNarrowFixedEntry]
      (mkToyFinalSpec toyTwoLimbs.1 toyTwoLimbs.2).source [compressFinalNarrowEntry]
      toySem toyBatchClaim toyClaimsBindStmt (0 : ℝ) where
  manifest_pinned := toyManifest_pinned _
  finalCfg_validated := toyFinalCfg_validated
  finalCfg_matches_manifest := ⟨rfl, rfl⟩
  vk_matches_manifest := ⟨rfl, rfl⟩
  policy_matches_manifest := rfl
  public_statement_eq := Prod.mk.eta
  WrapFriAccepted := fun k c =>
    k = toyWrapKeyBytes ∧ c = toyWrapPolicy.claimsBytes toyRootWords
  RootFriAccepted := fun k c =>
    k = toyRootKeyBytes ∧ c = toyRootClaimsBytes
  FinalExecRel := fun low high value₄ _ finalPolicy w₂ prevAcc cur₂ prevAccWords =>
    low = toyTwoLimbs.1 ∧ high = toyTwoLimbs.2 ∧
    value₄ = .tuple (bn254AffineZeroPairWords.map Aiur.Value.field) ∧
    finalPolicy = toyPolicy ∧ w₂ = toyW2 ∧ prevAcc = toyPrevAcc ∧
    cur₂ = toyCur2 ∧ prevAccWords = toyPrevAccWords
  finalExecRel_spec := by
    rintro low high v4 h4 fPol w2 pAcc c2 pWords _ _ _ ⟨_, _, hv4, hfPol, hw2, hpAcc, hc2, hpWords⟩
    rw [hfPol, hw2, hpAcc, hc2, hpWords]
    refine ⟨toyPolicy_wf, rfl, rfl, toyW2_ne_zero, rfl, ?_⟩
    rw [hv4, decodeFinalSourceValue_fieldTuple, toyFold2_eq]
    exact decodeBn254AffinePairWords_zeroPair toyAffineCodec
  NarrowExecRel := fun polWords stmtWords value₃ _ narrowPolicy w₁ cur₁ =>
    polWords = toyPolicyWords ∧ stmtWords = toyGlWords ∧
    value₃ = .tuple (toyPrevAccWords.map Aiur.Value.field) ∧
    narrowPolicy = toyPolicy ∧ w₁ = toyW1 ∧ cur₁ = toyCur1
  narrowExecRel_spec := by
    rintro pW sW v3 h3 nPol w1 c1 _ _ _ ⟨hpW, _, hv3, hnPol, hw1, hc1⟩
    rw [hpW, hnPol, hw1, hc1]
    refine ⟨toyPolicy_wf, rfl, rfl, toyW1_ne_zero, ?_⟩
    rw [hv3, decodeNarrowSourceValue_fieldTuple, toyFold1_eq]
    rfl
  GlExecRel := fun stmtWords _ _ ik ic =>
    stmtWords = toyGlWords ∧ ik = toyWrapKeyBytes ∧ ic = toyWrapPolicy.claimsBytes toyRootWords
  glExecRel_spec := by
    rintro sW v2 h2 ik ic _ _ ⟨hsW, hik, hic⟩
    rw [hsW, hik, hic]
    exact ⟨rfl, ⟨rfl, rfl⟩⟩
  WrapExecRel := fun stmtWords _ _ rk rc =>
    stmtWords = toyRootWords ∧ rk = toyRootKeyBytes ∧ rc = toyRootClaimsBytes
  wrapExecRel_spec := by
    rintro sW v1 h1 rk rc _ _ ⟨hsW, hrk, hrc⟩
    rw [hsW, hrk, hrc]
    exact ⟨rfl, ⟨rfl, rfl⟩⟩
  finalSemantic := by
    intro low high v4 h4 hL hH hEv
    obtain ⟨hLowEq, hHighEq, hv4⟩ := toyFinalSpec_eval_inv toyTwoLimbs_lt.1 toyTwoLimbs_lt.2 hL hH hEv
    exact ⟨toyPolicy, toyW2, toyPrevAcc, toyCur2, toyPrevAccWords,
      hLowEq, hHighEq, hv4, rfl, rfl, rfl, rfl, rfl⟩
  narrowSemantic := by
    intro pW sW v3 h3 hP hS hEv
    obtain ⟨hpW, hsW, hv3⟩ := toyNarrowSpec_eval_inv toyPolicyWords_canon toyGlWords_canon hP hS hEv
    exact ⟨toyPolicy, toyW1, toyCur1, hpW, hsW, hv3, rfl, rfl, rfl⟩
  glSemantic := by
    intro sW v2 h2 hS hEv
    have hs := verifyRootSpec_eval_inv (p := bn254FrModulus) (by decide)
      MultiStark.CompressGL.entry (mkToyGlSpec_sym toyGlWords) toyGlWords_canon hS hEv
    exact ⟨toyWrapKeyBytes, toyWrapPolicy.claimsBytes toyRootWords, hs, rfl, rfl⟩
  wrapSemantic := by
    intro sW v1 h1 hS hEv
    have hs := verifyRootSpec_eval_inv (p := Aiur.Library.U32.Goldilocks.modulus) (by decide)
      compressWrapEntry toyWrapSpec_sym toyRootWords_canon hS hEv
    exact ⟨toyRootKeyBytes, toyRootClaimsBytes, hs, rfl, rfl⟩
  outerToFinalScs := by
    intro w H hSat
    have hPin : ∀ g ∈ toyOutputPinGates, g.Holds w :=
      fun g hg => hSat.2.2 g (List.mem_append_right _ hg)
    have hOut := outputWires_eq_of_pinGates hPin
    refine ⟨mkToyFinalWitness toyTwoLimbs.1 toyTwoLimbs.2, ?_⟩
    dsimp only [mkToyFinalWitness, FlatAssertSpec.resultVal, toyTwoVk, mkToyVk, mkToyOuterSpec]
    rw [hOut]
    rfl
  narrowKzgToTiling := by
    rintro low high v4 h4 fPol w2 pAcc c2 pWords _ _ _ ⟨hLowEq, hHighEq, _, _, _, _, _, hPWEq⟩ _
    rw [hLowEq, hHighEq, hPWEq, toyTwoLimbs_unpack]
    exact ⟨mkToyNarrowWitness toyPolicyWords toyGlWords toyPolicyWords_canon.1 toyGlWords_canon.1, rfl⟩
  glKzgToGroupedWide := by
    rintro sW v3 h3 nPol w1 c1 _ _ ⟨_, hsW, _, _, _, _⟩ _
    rw [hsW]
    exact ⟨mkToyGlWitness toyGlWords⟩
  wrapFriToWideGoldilocks := by
    rintro wk rW hCanon _ ⟨hwk, hc⟩
    have hUnp : rW = toyRootWords :=
      (WrapPolicySpec.claimsBytes_injective hCanon.1 toyRootWords_canon.1 hCanon.2 toyRootWords_canon.2 rfl hc).2
    rw [hUnp]
    exact ⟨toyWrapWitness⟩
  rootFriToAggr := by
    rintro rk _ ⟨_, _⟩
    exact ⟨toyRootStmt, toyAggrTree, [], ⟨rfl, rfl⟩, rfl, fun _ h => absurd h List.not_mem_nil⟩

/-- **Mandatory Non-Vacuity & Constructive Consistency Gate (Two-Layer Deployed Mode):**
Constructively inhabits the ENTIRE hypothesis bundle of `aiur_compression_l3_bn254_sound`
(`AiurScsOuterAccepted` + `Bn254AiurCompressionTcbGaps`) on a non-trivial bilinear pairing
(`e(1, 1) ≠ 1`) with real kernel-compiled stage witnesses for ALL FOUR L3 stages, AND proves
`¬ Bn254AiurEscape` so `aiur_compression_l3_bn254_sound` reaches the main non-escape soundness
branch! -/
theorem bn254AiurCompression_consistent :
    ∃ (sha256 : List UInt8 → List UInt8)
      (manifest : StageManifest)
      (wp : WrapPolicySpec)
      (rootClaimsBytes : List UInt8)
      (finalCfg : _root_.MultiStark.Final.Configuration)
      (finalHeaders : List NarrowClaimHeader)
      (bp : BilinearPairing)
      (vk : AiurScsVerifyingKey bp sha256)
      (packedCodec : Bn254PackedAccCodec bp)
      (stmtLow stmtHigh : Nat)
      (wrapSrc : Generic.Source _root_.MultiStark.F) (wrapEntries : List String)
      (glSrc : Generic.Source BN254Fr) (glEntries : List String)
      (narrowSrc : Generic.Source BN254Fr) (narrowEntries : List String)
      (finalSrc : Generic.Source BN254Fr) (finalEntries : List String)
      (sem : _root_.Aggr.AggrSemantics Address Address Ix.DynamicLink.EvalAssumption Address K
        Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry)
      (batchClaim : Nat → _root_.Aggr.ValidatorMode Address → (Address → Prop) → (Address → Prop) →
        (Address → Prop) → (Ix.DynamicLink.EvalAssumption → Prop) → Prop)
      (claimsBindStmt : List UInt8 →
        _root_.Aggr.AggrNodeStmt Address Address Ix.DynamicLink.EvalAssumption Address K
          Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry → Prop)
      (ε : ℝ)
      (acc : AiurScsOuterAccepted vk stmtLow stmtHigh)
      (gaps : Bn254AiurCompressionTcbGaps sha256 manifest (.twoLayerWrap wp) rootClaimsBytes
        finalCfg finalHeaders bp vk packedCodec stmtLow stmtHigh
        wrapSrc wrapEntries glSrc glEntries narrowSrc narrowEntries finalSrc finalEntries
        sem batchClaim claimsBindStmt ε),
      (∃ P Q, bp.e P Q ≠ 1) ∧ ¬ Bn254AiurEscape acc gaps := by
  refine ⟨toySha256, toyManifest (aiurScsMagic ++ [0x01]), toyWrapPolicy, toyRootClaimsBytes,
    toyFinalCfg, toyFinalHeaders, toyPairing, toyTwoVk, toyPackedCodec,
    toyTwoLimbs.1, toyTwoLimbs.2,
    toyWrapSpec.source, [compressWrapEntry],
    (mkToyGlSpec toyGlWords).source, [MultiStark.CompressGL.entry],
    (mkToyNarrowSpec toyPolicyWords toyGlWords).source, [compressNarrowFixedEntry],
    (mkToyFinalSpec toyTwoLimbs.1 toyTwoLimbs.2).source, [compressFinalNarrowEntry],
    toySem, toyBatchClaim, toyClaimsBindStmt, (0 : ℝ),
    toyTwoAcc, toyTwoGaps, ⟨1, 1, toyPairing_nontrivial⟩, ?_⟩
  refine bn254AiurEscape_false_on_honest toyTwoAcc toyTwoGaps rfl rfl ?_ ?_ ?_
  · rintro v4 h4 fPol w2 pAcc c2 pWords _ ⟨_, _, _, hfPol, _, hpAcc, hc2, _⟩
    rw [hfPol, hpAcc, hc2]
    exact ⟨rfl, Or.inl ⟨toyPrevAcc_passes, toyCur2_passes⟩⟩
  · rintro v3 h3 nPol w1 c1 _ ⟨_, _, _, hnPol, _, _⟩
    rw [hnPol]
    rfl
  · dsimp only
    refine ⟨?_, ?_⟩
    · rintro v2 h2 ik ic _ ⟨_, hik, hic⟩
      rw [hik, hic]
      exact ⟨rfl, rfl⟩
    · rintro v1 h1 rk rc _ ⟨_, hrk, hrc⟩
      rw [hrk, hrc]
      exact ⟨rfl, rfl⟩

-- Mode 2: Single-Layer Fixed-Wrapper Mode (`StatementPolicy.singleLayerDirect`)
def toyOneVk := mkToyVk toyOneLimbs.1 toyOneLimbs.2 0x02
def toyOneAcc := mkToyAcc toyOneLimbs.1 toyOneLimbs.2 toyOneLimbs_lt.1 toyOneLimbs_lt.2 0x02

def toyOneGaps :
    Bn254AiurCompressionTcbGaps toySha256 (toyManifest (aiurScsMagic ++ [0x02]))
      .singleLayerDirect toyRootClaimsBytes toyFinalCfg toyFinalHeaders
      toyPairing toyOneVk toyPackedCodec toyOneLimbs.1 toyOneLimbs.2
      toyWrapSpec.source [compressWrapEntry]
      (mkToyGlSpec toyRootWords).source [MultiStark.CompressGL.entry]
      (mkToyNarrowSpec toyPolicyWords toyRootWords).source [compressNarrowFixedEntry]
      (mkToyFinalSpec toyOneLimbs.1 toyOneLimbs.2).source [compressFinalNarrowEntry]
      toySem toyBatchClaim toyClaimsBindStmt (0 : ℝ) where
  manifest_pinned := toyManifest_pinned _
  finalCfg_validated := toyFinalCfg_validated
  finalCfg_matches_manifest := ⟨rfl, rfl⟩
  vk_matches_manifest := ⟨rfl, rfl⟩
  policy_matches_manifest := trivial
  public_statement_eq := Prod.mk.eta
  WrapFriAccepted := fun _ _ => False
  RootFriAccepted := fun k c =>
    k = toyRootKeyBytes ∧ c = toyRootClaimsBytes
  FinalExecRel := fun low high value₄ _ finalPolicy w₂ prevAcc cur₂ prevAccWords =>
    low = toyOneLimbs.1 ∧ high = toyOneLimbs.2 ∧
    value₄ = .tuple (bn254AffineZeroPairWords.map Aiur.Value.field) ∧
    finalPolicy = toyPolicy ∧ w₂ = toyW2 ∧ prevAcc = toyPrevAcc ∧
    cur₂ = toyCur2 ∧ prevAccWords = toyPrevAccWords
  finalExecRel_spec := by
    rintro low high v4 h4 fPol w2 pAcc c2 pWords _ _ _ ⟨_, _, hv4, hfPol, hw2, hpAcc, hc2, hpWords⟩
    rw [hfPol, hw2, hpAcc, hc2, hpWords]
    refine ⟨toyPolicy_wf, rfl, rfl, toyW2_ne_zero, rfl, ?_⟩
    rw [hv4, decodeFinalSourceValue_fieldTuple, toyFold2_eq]
    exact decodeBn254AffinePairWords_zeroPair toyAffineCodec
  NarrowExecRel := fun polWords stmtWords value₃ _ narrowPolicy w₁ cur₁ =>
    polWords = toyPolicyWords ∧ stmtWords = toyRootWords ∧
    value₃ = .tuple (toyPrevAccWords.map Aiur.Value.field) ∧
    narrowPolicy = toyPolicy ∧ w₁ = toyW1 ∧ cur₁ = toyCur1
  narrowExecRel_spec := by
    rintro pW sW v3 h3 nPol w1 c1 _ _ _ ⟨hpW, _, hv3, hnPol, hw1, hc1⟩
    rw [hpW, hnPol, hw1, hc1]
    refine ⟨toyPolicy_wf, rfl, rfl, toyW1_ne_zero, ?_⟩
    rw [hv3, decodeNarrowSourceValue_fieldTuple, toyFold1_eq]
    rfl
  GlExecRel := fun stmtWords _ _ ik ic =>
    stmtWords = toyRootWords ∧ ik = toyRootKeyBytes ∧ ic = toyRootClaimsBytes
  glExecRel_spec := by
    rintro sW v2 h2 ik ic _ _ ⟨hsW, hik, hic⟩
    rw [hsW, hik, hic]
    exact ⟨rfl, ⟨rfl, rfl⟩⟩
  WrapExecRel := fun _ _ _ _ _ => True
  wrapExecRel_spec := trivial
  finalSemantic := by
    intro low high v4 h4 hL hH hEv
    obtain ⟨hLowEq, hHighEq, hv4⟩ := toyFinalSpec_eval_inv toyOneLimbs_lt.1 toyOneLimbs_lt.2 hL hH hEv
    exact ⟨toyPolicy, toyW2, toyPrevAcc, toyCur2, toyPrevAccWords,
      hLowEq, hHighEq, hv4, rfl, rfl, rfl, rfl, rfl⟩
  narrowSemantic := by
    intro pW sW v3 h3 hP hS hEv
    obtain ⟨hpW, hsW, hv3⟩ := toyNarrowSpec_eval_inv toyPolicyWords_canon toyRootWords_canon hP hS hEv
    exact ⟨toyPolicy, toyW1, toyCur1, hpW, hsW, hv3, rfl, rfl, rfl⟩
  glSemantic := by
    intro sW v2 h2 hS hEv
    have hs := verifyRootSpec_eval_inv (p := bn254FrModulus) (by decide)
      MultiStark.CompressGL.entry (mkToyGlSpec_sym toyRootWords) toyRootWords_canon hS hEv
    exact ⟨toyRootKeyBytes, toyRootClaimsBytes, hs, rfl, rfl⟩
  wrapSemantic := trivial
  outerToFinalScs := by
    intro w H hSat
    have hPin : ∀ g ∈ toyOutputPinGates, g.Holds w :=
      fun g hg => hSat.2.2 g (List.mem_append_right _ hg)
    have hOut := outputWires_eq_of_pinGates hPin
    refine ⟨mkToyFinalWitness toyOneLimbs.1 toyOneLimbs.2, ?_⟩
    dsimp only [mkToyFinalWitness, FlatAssertSpec.resultVal, toyOneVk, mkToyVk, mkToyOuterSpec]
    rw [hOut]
    rfl
  narrowKzgToTiling := by
    rintro low high v4 h4 fPol w2 pAcc c2 pWords _ _ _ ⟨hLowEq, hHighEq, _, _, _, _, _, hPWEq⟩ _
    rw [hLowEq, hHighEq, hPWEq, toyOneLimbs_unpack]
    exact ⟨mkToyNarrowWitness toyPolicyWords toyRootWords toyPolicyWords_canon.1 toyRootWords_canon.1, rfl⟩
  glKzgToGroupedWide := by
    rintro sW v3 h3 nPol w1 c1 _ _ ⟨_, hsW, _, _, _, _⟩ _
    rw [hsW]
    exact ⟨mkToyGlWitness toyRootWords⟩
  wrapFriToWideGoldilocks := trivial
  rootFriToAggr := by
    rintro rk _ ⟨_, _⟩
    exact ⟨toyRootStmt, toyAggrTree, [], ⟨rfl, rfl⟩, rfl, fun _ h => absurd h List.not_mem_nil⟩

/-- **Mandatory Non-Vacuity & Constructive Consistency Gate (Single-Layer Direct Mode):**
Constructively inhabits the entire `StatementPolicy.singleLayerDirect` hypothesis bundle of
`aiur_compression_l3_bn254_sound` on `toyPairing` (`e(1, 1) ≠ 1`) with real kernel-compiled
stage witnesses and proves `¬ Bn254AiurEscape`! -/
theorem bn254AiurCompression_singleLayer_consistent :
    ∃ (sha256 : List UInt8 → List UInt8)
      (manifest : StageManifest)
      (rootClaimsBytes : List UInt8)
      (finalCfg : _root_.MultiStark.Final.Configuration)
      (finalHeaders : List NarrowClaimHeader)
      (bp : BilinearPairing)
      (vk : AiurScsVerifyingKey bp sha256)
      (packedCodec : Bn254PackedAccCodec bp)
      (stmtLow stmtHigh : Nat)
      (wrapSrc : Generic.Source _root_.MultiStark.F) (wrapEntries : List String)
      (glSrc : Generic.Source BN254Fr) (glEntries : List String)
      (narrowSrc : Generic.Source BN254Fr) (narrowEntries : List String)
      (finalSrc : Generic.Source BN254Fr) (finalEntries : List String)
      (sem : _root_.Aggr.AggrSemantics Address Address Ix.DynamicLink.EvalAssumption Address K
        Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry)
      (batchClaim : Nat → _root_.Aggr.ValidatorMode Address → (Address → Prop) → (Address → Prop) →
        (Address → Prop) → (Ix.DynamicLink.EvalAssumption → Prop) → Prop)
      (claimsBindStmt : List UInt8 →
        _root_.Aggr.AggrNodeStmt Address Address Ix.DynamicLink.EvalAssumption Address K
          Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry → Prop)
      (ε : ℝ)
      (acc : AiurScsOuterAccepted vk stmtLow stmtHigh)
      (gaps : Bn254AiurCompressionTcbGaps sha256 manifest .singleLayerDirect rootClaimsBytes
        finalCfg finalHeaders bp vk packedCodec stmtLow stmtHigh
        wrapSrc wrapEntries glSrc glEntries narrowSrc narrowEntries finalSrc finalEntries
        sem batchClaim claimsBindStmt ε),
      (∃ P Q, bp.e P Q ≠ 1) ∧ ¬ Bn254AiurEscape acc gaps := by
  refine ⟨toySha256, toyManifest (aiurScsMagic ++ [0x02]), toyRootClaimsBytes,
    toyFinalCfg, toyFinalHeaders, toyPairing, toyOneVk, toyPackedCodec,
    toyOneLimbs.1, toyOneLimbs.2,
    toyWrapSpec.source, [compressWrapEntry],
    (mkToyGlSpec toyRootWords).source, [MultiStark.CompressGL.entry],
    (mkToyNarrowSpec toyPolicyWords toyRootWords).source, [compressNarrowFixedEntry],
    (mkToyFinalSpec toyOneLimbs.1 toyOneLimbs.2).source, [compressFinalNarrowEntry],
    toySem, toyBatchClaim, toyClaimsBindStmt, (0 : ℝ),
    toyOneAcc, toyOneGaps, ⟨1, 1, toyPairing_nontrivial⟩, ?_⟩
  refine bn254AiurEscape_false_on_honest toyOneAcc toyOneGaps rfl rfl ?_ ?_ ?_
  · rintro v4 h4 fPol w2 pAcc c2 pWords _ ⟨_, _, _, hfPol, _, hpAcc, hc2, _⟩
    rw [hfPol, hpAcc, hc2]
    exact ⟨rfl, Or.inl ⟨toyPrevAcc_passes, toyCur2_passes⟩⟩
  · rintro v3 h3 nPol w1 c1 _ ⟨_, _, _, hnPol, _, _⟩
    rw [hnPol]
    rfl
  · dsimp only
    rintro v2 h2 ik ic _ ⟨_, hik, hic⟩
    rw [hik, hic]
    exact ⟨rfl, rfl⟩

end Ix.Cert.AiurCompression.Consistency
