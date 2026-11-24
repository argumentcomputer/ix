import Ix.Cert.Compression.EndToEnd
import Ix.Cert.Compression.Bls12381.Audit
import Ix.Cert.Compression.StarkShrinkerAudit
import Ix.Cert.MultiStark.Security128Audit
import CertiFriProofs.Audit128

/-! # 128-Bit Proof-Compression Security Audit (`Ix.Cert.Compression.Security128Audit`)

Mechanically pins (via `#guard_msgs` on `#check` and `#print axioms`) the 128-bit
compression endpoint security profile across the three-endpoint architecture:

1. **Endpoint 1 (`stark128Xof48` — Native `Fp^3` `multi-stark` `v6` STARK Shrinker):**
   Transparent pure-ROM 128-bit security (`p^3 ≥ 2^191`, 48-byte BLAKE3 XOF,
   reusing `FriVerifier.friVerifierCircuit_sound` with zero pairing/SRS assumptions).
2. **Endpoint 2 (`bls12381Plonk` — BLS12-381 KZG + EIP-2537 PLONK):**
   Exact IETF/EIP-2537 BLS12-381 parameters (`|Fq| ≥ 2^380`, `|Fr| ≥ 2^254`,
   cofactor `h1 > 1` with **mandatory `G1` prime-order subgroup check**).
3. **Endpoint 3 (`bn254Plonk` — Retained Pre-Pectra BN254):**
   Constructively **rejected** on the 128-bit profile (`|Fq| < 2^255 < 2^380`,
   ~100-bit classical exTNFS security).

Every theorem pinned here depends strictly on standard Lean axioms
(`propext`, `Classical.choice`, `Quot.sound`) — zero `sorry`, zero custom
axioms, zero `native_decide`, zero `bv_decide`.
-/

namespace Ix.Cert.Compression.Security128

open Ix.Cert.Compression
open Ix.Cert.Compression.Foreign
open Ix.Cert.Compression.NativeField
open Ix.Cert.MultiStark.Security128

/-! ## 1. BLS12-381 Curve Constants & Pairing-Curve 128-Bit Floor -/

/-- Absolute value of the BLS12-381 Barreto–Lynn–Scott seed `|u| = 0xd201000000010000`
(`u = -0xd201000000010000`). -/
def bls12381SeedAbs : Nat := 0xd201000000010000

/-- BLS12-381 scalar field prime modulus `r = u^4 - u^2 + 1` (255 bits). -/
def bls12381FrModulus : Nat :=
  0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

/-- BLS12-381 base field prime modulus `q = (u - 1)^2 · r / 3 + u` (381 bits). -/
def bls12381FqModulus : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

/-- BLS12-381 `G1` cofactor `h1 = (u - 1)^2 / 3` (non-trivial: requires prime-order subgroup check). -/
def bls12381G1Cofactor : Nat :=
  0x396c8c005555e1568c00aaab0000aaab

/-- Algebraic certification of the BLS12-381 constants from the BLS seed `u = -bls12381SeedAbs`:
`r + |u|^2 = |u|^4 + 1`, `3 · h1 = (|u| + 1)^2`, and `q + |u| = h1 · r`. -/
theorem bls12381_curve_identities :
    bls12381FrModulus + bls12381SeedAbs ^ 2 = bls12381SeedAbs ^ 4 + 1 ∧
    3 * bls12381G1Cofactor = (bls12381SeedAbs + 1) ^ 2 ∧
    bls12381FqModulus + bls12381SeedAbs = bls12381G1Cofactor * bls12381FrModulus := by
  unfold bls12381FrModulus bls12381FqModulus bls12381G1Cofactor bls12381SeedAbs
  norm_num

/-- Minimum pairing base-field bit floor against exTNFS (`|Fq| ≥ 2^380`), scalar-field
Pollard-`ρ` floor (`|Fr| ≥ 2^254`), and mandatory `G1` subgroup membership check
whenever the curve has non-trivial cofactor `h1 > 1`. -/
structure PairingCurveSpec where
  fqModulus : Nat
  frModulus : Nat
  g1Cofactor : Nat
  enforcesG1SubgroupCheck : Bool
  deriving DecidableEq, Repr

/-- 128-bit pairing-curve security envelope predicate. -/
def PairingCurve128Ok (c : PairingCurveSpec) : Prop :=
  2 ^ 380 ≤ c.fqModulus ∧
  2 ^ 254 ≤ c.frModulus ∧
  (1 < c.g1Cofactor → c.enforcesG1SubgroupCheck = true)

/-- BLS12-381 curve specification with mandatory `G1` prime-order subgroup check enabled. -/
def bls12381CurveSpec : PairingCurveSpec :=
  { fqModulus := bls12381FqModulus
    frModulus := bls12381FrModulus
    g1Cofactor := bls12381G1Cofactor
    enforcesG1SubgroupCheck := true }

/-- Misconfigured BLS12-381 curve specification omitting the mandatory `G1` subgroup check. -/
def bls12381UncheckedSpec : PairingCurveSpec :=
  { fqModulus := bls12381FqModulus
    frModulus := bls12381FrModulus
    g1Cofactor := bls12381G1Cofactor
    enforcesG1SubgroupCheck := false }

/-- Legacy BN254 curve specification (`NativeField.bn254FqModulus`, `Foreign.bn254FrModulus`). -/
def bn254CurveSpec : PairingCurveSpec :=
  { fqModulus := bn254FqModulus
    frModulus := bn254FrModulus
    g1Cofactor := 1
    enforcesG1SubgroupCheck := true }

/-- Compression endpoints in the three-endpoint architecture. -/
inductive CompressionEndpoint where
  | stark128Xof48
  | bls12381Plonk
  | bn254Plonk
  deriving DecidableEq, Repr

/-- 128-bit compression profile predicate across endpoints. -/
def CompressionProfile128Ok : CompressionEndpoint → Prop
  | .stark128Xof48 => Security128Profile 3 6 48 v6Ud160Params true
  | .bls12381Plonk => PairingCurve128Ok bls12381CurveSpec
  | .bn254Plonk => PairingCurve128Ok bn254CurveSpec

/-! ## 2. Positive 128-Bit Compression Theorems -/

/-- BLS12-381 clears the 380-bit exTNFS base-field floor (`2^380 ≤ q`), the 254-bit
scalar-field floor (`2^254 ≤ r`), and has non-trivial `G1` cofactor `h1 > 1`. -/
theorem bls12381_field_bounds :
    2 ^ 380 ≤ bls12381FqModulus ∧
    2 ^ 254 ≤ bls12381FrModulus ∧
    1 < bls12381G1Cofactor := by
  refine ⟨?_, ?_, ?_⟩
  · have h380 : (2 : ℕ) ^ 380 = (2 : ℕ) ^ 190 * (2 : ℕ) ^ 190 := by rw [← pow_add]
    have h190 : (2 : ℕ) ^ 190 = 1569275433846670190958947355801916604025588861116008628224 := by
      norm_num
    rw [h380, h190]
    unfold bls12381FqModulus
    norm_num
  · unfold bls12381FrModulus
    norm_num
  · unfold bls12381G1Cofactor
    norm_num

/-- Endpoint 1 (`stark128Xof48`) satisfies the 128-bit compression profile. -/
theorem stark128Xof48_profile_ok :
    CompressionProfile128Ok .stark128Xof48 :=
  v6_positive_128_profiles.1

/-- Endpoint 2 (`bls12381Plonk`) satisfies the 128-bit compression profile. -/
theorem bls12381Plonk_profile_ok :
    CompressionProfile128Ok .bls12381Plonk := by
  obtain ⟨hfq, hfr, _⟩ := bls12381_field_bounds
  exact ⟨hfq, hfr, fun _ => rfl⟩

/-! ## 3. Constructive Negative Controls (Rejecting BN254 & Unchecked Cofactor) -/

/-- Negative control 1: BN254's base field prime `bn254FqModulus` is strictly below `2^255`
and strictly below the `2^380` exTNFS base-field floor (~100-bit classical security). -/
theorem negControl_bn254_fq_below_380 :
    bn254FqModulus < 2 ^ 255 ∧ bn254FqModulus < 2 ^ 380 := by
  have h255 : bn254FqModulus < 2 ^ 255 := by
    unfold bn254FqModulus
    norm_num
  have hpow : (2 : ℕ) ^ 255 ≤ (2 : ℕ) ^ 380 := by
    have hstep : ∀ (a n m : ℕ), 0 < a → n ≤ m → a ^ n ≤ a ^ m :=
      fun _ _ _ ha hnm => Nat.pow_le_pow_right ha hnm
    exact hstep 2 255 380 (by decide) (by decide)
  exact ⟨h255, lt_of_lt_of_le h255 hpow⟩

/-- Negative control 2: BN254 (`bn254Plonk`) is constructively REJECTED on the 128-bit
compression profile (`¬ CompressionProfile128Ok .bn254Plonk`). -/
theorem negControl_bn254_rejected_128 :
    ¬ CompressionProfile128Ok .bn254Plonk := by
  intro h
  exact not_le_of_gt negControl_bn254_fq_below_380.2 h.1

/-- Negative control 3: BLS12-381 WITHOUT the mandatory `G1` prime-order subgroup check
is constructively REJECTED by `PairingCurve128Ok` because `h1 > 1`. -/
theorem negControl_bls12381_missing_subgroup_check_rejected :
    ¬ PairingCurve128Ok bls12381UncheckedSpec := by
  intro h
  have hsub := h.2.2 bls12381_field_bounds.2.2
  exact Bool.false_ne_true hsub

end Ix.Cert.Compression.Security128

/-! ## 4. Mechanical `#guard_msgs` Statement & Axiom Pins -/

/-- info: Ix.Cert.Compression.Security128.bls12381_curve_identities : Ix.Cert.Compression.Security128.bls12381FrModulus + Ix.Cert.Compression.Security128.bls12381SeedAbs ^ 2 = Ix.Cert.Compression.Security128.bls12381SeedAbs ^ 4 + 1 ∧ 3 * Ix.Cert.Compression.Security128.bls12381G1Cofactor = (Ix.Cert.Compression.Security128.bls12381SeedAbs + 1) ^ 2 ∧ Ix.Cert.Compression.Security128.bls12381FqModulus + Ix.Cert.Compression.Security128.bls12381SeedAbs = Ix.Cert.Compression.Security128.bls12381G1Cofactor * Ix.Cert.Compression.Security128.bls12381FrModulus -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Security128.bls12381_curve_identities

/-- info: Ix.Cert.Compression.Security128.bls12381_field_bounds : 2 ^ 380 ≤ Ix.Cert.Compression.Security128.bls12381FqModulus ∧ 2 ^ 254 ≤ Ix.Cert.Compression.Security128.bls12381FrModulus ∧ 1 < Ix.Cert.Compression.Security128.bls12381G1Cofactor -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Security128.bls12381_field_bounds

/-- info: Ix.Cert.Compression.Security128.stark128Xof48_profile_ok : Ix.Cert.Compression.Security128.CompressionProfile128Ok Ix.Cert.Compression.Security128.CompressionEndpoint.stark128Xof48 -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Security128.stark128Xof48_profile_ok

/-- info: Ix.Cert.Compression.Security128.bls12381Plonk_profile_ok : Ix.Cert.Compression.Security128.CompressionProfile128Ok Ix.Cert.Compression.Security128.CompressionEndpoint.bls12381Plonk -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Security128.bls12381Plonk_profile_ok

/-- info: Ix.Cert.Compression.Security128.negControl_bn254_fq_below_380 : Ix.Cert.Compression.NativeField.bn254FqModulus < 2 ^ 255 ∧ Ix.Cert.Compression.NativeField.bn254FqModulus < 2 ^ 380 -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Security128.negControl_bn254_fq_below_380

/-- info: Ix.Cert.Compression.Security128.negControl_bn254_rejected_128 : ¬Ix.Cert.Compression.Security128.CompressionProfile128Ok Ix.Cert.Compression.Security128.CompressionEndpoint.bn254Plonk -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Security128.negControl_bn254_rejected_128

/-- info: Ix.Cert.Compression.Security128.negControl_bls12381_missing_subgroup_check_rejected : ¬Ix.Cert.Compression.Security128.PairingCurve128Ok Ix.Cert.Compression.Security128.bls12381UncheckedSpec -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Security128.negControl_bls12381_missing_subgroup_check_rejected

/-- info: 'Ix.Cert.Compression.Security128.bls12381_curve_identities' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Security128.bls12381_curve_identities

/-- info: 'Ix.Cert.Compression.Security128.bls12381_field_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Security128.bls12381_field_bounds

/-- info: 'Ix.Cert.Compression.Security128.stark128Xof48_profile_ok' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Security128.stark128Xof48_profile_ok

/-- info: 'Ix.Cert.Compression.Security128.bls12381Plonk_profile_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Security128.bls12381Plonk_profile_ok

/-- info: 'Ix.Cert.Compression.Security128.negControl_bn254_fq_below_380' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Security128.negControl_bn254_fq_below_380

/-- info: 'Ix.Cert.Compression.Security128.negControl_bn254_rejected_128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Security128.negControl_bn254_rejected_128

/-- info: 'Ix.Cert.Compression.Security128.negControl_bls12381_missing_subgroup_check_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Security128.negControl_bls12381_missing_subgroup_check_rejected

/-- info: 'Ix.Cert.Compression.FriVerifier.friVerifierCircuit_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.FriVerifier.friVerifierCircuit_sound

/-- info: 'Ix.Cert.Compression.OuterRelation.gnark_folded_pairing_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.OuterRelation.gnark_folded_pairing_sound

/-! ## 5. Direct Wiring to Native STARK Shrinker (`v6` / `v6-zk`), BLS12-381 Pipeline & Unconditional `CertiFRI` -/

/-- info: @Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_endoSubgroupCheck_sound : ∀ {P : Ix.Cert.Compression.Bls12381.CurveMsm.bls12381Curve.Point}, Ix.Cert.Compression.Bls12381.CurveMsm.EndoSubgroupChecked P → Ix.Cert.Compression.Bls12381.CurveMsm.InPrimeSubgroup P -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_endoSubgroupCheck_sound

/-- info: Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_torsionPoint_not_inPrimeSubgroup : ¬Ix.Cert.Compression.Bls12381.CurveMsm.InPrimeSubgroup Ix.Cert.Compression.Bls12381.CurveMsm.bls12381TorsionPoint -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_torsionPoint_not_inPrimeSubgroup

/-- info: 'Ix.Cert.Compression.StarkShrinker.starkShrinker_v6_sound_128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinker.starkShrinker_v6_sound_128

/-- info: 'Ix.Cert.Compression.StarkShrinker.starkShrinker_v6_concrete_prob_128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinker.starkShrinker_v6_concrete_prob_128

/-- info: 'Ix.Cert.Compression.StarkShrinkerZk.starkShrinker_v6zk_sound_128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.StarkShrinkerZk.starkShrinker_v6zk_sound_128

/-- info: 'Ix.Cert.Compression.Bls12381.EndToEnd.bls12381_compression_pipeline_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.EndToEnd.bls12381_compression_pipeline_sound

/-- info: 'Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_endoSubgroupCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_endoSubgroupCheck_sound

/-- info: 'Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_torsionPoint_not_inPrimeSubgroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.CurveMsm.bls12381_torsionPoint_not_inPrimeSubgroup

/-- info: 'Ix.Cert.Compression.Bls12381.OuterRelation.bls12381_gnark_folded_pairing_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Compression.Bls12381.OuterRelation.bls12381_gnark_folded_pairing_sound

/-- info: 'CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_xof48_johnson_lb3_78_128_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_xof48_johnson_lb3_78_128_unconditional

/-- info: 'CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_xof48_johnson_lb4_58_128_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_xof48_johnson_lb4_58_128_unconditional

/-- info: 'CertiFri.P3.Exec.goldilocksExt3_v6Zk_soundness_xof48_johnson_128_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.goldilocksExt3_v6Zk_soundness_xof48_johnson_128_unconditional
