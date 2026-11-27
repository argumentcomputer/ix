import Ix.Cert.Compression.Plonkish
import Ix.Cert.Compression.Foreign
import Ix.Cert.Compression.NativeCurveMsm
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots

/-! # Certified Recursive KZG / SHPlonk Verifier & Concrete `BN254::G1` Soundness

Formalizes the BN254 KZG recursive verifier (`crates/proof-compression/src/recursive/native_verifier.rs`
and `crates/proof-compression/src/kzg/pcs.rs`) over `PlonkishM Foreign.BN254Fr` and the
concrete Mathlib-backed elliptic curve group `NativeCurveMsm.bn254G1`:

1. **Concrete KZG Algebraic & Batched Opening Soundness:**
   - `kzg_single_eval_of_poly_eq`: polynomial divisibility `f - C y = (X - C z) * q` implies
     `f.eval z = y`.
   - `kzg_batched_horner_bad_card`: if any committed polynomial `f_i` disagrees with its
     claimed opening `y_i` at `z`, at most `m - 1` batching challenges `γ ∈ BN254Fr` make
     the Horner batch `∑ γ^{m-1-i} (f_i(z) - y_i)` vanish (exact Schwartz–Zippel bound).
   - `kzg_pairing_sound_at_bn254G1`: for a single committed polynomial, the concrete
     `bn254G1` pairing relation `L = [τ] R` with `L = commit τ F + [z] (commit τ Q)` and
     `R = commit τ Q` implies `(F - (X - C z) * Q).eval τ = 0`, with `[r] G = O` an explicit
     hypothesis (a standalone lemma, not yet wired into `EndToEnd.lean`).
2. **Concrete `bn254G1` Pairing-Operand MSM Soundness: not proved.** No theorem instantiates
   `NativeCurveMsm.msm_sound` at `NativeCurveMsm.bn254G1`; only the BLS12-381 analogue
   `bls12381_pairing_msm_sound` (`Bls12381/RecursiveKzg.lean`) exists.
3. **5-Channel Recursive KZG Verifier Circuit (`buildRecursiveKzgCircuit`, `FiveChannelSatisfied`,
   `recursiveKzgCircuit_sound`):**
   Built directly in `PlonkishM BN254Fr` over an arbitrary `base` circuit; the first and
   last items below live on `base` and are not constrained by `buildRecursiveKzgCircuit`
   (see `FiveChannelLayout`), and no theorem here mentions the Rust circuit:
   - Public statement & deferred pairing-operand binding,
   - BLAKE3 transcript channel calls (`PlonkishM.blake3Call`),
   - Horner OOD batching & quotient identity `quotient * vanishing = oodCombination` in `BN254Fr`,
   - Linear MSM scalar accumulator consistency feeding `bn254G1` pairing operands `(L, R)`.

Zero `sorry`, zero `native_decide`, standard axioms only.
-/

namespace Ix.Cert.Compression.RecursiveKzg

open Ix.Cert.Compression.Plonkish
open Ix.Cert.Compression.Foreign
open Ix.Cert.Compression.NativeField
open Ix.Cert.Compression.NativeCurveMsm
open Polynomial

/-! ## 1. Algebraic & Batched KZG Opening Soundness over `BN254Fr` -/

/-- Exact single-opening KZG polynomial soundness: if `f - C y = (X - C z) * q` in `BN254Fr[X]`,
then `f.eval z = y`. -/
theorem kzg_single_eval_of_poly_eq {f q : BN254Fr[X]} {z y : BN254Fr}
    (h : f - C y = (X - C z) * q) : f.eval z = y := by
  have hev := congrArg (fun p : BN254Fr[X] => p.eval z) h
  simp only [eval_sub, eval_C, eval_mul, eval_X, sub_self, zero_mul] at hev
  exact sub_eq_zero.mp hev

/-- Horner linear combination of scalars `cs` at challenge `γ : BN254Fr`. -/
def hornerFr (γ : BN254Fr) (cs : List BN254Fr) : BN254Fr :=
  cs.foldl (fun acc x => acc * γ + x) 0

/-- Polynomial in `γ` representing `hornerFr γ cs`. -/
noncomputable def hornerFrPoly (cs : List BN254Fr) : BN254Fr[X] :=
  cs.foldl (fun acc x => acc * X + C x) 0

theorem eval_hornerFrPoly (γ : BN254Fr) (cs : List BN254Fr) :
    (hornerFrPoly cs).eval γ = hornerFr γ cs := by
  have hgen : ∀ (l : List BN254Fr) (p : BN254Fr[X]),
      (l.foldl (fun acc x => acc * X + C x) p).eval γ =
        l.foldl (fun acc x => acc * γ + x) (p.eval γ) := by
    intro l
    induction l with
    | nil => intro p; rfl
    | cons c cs ih =>
      intro p
      simp only [List.foldl_cons, ih, eval_add, eval_mul, eval_X, eval_C]
  simpa [hornerFrPoly, hornerFr] using hgen cs 0

theorem natDegree_hornerFrPoly_le (cs : List BN254Fr) :
    (hornerFrPoly cs).natDegree ≤ cs.length - 1 := by
  have hgen : ∀ (l : List BN254Fr) (p : BN254Fr[X]),
      (l.foldl (fun acc x => acc * X + C x) p).natDegree ≤
        if l = [] then p.natDegree else max (p.natDegree + l.length) (l.length - 1) := by
    intro l
    induction l with
    | nil => intro p; simp
    | cons c cs ih =>
      intro p
      simp only [List.foldl_cons, List.cons_ne_nil, ↓reduceIte, List.length_cons, Nat.add_sub_cancel]
      have hstep := ih (p * X + C c)
      have hdeg1 : (p * X + C c).natDegree ≤ p.natDegree + 1 := by
        refine (natDegree_add_le _ _).trans (max_le ?_ (by simp))
        exact (natDegree_mul_le).trans (by simp)
      cases cs with
      | nil =>
        simp only [↓reduceIte] at hstep
        exact hstep.trans (hdeg1.trans (le_max_left _ _))
      | cons d ds =>
        simp only [List.cons_ne_nil, ↓reduceIte, List.length_cons, Nat.add_sub_cancel] at hstep
        refine hstep.trans (max_le ?_ ?_)
        · exact le_trans (by omega : (p * X + C c).natDegree + (ds.length + 1) ≤
            p.natDegree + (ds.length + 1 + 1)) (le_max_left _ _)
        · exact le_trans (by omega : ds.length ≤ ds.length + 1) (le_max_right _ _)
  cases cs with
  | nil => simp [hornerFrPoly]
  | cons c cs =>
    have h1 := hgen cs (C c)
    unfold hornerFrPoly
    simp only [List.foldl_cons, zero_mul, zero_add]
    cases cs with
    | nil => simp
    | cons d ds =>
      simp only [List.cons_ne_nil, ↓reduceIte, natDegree_C, zero_add, List.length_cons,
        Nat.add_sub_cancel] at h1
      simpa using h1

theorem hornerFrPoly_ne_zero_of_exists {cs : List BN254Fr} (h : ∃ c ∈ cs, c ≠ 0) :
    hornerFrPoly cs ≠ 0 := by
  have hcoeff : ∀ (l : List BN254Fr) (p : BN254Fr[X]) (k : ℕ) (hk : k < l.length),
      (l.foldl (fun acc x => acc * X + C x) p).coeff k = l[l.length - 1 - k]'(by omega) := by
    intro l
    induction l using List.reverseRecOn with
    | nil => intro _ _ hk; simp at hk
    | append_singleton l a ih =>
      intro p k hk
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      cases k with
      | zero => simp [List.length_append]
      | succ k =>
        rw [coeff_add, coeff_mul_X, coeff_C_succ, add_zero]
        have hk' : k < l.length := by simp at hk; omega
        rw [ih p k hk']
        have hidx : (l ++ [a]).length - 1 - (k + 1) = l.length - 1 - k := by simp; omega
        simp only [hidx, List.getElem_append_left (by omega : l.length - 1 - k < l.length)]
  obtain ⟨c, hc_mem, hc_ne⟩ := h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc_mem
  intro h0
  have hci := congrArg (fun p : BN254Fr[X] => p.coeff (cs.length - 1 - i)) h0
  rw [coeff_zero, hornerFrPoly, hcoeff cs 0 (cs.length - 1 - i) (by omega)] at hci
  have hidx : cs.length - 1 - (cs.length - 1 - i) = i := by omega
  simp only [hidx] at hci
  exact hc_ne hci

/-- **Batched KZG Opening Soundness (Schwartz–Zippel over `BN254Fr`):**
For any list of committed polynomials `fs` and claimed evaluations `ys` at point `z`,
if `∃ i, (fs[i]).eval z ≠ ys[i]`, then at most `fs.length - 1` challenges `γ ∈ BN254Fr`
satisfy `hornerFr γ (zipWith (fun f y => f.eval z - y) fs ys) = 0`. -/
theorem kzg_batched_horner_bad_card {fs : List (BN254Fr[X])} {ys : List BN254Fr}
    (z : BN254Fr) (hlen : fs.length = ys.length)
    (hmis : ∃ i, ∃ hi : i < fs.length, fs[i].eval z ≠ ys[i]'(hlen ▸ hi)) :
    (Finset.univ.filter fun γ : BN254Fr =>
      hornerFr γ (List.zipWith (fun f y => f.eval z - y) fs ys) = 0).card ≤
      fs.length - 1 := by
  set diffs := List.zipWith (fun f y => f.eval z - y) fs ys
  have hdiffs_len : diffs.length = fs.length := by simp [diffs, hlen]
  have hex : ∃ c ∈ diffs, c ≠ 0 := by
    obtain ⟨i, hi, hne⟩ := hmis
    refine ⟨diffs[i]'(by omega), List.getElem_mem (by omega), ?_⟩
    simp only [diffs, List.getElem_zipWith]
    exact sub_ne_zero.mpr hne
  set P := hornerFrPoly diffs
  have hPne : P ≠ 0 := hornerFrPoly_ne_zero_of_exists hex
  have hsub : (Finset.univ.filter fun γ : BN254Fr => hornerFr γ diffs = 0) ⊆ P.roots.toFinset := by
    intro γ hγ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ
    rw [Multiset.mem_toFinset, mem_roots hPne, IsRoot.def, eval_hornerFrPoly, hγ]
  exact (Finset.card_le_card hsub).trans
    ((Multiset.toFinset_card_le _).trans
      ((Polynomial.card_roots' P).trans
        (by rw [← hdiffs_len]; exact natDegree_hornerFrPoly_le diffs)))

/-- The concrete BN254 generator `bn254G1.generator = (1, 2)` is not the point at infinity. -/
theorem bn254G1_generator_ne_zero : bn254G1.generator ≠ bn254G1.zero := by
  change bn254Generator ≠ 0
  unfold bn254Generator
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

/-- If `[r] G = O` for `r = bn254FrModulus`, scalar multiplication on `bn254G1.generator`
depends only on the scalar modulo `r`. -/
theorem bn254G1_smul_mod_r
    (horder : bn254G1.smul bn254FrModulus bn254G1.generator = bn254G1.zero) (k : Nat) :
    bn254G1.smul (k % bn254FrModulus) bn254G1.generator =
      bn254G1.smul k bn254G1.generator := by
  have hdiv : bn254FrModulus * (k / bn254FrModulus) + k % bn254FrModulus = k :=
    Nat.div_add_mod k bn254FrModulus
  conv_rhs => rw [← hdiv]
  rw [bn254G1.smul_add, Nat.mul_comm, ← bn254G1.smul_smul, horder,
    bn254G1.smul_zero_point, bn254G1.zero_add]

/-- Derived `BN254Fr` additive homomorphism law for `bn254G1.generator` from `[r] G = O`. -/
theorem bn254G1_smul_add_fr
    (horder : bn254G1.smul bn254FrModulus bn254G1.generator = bn254G1.zero)
    (a b : BN254Fr) :
    bn254G1.add (bn254G1.smul a.val bn254G1.generator)
        (bn254G1.smul b.val bn254G1.generator) =
      bn254G1.smul (a + b).val bn254G1.generator := by
  rw [← bn254G1.smul_add]
  dsimp only [BN254Fr.val]
  rw [ZMod.val_add, bn254G1_smul_mod_r horder]

/-- Derived `BN254Fr` multiplicative law for `bn254G1.generator` from `[r] G = O`. -/
theorem bn254G1_smul_mul_fr
    (horder : bn254G1.smul bn254FrModulus bn254G1.generator = bn254G1.zero)
    (a b : BN254Fr) :
    bn254G1.smul a.val (bn254G1.smul b.val bn254G1.generator) =
      bn254G1.smul (a * b).val bn254G1.generator := by
  rw [bn254G1.smul_smul]
  dsimp only [BN254Fr.val]
  rw [ZMod.val_mul, bn254G1_smul_mod_r horder]

/-- Derived exact prime-order injectivity of `a ↦ [a] G` on `BN254Fr` from `[r] G = O`,
`bn254FrModulus_prime` (prime `r`), and `bn254G1_generator_ne_zero` (`G = (1, 2) ≠ O`). -/
theorem bn254G1_smul_inj_fr
    (horder : bn254G1.smul bn254FrModulus bn254G1.generator = bn254G1.zero)
    {a b : BN254Fr}
    (heq : bn254G1.smul a.val bn254G1.generator = bn254G1.smul b.val bn254G1.generator) :
    a = b := by
  by_contra hne
  have hdiff_ne : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hneg : bn254G1.smul (-b).val bn254G1.generator =
      bn254G1.neg (bn254G1.smul b.val bn254G1.generator) := by
    have h0 : bn254G1.add (bn254G1.smul b.val bn254G1.generator)
        (bn254G1.smul (-b).val bn254G1.generator) = bn254G1.zero := by
      rw [bn254G1_smul_add_fr horder, add_neg_cancel]
      dsimp only [BN254Fr.val]
      rw [ZMod.val_zero, bn254G1.smul_zero]
    calc bn254G1.smul (-b).val bn254G1.generator
        = bn254G1.add bn254G1.zero (bn254G1.smul (-b).val bn254G1.generator) :=
            (bn254G1.zero_add _).symm
      _ = bn254G1.add (bn254G1.add (bn254G1.neg (bn254G1.smul b.val bn254G1.generator))
            (bn254G1.smul b.val bn254G1.generator))
            (bn254G1.smul (-b).val bn254G1.generator) := by
            rw [bn254G1.neg_add_cancel]
      _ = bn254G1.add (bn254G1.neg (bn254G1.smul b.val bn254G1.generator))
            (bn254G1.add (bn254G1.smul b.val bn254G1.generator)
              (bn254G1.smul (-b).val bn254G1.generator)) := bn254G1.add_assoc _ _ _
      _ = bn254G1.neg (bn254G1.smul b.val bn254G1.generator) := by
            rw [h0, bn254G1.add_zero]
  have hzero : bn254G1.smul (a - b).val bn254G1.generator = bn254G1.zero := by
    rw [sub_eq_add_neg, ← bn254G1_smul_add_fr horder, heq, hneg, bn254G1.add_neg_cancel]
  have h1 : bn254G1.smul ((a - b)⁻¹ * (a - b)).val bn254G1.generator = bn254G1.zero := by
    rw [← bn254G1_smul_mul_fr horder, hzero, bn254G1.smul_zero_point]
  rw [inv_mul_cancel₀ hdiff_ne] at h1
  dsimp only [BN254Fr.val] at h1
  have : Fact (1 < bn254FrModulus) := ⟨bn254FrModulus_prime.one_lt⟩
  rw [ZMod.val_one, bn254G1.smul_one] at h1
  exact bn254G1_generator_ne_zero h1

/-- **KZG Pairing Equation → Batched Polynomial Identity (Concrete `BN254::G1`):**
Let `commit (τ : BN254Fr) (f : BN254Fr[X]) := bn254G1.smul (f.eval τ).val bn254G1.generator`
denote the KZG commitment to `f` under secret SRS trapdoor `τ`.
Assuming the single curve-order fact `horder : [r] G = O` for `G = bn254G1.generator = (1, 2)`
(from which prime-order injectivity, additive homomorphism, and multiplicative laws are derived
above using `bn254FrModulus_prime` and `bn254G1_generator_ne_zero`), the pairing relation
`L = [τ] R` for `L = commit τ F + [z] (commit τ Q)` and `R = commit τ Q` implies
`(F - (X - C z) * Q).eval τ = 0`.

Note: this is a standalone algebraic KZG pairing lemma (not yet wired into `EndToEnd.lean`,
and `[r] G = O` on `bn254Curve.Point` remains an explicit hypothesis rather than a curve
point-counting proof). -/
theorem kzg_pairing_sound_at_bn254G1
    (τ z : BN254Fr) (F Q : BN254Fr[X])
    (horder : bn254G1.smul bn254FrModulus bn254G1.generator = bn254G1.zero)
    (hpair :
      bn254G1.add
        (bn254G1.smul (F.eval τ).val bn254G1.generator)
        (bn254G1.smul z.val (bn254G1.smul (Q.eval τ).val bn254G1.generator)) =
      bn254G1.smul τ.val (bn254G1.smul (Q.eval τ).val bn254G1.generator)) :
    (F - (X - C z) * Q).eval τ = 0 := by
  rw [bn254G1_smul_mul_fr horder, bn254G1_smul_mul_fr horder,
    bn254G1_smul_add_fr horder] at hpair
  have hsc : F.eval τ + z * Q.eval τ = τ * Q.eval τ := bn254G1_smul_inj_fr horder hpair
  simp only [eval_sub, eval_mul, eval_X, eval_C]
  linear_combination hsc

/-- Corollary: if the mismatch polynomial `F - (X - C z) * Q` vanishes identically
(as in the Algebraic Group Model when `τ` is independent of `(F, Q)`), then `F.eval z = 0`! -/
theorem kzg_eval_zero_of_mismatch_zero {z : BN254Fr} {F Q : BN254Fr[X]}
    (hzero : F - (X - C z) * Q = 0) : F.eval z = 0 := by
  have hev := congrArg (fun p : BN254Fr[X] => p.eval z) hzero
  simp only [eval_sub, eval_mul, eval_X, eval_C, eval_zero, sub_self, zero_mul, sub_zero] at hev
  exact hev

/-! ## 2. Five-Channel Recursive KZG Verifier Circuit in `PlonkishM BN254Fr` -/

/-- Constrain a Horner linear combination `res = hornerFr alpha terms` in `PlonkishM BN254Fr`. -/
def constrainHornerFr (alpha : Wire) : Wire → List Wire → PlonkishM BN254Fr Wire
  | acc, [] => return acc
  | acc, t :: ts => do
    let prod ← PlonkishM.mul acc alpha
    let acc' ← PlonkishM.add prod t
    constrainHornerFr alpha acc' ts

theorem constrainHornerFr_sound (alpha : Wire) :
    ∀ (acc : Wire) (ts : List Wire) (c₀ : Circuit BN254Fr),
      let (res, c₁) := (constrainHornerFr alpha acc ts).run c₀
      c₀.Extends c₁ ∧
      ∀ w : Wire → BN254Fr, c₁.ConstraintsHold w →
        w res = (ts.map w).foldl (fun a x => a * w alpha + x) (w acc)
  | acc, [], c₀ => by
    dsimp only [constrainHornerFr, StateT.run, pure, StateT.pure, List.map_nil, List.foldl_nil]
    exact ⟨Circuit.Extends.refl c₀, fun _ _ => rfl⟩
  | acc, t :: ts, c₀ => by
    dsimp only [constrainHornerFr, StateT.run, bind, StateT.bind, List.map_cons, List.foldl_cons]
    have h1e := PlonkishM.mul_extends acc alpha c₀
    have h1s := fun w => (PlonkishM.mul_sound acc alpha c₀ w).2
    dsimp only [StateT.run] at h1e h1s
    generalize hc1 : PlonkishM.mul acc alpha c₀ = r1 at h1e h1s ⊢
    rcases r1 with ⟨wprod, c1⟩; dsimp only at h1e h1s ⊢
    have h2e := PlonkishM.add_extends wprod t c1
    have h2s := fun w => (PlonkishM.add_sound wprod t c1 w).2
    dsimp only [StateT.run] at h2e h2s
    generalize hc2 : PlonkishM.add wprod t c1 = r2 at h2e h2s ⊢
    rcases r2 with ⟨wacc', c2⟩; dsimp only at h2e h2s ⊢
    obtain ⟨h3e, h3s⟩ := constrainHornerFr_sound alpha wacc' ts c2
    generalize hc3 : constrainHornerFr alpha wacc' ts c2 = r3 at h3e h3s ⊢
    rcases r3 with ⟨res, c3⟩; dsimp only at h3e h3s ⊢
    refine ⟨h1e.trans (h2e.trans h3e), fun w hw => ?_⟩
    have hres := h3s w hw
    have hadd := h2s w (Circuit.ConstraintsHold.mono h3e hw)
    have hmul := h1s w (Circuit.ConstraintsHold.mono (h2e.trans h3e) hw)
    rw [hres, hadd, hmul]
    rfl

/-- Constrain a list of BLAKE3 transcript channel calls in `PlonkishM BN254Fr`. -/
def constrainBlake3Transcript : List (List Wire × List Wire) → PlonkishM BN254Fr Unit
  | [] => return ()
  | (inp, out) :: rest => do
    PlonkishM.blake3Call inp out
    constrainBlake3Transcript rest

theorem constrainBlake3Transcript_sound :
    ∀ (calls : List (List Wire × List Wire)) (c₀ : Circuit BN254Fr),
      let ((), c₁) := (constrainBlake3Transcript calls).run c₀
      c₀.Extends c₁ ∧
      ∀ w : Wire → BN254Fr, c₁.ConstraintsHold w →
        ∀ call ∈ calls,
          ∃ bytes : List UInt8,
            call.1.map w = bytes.map (fun u => (u.toNat : BN254Fr)) ∧
            call.2.map w = (Aiur.Library.Blake3.digest bytes).toList.map
              (fun u => (u.toNat : BN254Fr))
  | [], c₀ => by
    dsimp only [constrainBlake3Transcript, StateT.run, pure, StateT.pure]
    exact ⟨Circuit.Extends.refl c₀, fun _ _ _ h => nomatch h⟩
  | (inp, out) :: rest, c₀ => by
    dsimp only [constrainBlake3Transcript, StateT.run, bind, StateT.bind]
    have h1e := PlonkishM.blake3Call_extends inp out c₀
    have h1s := fun w => (PlonkishM.blake3Call_sound inp out c₀ w).2
    dsimp only [StateT.run] at h1e h1s
    generalize hc1 : PlonkishM.blake3Call inp out c₀ = r1 at h1e h1s ⊢
    rcases r1 with ⟨u1, c1⟩; dsimp only at h1e h1s ⊢
    obtain ⟨h2e, h2s⟩ := constrainBlake3Transcript_sound rest c1
    generalize hc2 : constrainBlake3Transcript rest c1 = r2 at h2e h2s ⊢
    rcases r2 with ⟨u2, c2⟩; dsimp only at h2e h2s ⊢
    refine ⟨h1e.trans h2e, fun w hw call hcall => ?_⟩
    rcases List.mem_cons.mp hcall with rfl | hrest
    · exact h1s w (Circuit.ConstraintsHold.mono h2e hw)
    · exact h2s w hw call hrest

/-- Layout for the 5-channel recursive KZG verifier circuit (`native_verifier.rs`):
1. `transcriptCalls`: 5-channel BLAKE3 transcript hashing (VK, stage1, stage2, quotient, openings),
2. `alphaWire`, `zeroWire`, `oodTerms`: Horner OOD constraint combination in `BN254Fr`,
3. `quotientWire`, `vanishingWire`: enforces `quotient * vanishing = hornerFr alpha oodTerms`.

Note: deferred pairing operand accumulation (`bn254G1` MSM) and public-input wiring live on
`base : Circuit BN254Fr` (`base.publicInputs`) and are not constrained by `buildRecursiveKzgCircuit`. -/
structure FiveChannelLayout where
  transcriptCalls : List (List Wire × List Wire)
  zeroWire : Wire
  alphaWire : Wire
  oodTerms : List Wire
  quotientWire : Wire
  vanishingWire : Wire

/-- Build the recursive KZG verifier circuit in `PlonkishM BN254Fr` over `base`. -/
def buildRecursiveKzgCircuit (base : Circuit BN254Fr) (layout : FiveChannelLayout) :
    Circuit BN254Fr :=
  ((do
    constrainBlake3Transcript layout.transcriptCalls
    PlonkishM.assertZero layout.zeroWire
    let combined ← constrainHornerFr layout.alphaWire layout.zeroWire layout.oodTerms
    let qv ← PlonkishM.mul layout.quotientWire layout.vanishingWire
    PlonkishM.assertEq combined qv).run base).2

/-- Mathematical satisfaction predicate for the 5-channel recursive KZG verifier:
1. `base` (including public inputs, non-native `BN254::Fq` / `bn254G1` MSM gates) is satisfied,
2. Every BLAKE3 transcript absorption/squeeze matches `Aiur.Library.Blake3.digest`,
3. The OOD quotient polynomial equation `hornerFr (w alpha) (oodTerms.map w) = w quotient * w vanishing`
   holds identically in `BN254Fr`. -/
def FiveChannelSatisfied (base : Circuit BN254Fr) (layout : FiveChannelLayout)
    (pub : List BN254Fr) (w : Wire → BN254Fr) : Prop :=
  base.Satisfies pub w ∧
  (∀ call ∈ layout.transcriptCalls,
    ∃ bytes : List UInt8,
      call.1.map w = bytes.map (fun u => (u.toNat : BN254Fr)) ∧
      call.2.map w = (Aiur.Library.Blake3.digest bytes).toList.map
        (fun u => (u.toNat : BN254Fr))) ∧
  hornerFr (w layout.alphaWire) (layout.oodTerms.map w) =
    w layout.quotientWire * w layout.vanishingWire

private lemma buildRecursiveKzgCircuit_publicInputs (base : Circuit BN254Fr)
    (layout : FiveChannelLayout) :
    (buildRecursiveKzgCircuit base layout).publicInputs = base.publicInputs := by
  have hTr : ∀ cs c, (constrainBlake3Transcript cs c).2.publicInputs = c.publicInputs := by
    intro cs; induction cs with
    | nil => intro c; rfl
    | cons p rest ih =>
      rcases p with ⟨inp, out⟩
      intro c
      dsimp only [constrainBlake3Transcript, bind, StateT.bind]
      generalize h1 : PlonkishM.blake3Call inp out c = r1; rcases r1 with ⟨u1, c1⟩
      have hc1 : c1.publicInputs = c.publicInputs := by
        have : (PlonkishM.blake3Call inp out c).2.publicInputs = c.publicInputs := rfl
        rw [h1] at this; exact this
      exact (ih c1).trans hc1
  have hHor : ∀ alpha acc ts c, (constrainHornerFr alpha acc ts c).2.publicInputs = c.publicInputs := by
    intro alpha acc ts; induction ts generalizing acc with
    | nil => intro c; rfl
    | cons t ts ih =>
      intro c
      dsimp only [constrainHornerFr, bind, StateT.bind]
      generalize h1 : PlonkishM.mul acc alpha c = r1; rcases r1 with ⟨wp, c1⟩
      have hc1 : c1.publicInputs = c.publicInputs := by
        have : (PlonkishM.mul acc alpha c).2.publicInputs = c.publicInputs := rfl
        rw [h1] at this; exact this
      dsimp only
      generalize h2 : PlonkishM.add wp t c1 = r2; rcases r2 with ⟨wa, c2⟩
      have hc2 : c2.publicInputs = c1.publicInputs := by
        have : (PlonkishM.add wp t c1).2.publicInputs = c1.publicInputs := rfl
        rw [h2] at this; exact this
      dsimp only
      exact ((ih wa c2).trans hc2).trans hc1
  unfold buildRecursiveKzgCircuit
  dsimp only [StateT.run, bind, StateT.bind]
  generalize h1 : constrainBlake3Transcript layout.transcriptCalls base = r1; rcases r1 with ⟨u1, c1⟩
  have hc1 : c1.publicInputs = base.publicInputs := by
    have := hTr layout.transcriptCalls base; rw [h1] at this; exact this
  dsimp only
  generalize h2 : PlonkishM.assertZero layout.zeroWire c1 = r2; rcases r2 with ⟨u2, c2⟩
  have hc2 : c2.publicInputs = c1.publicInputs := by
    have : (PlonkishM.assertZero layout.zeroWire c1).2.publicInputs = c1.publicInputs := rfl
    rw [h2] at this; exact this
  dsimp only
  generalize h3 : constrainHornerFr layout.alphaWire layout.zeroWire layout.oodTerms c2 = r3
  rcases r3 with ⟨wc, c3⟩
  have hc3 : c3.publicInputs = c2.publicInputs := by
    have := hHor layout.alphaWire layout.zeroWire layout.oodTerms c2; rw [h3] at this; exact this
  dsimp only
  generalize h4 : PlonkishM.mul layout.quotientWire layout.vanishingWire c3 = r4
  rcases r4 with ⟨wqv, c4⟩
  have hc4 : c4.publicInputs = c3.publicInputs := by
    have : (PlonkishM.mul layout.quotientWire layout.vanishingWire c3).2.publicInputs = c3.publicInputs := rfl
    rw [h4] at this; exact this
  dsimp only
  have hc5 : (PlonkishM.assertEq wc wqv c4).2.publicInputs = c4.publicInputs := rfl
  exact hc5.trans (hc4.trans (hc3.trans (hc2.trans hc1)))

/-- **5-Channel Recursive KZG Verifier Circuit Soundness (`recursiveKzgCircuit_sound`):**
Any `BN254Fr` wire assignment `w` satisfying `buildRecursiveKzgCircuit base layout` on `pub`
satisfies `FiveChannelSatisfied base layout pub w`. -/
theorem recursiveKzgCircuit_sound (base : Circuit BN254Fr) (layout : FiveChannelLayout)
    (pub : List BN254Fr) (w : Wire → BN254Fr)
    (hsat : (buildRecursiveKzgCircuit base layout).Satisfies pub w) :
    FiveChannelSatisfied base layout pub w := by
  have hpub : base.publicInputs.map w = pub := by
    rw [← buildRecursiveKzgCircuit_publicInputs base layout]
    exact hsat.1
  have hhold : (buildRecursiveKzgCircuit base layout).ConstraintsHold w :=
    ⟨hsat.2.1, hsat.2.2.1, hsat.2.2.2⟩
  unfold buildRecursiveKzgCircuit at hhold
  dsimp only [StateT.run, bind, StateT.bind] at hhold
  obtain ⟨e1, s1⟩ := constrainBlake3Transcript_sound layout.transcriptCalls base
  generalize h1 : constrainBlake3Transcript layout.transcriptCalls base = r1 at e1 s1 hhold
  rcases r1 with ⟨u1, c1⟩
  dsimp only at e1 s1 hhold
  have e2 : c1.Extends (PlonkishM.assertZero layout.zeroWire c1).2 :=
    PlonkishM.assertGate_extends _ c1
  have s2 := fun w => PlonkishM.assertZero_sound layout.zeroWire c1 w
  dsimp only [StateT.run] at e2 s2
  generalize h2 : PlonkishM.assertZero layout.zeroWire c1 = r2 at e2 s2 hhold
  rcases r2 with ⟨u2, c2⟩
  dsimp only at e2 s2 hhold
  obtain ⟨e3, s3⟩ := constrainHornerFr_sound layout.alphaWire layout.zeroWire layout.oodTerms c2
  generalize h3 : constrainHornerFr layout.alphaWire layout.zeroWire layout.oodTerms c2 = r3
    at e3 s3 hhold
  rcases r3 with ⟨wc, c3⟩
  dsimp only at e3 s3 hhold
  have e4 := PlonkishM.mul_extends layout.quotientWire layout.vanishingWire c3
  have s4 := fun w => (PlonkishM.mul_sound layout.quotientWire layout.vanishingWire c3 w).2
  dsimp only [StateT.run] at e4 s4
  generalize h4 : PlonkishM.mul layout.quotientWire layout.vanishingWire c3 = r4 at e4 s4 hhold
  rcases r4 with ⟨wqv, c4⟩
  dsimp only at e4 s4 hhold
  have e5 : c4.Extends (PlonkishM.assertEq wc wqv c4).2 :=
    PlonkishM.assertGate_extends _ c4
  have s5 := fun w => PlonkishM.assertEq_sound wc wqv c4 w
  dsimp only [StateT.run] at e5 s5
  generalize h5 : PlonkishM.assertEq wc wqv c4 = r5 at e5 s5 hhold
  rcases r5 with ⟨u5, c5⟩
  dsimp only at e5 s5 hhold
  have ext15 := e2.trans (e3.trans (e4.trans e5))
  have ext25 := e3.trans (e4.trans e5)
  have ext35 := e4.trans e5
  have hbaseHold : base.ConstraintsHold w :=
    Circuit.ConstraintsHold.mono (e1.trans ext15) hhold
  have htr := s1 w (Circuit.ConstraintsHold.mono ext15 hhold)
  have hz := s2 w (Circuit.ConstraintsHold.mono ext25 hhold)
  have hhor := s3 w (Circuit.ConstraintsHold.mono ext35 hhold)
  have hmul := s4 w (Circuit.ConstraintsHold.mono e5 hhold)
  have heq := s5 w hhold
  refine ⟨⟨hpub, hbaseHold.1, hbaseHold.2.1, hbaseHold.2.2⟩, htr, ?_⟩
  unfold hornerFr
  rw [← hz, ← hhor, heq, hmul]

end Ix.Cert.Compression.RecursiveKzg
