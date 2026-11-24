import Ix.Cert.Compression.Plonkish
import Ix.Cert.Compression.Bls12381.Field
import Ix.Cert.Compression.Bls12381.CurveMsm
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots

/-! # Certified BLS12-381 Recursive KZG / SHPlonk Verifier & Concrete `BLS12381::G1` Soundness

Formalizes the BLS12-381 KZG recursive verifier
(`crates/proof-compression/src/recursive/native_verifier.rs` and `src/kzg/pcs.rs`) over
`PlonkishM BLS12381Fr` and the concrete Mathlib-backed elliptic curve group
`CurveMsm.bls12381G1`:

1. **Concrete KZG Algebraic & Batched Opening Soundness over `BLS12381Fr`:**
   - `bls12381_kzg_single_eval_of_poly_eq`: `f - C y = (X - C z) * q` implies `f.eval z = y`.
   - `bls12381_kzg_batched_horner_bad_card`: exact Schwartz–Zippel bound (`≤ fs.length - 1`
     out of `bls12381FrModulus` challenges `γ : BLS12381Fr`).
   - Unconditional prime-order generator laws (`bls12381G1_smul_add_fr`,
     `bls12381G1_smul_mul_fr`, `bls12381G1_smul_inj_fr`) derived directly from our
     kernel-checked Endomorphism-ECPP certificate (`bls12381Generator_inPrimeSubgroup`,
     zero extra `horder` hypothesis!).
   - `Bls12381KzgPairingCheck`: algebraic pairing check explicitly enforcing
     `InPrimeSubgroup` on both commitment `C` and opening proof `W` (`bls12381_kzg_pairing_sound_at_bls12381G1`),
     plus negative control `bls12381_kzg_pairingCheck_rejects_torsion` showing that the
     3-torsion point `(0, 2)` is rejected.
   - `bls12381_pairing_msm_sound`: concrete 64-round Straus MSM soundness + `InPrimeSubgroup`
     preservation on `bls12381G1`.
2. **5-Channel Recursive KZG Verifier Circuit (`buildBls12381RecursiveKzgCircuit`,
   `Bls12381FiveChannelSatisfied`, `bls12381_recursiveKzgCircuit_sound`):**
   Built directly in `PlonkishM BLS12381Fr`.

Zero `sorry`, zero `native_decide`, strictly `[propext, Classical.choice, Quot.sound]`.
-/

namespace Ix.Cert.Compression.Bls12381.RecursiveKzg

open Ix.Cert.Compression.Plonkish
open Ix.Cert.Compression.Bls12381.Field
open Ix.Cert.Compression.Bls12381.CurveMsm
open Polynomial

/-! ## 1. Algebraic & Batched KZG Opening Soundness over `BLS12381Fr` -/

/-- Exact single-opening KZG polynomial soundness over `BLS12381Fr`. -/
theorem bls12381_kzg_single_eval_of_poly_eq {f q : BLS12381Fr[X]} {z y : BLS12381Fr}
    (h : f - C y = (X - C z) * q) : f.eval z = y := by
  have hev := congrArg (fun p : BLS12381Fr[X] => p.eval z) h
  simp only [eval_sub, eval_C, eval_mul, eval_X, sub_self, zero_mul] at hev
  exact sub_eq_zero.mp hev

/-- Horner linear combination of scalars `cs` at challenge `γ : BLS12381Fr`. -/
def hornerBlsFr (γ : BLS12381Fr) (cs : List BLS12381Fr) : BLS12381Fr :=
  cs.foldl (fun acc x => acc * γ + x) 0

/-- Polynomial in `γ` representing `hornerBlsFr γ cs`. -/
noncomputable def hornerBlsFrPoly (cs : List BLS12381Fr) : BLS12381Fr[X] :=
  cs.foldl (fun acc x => acc * X + C x) 0

theorem eval_hornerBlsFrPoly (γ : BLS12381Fr) (cs : List BLS12381Fr) :
    (hornerBlsFrPoly cs).eval γ = hornerBlsFr γ cs := by
  have hgen : ∀ (l : List BLS12381Fr) (p : BLS12381Fr[X]),
      (l.foldl (fun acc x => acc * X + C x) p).eval γ =
        l.foldl (fun acc x => acc * γ + x) (p.eval γ) := by
    intro l
    induction l with
    | nil => intro p; rfl
    | cons c cs ih =>
      intro p
      simp only [List.foldl_cons, ih, eval_add, eval_mul, eval_X, eval_C]
  simpa [hornerBlsFrPoly, hornerBlsFr] using hgen cs 0

theorem natDegree_hornerBlsFrPoly_le (cs : List BLS12381Fr) :
    (hornerBlsFrPoly cs).natDegree ≤ cs.length - 1 := by
  have hgen : ∀ (l : List BLS12381Fr) (p : BLS12381Fr[X]),
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
  | nil => simp [hornerBlsFrPoly]
  | cons c cs =>
    have h1 := hgen cs (C c)
    unfold hornerBlsFrPoly
    simp only [List.foldl_cons, zero_mul, zero_add]
    cases cs with
    | nil => simp
    | cons d ds =>
      simp only [List.cons_ne_nil, ↓reduceIte, natDegree_C, zero_add, List.length_cons,
        Nat.add_sub_cancel] at h1
      simpa using h1

theorem hornerBlsFrPoly_ne_zero_of_exists {cs : List BLS12381Fr} (h : ∃ c ∈ cs, c ≠ 0) :
    hornerBlsFrPoly cs ≠ 0 := by
  have hcoeff : ∀ (l : List BLS12381Fr) (p : BLS12381Fr[X]) (k : ℕ) (hk : k < l.length),
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
  have hci := congrArg (fun p : BLS12381Fr[X] => p.coeff (cs.length - 1 - i)) h0
  rw [coeff_zero, hornerBlsFrPoly, hcoeff cs 0 (cs.length - 1 - i) (by omega)] at hci
  have hidx : cs.length - 1 - (cs.length - 1 - i) = i := by omega
  simp only [hidx] at hci
  exact hc_ne hci

/-- **Batched KZG Opening Soundness (Schwartz–Zippel over `BLS12381Fr`):**
For any list of committed polynomials `fs` and claimed evaluations `ys` at point `z`,
if `∃ i, (fs[i]).eval z ≠ ys[i]`, then at most `fs.length - 1` challenges `γ ∈ BLS12381Fr`
satisfy `hornerBlsFr γ (zipWith (fun f y => f.eval z - y) fs ys) = 0`. -/
theorem bls12381_kzg_batched_horner_bad_card {fs : List (BLS12381Fr[X])} {ys : List BLS12381Fr}
    (z : BLS12381Fr) (hlen : fs.length = ys.length)
    (hmis : ∃ i, ∃ hi : i < fs.length, fs[i].eval z ≠ ys[i]'(hlen ▸ hi)) :
    (Finset.univ.filter fun γ : BLS12381Fr =>
      hornerBlsFr γ (List.zipWith (fun f y => f.eval z - y) fs ys) = 0).card ≤
      fs.length - 1 := by
  set diffs := List.zipWith (fun f y => f.eval z - y) fs ys
  have hdiffs_len : diffs.length = fs.length := by simp [diffs, hlen]
  have hex : ∃ c ∈ diffs, c ≠ 0 := by
    obtain ⟨i, hi, hne⟩ := hmis
    refine ⟨diffs[i]'(by omega), List.getElem_mem (by omega), ?_⟩
    simp only [diffs, List.getElem_zipWith]
    exact sub_ne_zero.mpr hne
  set P := hornerBlsFrPoly diffs
  have hPne : P ≠ 0 := hornerBlsFrPoly_ne_zero_of_exists hex
  have hsub : (Finset.univ.filter fun γ : BLS12381Fr => hornerBlsFr γ diffs = 0) ⊆ P.roots.toFinset := by
    intro γ hγ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ
    rw [Multiset.mem_toFinset, mem_roots hPne, IsRoot.def, eval_hornerBlsFrPoly, hγ]
  exact (Finset.card_le_card hsub).trans
    ((Multiset.toFinset_card_le _).trans
      ((Polynomial.card_roots' P).trans
        (by rw [← hdiffs_len]; exact natDegree_hornerBlsFrPoly_le diffs)))

/-! ### Unconditional Prime-Order `BLS12381::G1` Generator Laws & Subgroup-Checked KZG Pairing -/

theorem bls12381G1_generator_ne_zero : bls12381G1.generator ≠ bls12381G1.zero :=
  bls12381Generator_ne_zero

theorem bls12381G1_generator_order :
    bls12381G1.smul bls12381FrModulus bls12381G1.generator = bls12381G1.zero :=
  bls12381Generator_inPrimeSubgroup

theorem bls12381G1_smul_mod_r (k : Nat) :
    bls12381G1.smul (k % bls12381FrModulus) bls12381G1.generator =
      bls12381G1.smul k bls12381G1.generator := by
  have hdiv : bls12381FrModulus * (k / bls12381FrModulus) + k % bls12381FrModulus = k :=
    Nat.div_add_mod k bls12381FrModulus
  conv_rhs => rw [← hdiv]
  rw [bls12381G1.smul_add, Nat.mul_comm, ← bls12381G1.smul_smul, bls12381G1_generator_order,
    bls12381G1.smul_zero_point, bls12381G1.zero_add]

theorem bls12381G1_smul_add_fr (a b : BLS12381Fr) :
    bls12381G1.add (bls12381G1.smul a.val bls12381G1.generator)
        (bls12381G1.smul b.val bls12381G1.generator) =
      bls12381G1.smul (a + b).val bls12381G1.generator := by
  rw [← bls12381G1.smul_add]
  dsimp only [BLS12381Fr.val]
  rw [ZMod.val_add, bls12381G1_smul_mod_r]

theorem bls12381G1_smul_mul_fr (a b : BLS12381Fr) :
    bls12381G1.smul a.val (bls12381G1.smul b.val bls12381G1.generator) =
      bls12381G1.smul (a * b).val bls12381G1.generator := by
  rw [bls12381G1.smul_smul]
  dsimp only [BLS12381Fr.val]
  rw [ZMod.val_mul, bls12381G1_smul_mod_r]

/-- Unconditional prime-order injectivity of `a ↦ [a] G` on `BLS12381Fr`
(derived from `bls12381FrModulus_prime`, `bls12381G1_generator_ne_zero`, and our
unconditional Endomorphism-ECPP theorem `bls12381Generator_inPrimeSubgroup`). -/
theorem bls12381G1_smul_inj_fr {a b : BLS12381Fr}
    (heq : bls12381G1.smul a.val bls12381G1.generator =
      bls12381G1.smul b.val bls12381G1.generator) :
    a = b := by
  by_contra hne
  have hdiff_ne : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hneg : bls12381G1.smul (-b).val bls12381G1.generator =
      bls12381G1.neg (bls12381G1.smul b.val bls12381G1.generator) := by
    have h0 : bls12381G1.add (bls12381G1.smul b.val bls12381G1.generator)
        (bls12381G1.smul (-b).val bls12381G1.generator) = bls12381G1.zero := by
      rw [bls12381G1_smul_add_fr, add_neg_cancel]
      dsimp only [BLS12381Fr.val]
      rw [ZMod.val_zero, bls12381G1.smul_zero]
    calc bls12381G1.smul (-b).val bls12381G1.generator
        = bls12381G1.add bls12381G1.zero (bls12381G1.smul (-b).val bls12381G1.generator) :=
            (bls12381G1.zero_add _).symm
      _ = bls12381G1.add (bls12381G1.add (bls12381G1.neg (bls12381G1.smul b.val bls12381G1.generator))
            (bls12381G1.smul b.val bls12381G1.generator))
            (bls12381G1.smul (-b).val bls12381G1.generator) := by
            rw [bls12381G1.neg_add_cancel]
      _ = bls12381G1.add (bls12381G1.neg (bls12381G1.smul b.val bls12381G1.generator))
            (bls12381G1.add (bls12381G1.smul b.val bls12381G1.generator)
              (bls12381G1.smul (-b).val bls12381G1.generator)) := bls12381G1.add_assoc _ _ _
      _ = bls12381G1.neg (bls12381G1.smul b.val bls12381G1.generator) := by
            rw [h0, bls12381G1.add_zero]
  have hzero : bls12381G1.smul (a - b).val bls12381G1.generator = bls12381G1.zero := by
    rw [sub_eq_add_neg, ← bls12381G1_smul_add_fr, heq, hneg, bls12381G1.add_neg_cancel]
  have h1 : bls12381G1.smul ((a - b)⁻¹ * (a - b)).val bls12381G1.generator = bls12381G1.zero := by
    rw [← bls12381G1_smul_mul_fr, hzero, bls12381G1.smul_zero_point]
  rw [inv_mul_cancel₀ hdiff_ne] at h1
  dsimp only [BLS12381Fr.val] at h1
  have : Fact (1 < bls12381FrModulus) := ⟨bls12381FrModulus_prime.one_lt⟩
  rw [ZMod.val_one, bls12381G1.smul_one] at h1
  exact bls12381G1_generator_ne_zero h1

/-- KZG commitment to polynomial `f : BLS12381Fr[X]` under SRS trapdoor `τ : BLS12381Fr`. -/
noncomputable def bls12381KzgCommit (τ : BLS12381Fr) (f : BLS12381Fr[X]) : bls12381G1.Point :=
  bls12381G1.smul (f.eval τ).val bls12381G1.generator

theorem bls12381KzgCommit_inPrimeSubgroup (τ : BLS12381Fr) (f : BLS12381Fr[X]) :
    InPrimeSubgroup (bls12381KzgCommit τ f) :=
  inPrimeSubgroup_smul bls12381G1 (f.eval τ).val bls12381Generator_inPrimeSubgroup

/-- **Subgroup-Enforced KZG Pairing Check (`Bls12381KzgPairingCheck`):**
Unlike BN254 ($h_1 = 1$), BLS12-381 KZG verification MUST explicitly enforce
`InPrimeSubgroup` on both commitment `comm` and opening witness `W` in addition to the
pairing relation `comm + [z] W = [τ] W`. -/
def Bls12381KzgPairingCheck (comm W : bls12381G1.Point) (z τ : BLS12381Fr) : Prop :=
  InPrimeSubgroup comm ∧
  InPrimeSubgroup W ∧
  bls12381G1.add comm (bls12381G1.smul z.val W) = bls12381G1.smul τ.val W

/-- **KZG Pairing Equation → Polynomial Identity (Concrete `BLS12381::G1`, Subgroup-Checked):**
When `(comm, W)` pass `Bls12381KzgPairingCheck comm W z τ` (including mandatory `InPrimeSubgroup`
checks on both `comm` and `W`) and have AGM representations `comm = bls12381KzgCommit τ F` and
`W = bls12381KzgCommit τ Q`, then `(F - (X - C z) * Q).eval τ = 0`. -/
theorem bls12381_kzg_pairing_sound_at_bls12381G1
    (τ z : BLS12381Fr) (F Q : BLS12381Fr[X]) (comm W : bls12381G1.Point)
    (hC : comm = bls12381KzgCommit τ F)
    (hW : W = bls12381KzgCommit τ Q)
    (hcheck : Bls12381KzgPairingCheck comm W z τ) :
    (F - (X - Polynomial.C z) * Q).eval τ = 0 := by
  have hpair := hcheck.2.2
  rw [hC, hW] at hpair
  unfold bls12381KzgCommit at hpair
  rw [bls12381G1_smul_mul_fr, bls12381G1_smul_mul_fr, bls12381G1_smul_add_fr] at hpair
  have hsc : F.eval τ + z * Q.eval τ = τ * Q.eval τ := bls12381G1_smul_inj_fr hpair
  simp only [eval_sub, eval_mul, eval_X, eval_C]
  linear_combination hsc

/-- Constructive negative control: `Bls12381KzgPairingCheck` rejects the 3-torsion point `(0, 2)`
as either commitment `C` or opening witness `W`. -/
theorem bls12381_kzg_pairingCheck_rejects_torsion (P : bls12381G1.Point) (z τ : BLS12381Fr) :
    ¬ Bls12381KzgPairingCheck bls12381TorsionPoint P z τ ∧
    ¬ Bls12381KzgPairingCheck P bls12381TorsionPoint z τ :=
  ⟨fun h => bls12381_torsionPoint_not_inPrimeSubgroup h.1,
   fun h => bls12381_torsionPoint_not_inPrimeSubgroup h.2.1⟩

/-- If the mismatch polynomial vanishes identically (AGM), then `F.eval z = 0`. -/
theorem bls12381_kzg_eval_zero_of_mismatch_zero {z : BLS12381Fr} {F Q : BLS12381Fr[X]}
    (hzero : F - (X - C z) * Q = 0) : F.eval z = 0 := by
  have hev := congrArg (fun p : BLS12381Fr[X] => p.eval z) hzero
  simp only [eval_sub, eval_mul, eval_X, eval_C, eval_zero, sub_self, zero_mul, sub_zero] at hev
  exact hev

/-- **Concrete `bls12381G1` Pairing-Operand MSM Soundness + Subgroup Preservation
(`bls12381_pairing_msm_sound`):**
When all base points `points` pass `InPrimeSubgroup`, the 64-round 4-bit Straus MSM produces
the exact multi-scalar multiplication AND guarantees that the result remains in the
prime-order subgroup $G_1$. -/
theorem bls12381_pairing_msm_sound
    (points : List bls12381G1.Point) (h : bls12381G1.Point)
    (rounds : List (List Nat))
    (hLen64 : rounds.length = 64)
    (hRows : ∀ row ∈ rounds, row.length = points.length)
    (hSub : ∀ P ∈ points, InPrimeSubgroup P) :
    let acc64 := bls12381StrausLoop bls12381G1 points h rounds
    let scalars := bls12381FoldWindowRows points.length rounds
    let res := bls12381G1.add acc64 (bls12381G1.neg (bls12381G1.smul (16 ^ 64) h))
    res = bls12381MsmEval bls12381G1 scalars points ∧ InPrimeSubgroup res := by
  dsimp only
  have hmsm := (bls12381_msm_sound bls12381G1 points h rounds hLen64 hRows).2
  refine ⟨hmsm, ?_⟩
  rw [hmsm]
  exact bls12381_msm_inPrimeSubgroup bls12381G1 _ points hSub

/-! ## 2. Five-Channel Recursive KZG Verifier Circuit in `PlonkishM BLS12381Fr` -/

/-- Constrain a Horner linear combination `res = hornerBlsFr alpha terms` in `PlonkishM BLS12381Fr`. -/
def constrainHornerBlsFr (alpha : Wire) : Wire → List Wire → PlonkishM BLS12381Fr Wire
  | acc, [] => return acc
  | acc, t :: ts => do
    let prod ← PlonkishM.mul acc alpha
    let acc' ← PlonkishM.add prod t
    constrainHornerBlsFr alpha acc' ts

theorem constrainHornerBlsFr_sound (alpha : Wire) :
    ∀ (acc : Wire) (ts : List Wire) (c₀ : Circuit BLS12381Fr),
      let (res, c₁) := (constrainHornerBlsFr alpha acc ts).run c₀
      c₀.Extends c₁ ∧
      ∀ w : Wire → BLS12381Fr, c₁.ConstraintsHold w →
        w res = (ts.map w).foldl (fun a x => a * w alpha + x) (w acc)
  | acc, [], c₀ => by
    dsimp only [constrainHornerBlsFr, StateT.run, pure, StateT.pure, List.map_nil, List.foldl_nil]
    exact ⟨Circuit.Extends.refl c₀, fun _ _ => rfl⟩
  | acc, t :: ts, c₀ => by
    dsimp only [constrainHornerBlsFr, StateT.run, bind, StateT.bind, List.map_cons, List.foldl_cons]
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
    obtain ⟨h3e, h3s⟩ := constrainHornerBlsFr_sound alpha wacc' ts c2
    generalize hc3 : constrainHornerBlsFr alpha wacc' ts c2 = r3 at h3e h3s ⊢
    rcases r3 with ⟨res, c3⟩; dsimp only at h3e h3s ⊢
    refine ⟨h1e.trans (h2e.trans h3e), fun w hw => ?_⟩
    have hres := h3s w hw
    have hadd := h2s w (Circuit.ConstraintsHold.mono h3e hw)
    have hmul := h1s w (Circuit.ConstraintsHold.mono (h2e.trans h3e) hw)
    rw [hres, hadd, hmul]
    rfl

/-- Constrain a list of BLAKE3 transcript channel calls in `PlonkishM BLS12381Fr`. -/
def constrainBlsBlake3Transcript : List (List Wire × List Wire) → PlonkishM BLS12381Fr Unit
  | [] => return ()
  | (inp, out) :: rest => do
    PlonkishM.blake3Call inp out
    constrainBlsBlake3Transcript rest

theorem constrainBlsBlake3Transcript_sound :
    ∀ (calls : List (List Wire × List Wire)) (c₀ : Circuit BLS12381Fr),
      let ((), c₁) := (constrainBlsBlake3Transcript calls).run c₀
      c₀.Extends c₁ ∧
      ∀ w : Wire → BLS12381Fr, c₁.ConstraintsHold w →
        ∀ call ∈ calls,
          ∃ bytes : List UInt8,
            call.1.map w = bytes.map (fun u => (u.toNat : BLS12381Fr)) ∧
            call.2.map w = (Aiur.Library.Blake3.digest bytes).toList.map
              (fun u => (u.toNat : BLS12381Fr))
  | [], c₀ => by
    dsimp only [constrainBlsBlake3Transcript, StateT.run, pure, StateT.pure]
    exact ⟨Circuit.Extends.refl c₀, fun _ _ _ h => nomatch h⟩
  | (inp, out) :: rest, c₀ => by
    dsimp only [constrainBlsBlake3Transcript, StateT.run, bind, StateT.bind]
    have h1e := PlonkishM.blake3Call_extends inp out c₀
    have h1s := fun w => (PlonkishM.blake3Call_sound inp out c₀ w).2
    dsimp only [StateT.run] at h1e h1s
    generalize hc1 : PlonkishM.blake3Call inp out c₀ = r1 at h1e h1s ⊢
    rcases r1 with ⟨u1, c1⟩; dsimp only at h1e h1s ⊢
    obtain ⟨h2e, h2s⟩ := constrainBlsBlake3Transcript_sound rest c1
    generalize hc2 : constrainBlsBlake3Transcript rest c1 = r2 at h2e h2s ⊢
    rcases r2 with ⟨u2, c2⟩; dsimp only at h2e h2s ⊢
    refine ⟨h1e.trans h2e, fun w hw call hcall => ?_⟩
    rcases List.mem_cons.mp hcall with rfl | hrest
    · exact h1s w (Circuit.ConstraintsHold.mono h2e hw)
    · exact h2s w hw call hrest

/-- Layout for the 5-channel BLS12-381 recursive KZG verifier circuit. -/
structure Bls12381FiveChannelLayout where
  transcriptCalls : List (List Wire × List Wire)
  zeroWire : Wire
  alphaWire : Wire
  oodTerms : List Wire
  quotientWire : Wire
  vanishingWire : Wire

/-- Build the 5-channel BLS12-381 recursive KZG verifier circuit in `PlonkishM BLS12381Fr`. -/
def buildBls12381RecursiveKzgCircuit (base : Circuit BLS12381Fr)
    (layout : Bls12381FiveChannelLayout) : Circuit BLS12381Fr :=
  ((do
    constrainBlsBlake3Transcript layout.transcriptCalls
    PlonkishM.assertZero layout.zeroWire
    let combined ← constrainHornerBlsFr layout.alphaWire layout.zeroWire layout.oodTerms
    let qv ← PlonkishM.mul layout.quotientWire layout.vanishingWire
    PlonkishM.assertEq combined qv).run base).2

/-- Mathematical satisfaction predicate for the 5-channel BLS12-381 recursive KZG verifier. -/
def Bls12381FiveChannelSatisfied (base : Circuit BLS12381Fr) (layout : Bls12381FiveChannelLayout)
    (pub : List BLS12381Fr) (w : Wire → BLS12381Fr) : Prop :=
  base.Satisfies pub w ∧
  (∀ call ∈ layout.transcriptCalls,
    ∃ bytes : List UInt8,
      call.1.map w = bytes.map (fun u => (u.toNat : BLS12381Fr)) ∧
      call.2.map w = (Aiur.Library.Blake3.digest bytes).toList.map
        (fun u => (u.toNat : BLS12381Fr))) ∧
  hornerBlsFr (w layout.alphaWire) (layout.oodTerms.map w) =
    w layout.quotientWire * w layout.vanishingWire

private lemma buildBls12381RecursiveKzgCircuit_publicInputs (base : Circuit BLS12381Fr)
    (layout : Bls12381FiveChannelLayout) :
    (buildBls12381RecursiveKzgCircuit base layout).publicInputs = base.publicInputs := by
  have hTr : ∀ cs c, (constrainBlsBlake3Transcript cs c).2.publicInputs = c.publicInputs := by
    intro cs; induction cs with
    | nil => intro c; rfl
    | cons p rest ih =>
      rcases p with ⟨inp, out⟩
      intro c
      dsimp only [constrainBlsBlake3Transcript, bind, StateT.bind]
      generalize h1 : PlonkishM.blake3Call inp out c = r1; rcases r1 with ⟨u1, c1⟩
      have hc1 : c1.publicInputs = c.publicInputs := by
        have : (PlonkishM.blake3Call inp out c).2.publicInputs = c.publicInputs := rfl
        rw [h1] at this; exact this
      exact (ih c1).trans hc1
  have hHor : ∀ alpha acc ts c,
      (constrainHornerBlsFr alpha acc ts c).2.publicInputs = c.publicInputs := by
    intro alpha acc ts; induction ts generalizing acc with
    | nil => intro c; rfl
    | cons t ts ih =>
      intro c
      dsimp only [constrainHornerBlsFr, bind, StateT.bind]
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
  unfold buildBls12381RecursiveKzgCircuit
  dsimp only [StateT.run, bind, StateT.bind]
  generalize h1 : constrainBlsBlake3Transcript layout.transcriptCalls base = r1
  rcases r1 with ⟨u1, c1⟩
  have hc1 : c1.publicInputs = base.publicInputs := by
    have := hTr layout.transcriptCalls base; rw [h1] at this; exact this
  dsimp only
  generalize h2 : PlonkishM.assertZero layout.zeroWire c1 = r2; rcases r2 with ⟨u2, c2⟩
  have hc2 : c2.publicInputs = c1.publicInputs := by
    have : (PlonkishM.assertZero layout.zeroWire c1).2.publicInputs = c1.publicInputs := rfl
    rw [h2] at this; exact this
  dsimp only
  generalize h3 : constrainHornerBlsFr layout.alphaWire layout.zeroWire layout.oodTerms c2 = r3
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

/-- **5-Channel BLS12-381 Recursive KZG Verifier Circuit Soundness
(`bls12381_recursiveKzgCircuit_sound`)**. -/
theorem bls12381_recursiveKzgCircuit_sound (base : Circuit BLS12381Fr)
    (layout : Bls12381FiveChannelLayout)
    (pub : List BLS12381Fr) (w : Wire → BLS12381Fr)
    (hsat : (buildBls12381RecursiveKzgCircuit base layout).Satisfies pub w) :
    Bls12381FiveChannelSatisfied base layout pub w := by
  have hpub : base.publicInputs.map w = pub := by
    rw [← buildBls12381RecursiveKzgCircuit_publicInputs base layout]
    exact hsat.1
  have hhold : (buildBls12381RecursiveKzgCircuit base layout).ConstraintsHold w :=
    ⟨hsat.2.1, hsat.2.2.1, hsat.2.2.2⟩
  unfold buildBls12381RecursiveKzgCircuit at hhold
  dsimp only [StateT.run, bind, StateT.bind] at hhold
  obtain ⟨e1, s1⟩ := constrainBlsBlake3Transcript_sound layout.transcriptCalls base
  generalize h1 : constrainBlsBlake3Transcript layout.transcriptCalls base = r1 at e1 s1 hhold
  rcases r1 with ⟨u1, c1⟩
  dsimp only at e1 s1 hhold
  have e2 : c1.Extends (PlonkishM.assertZero layout.zeroWire c1).2 :=
    PlonkishM.assertGate_extends _ c1
  have s2 := fun w => PlonkishM.assertZero_sound layout.zeroWire c1 w
  dsimp only [StateT.run] at e2 s2
  generalize h2 : PlonkishM.assertZero layout.zeroWire c1 = r2 at e2 s2 hhold
  rcases r2 with ⟨u2, c2⟩
  dsimp only at e2 s2 hhold
  obtain ⟨e3, s3⟩ := constrainHornerBlsFr_sound layout.alphaWire layout.zeroWire layout.oodTerms c2
  generalize h3 : constrainHornerBlsFr layout.alphaWire layout.zeroWire layout.oodTerms c2 = r3
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
  unfold hornerBlsFr
  rw [← hz, ← hhor, heq, hmul]

end Ix.Cert.Compression.Bls12381.RecursiveKzg
