import IxVMRefinement.Nat.PrimStr
import IxVMRefinement.Nat.PrimNat
import IxVMRefinement.Lib.Words

/-! # `KernelNatPrim`: `Int` native acceleration step lemmas

Step lemmas of the twelve `Int` acceleration functions of `KernelNatPrim`, against their
registered specs in `Core/Specs/Nat.lean`:
* `try_extract_int_prim`: reads `Int.ofNat n` / `Int.negSucc n` with a readable `Nat` argument.
* `mk_int_prim`: builds `intLitExpr (intOfSignMag s m)` using `role_used_implicitly`.
* `int_add_prim`, `int_emod_prim`, `int_ediv_prim`, `int_bmod_prim`, `int_bdiv_prim`:
  pure arithmetic helpers computing the signed magnitude and calling `mk_int_prim`.
* `try_int_unop_dispatch`, `try_int_nat_arg_prim`, `try_int_int_arg_prim`,
  `try_int_binop_second`, `try_int_prim_dispatch`: dispatch all ten `Int` operations
  (`neg`, `natAbs`, `bmod`, `bdiv`, `pow`, `add`, `sub`, `mul`, `emod`, `ediv`) via
  `EnvFacts.primEqn`.
-/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red)
open NatAux

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PrimInt

/-! ## Field and sign-magnitude arithmetic helpers -/

theorem field_val_eq_nat {x : F} {k : Nat} (hk : k < 20) (h : x = (k : F)) : ZMod.val x = k := by
  subst h
  exact val_natCast (by omega)

theorem field_sub_eq {a b : F} {v : SourceValue F}
    (h : evalBinOp .sub (.field a) (.field b) = .ok v) : v = .field (a - b) :=
  NatAux.sub_ok h

theorem field_add_eq {a b : F} {v : SourceValue F}
    (h : evalBinOp .add (.field a) (.field b) = .ok v) : v = .field (a + b) :=
  NatAux.add_ok h

theorem field_mul_eq {a b : F} {v : SourceValue F}
    (h : evalBinOp .mul (.field a) (.field b) = .ok v) : v = .field (a * b) :=
  NatAux.mul_ok h

theorem field_one_add_one_sub_two : (1 : F) + 1 - 2 = 0 := by decide

theorem bit_sub_self_zero {s : F} (hs : s = 0 ∨ s = 1) : (1 - s = 0) ∨ (1 - s = 1) := by
  rcases hs with rfl | rfl <;> simp

theorem bit_mul_bit {a b : F} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    (a * b = 0) ∨ (a * b = 1) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp

theorem bit_xor_bit {a b : F} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    (a + b - 2 * a * b = 0) ∨ (a + b - 2 * a * b = 1) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [field_one_add_one_sub_two]

theorem bit_ite_zero_one (P : Prop) [Decidable P] :
    ((if P then (1 : F) else 0) = 0) ∨ ((if P then (1 : F) else 0) = 1) := by
  by_cases h : P
  · rw [ite_eq_left h]; exact .inr rfl
  · rw [ite_eq_right h]; exact .inl rfl

private theorem toLimbs {h : Heap F} {n : Nat} {v : SourceValue F} (hc : Specs.Nat.RepLimbsC h n v) :
    RepLimbs h n v :=
  RepLimbsC.toRepLimbs hc

/-- The `Int` value encoded by a sign bit `s ∈ {0, 1}` and magnitude `n`. -/
theorem intOfSignMag_zero (n : Nat) : Specs.Nat.intOfSignMag 0 n = Int.ofNat n := by
  simp [Specs.Nat.intOfSignMag]

theorem intOfSignMag_one (n : Nat) : Specs.Nat.intOfSignMag 1 n = -(Int.ofNat n) := by
  cases n with
  | zero => simp [Specs.Nat.intOfSignMag]
  | succ k => simp [Specs.Nat.intOfSignMag, one_ne_zero]; omega

theorem intOfSignMag_zero_mag (s : F) : Specs.Nat.intOfSignMag s 0 = 0 := by
  simp [Specs.Nat.intOfSignMag]

theorem intOfSignMag_negSucc (k : Nat) :
    Specs.Nat.intOfSignMag 1 (k + 1) = Int.negSucc k := by
  rw [intOfSignMag_one]
  rfl

theorem intLitExpr_of_signMag_zero (n : Nat) :
    intLitExpr (Specs.Nat.intOfSignMag 0 n) = .app (.const (.role .intOfNat) []) (Specs.Nat.natLit n) := by
  rw [intOfSignMag_zero]; rfl

theorem intLitExpr_of_signMag_one_succ (k : Nat) :
    intLitExpr (Specs.Nat.intOfSignMag 1 (k + 1)) = .app (.const (.role .intNegSucc) []) (Specs.Nat.natLit k) := by
  rw [intOfSignMag_negSucc]; rfl

theorem intOfSignMag_norm_sign (s : F) (n : Nat) (hs : s = 0 ∨ s = 1) :
    Specs.Nat.intOfSignMag (s * (1 - if n = 0 then 1 else 0)) n = Specs.Nat.intOfSignMag s n := by
  by_cases hn : n = 0
  · subst hn; simp [intOfSignMag_zero_mag]
  · rcases hs with rfl | rfl <;> simp [hn]

theorem intOfSignMag_neg (s : F) (n : Nat) (hs : s = 0 ∨ s = 1) :
    Specs.Nat.intOfSignMag ((1 - s) * (1 - if n = 0 then 1 else 0)) n =
      -(Specs.Nat.intOfSignMag s n) := by
  by_cases hn : n = 0
  · subst hn; simp [intOfSignMag_zero_mag]
  · rcases hs with rfl | rfl <;> simp [hn, intOfSignMag_zero, intOfSignMag_one]

theorem intOfSignMag_natAbs (s : F) (n : Nat) (hs : s = 0 ∨ s = 1) :
    (Specs.Nat.intOfSignMag s n).natAbs = n := by
  rcases hs with rfl | rfl
  · rw [intOfSignMag_zero]; exact Int.natAbs_natCast n
  · rw [intOfSignMag_one, Int.natAbs_neg]; exact Int.natAbs_natCast n

theorem intOfSignMag_add_same (s : F) (na nb : Nat) (hs : s = 0 ∨ s = 1) :
    Specs.Nat.intOfSignMag s (na + nb) =
      Specs.Nat.intOfSignMag s na + Specs.Nat.intOfSignMag s nb := by
  rcases hs with rfl | rfl
  · simp [intOfSignMag_zero]
  · simp [intOfSignMag_one]; omega

theorem intOfSignMag_add_diff_le {sa sb : F} {na nb : Nat}
    (hsa : sa = 0 ∨ sa = 1) (hsb : sb = 0 ∨ sb = 1) (hne : sa ≠ sb) (hle : na ≤ nb) :
    Specs.Nat.intOfSignMag sb (nb - na) =
      Specs.Nat.intOfSignMag sa na + Specs.Nat.intOfSignMag sb nb := by
  rcases hsa with rfl | rfl <;> rcases hsb with rfl | rfl
  · exact absurd rfl hne
  · simp [intOfSignMag_zero, intOfSignMag_one]; omega
  · simp [intOfSignMag_zero, intOfSignMag_one]; omega
  · exact absurd rfl hne

theorem intOfSignMag_add_diff_gt {sa sb : F} {na nb : Nat}
    (hsa : sa = 0 ∨ sa = 1) (hsb : sb = 0 ∨ sb = 1) (hne : sa ≠ sb) (hgt : ¬ na ≤ nb) :
    Specs.Nat.intOfSignMag sa (na - nb) =
      Specs.Nat.intOfSignMag sa na + Specs.Nat.intOfSignMag sb nb := by
  rcases hsa with rfl | rfl <;> rcases hsb with rfl | rfl
  · exact absurd rfl hne
  · simp [intOfSignMag_zero, intOfSignMag_one]; omega
  · simp [intOfSignMag_zero, intOfSignMag_one]; omega
  · exact absurd rfl hne

theorem intOfSignMag_mul (sa sb : F) (na nb : Nat)
    (hsa : sa = 0 ∨ sa = 1) (hsb : sb = 0 ∨ sb = 1) :
    Specs.Nat.intOfSignMag
        (((sa + sb - 2 * sa * sb) * (1 - if na = 0 then 1 else 0)) *
          (1 - if nb = 0 then 1 else 0)) (na * nb) =
      Specs.Nat.intOfSignMag sa na * Specs.Nat.intOfSignMag sb nb := by
  by_cases ha : na = 0
  · subst ha; simp [intOfSignMag_zero_mag]
  by_cases hb : nb = 0
  · subst hb; simp [intOfSignMag_zero_mag]
  rcases hsa with rfl | rfl <;> rcases hsb with rfl | rfl
  · simp [ha, hb, intOfSignMag_zero]
  · simp [ha, hb, intOfSignMag_zero, intOfSignMag_one]
  · simp [ha, hb, intOfSignMag_zero, intOfSignMag_one]
  · simp [ha, hb, field_one_add_one_sub_two, intOfSignMag_zero, intOfSignMag_one]

theorem intOfSignMag_pow (sa : F) (na nb : Nat) (hsa : sa = 0 ∨ sa = 1) :
    Specs.Nat.intOfSignMag (sa * (1 - if nb % 2 = 0 then 1 else 0)) (na ^ nb) =
      (Specs.Nat.intOfSignMag sa na) ^ nb := by
  rcases hsa with rfl | rfl
  · simp [intOfSignMag_zero]
  · by_cases hev : nb % 2 = 0
    · simp only [hev, ↓reduceIte, sub_self, mul_zero, intOfSignMag_zero, intOfSignMag_one]
      obtain ⟨k, rfl⟩ : ∃ k, nb = 2 * k := ⟨nb / 2, by omega⟩
      clear hev
      induction k with
      | zero => simp
      | succ k ih =>
        have h1 : 2 * (k + 1) = 2 * k + 2 := by omega
        rw [h1, Int.pow_succ, Int.pow_succ, Nat.pow_succ, Nat.pow_succ, ← ih]
        simp [Int.neg_mul, Int.mul_neg, Int.neg_neg, Int.natCast_mul]
    · simp only [hev, ↓reduceIte, sub_zero, mul_one, intOfSignMag_one]
      obtain ⟨k, rfl⟩ : ∃ k, nb = 2 * k + 1 := ⟨nb / 2, by omega⟩
      clear hev
      have heven : (-(Int.ofNat na)) ^ (2 * k) = Int.ofNat (na ^ (2 * k)) := by
        induction k with
        | zero => simp
        | succ k ih =>
          have h1 : 2 * (k + 1) = 2 * k + 2 := by omega
          rw [h1, Int.pow_succ, Int.pow_succ, Nat.pow_succ, Nat.pow_succ, ih]
          simp [Int.neg_mul, Int.mul_neg, Int.neg_neg, Int.natCast_mul]
      rw [Int.pow_succ, Nat.pow_succ, heven]
      simp [Int.mul_neg, Int.natCast_mul]

private theorem int_divmod_unique {a b q r : Int} (h : a = b * q + r) (hr0 : 0 ≤ r) (hrb : r < b) :
    a / b = q ∧ a % b = r := by
  have hbnz : b ≠ 0 := by omega
  have hmod : a % b = r := by
    rw [h, Int.mul_add_emod_self_left, Int.emod_eq_of_lt hr0 hrb]
  have hdiv : a / b = q := by
    rw [h, Int.mul_add_ediv_left _ _ hbnz, Int.ediv_eq_zero_of_lt hr0 hrb, Int.add_zero]
  exact ⟨hdiv, hmod⟩

private theorem int_neg_divmod {na nb : Nat} (hb : nb ≠ 0) :
    let r : Nat := if na % nb = 0 then 0 else nb - na % nb
    let q : Int := if na % nb = 0 then -(Int.ofNat (na / nb)) else -(Int.ofNat (na / nb + 1))
    (-(Int.ofNat na)) / (Int.ofNat nb) = q ∧ (-(Int.ofNat na)) % (Int.ofNat nb) = Int.ofNat r := by
  intro r q
  simp only [Int.ofNat_eq_natCast]
  have hpos : 0 < nb := Nat.pos_of_ne_zero hb
  have hdm : na = nb * (na / nb) + na % nb := (Nat.div_add_mod na nb).symm
  have hlt : na % nb < nb := Nat.mod_lt na hpos
  have hdmZ : (na : Int) = (nb : Int) * ((na / nb : Nat) : Int) + ((na % nb : Nat) : Int) := by
    exact_mod_cast hdm
  by_cases hr : na % nb = 0
  · simp only [r, q, hr, ↓reduceIte, Int.ofNat_eq_natCast]
    have hmul : -(na : Int) = (nb : Int) * (-((na / nb : Nat) : Int)) + ((0 : Nat) : Int) := by
      rw [Int.mul_neg, hdmZ, hr]; omega
    exact int_divmod_unique hmul (by omega) (by omega)
  · simp only [r, q, hr, ↓reduceIte, Int.ofNat_eq_natCast]
    have hmul : -(na : Int) =
        (nb : Int) * (-(((na / nb + 1 : Nat) : Int))) + (((nb - na % nb : Nat) : Int)) := by
      rw [Int.mul_neg]
      have h1 : (nb : Int) * (((na / nb + 1 : Nat) : Int)) =
          (nb : Int) * ((na / nb : Nat) : Int) + (nb : Int) := by
        rw [Int.natCast_add, Int.natCast_one, Int.mul_add, Int.mul_one]
      omega
    exact int_divmod_unique hmul (by omega) (by omega)

theorem intOfSignMag_emod_sign_indep (sa sb : F) (na nb : Nat)
    (hsb : sb = 0 ∨ sb = 1) :
    (Specs.Nat.intOfSignMag sa na).emod (Specs.Nat.intOfSignMag sb nb) =
      (Specs.Nat.intOfSignMag sa na).emod (Int.ofNat nb) := by
  rcases hsb with rfl | rfl
  · rw [intOfSignMag_zero]
  · rw [intOfSignMag_one]
    exact Int.emod_neg (Specs.Nat.intOfSignMag sa na) (Int.ofNat nb)

theorem intOfSignMag_emod_zero (sa : F) (na : Nat) :
    (Specs.Nat.intOfSignMag sa na).emod (Int.ofNat 0) = Specs.Nat.intOfSignMag sa na :=
  Int.emod_zero _

theorem intOfSignMag_emod_pos_neg_nz {na nb : Nat} (hb : nb ≠ 0) (hr : na % nb ≠ 0) :
    (Specs.Nat.intOfSignMag 1 na).emod (Int.ofNat nb) = Int.ofNat (nb - na % nb) := by
  rw [intOfSignMag_one]
  have h := (int_neg_divmod (na := na) hb).2
  simp only [hr, ↓reduceIte] at h
  exact h

theorem intOfSignMag_emod_pos_other {sa : F} {na nb : Nat} (hsa : sa = 0 ∨ sa = 1)
    (hb : nb ≠ 0) (hcond : sa = 0 ∨ na % nb = 0) :
    (Specs.Nat.intOfSignMag sa na).emod (Int.ofNat nb) = Int.ofNat (na % nb) := by
  rcases hcond with rfl | hr0
  · rw [intOfSignMag_zero]; rfl
  · rcases hsa with rfl | rfl
    · rw [intOfSignMag_zero]; rfl
    · rw [intOfSignMag_one]
      have h := (int_neg_divmod (na := na) hb).2
      simp only [hr0, ↓reduceIte] at h
      rw [hr0]
      exact h

theorem intOfSignMag_ediv_zero (sa sb : F) (na : Nat) :
    (Specs.Nat.intOfSignMag sa na).ediv (Specs.Nat.intOfSignMag sb 0) = 0 := by
  rw [intOfSignMag_zero_mag]
  exact Int.ediv_zero _

theorem intOfSignMag_ediv_pos {sa sb : F} {na nb : Nat}
    (hsa : sa = 0 ∨ sa = 1) (hsb : sb = 0 ∨ sb = 1) (hb : nb ≠ 0) :
    let q := if sa = 1 ∧ na % nb ≠ 0 then na / nb + 1 else na / nb
    Specs.Nat.intOfSignMag
        ((sa + sb - 2 * sa * sb) * (1 - if q = 0 then 1 else 0)) q =
      (Specs.Nat.intOfSignMag sa na).ediv (Specs.Nat.intOfSignMag sb nb) := by
  intro q
  have heq_pos : (Specs.Nat.intOfSignMag sa na).ediv (Int.ofNat nb) =
      if sa = 0 then Int.ofNat (na / nb)
      else if na % nb = 0 then -(Int.ofNat (na / nb))
      else -(Int.ofNat (na / nb + 1)) := by
    rcases hsa with rfl | rfl
    · simp [intOfSignMag_zero]; rfl
    · simp only [one_ne_zero, ↓reduceIte, intOfSignMag_one]
      exact (int_neg_divmod (na := na) hb).1
  rcases hsb with rfl | rfl
  · rw [intOfSignMag_zero, heq_pos]
    rcases hsa with rfl | rfl
    · by_cases hq : na / nb = 0 <;> simp [q, hq, intOfSignMag_zero]
    · by_cases hr : na % nb = 0
      · by_cases hq : na / nb = 0 <;> simp [q, hr, hq, intOfSignMag_zero, intOfSignMag_one]
      · simp [q, hr, intOfSignMag_one]
  · rw [intOfSignMag_one]
    have hneg : (Specs.Nat.intOfSignMag sa na).ediv (-Int.ofNat nb) =
        -((Specs.Nat.intOfSignMag sa na).ediv (Int.ofNat nb)) :=
      Int.ediv_neg (Specs.Nat.intOfSignMag sa na) (Int.ofNat nb)
    rw [hneg, heq_pos]
    rcases hsa with rfl | rfl
    · by_cases hq : na / nb = 0 <;> simp [q, hq, intOfSignMag_zero, intOfSignMag_one]
    · by_cases hr : na % nb = 0
      · by_cases hq : na / nb = 0 <;>
          simp [q, hr, hq, field_one_add_one_sub_two, intOfSignMag_zero]
      · simp [q, hr, field_one_add_one_sub_two, intOfSignMag_zero]

theorem intOfSignMag_bmod_zero (sa : F) (na : Nat) :
    (Specs.Nat.intOfSignMag sa na).bmod 0 = Specs.Nat.intOfSignMag sa na := by
  simp [Int.bmod]

private theorem int_bmod_bdiv_of_emod (x : Int) (nm r : Nat) (hm : nm ≠ 0)
    (hr_eq : x % (nm : Int) = (r : Int)) (hr_lt : r < nm) :
    (x.bmod nm = if (nm + 1) / 2 ≤ r then -(Int.ofNat (nm - r)) else Int.ofNat r) ∧
    (x.bdiv nm = if (nm + 1) / 2 ≤ r then x / (nm : Int) + 1 else x / (nm : Int)) := by
  have hdiv : ((nm : Int) + 1) / 2 = (((nm + 1) / 2 : Nat) : Int) := by omega
  constructor
  · simp only [Int.bmod, hr_eq, hdiv, Int.ofNat_eq_natCast]
    by_cases hle : (nm + 1) / 2 ≤ r
    · rw [ite_eq_right (by omega), ite_eq_left hle]; omega
    · rw [ite_eq_left (by omega), ite_eq_right hle]
  · simp only [Int.bdiv, hm, ↓reduceIte, hr_eq, hdiv]
    by_cases hle : (nm + 1) / 2 ≤ r
    · rw [ite_eq_right (by omega), ite_eq_left hle]
    · rw [ite_eq_left (by omega), ite_eq_right hle]

theorem intOfSignMag_bmod_pos {sa : F} {na nm : Nat} (hsa : sa = 0 ∨ sa = 1) (hm : nm ≠ 0) :
    let r := if sa = 1 ∧ na % nm ≠ 0 then nm - na % nm else na % nm
    (Specs.Nat.intOfSignMag sa na).bmod nm =
      if (nm + 1) / 2 ≤ r then Specs.Nat.intOfSignMag 1 (nm - r)
      else Specs.Nat.intOfSignMag 0 r := by
  intro r
  have hr_eq : (Specs.Nat.intOfSignMag sa na) % (nm : Int) = (r : Int) := by
    by_cases hc : sa = 1 ∧ na % nm ≠ 0
    · obtain ⟨hsa1, hrnz⟩ := hc
      subst hsa1
      have h := intOfSignMag_emod_pos_neg_nz (na := na) hm hrnz
      change (Specs.Nat.intOfSignMag 1 na) % (nm : Int) = Int.ofNat (nm - na % nm) at h
      simpa [r, hrnz] using h
    · have hcond : sa = 0 ∨ na % nm = 0 := by
        rcases hsa with rfl | rfl
        · exact .inl rfl
        · by_cases hz : na % nm = 0
          · exact .inr hz
          · exact absurd ⟨rfl, hz⟩ hc
      have h := intOfSignMag_emod_pos_other (na := na) hsa hm hcond
      change (Specs.Nat.intOfSignMag sa na) % (nm : Int) = Int.ofNat (na % nm) at h
      simpa [r, hc] using h
  have hr_lt : r < nm := by
    have hlt := Nat.mod_lt na (Nat.pos_of_ne_zero hm)
    by_cases hc : sa = 1 ∧ na % nm ≠ 0 <;> simp [r, hc] <;> omega
  have h := (int_bmod_bdiv_of_emod (Specs.Nat.intOfSignMag sa na) nm r hm hr_eq hr_lt).1
  rw [h, intOfSignMag_one, intOfSignMag_zero]

theorem intOfSignMag_bdiv_zero (sa : F) (na : Nat) :
    (Specs.Nat.intOfSignMag sa na).bdiv 0 = 0 := by
  simp [Int.bdiv]

theorem intOfSignMag_bdiv_pos {sa : F} {na nm : Nat} (hsa : sa = 0 ∨ sa = 1) (hm : nm ≠ 0) :
    let r := if sa = 1 ∧ na % nm ≠ 0 then nm - na % nm else na % nm
    let q := if sa = 1 ∧ na % nm ≠ 0 then na / nm + 1 else na / nm
    let qs := sa * (1 - if q = 0 then 1 else 0)
    (Specs.Nat.intOfSignMag sa na).bdiv nm =
      if (nm + 1) / 2 ≤ r then Specs.Nat.intOfSignMag qs q + 1
      else Specs.Nat.intOfSignMag qs q := by
  intro r q qs
  have hq_eq : Specs.Nat.intOfSignMag qs q = (Specs.Nat.intOfSignMag sa na) / (nm : Int) := by
    have h := intOfSignMag_ediv_pos (sa := sa) (sb := 0) (na := na) (nb := nm) hsa (.inl rfl) hm
    rw [intOfSignMag_zero] at h
    change _ = (Specs.Nat.intOfSignMag sa na) / (nm : Int) at h
    simpa [q, qs] using h
  have hr_eq : (Specs.Nat.intOfSignMag sa na) % (nm : Int) = (r : Int) := by
    by_cases hc : sa = 1 ∧ na % nm ≠ 0
    · obtain ⟨hsa1, hrnz⟩ := hc
      subst hsa1
      have h := intOfSignMag_emod_pos_neg_nz (na := na) hm hrnz
      change (Specs.Nat.intOfSignMag 1 na) % (nm : Int) = Int.ofNat (nm - na % nm) at h
      simpa [r, hrnz] using h
    · have hcond : sa = 0 ∨ na % nm = 0 := by
        rcases hsa with rfl | rfl
        · exact .inl rfl
        · by_cases hz : na % nm = 0
          · exact .inr hz
          · exact absurd ⟨rfl, hz⟩ hc
      have h := intOfSignMag_emod_pos_other (na := na) hsa hm hcond
      change (Specs.Nat.intOfSignMag sa na) % (nm : Int) = Int.ofNat (na % nm) at h
      simpa [r, hc] using h
  have hr_lt : r < nm := by
    have hlt := Nat.mod_lt na (Nat.pos_of_ne_zero hm)
    by_cases hc : sa = 1 ∧ na % nm ≠ 0 <;> simp [r, hc] <;> omega
  have h := (int_bmod_bdiv_of_emod (Specs.Nat.intOfSignMag sa na) nm r hm hr_eq hr_lt).2
  rw [h, ← hq_eq]

theorem repLimbs_nil {h m : Heap F} (hm : m = h ++ [.construct limbListEnum "Nil" []]) :
    RepLimbs m 0 (.ptr (.enum limbListEnum) h.length) := by
  subst hm
  exact ⟨[], lrep_store_nil h, rfl⟩

theorem repLimbs_one {h m1 m2 : Heap F}
    (hm1 : m1 = h ++ [.construct limbListEnum "Nil" []])
    (hm2 : m2 = m1 ++ [.construct limbListEnum "Cons"
      [.tuple [.field 1, .field 0, .field 0, .field 0, .field 0, .field 0, .field 0, .field 0],
       .ptr (.enum limbListEnum) h.length]]) :
    RepLimbs m2 1 (.ptr (.enum limbListEnum) m1.length) := by
  subst hm1 hm2
  obtain ⟨w, hw, hr⟩ := word_one (h ++ [.construct limbListEnum "Nil" []])
  exact ⟨[w], lrep_store_cons hr (lrep_store_nil h), by simp [limbsVal_cons, limbsVal_nil, hw]⟩

theorem repLimbs_two {h m1 m2 : Heap F}
    (hm1 : m1 = h ++ [.construct limbListEnum "Nil" []])
    (hm2 : m2 = m1 ++ [.construct limbListEnum "Cons"
      [.tuple [.field 2, .field 0, .field 0, .field 0, .field 0, .field 0, .field 0, .field 0],
       .ptr (.enum limbListEnum) h.length]]) :
    RepLimbs m2 2 (.ptr (.enum limbListEnum) m1.length) := by
  subst hm1 hm2
  obtain ⟨w, hw, hr⟩ := word_two (h ++ [.construct limbListEnum "Nil" []])
  exact ⟨[w], lrep_store_cons hr (lrep_store_nil h), by simp [limbsVal_cons, limbsVal_nil, hw]⟩

theorem repLimbs_pow24 {h m1 m2 : Heap F}
    (hm1 : m1 = h ++ [.construct limbListEnum "Nil" []])
    (hm2 : m2 = m1 ++ [.construct limbListEnum "Cons"
      [.tuple [.field 0, .field 0, .field 0, .field 1, .field 0, .field 0, .field 0, .field 0],
       .ptr (.enum limbListEnum) h.length]]) :
    RepLimbs m2 (2 ^ 24) (.ptr (.enum limbListEnum) m1.length) := by
  subst hm1 hm2
  obtain ⟨w, hw, hr⟩ := word_of (h ++ [.construct limbListEnum "Nil" []]) (m := 2 ^ 24) (by decide)
  have hu : TagN.u64Value (2 ^ 24) =
      .tuple [.field 0, .field 0, .field 0, .field 1, .field 0, .field 0, .field 0, .field 0] := by
    rw [PrimStrAux.u64Value_lt32 (by decide)]
    simp
  rw [hu] at hr
  exact ⟨[w], lrep_store_cons hr (lrep_store_nil h), by simp [limbsVal_cons, limbsVal_nil, hw]⟩

/-- Every `Int` primitive role has group `≥ 46`. -/
theorem intPrimOp_group_ge46 {ro : Ix.Kernel.Role} {o : Nat}
    (h : Specs.Nat.intPrimOp ro = some o) : 46 ≤ Ix.SpecDigest.groupOf ro := by
  cases ro <;> simp [Specs.Nat.intPrimOp] at h <;> decide

theorem primEqn_of_intOpAt {c : ScopedCtx} (hc : ScopedCoreBase c) {a : Bytes.Address} {o : Nat}
    (hop : Specs.Nat.IntOpAt c a o) : PrimEqnEnv c.env := by
  obtain ⟨ro, hro, _, hforce⟩ := hop
  exact hc.env.primEqn ⟨ro, intPrimOp_group_ge46 hro, hforce⟩

theorem intOpAt_key_eq {c : ScopedCtx} (hc : ScopedCoreBase c) {a : Bytes.Address} {o : Nat}
    {ro : Ix.Kernel.Role} (hro : Specs.Nat.intPrimOp ro = some o)
    (haddr : c.t.addressOf? ro = some (ixAddr a)) (hforce : c.inForce ro) :
    c.κ (ixAddr a) = .role ro := by
  have hprim := hc.env.primEqn ⟨ro, intPrimOp_group_ge46 hro, hforce⟩
  have hmem : ro ∈ [.intNeg, .intNatAbs, .intAdd, .intSub, .intMul, .intEdiv, .intEmod,
      .intPow, .intBmod, .intBdiv] := by
    cases ro <;> simp [Specs.Nat.intPrimOp] at hro <;> decide
  obtain ⟨ci, hci⟩ := hprim.intOpStored ro hmem
  have hres : c.κ (ixAddr a) ≠ unresolvedKey :=
    hc.loads.storedRes (ixAddr a) ci (by rw [keyOf_of_addressOf hc.env.tableWf haddr]; exact hci)
  exact (c.key_eq hres).trans (keyOf_of_addressOf hc.env.tableWf haddr)

/-- `Int.neg` / `Int.natAbs` codes. -/
theorem intPrimOp_eq_of_val {ro : Ix.Kernel.Role} {o : Nat}
    (h : Specs.Nat.intPrimOp ro = some o) :
    (o = 1 → ro = .intNeg) ∧ (o = 2 → ro = .intNatAbs) ∧ (o = 3 → ro = .intBmod) ∧
    (o = 4 → ro = .intBdiv) ∧ (o = 5 → ro = .intPow) ∧ (o = 6 → ro = .intAdd) ∧
    (o = 7 → ro = .intSub) ∧ (o = 8 → ro = .intMul) ∧ (o = 9 → ro = .intEmod) ∧
    (o = 10 → ro = .intEdiv) := by
  cases ro <;> simp [Specs.Nat.intPrimOp] at h <;> subst h <;> decide

theorem tag_tuple2_ne {x y : SourceValue F} :
    (Value.tuple [.field 1, x] : SourceValue F) ≠ .tuple [.field 0, y] :=
  PrimNat.tag_one_ne_zero

theorem tag_tuple3_ne {s a b c : SourceValue F} :
    (Value.tuple [.field 1, s, a] : SourceValue F) ≠ .tuple [.field 0, b, c] :=
  PrimNat.tag3_one_ne_zero

theorem is_zero_sub_field {a b : F} {v r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hop : evalBinOp .sub (.field a) (.field b) = .ok v)
    (hev : ObsFn W "Fields::is_zero" [v] h r h' cs) :
    r = .field (if a = b then 1 else 0) ∧ h' = h := by
  have hv := field_sub_eq hop
  subst hv
  obtain ⟨hr, hh⟩ := Lib.is_zero_field hev
  refine ⟨hr.trans ?_, hh⟩
  by_cases h : a = b
  · subst h; simp
  · have hne : a - b ≠ 0 := sub_ne_zero.mpr h
    simp [h, hne]

end PrimInt

/-! ## Step lemmas for the twelve `Int` functions -/

open PrimInt

/-- `KernelNatPrim::try_extract_nat_or_whnf(rc, e, types)`. -/
theorem try_extract_nat_or_whnf_step (c : ScopedCtx)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::try_extract_nat_or_whnf" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.try_extract_nat_or_whnf c args h r h' calls := by
  intro rc e types hargs good hrc d Γ htypes E hE x hr
  subst hargs
  cases Obs.«KernelNatPrim::try_extract_nat_or_whnf».obs ev with
  | n1_bind m1 cs1 x_n ev_nat he_r he_h hc_c =>
    subst hc_c he_h
    obtain rfl : x = x_n := PrimNat.tag_snd (hr.symm.trans he_r)
    exact ih.get (.nat .try_extract_nat) (by nat_lt_calls) ev_nat rc e rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ E hE x rfl
  | other v1 m1 cs1 cs3 v_w m2 cs2 ev_nat1 ev_whnf ev_nat2 hc_c =>
    subst hc_c
    have e1 := ObsFn.heap_extends ev_nat1
    obtain ⟨W₀, hW₀, hredW⟩ := ih.get (.whnf .whnf) (by nat_lt_calls) ev_whnf rc e types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ (types_mono e1 htypes) E
      (Tm.mono e1 hE)
    have e2 := e1.trans (ObsFn.heap_extends ev_whnf)
    obtain ⟨n, hlim, hredN⟩ := ih.get (.nat .try_extract_nat) (by nat_lt_calls) ev_nat2 rc v_w rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e2 hrc) d Γ W₀ hW₀ x hr
    exact ⟨n, hlim, .trans hredW hredN⟩

/-- `KernelNatPrim::try_extract_int_prim(rc, e, types)`. -/
theorem try_extract_int_prim_step (c : ScopedCtx) (hc : ScopedCoreBase c)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::try_extract_int_prim" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.try_extract_int_prim c args h r h' calls := by
  intro rc e types hargs good hrc d Γ htypes E hE sv m hr
  subst hargs
  cases Obs.«KernelNatPrim::try_extract_int_prim».obs ev with
  | App_Const_n1_n1_n1_bind x_f x_a x_caddr x_clvls m1 cs1 m3 cs3 v_ron m2 cs2 m4 cs4 x_n
      v_norm m5 cs5 ld_e ld_f ev_le ev_ron ev_ris ev_nat he_r ev_norm he_h hc_c =>
    subst hc_c he_h
    rw [he_r] at hr
    obtain ⟨rfl, rfl⟩ := PrimNat.tag3_snd hr
    obtain ⟨Ef, Ea, rfl, hf, ha⟩ := Tm.app_of_load hE ld_e
    obtain ⟨a, us, rfl, ha_addr, hus⟩ := Tm.const_of_load hf ld_f
    obtain ⟨hle, rfl⟩ := ih.get (.nat .lvls_empty) (by nat_lt_calls) ev_le x_clvls rfl
      (good.sub fun x hx => by simp [hx]) us hus
    have hus_nil : us = [] := by
      by_contra hne; rw [ite_eq_right hne] at hle; exact field_one_ne_zero hle
    subst hus_nil
    obtain ⟨hv_ron, hm2⟩ := ih.get (.roles .role_int_of_nat) (by nat_lt_calls) ev_ron rfl
    subst hv_ron hm2
    have ⟨hb_on, _⟩ := ih.get (.roles .role_is) (by nat_lt_calls) ev_ris rc x_caddr a .intOfNat rfl
      (good.sub fun x hx => by simp [hx]) hrc ha_addr field_one_ne_zero
    have e3 := ObsFn.heap_extends ev_ris
    obtain ⟨n, hlim, hredA⟩ := ih.get (.nat .try_extract_nat_or_whnf) (by nat_lt_calls) ev_nat
      rc x_a types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e3 hrc) d Γ
      (types_mono e3 htypes) Ea (Tm.mono e3 ha) x_n rfl
    have hnorm := ih.get (.nat .klimbs_normalize) (by nat_lt_calls) ev_norm x_n rfl
      (good.sub fun x hx => by simp [hx]) n (toLimbs hlim)
    have hk : c.κ (ixAddr a) = .role .intOfNat :=
      (c.key_eq (by resolve_key)).trans (keyOf_of_addressOf hc.env.tableWf hb_on)
    refine ⟨0, n, rfl, .inl rfl, fun h => absurd h zero_ne_one, hnorm, ?_⟩
    rw [intLitExpr_of_signMag_zero, hk]
    exact .appArg hredA
  | App_Const_n1_n1_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ he_r _ _ _ =>
    exact (tag_tuple3_ne (hr.symm.trans he_r)).elim
  | App_Const_n1_other_n1_n1_bind x_f x_a x_caddr x_clvls m1 cs1 v_ris1 m3 cs3 v_ron m2 cs2
      m5 cs5 v_rns m4 cs4 m6 cs6 x_n v_norm m8 cs8 v_succ m7 cs7
      ld_e ld_f ev_le ev_ron ev_ris1 hne1 ev_rns ev_ris2 ev_nat he_r ev_succ ev_norm he_h hc_c =>
    subst hc_c he_h
    rw [he_r] at hr
    obtain ⟨rfl, rfl⟩ := PrimNat.tag3_snd hr
    obtain ⟨Ef, Ea, rfl, hf, ha⟩ := Tm.app_of_load hE ld_e
    obtain ⟨a, us, rfl, ha_addr, hus⟩ := Tm.const_of_load hf ld_f
    obtain ⟨hle, rfl⟩ := ih.get (.nat .lvls_empty) (by nat_lt_calls) ev_le x_clvls rfl
      (good.sub fun x hx => by simp [hx]) us hus
    have hus_nil : us = [] := by
      by_contra hne; rw [ite_eq_right hne] at hle; exact field_one_ne_zero hle
    subst hus_nil
    obtain ⟨hv_ron, hm2⟩ := ih.get (.roles .role_int_of_nat) (by nat_lt_calls) ev_ron rfl
    subst hv_ron hm2
    have e3 := ObsFn.heap_extends ev_ris1
    obtain ⟨hv_rns, hm4⟩ := ih.get (.roles .role_int_neg_succ) (by nat_lt_calls) ev_rns rfl
    subst hv_rns hm4
    have ⟨hb_ns, _⟩ := ih.get (.roles .role_is) (by nat_lt_calls) ev_ris2 rc x_caddr a .intNegSucc rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e3 hrc)
      (Bytes.repAddressRef_heapMono₂ addrTy e3 ha_addr) field_one_ne_zero
    have e5 := e3.trans (ObsFn.heap_extends ev_ris2)
    obtain ⟨n, hlim, hredA⟩ := ih.get (.nat .try_extract_nat_or_whnf) (by nat_lt_calls) ev_nat
      rc x_a types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e5 hrc) d Γ
      (types_mono e5 htypes) Ea (Tm.mono e5 ha) x_n rfl
    have hsucc := (ih.get (.nat .klimbs_succ) (by nat_lt_calls) ev_succ x_n rfl
      (good.sub fun x hx => by simp [hx]) n).1 (toLimbs hlim)
    have hnorm := ih.get (.nat .klimbs_normalize) (by nat_lt_calls) ev_norm v_succ rfl
      (good.sub fun x hx => by simp [hx]) (n + 1) hsucc
    have hk : c.κ (ixAddr a) = .role .intNegSucc :=
      (c.key_eq (by resolve_key)).trans (keyOf_of_addressOf hc.env.tableWf hb_ns)
    refine ⟨1, n + 1, rfl, .inr rfl, fun _ => Nat.succ_pos n, hnorm, ?_⟩
    rw [intLitExpr_of_signMag_one_succ, hk]
    exact .appArg hredA
  | App_Const_n1_other_n1_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      he_r _ _ _ =>
    exact (tag_tuple3_ne (hr.symm.trans he_r)).elim
  | App_Const_n1_other_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      he_r _ _ _ =>
    exact (tag_tuple3_ne (hr.symm.trans he_r)).elim
  | App_Const_other _ _ _ _ _ _ _ _ _ _ _ _ he_r _ _ _ =>
    exact (tag_tuple3_ne (hr.symm.trans he_r)).elim
  | App_other _ _ _ _ _ _ _ he_r _ _ _ =>
    exact (tag_tuple3_ne (hr.symm.trans he_r)).elim
  | other _ _ _ _ he_r _ _ _ =>
    exact (tag_tuple3_ne (hr.symm.trans he_r)).elim

/-- `KernelNatPrim::mk_int_prim(rc, sign, magnitude)`. -/
theorem mk_int_prim_step (c : ScopedCtx) (hc : ScopedCoreBase c)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::mk_int_prim" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.mk_int_prim c args h r h' calls := by
  intro rc s mag hargs good hrc hprim hs m hm
  subst hargs
  obtain ⟨v_mag, m1, cs1, v_neg, m2, y_sub, y_iz, cs2, v_caddr, m3, cs3, v_arg, m4, cs4,
    v_lit, m5, m6, m7, cs5, ev_norm, ev_iz, op_sub, op_mul, sg_ca, sg_arg, he_r, hm_app,
    hm_const, hm_nil, ev_lit, hc_c⟩ := Obs.«KernelNatPrim::mk_int_prim».obs ev
  subst hc_c he_r
  have hmag := ih.get (.nat .klimbs_normalize) (by nat_lt_calls) ev_norm mag rfl
    (good.sub fun x hx => by simp [hx]) m hm
  have e1 := ObsFn.heap_extends ev_norm
  have hiz := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_iz v_mag rfl
    (good.sub fun x hx => by simp [hx]) m (toLimbs hmag)
  subst hiz
  have hsub := field_sub_eq op_sub
  subst hsub
  have hmul := field_mul_eq op_mul
  subst hmul
  have e2 := e1.trans (ObsFn.heap_extends ev_iz)
  have hmag2 := repLimbsC_mono (ObsFn.heap_extends ev_iz) hmag
  cases sg_ca with
  | n0 cs_u v_r m_r cs_r hv_n0 ev_r ev_u hc_u =>
    subst hc_u
    obtain ⟨hv_r, hm_r⟩ := ih.get (.roles .role_int_of_nat) (by nat_lt_calls) ev_r rfl
    subst hv_r hm_r
    obtain ⟨a, ha_m3, hb_on, _⟩ := ih.get (.roles .role_used_implicitly) (by nat_lt_calls) ev_u
      rc .intOfNat rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e2 hrc)
    cases sg_arg with
    | n0 _ he_arg he_m4 hc_arg =>
      subst hc_arg he_arg he_m4
      have hmag3 := repLimbsC_mono (ObsFn.heap_extends ev_u) hmag2
      obtain ⟨ci, hci⟩ := hprim.intOfNatStored
      have hres : c.κ (ixAddr a) ≠ unresolvedKey :=
        hc.loads.storedRes (ixAddr a) ci (by rw [keyOf_of_addressOf hc.env.tableWf hb_on]; exact hci)
      have hconst := PrimStrAux.tmc_role_const_nil hc ha_m3 hb_on hres hm_nil hm_const
      have e_mc := (PrimStrAux.ext_of_eq_snoc hm_nil).trans (PrimStrAux.ext_of_eq_snoc hm_const)
      have hlit := ih.get (.nat .mk_nat_lit) (by nat_lt_calls) ev_lit v_arg rfl
        (good.sub fun x hx => by simp [hx]) m (repLimbsC_mono e_mc hmag3)
      have happ : c.tmc h' (.app (.const (.role .intOfNat) []) (Specs.Nat.natLit m))
          (.ptr (.enum kexprEnum) m7.length) := fun d Γ =>
        PrimStrAux.tm_store_app' hm_app (Tm.mono (ObsFn.heap_extends ev_lit) (hconst d Γ)) (hlit d Γ)
      have hneg0 : s * (1 - if m = 0 then (1 : F) else 0) = 0 := Value.field.inj hv_n0
      have hint : Specs.Nat.intOfSignMag s m = Int.ofNat m := by
        rw [← intOfSignMag_norm_sign s m hs, hneg0, intOfSignMag_zero]
      rw [hint]
      exact happ
    | other _ _ _ _ hne_arg _ _ _ => exact absurd hv_n0 hne_arg
  | other cs_u v_r m_r cs_r hne_n0 ev_r ev_u hc_u =>
    subst hc_u
    obtain ⟨hv_r, hm_r⟩ := ih.get (.roles .role_int_neg_succ) (by nat_lt_calls) ev_r rfl
    subst hv_r hm_r
    obtain ⟨a, ha_m3, hb_ns, _⟩ := ih.get (.roles .role_used_implicitly) (by nat_lt_calls) ev_u
      rc .intNegSucc rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e2 hrc)
    cases sg_arg with
    | n0 hv_z _ _ _ => exact absurd hv_z hne_n0
    | other cs_n2 v_dec m_dec cs_dec _ ev_dec ev_n2 hc_arg =>
      subst hc_arg
      have hmag3 := repLimbsC_mono (ObsFn.heap_extends ev_u) hmag2
      have hdec := ih.get (.nat .klimbs_dec) (by nat_lt_calls) ev_dec v_mag rfl
        (good.sub fun x hx => by simp [hx]) m (toLimbs hmag3)
      have harg := ih.get (.nat .klimbs_normalize) (by nat_lt_calls) ev_n2 v_dec rfl
        (good.sub fun x hx => by simp [hx]) (m - 1) (toLimbs hdec)
      have e34 := (ObsFn.heap_extends ev_dec).trans (ObsFn.heap_extends ev_n2)
      obtain ⟨ci, hci⟩ := hprim.intNegSuccStored
      have hres : c.κ (ixAddr a) ≠ unresolvedKey :=
        hc.loads.storedRes (ixAddr a) ci (by rw [keyOf_of_addressOf hc.env.tableWf hb_ns]; exact hci)
      have hconst := PrimStrAux.tmc_role_const_nil hc
        (Bytes.repAddressRef_heapMono₂ addrTy e34 ha_m3) hb_ns hres hm_nil hm_const
      have e_mc := (PrimStrAux.ext_of_eq_snoc hm_nil).trans (PrimStrAux.ext_of_eq_snoc hm_const)
      have hlit := ih.get (.nat .mk_nat_lit) (by nat_lt_calls) ev_lit v_arg rfl
        (good.sub fun x hx => by simp [hx]) (m - 1) (repLimbsC_mono e_mc harg)
      have happ : c.tmc h' (.app (.const (.role .intNegSucc) []) (Specs.Nat.natLit (m - 1)))
          (.ptr (.enum kexprEnum) m7.length) := fun d Γ =>
        PrimStrAux.tm_store_app' hm_app (Tm.mono (ObsFn.heap_extends ev_lit) (hconst d Γ)) (hlit d Γ)
      have hne_f : s * (1 - if m = 0 then (1 : F) else 0) ≠ 0 :=
        fun h0 => hne_n0 (by rw [h0])
      have hs1 : s = 1 := by
        rcases hs with rfl | rfl
        · exact absurd (by simp) hne_f
        · rfl
      have hm_nz : m ≠ 0 := by
        intro h0; subst h0; exact absurd (by simp) hne_f
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := Nat.exists_eq_succ_of_ne_zero hm_nz
      rw [Nat.add_sub_cancel] at happ
      rw [hs1, intOfSignMag_negSucc]
      exact happ

/-- `KernelNatPrim::int_add_prim(rc, sa, a, sb, b)`. -/
theorem int_add_prim_step (c : ScopedCtx)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::int_add_prim" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.int_add_prim c args h r h' calls := by
  intro rc sa a sb b hargs good hrc hprim hsa hsb na nb ha hb
  subst hargs
  rcases Obs.«KernelNatPrim::int_add_prim».obs ev with
    ⟨cs_mk, v_sum, m1, cs_add, op_sub, ev_add, ev_mk, hc_c⟩ |
    ⟨v_sub, m1, cs_le, cs_mk, v_diff, m2, cs_sub, op_sub, hne_sub, ev_le, ev_sub, ev_mk, hc_c⟩ |
    ⟨v_sub, v_le, m1, cs_le, cs_mk, v_diff, m2, cs_sub, op_sub, hne_sub, ev_le, hne_le, ev_sub,
      ev_mk, hc_c⟩
  · subst hc_c
    have hs_eq : sa = sb := sub_eq_zero.mp (Value.field.inj (field_sub_eq op_sub).symm)
    subst hs_eq
    have hsum := ih.get (.nat .klimbs_add) (by nat_lt_calls) ev_add a b rfl
      (good.sub fun x hx => by simp [hx]) na nb ha hb
    have hmk := ih.get (.nat .mk_int_prim) (by nat_lt_calls) ev_mk rc sa v_sum rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono (ObsFn.heap_extends ev_add) hrc) hprim hsa
      (na + nb) hsum
    rwa [intOfSignMag_add_same sa na nb hsa] at hmk
  · subst hc_c
    have hne : sa ≠ sb := fun he => hne_sub (by rw [field_sub_eq op_sub, he, sub_self])
    have hle_f := ih.get (.nat .klimbs_le) (by nat_lt_calls) ev_le a b rfl
      (good.sub fun x hx => by simp [hx]) na nb ha hb
    have hle : na ≤ nb := by
      by_contra hlt; rw [ite_eq_right hlt] at hle_f; exact field_one_ne_zero hle_f
    have e1 := ObsFn.heap_extends ev_le
    have hsub := ih.get (.nat .klimbs_sub) (by nat_lt_calls) ev_sub b a rfl
      (good.sub fun x hx => by simp [hx]) nb na (repLimbs_mono e1 hb) (repLimbs_mono e1 ha)
    have hmk := ih.get (.nat .mk_int_prim) (by nat_lt_calls) ev_mk rc sb v_diff rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono (e1.trans (ObsFn.heap_extends ev_sub)) hrc)
      hprim hsb (nb - na) (toLimbs hsub)
    rwa [intOfSignMag_add_diff_le hsa hsb hne hle] at hmk
  · subst hc_c
    have hne : sa ≠ sb := fun he => hne_sub (by rw [field_sub_eq op_sub, he, sub_self])
    have hle_f := ih.get (.nat .klimbs_le) (by nat_lt_calls) ev_le a b rfl
      (good.sub fun x hx => by simp [hx]) na nb ha hb
    have hgt : ¬ na ≤ nb := fun hle => hne_le (by rw [hle_f, ite_eq_left hle])
    have e1 := ObsFn.heap_extends ev_le
    have hsub := ih.get (.nat .klimbs_sub) (by nat_lt_calls) ev_sub a b rfl
      (good.sub fun x hx => by simp [hx]) na nb (repLimbs_mono e1 ha) (repLimbs_mono e1 hb)
    have hmk := ih.get (.nat .mk_int_prim) (by nat_lt_calls) ev_mk rc sa v_diff rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono (e1.trans (ObsFn.heap_extends ev_sub)) hrc)
      hprim hsa (na - nb) (toLimbs hsub)
    rwa [intOfSignMag_add_diff_gt hsa hsb hne hgt] at hmk

/-- `KernelNatPrim::int_emod_prim(rc, sa, a, b)`. -/
theorem int_emod_prim_step (c : ScopedCtx)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::int_emod_prim" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.int_emod_prim c args h r h' calls := by
  intro rc sa a b hargs good hrc hprim hsa na nb ha hb
  subst hargs
  rcases Obs.«KernelNatPrim::int_emod_prim».obs ev with
    ⟨m1, cs1, cs2, ev_iz, ev_mk, hc_c⟩ |
    ⟨v_iz, m1, cs1, v_r0, m2, cs2, m3, y_s, y_r, cs3, cs4, v_diff, m4, cs5,
      ev_iz, hne_iz, ev_mod, ev_izr, op_sub, op_mul, ev_sub, ev_mk, hc_c⟩ |
    ⟨v_iz, m1, cs1, v_r0, m2, cs2, v_cond, m3, y_s, y_r, cs3, cs4,
      ev_iz, hne_iz, ev_mod, ev_izr, op_sub, op_mul, hne_c, ev_mk, hc_c⟩
  · subst hc_c
    have hiz := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_iz b rfl
      (good.sub fun x hx => by simp [hx]) nb hb
    have hb0 : nb = 0 := by
      by_contra hne; rw [ite_eq_right hne] at hiz; exact field_one_ne_zero hiz
    subst hb0
    have e1 := ObsFn.heap_extends ev_iz
    have hmk := ih.get (.nat .mk_int_prim) (by nat_lt_calls) ev_mk rc sa a rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) hprim hsa na (repLimbs_mono e1 ha)
    rwa [← intOfSignMag_emod_zero sa na] at hmk
  · subst hc_c
    have hiz := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_iz b rfl
      (good.sub fun x hx => by simp [hx]) nb hb
    have hbnz : nb ≠ 0 := fun h0 => hne_iz (by rw [hiz, ite_eq_left h0])
    have e1 := ObsFn.heap_extends ev_iz
    have hr0 := ih.get (.nat .klimbs_mod) (by nat_lt_calls) ev_mod a b rfl
      (good.sub fun x hx => by simp [hx]) na nb (repLimbs_mono e1 ha) (repLimbs_mono e1 hb)
    have e2 := e1.trans (ObsFn.heap_extends ev_mod)
    have hizr := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_izr v_r0 rfl
      (good.sub fun x hx => by simp [hx]) (na % nb) (toLimbs hr0)
    subst hizr
    have hsub1 := field_sub_eq op_sub; subst hsub1
    have hmul1 := Value.field.inj (field_mul_eq op_mul).symm
    have hsa1 : sa = 1 := by
      rcases hsa with rfl | rfl
      · simp at hmul1
      · rfl
    have hrnz : na % nb ≠ 0 := by
      intro hr; rw [hsa1, hr] at hmul1; simp at hmul1
    have e3 := e2.trans (ObsFn.heap_extends ev_izr)
    have hdiff := ih.get (.nat .klimbs_sub) (by nat_lt_calls) ev_sub b v_r0 rfl
      (good.sub fun x hx => by simp [hx]) nb (na % nb) (repLimbs_mono e3 hb)
      (repLimbs_mono (ObsFn.heap_extends ev_izr) (toLimbs hr0))
    have hmk := ih.get (.nat .mk_int_prim) (by nat_lt_calls) ev_mk rc 0 v_diff rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono (e3.trans (ObsFn.heap_extends ev_sub)) hrc)
      hprim (.inl rfl) (nb - na % nb) (toLimbs hdiff)
    rw [hsa1, intOfSignMag_emod_pos_neg_nz hbnz hrnz]
    simpa [intOfSignMag_zero] using hmk
  · subst hc_c
    have hiz := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_iz b rfl
      (good.sub fun x hx => by simp [hx]) nb hb
    have hbnz : nb ≠ 0 := fun h0 => hne_iz (by rw [hiz, ite_eq_left h0])
    have e1 := ObsFn.heap_extends ev_iz
    have hr0 := ih.get (.nat .klimbs_mod) (by nat_lt_calls) ev_mod a b rfl
      (good.sub fun x hx => by simp [hx]) na nb (repLimbs_mono e1 ha) (repLimbs_mono e1 hb)
    have e2 := e1.trans (ObsFn.heap_extends ev_mod)
    have hizr := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_izr v_r0 rfl
      (good.sub fun x hx => by simp [hx]) (na % nb) (toLimbs hr0)
    subst hizr
    have hsub1 := field_sub_eq op_sub; subst hsub1
    have hmul1 := field_mul_eq op_mul; subst hmul1
    have hcond : sa = 0 ∨ na % nb = 0 := by
      rcases hsa with rfl | rfl
      · exact .inl rfl
      · by_cases hr : na % nb = 0
        · exact .inr hr
        · exact absurd (by simp [hr]) hne_c
    have e3 := e2.trans (ObsFn.heap_extends ev_izr)
    have hmk := ih.get (.nat .mk_int_prim) (by nat_lt_calls) ev_mk rc 0 v_r0 rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e3 hrc) hprim (.inl rfl) (na % nb)
      (repLimbs_mono (ObsFn.heap_extends ev_izr) (toLimbs hr0))
    rw [intOfSignMag_emod_pos_other hsa hbnz hcond]
    simpa [intOfSignMag_zero] using hmk

/-- `KernelNatPrim::int_ediv_prim(rc, sa, a, sb, b)`. -/
theorem int_ediv_prim_step (c : ScopedCtx)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::int_ediv_prim" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.int_ediv_prim c args h r h' calls := by
  intro rc sa a sb b hargs good hrc hprim hsa hsb na nb ha hb
  subst hargs
  rcases Obs.«KernelNatPrim::int_ediv_prim».obs ev with
    ⟨m1, cs1, cs2, m2, ev_iz, hm_nil, ev_mk, hc_c⟩ |
    ⟨v_iz, m1, cs1, v_q0, m2, cs2, v_r0, m3, cs3, v_q, m4, cs4, cs5, v_qs, m5,
      x_xor, y_nz, x_sum, y_2ab, x_2a, y_izq, cs6,
      ev_iz, hne_iz, ev_div, ev_mod, sg_q, op_add, op_2a, op_2ab, op_xor, ev_izq, op_nz, op_qs,
      ev_mk, hc_c⟩
  · subst hc_c
    have hiz := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_iz b rfl
      (good.sub fun x hx => by simp [hx]) nb hb
    have hb0 : nb = 0 := by
      by_contra hne; rw [ite_eq_right hne] at hiz; exact field_one_ne_zero hiz
    subst hb0
    have e1 := (ObsFn.heap_extends ev_iz).trans (PrimStrAux.ext_of_eq_snoc hm_nil)
    have hmk := ih.get (.nat .mk_int_prim) (by nat_lt_calls) ev_mk rc 0 _ rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) hprim (.inl rfl) 0 (repLimbs_nil hm_nil)
    rw [intOfSignMag_ediv_zero sa sb na]
    simpa [intOfSignMag_zero_mag] using hmk
  · subst hc_c
    have hiz := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_iz b rfl
      (good.sub fun x hx => by simp [hx]) nb hb
    have hbnz : nb ≠ 0 := fun h0 => hne_iz (by rw [hiz, ite_eq_left h0])
    have e1 := ObsFn.heap_extends ev_iz
    have hq0 := ih.get (.nat .klimbs_div) (by nat_lt_calls) ev_div a b rfl
      (good.sub fun x hx => by simp [hx]) na nb (repLimbs_mono e1 ha) (repLimbs_mono e1 hb)
    have e2 := e1.trans (ObsFn.heap_extends ev_div)
    have hr0 := ih.get (.nat .klimbs_mod) (by nat_lt_calls) ev_mod a b rfl
      (good.sub fun x hx => by simp [hx]) na nb (repLimbs_mono e2 ha) (repLimbs_mono e2 hb)
    have e3 := e2.trans (ObsFn.heap_extends ev_mod)
    let qNat : Nat := if sa = 1 ∧ na % nb ≠ 0 then na / nb + 1 else na / nb
    have ⟨hq, e34⟩ : RepLimbs m4 qNat v_q ∧ Heap.Extends m3 m4 := by
      cases sg_q with
      | n1 m_r y_sr y_ir cs_ir cs_sq ev_ir op_sr op_mr ev_sq hc_sq =>
        subst hc_sq
        have hir := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_ir v_r0 rfl
          (good.sub fun x hx => by simp [hx]) (na % nb) (toLimbs hr0)
        subst hir
        have hsr := field_sub_eq op_sr; subst hsr
        have hmr := Value.field.inj (field_mul_eq op_mr).symm
        have hsa1 : sa = 1 := hsa.resolve_left (fun h0 => by rw [h0] at hmr; simp at hmr)
        have hrnz : na % nb ≠ 0 := by intro hr; rw [hsa1, hr] at hmr; simp at hmr
        have hsq := (ih.get (.nat .klimbs_succ) (by nat_lt_calls) ev_sq v_q0 rfl
          (good.sub fun x hx => by simp [hx]) (na / nb)).1
          (repLimbs_mono ((ObsFn.heap_extends ev_mod).trans (ObsFn.heap_extends ev_ir)) (toLimbs hq0))
        refine ⟨by simpa [qNat, hsa1, hrnz] using hsq,
          (ObsFn.heap_extends ev_ir).trans (ObsFn.heap_extends ev_sq)⟩
      | other v_c m_r y_sr y_ir cs_ir ev_ir op_sr op_mr hne_mr he_q he_m4 hc_sq =>
        subst hc_sq he_q he_m4
        have hir := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_ir v_r0 rfl
          (good.sub fun x hx => by simp [hx]) (na % nb) (toLimbs hr0)
        subst hir
        have hsr := field_sub_eq op_sr; subst hsr
        have hmr := field_mul_eq op_mr; subst hmr
        have hnot : ¬ (sa = 1 ∧ na % nb ≠ 0) := fun ⟨hs1, hrnz⟩ =>
          hne_mr (by simp [hs1, hrnz])
        refine ⟨by simpa [qNat, hnot] using repLimbs_mono ((ObsFn.heap_extends ev_mod).trans (ObsFn.heap_extends ev_ir)) (toLimbs hq0),
          ObsFn.heap_extends ev_ir⟩
    have hsum := field_add_eq op_add; subst hsum
    have h2a := field_mul_eq op_2a; subst h2a
    have h2ab := field_mul_eq op_2ab; subst h2ab
    have hxor := field_sub_eq op_xor; subst hxor
    have hizq := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_izq v_q rfl
      (good.sub fun x hx => by simp [hx]) qNat hq
    subst hizq
    have hnz := field_sub_eq op_nz; subst hnz
    have hqs := field_mul_eq op_qs; subst hqs
    have e45 := ObsFn.heap_extends ev_izq
    have hbit : ((sa + sb - 2 * sa * sb) * (1 - if qNat = 0 then (1 : F) else 0) = 0) ∨
        ((sa + sb - 2 * sa * sb) * (1 - if qNat = 0 then (1 : F) else 0) = 1) :=
      bit_mul_bit (bit_xor_bit hsa hsb) (bit_sub_self_zero (bit_ite_zero_one (qNat = 0)))
    have hmk := ih.get (.nat .mk_int_prim) (by nat_lt_calls) ev_mk rc _ v_q rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono (e3.trans (e34.trans e45)) hrc) hprim
      hbit qNat (repLimbs_mono e45 hq)
    have hed := intOfSignMag_ediv_pos (na := na) hsa hsb hbnz
    simpa [qNat, hed] using hmk

/-- `KernelNatPrim::int_bmod_prim(rc, sa, a, m)`. -/
theorem int_bmod_prim_step (c : ScopedCtx)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::int_bmod_prim" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.int_bmod_prim c args h r h' calls := by
  intro rc sa a m hargs good hrc hprim hsa na nm ha hm
  subst hargs
  rcases Obs.«KernelNatPrim::int_bmod_prim».obs ev with
    ⟨m1, cs1, cs2, ev_iz, ev_mk, hc_c⟩ |
    ⟨v_iz, m1, cs1, v_r0, m2, cs2, v_r, m3, cs3, m_two, m_nil, v_half, m4, cs4, v_m1, m5, cs5,
      m6, cs6, cs7, v_diff, m7, cs8,
      ev_iz, hne_iz, ev_mod, sg_r, hm_two, hm_nil, ev_succ, ev_div, ev_le, ev_sub, ev_mk, hc_c⟩ |
    ⟨v_iz, m1, cs1, v_r0, m2, cs2, v_r, m3, cs3, m_two, m_nil, v_half, m4, cs4, v_m1, m5, cs5,
      v_le, m6, cs6, cs7,
      ev_iz, hne_iz, ev_mod, sg_r, hm_two, hm_nil, ev_succ, ev_div, ev_le, hne_le, ev_mk, hc_c⟩
  · subst hc_c
    have hiz := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_iz m rfl
      (good.sub fun x hx => by simp [hx]) nm hm
    have hm0 : nm = 0 := by
      by_contra hne; rw [ite_eq_right hne] at hiz; exact field_one_ne_zero hiz
    subst hm0
    have e1 := ObsFn.heap_extends ev_iz
    have hmk := ih.get (.nat .mk_int_prim) (by nat_lt_calls) ev_mk rc sa a rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) hprim hsa na (repLimbs_mono e1 ha)
    rwa [← intOfSignMag_bmod_zero sa na] at hmk
  · subst hc_c
    have hiz := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_iz m rfl
      (good.sub fun x hx => by simp [hx]) nm hm
    have hmnz : nm ≠ 0 := fun h0 => hne_iz (by rw [hiz, ite_eq_left h0])
    have e1 := ObsFn.heap_extends ev_iz
    have hr0 := ih.get (.nat .klimbs_mod) (by nat_lt_calls) ev_mod a m rfl
      (good.sub fun x hx => by simp [hx]) na nm (repLimbs_mono e1 ha) (repLimbs_mono e1 hm)
    have e2 := e1.trans (ObsFn.heap_extends ev_mod)
    let rNat : Nat := if sa = 1 ∧ na % nm ≠ 0 then nm - na % nm else na % nm
    have ⟨hr, e23⟩ : RepLimbs m3 rNat v_r ∧ Heap.Extends m2 m3 := by
      cases sg_r with
      | n1 m_r y_sr y_ir cs_ir cs_sb ev_ir op_sr op_mr ev_sb hc_r =>
        subst hc_r
        have hir := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_ir v_r0 rfl
          (good.sub fun x hx => by simp [hx]) (na % nm) (toLimbs hr0)
        subst hir
        have hsr := field_sub_eq op_sr; subst hsr
        have hmr := Value.field.inj (field_mul_eq op_mr).symm
        have hsa1 : sa = 1 := hsa.resolve_left (fun h0 => by rw [h0] at hmr; simp at hmr)
        have hrnz : na % nm ≠ 0 := by intro hr; rw [hsa1, hr] at hmr; simp at hmr
        have hsb := ih.get (.nat .klimbs_sub) (by nat_lt_calls) ev_sb m v_r0 rfl
          (good.sub fun x hx => by simp [hx]) nm (na % nm)
          (repLimbs_mono (e2.trans (ObsFn.heap_extends ev_ir)) hm)
          (repLimbs_mono (ObsFn.heap_extends ev_ir) (toLimbs hr0))
        refine ⟨by simpa [rNat, hsa1, hrnz] using (toLimbs hsb),
          (ObsFn.heap_extends ev_ir).trans (ObsFn.heap_extends ev_sb)⟩
      | other v_c m_r y_sr y_ir cs_ir ev_ir op_sr op_mr hne_mr he_r he_m3 hc_r =>
        subst hc_r he_r he_m3
        have hir := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_ir v_r rfl
          (good.sub fun x hx => by simp [hx]) (na % nm) (toLimbs hr0)
        subst hir
        have hsr := field_sub_eq op_sr; subst hsr
        have hmr := field_mul_eq op_mr; subst hmr
        have hnot : ¬ (sa = 1 ∧ na % nm ≠ 0) := fun ⟨hs1, hrnz⟩ => hne_mr (by simp [hs1, hrnz])
        refine ⟨by simpa [rNat, hnot] using repLimbs_mono (ObsFn.heap_extends ev_ir) (toLimbs hr0),
          ObsFn.heap_extends ev_ir⟩
    have e3 := e2.trans e23
    have e_two := (PrimStrAux.ext_of_eq_snoc hm_nil).trans (PrimStrAux.ext_of_eq_snoc hm_two)
    have htwo : RepLimbs m_two 2 (.ptr (.enum limbListEnum) m_nil.length) :=
      repLimbs_two hm_nil hm_two
    have hm1 := (ih.get (.nat .klimbs_succ) (by nat_lt_calls) ev_succ m rfl
      (good.sub fun x hx => by simp [hx]) nm).1 (repLimbs_mono (e3.trans e_two) hm)
    have e_s := ObsFn.heap_extends ev_succ
    have hhalf := ih.get (.nat .klimbs_div) (by nat_lt_calls) ev_div v_m1 _ rfl
      (good.sub fun x hx => by simp [hx]) (nm + 1) 2 hm1 (repLimbs_mono e_s htwo)
    have e_d := ObsFn.heap_extends ev_div
    have hle_f := ih.get (.nat .klimbs_le) (by nat_lt_calls) ev_le v_half v_r rfl
      (good.sub fun x hx => by simp [hx]) ((nm + 1) / 2) rNat (toLimbs hhalf)
      (repLimbs_mono (e_two.trans (e_s.trans e_d)) hr)
    have hle : (nm + 1) / 2 ≤ rNat := by
      by_contra hlt; rw [ite_eq_right hlt] at hle_f; exact field_one_ne_zero hle_f
    have e4 := e3.trans (e_two.trans (e_s.trans (e_d.trans (ObsFn.heap_extends ev_le))))
    have hdiff := ih.get (.nat .klimbs_sub) (by nat_lt_calls) ev_sub m v_r rfl
      (good.sub fun x hx => by simp [hx]) nm rNat (repLimbs_mono e4 hm)
      (repLimbs_mono (e_two.trans (e_s.trans (e_d.trans (ObsFn.heap_extends ev_le)))) hr)
    have hmk := ih.get (.nat .mk_int_prim) (by nat_lt_calls) ev_mk rc 1 v_diff rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono (e4.trans (ObsFn.heap_extends ev_sub)) hrc)
      hprim (.inr rfl) (nm - rNat) (toLimbs hdiff)
    have hbm := intOfSignMag_bmod_pos (na := na) hsa hmnz
    simpa [rNat, hle, hbm] using hmk
  · subst hc_c
    have hiz := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_iz m rfl
      (good.sub fun x hx => by simp [hx]) nm hm
    have hmnz : nm ≠ 0 := fun h0 => hne_iz (by rw [hiz, ite_eq_left h0])
    have e1 := ObsFn.heap_extends ev_iz
    have hr0 := ih.get (.nat .klimbs_mod) (by nat_lt_calls) ev_mod a m rfl
      (good.sub fun x hx => by simp [hx]) na nm (repLimbs_mono e1 ha) (repLimbs_mono e1 hm)
    have e2 := e1.trans (ObsFn.heap_extends ev_mod)
    let rNat : Nat := if sa = 1 ∧ na % nm ≠ 0 then nm - na % nm else na % nm
    have ⟨hr, e23⟩ : RepLimbs m3 rNat v_r ∧ Heap.Extends m2 m3 := by
      cases sg_r with
      | n1 m_r y_sr y_ir cs_ir cs_sb ev_ir op_sr op_mr ev_sb hc_r =>
        subst hc_r
        have hir := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_ir v_r0 rfl
          (good.sub fun x hx => by simp [hx]) (na % nm) (toLimbs hr0)
        subst hir
        have hsr := field_sub_eq op_sr; subst hsr
        have hmr := Value.field.inj (field_mul_eq op_mr).symm
        have hsa1 : sa = 1 := hsa.resolve_left (fun h0 => by rw [h0] at hmr; simp at hmr)
        have hrnz : na % nm ≠ 0 := by intro hr; rw [hsa1, hr] at hmr; simp at hmr
        have hsb := ih.get (.nat .klimbs_sub) (by nat_lt_calls) ev_sb m v_r0 rfl
          (good.sub fun x hx => by simp [hx]) nm (na % nm)
          (repLimbs_mono (e2.trans (ObsFn.heap_extends ev_ir)) hm)
          (repLimbs_mono (ObsFn.heap_extends ev_ir) (toLimbs hr0))
        refine ⟨by simpa [rNat, hsa1, hrnz] using (toLimbs hsb),
          (ObsFn.heap_extends ev_ir).trans (ObsFn.heap_extends ev_sb)⟩
      | other v_c m_r y_sr y_ir cs_ir ev_ir op_sr op_mr hne_mr he_r he_m3 hc_r =>
        subst hc_r he_r he_m3
        have hir := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_ir v_r rfl
          (good.sub fun x hx => by simp [hx]) (na % nm) (toLimbs hr0)
        subst hir
        have hsr := field_sub_eq op_sr; subst hsr
        have hmr := field_mul_eq op_mr; subst hmr
        have hnot : ¬ (sa = 1 ∧ na % nm ≠ 0) := fun ⟨hs1, hrnz⟩ => hne_mr (by simp [hs1, hrnz])
        refine ⟨by simpa [rNat, hnot] using repLimbs_mono (ObsFn.heap_extends ev_ir) (toLimbs hr0),
          ObsFn.heap_extends ev_ir⟩
    have e3 := e2.trans e23
    have e_two := (PrimStrAux.ext_of_eq_snoc hm_nil).trans (PrimStrAux.ext_of_eq_snoc hm_two)
    have htwo : RepLimbs m_two 2 (.ptr (.enum limbListEnum) m_nil.length) :=
      repLimbs_two hm_nil hm_two
    have hm1 := (ih.get (.nat .klimbs_succ) (by nat_lt_calls) ev_succ m rfl
      (good.sub fun x hx => by simp [hx]) nm).1 (repLimbs_mono (e3.trans e_two) hm)
    have e_s := ObsFn.heap_extends ev_succ
    have hhalf := ih.get (.nat .klimbs_div) (by nat_lt_calls) ev_div v_m1 _ rfl
      (good.sub fun x hx => by simp [hx]) (nm + 1) 2 hm1 (repLimbs_mono e_s htwo)
    have e_d := ObsFn.heap_extends ev_div
    have hle_f := ih.get (.nat .klimbs_le) (by nat_lt_calls) ev_le v_half v_r rfl
      (good.sub fun x hx => by simp [hx]) ((nm + 1) / 2) rNat (toLimbs hhalf)
      (repLimbs_mono (e_two.trans (e_s.trans e_d)) hr)
    have hnle : ¬ (nm + 1) / 2 ≤ rNat := fun hle => hne_le (by rw [hle_f, ite_eq_left hle])
    have e4 := e3.trans (e_two.trans (e_s.trans (e_d.trans (ObsFn.heap_extends ev_le))))
    have hmk := ih.get (.nat .mk_int_prim) (by nat_lt_calls) ev_mk rc 0 v_r rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e4 hrc) hprim (.inl rfl) rNat
      (repLimbs_mono (e_two.trans (e_s.trans (e_d.trans (ObsFn.heap_extends ev_le)))) hr)
    have hbm := intOfSignMag_bmod_pos (na := na) hsa hmnz
    simpa [rNat, hnle, hbm] using hmk

/-- `KernelNatPrim::int_bdiv_prim(rc, sa, a, m)`. -/
theorem int_bdiv_prim_step (c : ScopedCtx)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::int_bdiv_prim" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.int_bdiv_prim c args h r h' calls := by
  intro rc sa a m hargs good hrc hprim hsa na nm ha hm
  subst hargs
  rcases Obs.«KernelNatPrim::int_bdiv_prim».obs ev with
    ⟨m1, cs1, cs2, m2, ev_iz, hm_nil, ev_mk, hc_c⟩ |
    ⟨v_iz, m1, cs1, v_r0, m2, cs2, v_r, m3, cs3, v_q0, m4, cs4, v_q, m5, cs5, v_qs, m6,
      y_nz, y_izq, cs6, m_two, m_nil2, v_half, m7, cs7, v_m1, m8, cs8, m9, cs9, cs10,
      ev_iz, hne_iz, ev_mod, sg_r, ev_div, sg_q, ev_izq, op_nz, op_qs, hm_two, hm_nil2,
      ev_succ, ev_div2, ev_le, ev_mk, hc_c⟩ |
    ⟨v_iz, m1, cs1, v_r0, m2, cs2, v_r, m3, cs3, v_q0, m4, cs4, v_q, m5, cs5, v_qs, m6,
      y_nz, y_izq, cs6, m_two, m_nil2, v_half, m7, cs7, v_m1, m8, cs8, v_le, m9, cs9, cs10,
      m_one, m_nil1,
      ev_iz, hne_iz, ev_mod, sg_r, ev_div, sg_q, ev_izq, op_nz, op_qs, hm_two, hm_nil2,
      ev_succ, ev_div2, ev_le, hne_le, hm_one, hm_nil1, ev_add, hc_c⟩
  · subst hc_c
    have hiz := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_iz m rfl
      (good.sub fun x hx => by simp [hx]) nm hm
    have hm0 : nm = 0 := by
      by_contra hne; rw [ite_eq_right hne] at hiz; exact field_one_ne_zero hiz
    subst hm0
    have e1 := (ObsFn.heap_extends ev_iz).trans (PrimStrAux.ext_of_eq_snoc hm_nil)
    have hmk := ih.get (.nat .mk_int_prim) (by nat_lt_calls) ev_mk rc 0 _ rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) hprim (.inl rfl) 0 (repLimbs_nil hm_nil)
    rw [intOfSignMag_bdiv_zero sa na]
    simpa [intOfSignMag_zero_mag] using hmk
  · subst hc_c
    have hiz := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_iz m rfl
      (good.sub fun x hx => by simp [hx]) nm hm
    have hmnz : nm ≠ 0 := fun h0 => hne_iz (by rw [hiz, ite_eq_left h0])
    have e1 := ObsFn.heap_extends ev_iz
    have hr0 := ih.get (.nat .klimbs_mod) (by nat_lt_calls) ev_mod a m rfl
      (good.sub fun x hx => by simp [hx]) na nm (repLimbs_mono e1 ha) (repLimbs_mono e1 hm)
    have e2 := e1.trans (ObsFn.heap_extends ev_mod)
    let rNat : Nat := if sa = 1 ∧ na % nm ≠ 0 then nm - na % nm else na % nm
    let qNat : Nat := if sa = 1 ∧ na % nm ≠ 0 then na / nm + 1 else na / nm
    have ⟨hr, e23⟩ : RepLimbs m3 rNat v_r ∧ Heap.Extends m2 m3 := by
      cases sg_r with
      | n1 m_r y_sr y_ir cs_ir cs_sb ev_ir op_sr op_mr ev_sb hc_r =>
        subst hc_r
        have hir := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_ir v_r0 rfl
          (good.sub fun x hx => by simp [hx]) (na % nm) (toLimbs hr0)
        subst hir
        have hsr := field_sub_eq op_sr; subst hsr
        have hmr := Value.field.inj (field_mul_eq op_mr).symm
        have hsa1 : sa = 1 := hsa.resolve_left (fun h0 => by rw [h0] at hmr; simp at hmr)
        have hrnz : na % nm ≠ 0 := by intro hr; rw [hsa1, hr] at hmr; simp at hmr
        have hsb := ih.get (.nat .klimbs_sub) (by nat_lt_calls) ev_sb m v_r0 rfl
          (good.sub fun x hx => by simp [hx]) nm (na % nm)
          (repLimbs_mono (e2.trans (ObsFn.heap_extends ev_ir)) hm)
          (repLimbs_mono (ObsFn.heap_extends ev_ir) (toLimbs hr0))
        refine ⟨by simpa [rNat, hsa1, hrnz] using (toLimbs hsb),
          (ObsFn.heap_extends ev_ir).trans (ObsFn.heap_extends ev_sb)⟩
      | other v_c m_r y_sr y_ir cs_ir ev_ir op_sr op_mr hne_mr he_r he_m3 hc_r =>
        subst hc_r he_r he_m3
        have hir := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_ir v_r rfl
          (good.sub fun x hx => by simp [hx]) (na % nm) (toLimbs hr0)
        subst hir
        have hsr := field_sub_eq op_sr; subst hsr
        have hmr := field_mul_eq op_mr; subst hmr
        have hnot : ¬ (sa = 1 ∧ na % nm ≠ 0) := fun ⟨hs1, hrnz⟩ => hne_mr (by simp [hs1, hrnz])
        refine ⟨by simpa [rNat, hnot] using repLimbs_mono (ObsFn.heap_extends ev_ir) (toLimbs hr0),
          ObsFn.heap_extends ev_ir⟩
    have e3 := e2.trans e23
    have hq0 := ih.get (.nat .klimbs_div) (by nat_lt_calls) ev_div a m rfl
      (good.sub fun x hx => by simp [hx]) na nm (repLimbs_mono e3 ha) (repLimbs_mono e3 hm)
    have e34 := ObsFn.heap_extends ev_div
    have ⟨hq, e45⟩ : RepLimbs m5 qNat v_q ∧ Heap.Extends m4 m5 := by
      cases sg_q with
      | n1 m_r y_sr y_ir cs_ir cs_sq ev_ir op_sr op_mr ev_sq hc_q =>
        subst hc_q
        have hir := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_ir v_r0 rfl
          (good.sub fun x hx => by simp [hx]) (na % nm) (repLimbs_mono (e23.trans e34) (toLimbs hr0))
        subst hir
        have hsr := field_sub_eq op_sr; subst hsr
        have hmr := Value.field.inj (field_mul_eq op_mr).symm
        have hsa1 : sa = 1 := hsa.resolve_left (fun h0 => by rw [h0] at hmr; simp at hmr)
        have hrnz : na % nm ≠ 0 := by intro hr; rw [hsa1, hr] at hmr; simp at hmr
        have hsq := (ih.get (.nat .klimbs_succ) (by nat_lt_calls) ev_sq v_q0 rfl
          (good.sub fun x hx => by simp [hx]) (na / nm)).1
          (repLimbs_mono (ObsFn.heap_extends ev_ir) (toLimbs hq0))
        refine ⟨by simpa [qNat, hsa1, hrnz] using hsq,
          (ObsFn.heap_extends ev_ir).trans (ObsFn.heap_extends ev_sq)⟩
      | other v_c m_r y_sr y_ir cs_ir ev_ir op_sr op_mr hne_mr he_q he_m5 hc_q =>
        subst hc_q he_q he_m5
        have hir := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_ir v_r0 rfl
          (good.sub fun x hx => by simp [hx]) (na % nm) (repLimbs_mono (e23.trans e34) (toLimbs hr0))
        subst hir
        have hsr := field_sub_eq op_sr; subst hsr
        have hmr := field_mul_eq op_mr; subst hmr
        have hnot : ¬ (sa = 1 ∧ na % nm ≠ 0) := fun ⟨hs1, hrnz⟩ => hne_mr (by simp [hs1, hrnz])
        refine ⟨by simpa [qNat, hnot] using repLimbs_mono (ObsFn.heap_extends ev_ir) (toLimbs hq0),
          ObsFn.heap_extends ev_ir⟩
    have hizq := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_izq v_q rfl
      (good.sub fun x hx => by simp [hx]) qNat hq
    subst hizq
    have hnz := field_sub_eq op_nz; subst hnz
    have hqs := field_mul_eq op_qs; subst hqs
    have e56 := ObsFn.heap_extends ev_izq
    have e_two := (PrimStrAux.ext_of_eq_snoc hm_nil2).trans (PrimStrAux.ext_of_eq_snoc hm_two)
    have htwo : RepLimbs m_two 2 (.ptr (.enum limbListEnum) m_nil2.length) :=
      repLimbs_two hm_nil2 hm_two
    have e3_two := e34.trans (e45.trans (e56.trans e_two))
    have hm1 := (ih.get (.nat .klimbs_succ) (by nat_lt_calls) ev_succ m rfl
      (good.sub fun x hx => by simp [hx]) nm).1 (repLimbs_mono (e3.trans e3_two) hm)
    have e_s := ObsFn.heap_extends ev_succ
    have hhalf := ih.get (.nat .klimbs_div) (by nat_lt_calls) ev_div2 v_m1 _ rfl
      (good.sub fun x hx => by simp [hx]) (nm + 1) 2 hm1 (repLimbs_mono e_s htwo)
    have e_d := ObsFn.heap_extends ev_div2
    have hle_f := ih.get (.nat .klimbs_le) (by nat_lt_calls) ev_le v_half v_r rfl
      (good.sub fun x hx => by simp [hx]) ((nm + 1) / 2) rNat (toLimbs hhalf)
      (repLimbs_mono (e3_two.trans (e_s.trans e_d)) hr)
    have hnle : ¬ (nm + 1) / 2 ≤ rNat := by
      intro hle; rw [ite_eq_left hle] at hle_f; exact field_one_ne_zero hle_f.symm
    have e5_9 := e56.trans (e_two.trans (e_s.trans (e_d.trans (ObsFn.heap_extends ev_le))))
    have hbit : (sa * (1 - if qNat = 0 then (1 : F) else 0) = 0) ∨
        (sa * (1 - if qNat = 0 then (1 : F) else 0) = 1) :=
      bit_mul_bit hsa (bit_sub_self_zero (bit_ite_zero_one (qNat = 0)))
    have hmk := ih.get (.nat .mk_int_prim) (by nat_lt_calls) ev_mk rc _ v_q rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono (e3.trans (e34.trans (e45.trans e5_9))) hrc)
      hprim hbit qNat (repLimbs_mono e5_9 hq)
    have hbd := intOfSignMag_bdiv_pos (na := na) hsa hmnz
    simpa [rNat, qNat, hnle, hbd] using hmk
  · subst hc_c
    have hiz := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_iz m rfl
      (good.sub fun x hx => by simp [hx]) nm hm
    have hmnz : nm ≠ 0 := fun h0 => hne_iz (by rw [hiz, ite_eq_left h0])
    have e1 := ObsFn.heap_extends ev_iz
    have hr0 := ih.get (.nat .klimbs_mod) (by nat_lt_calls) ev_mod a m rfl
      (good.sub fun x hx => by simp [hx]) na nm (repLimbs_mono e1 ha) (repLimbs_mono e1 hm)
    have e2 := e1.trans (ObsFn.heap_extends ev_mod)
    let rNat : Nat := if sa = 1 ∧ na % nm ≠ 0 then nm - na % nm else na % nm
    let qNat : Nat := if sa = 1 ∧ na % nm ≠ 0 then na / nm + 1 else na / nm
    have ⟨hr, e23⟩ : RepLimbs m3 rNat v_r ∧ Heap.Extends m2 m3 := by
      cases sg_r with
      | n1 m_r y_sr y_ir cs_ir cs_sb ev_ir op_sr op_mr ev_sb hc_r =>
        subst hc_r
        have hir := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_ir v_r0 rfl
          (good.sub fun x hx => by simp [hx]) (na % nm) (toLimbs hr0)
        subst hir
        have hsr := field_sub_eq op_sr; subst hsr
        have hmr := Value.field.inj (field_mul_eq op_mr).symm
        have hsa1 : sa = 1 := hsa.resolve_left (fun h0 => by rw [h0] at hmr; simp at hmr)
        have hrnz : na % nm ≠ 0 := by intro hr; rw [hsa1, hr] at hmr; simp at hmr
        have hsb := ih.get (.nat .klimbs_sub) (by nat_lt_calls) ev_sb m v_r0 rfl
          (good.sub fun x hx => by simp [hx]) nm (na % nm)
          (repLimbs_mono (e2.trans (ObsFn.heap_extends ev_ir)) hm)
          (repLimbs_mono (ObsFn.heap_extends ev_ir) (toLimbs hr0))
        refine ⟨by simpa [rNat, hsa1, hrnz] using (toLimbs hsb),
          (ObsFn.heap_extends ev_ir).trans (ObsFn.heap_extends ev_sb)⟩
      | other v_c m_r y_sr y_ir cs_ir ev_ir op_sr op_mr hne_mr he_r he_m3 hc_r =>
        subst hc_r he_r he_m3
        have hir := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_ir v_r rfl
          (good.sub fun x hx => by simp [hx]) (na % nm) (toLimbs hr0)
        subst hir
        have hsr := field_sub_eq op_sr; subst hsr
        have hmr := field_mul_eq op_mr; subst hmr
        have hnot : ¬ (sa = 1 ∧ na % nm ≠ 0) := fun ⟨hs1, hrnz⟩ => hne_mr (by simp [hs1, hrnz])
        refine ⟨by simpa [rNat, hnot] using repLimbs_mono (ObsFn.heap_extends ev_ir) (toLimbs hr0),
          ObsFn.heap_extends ev_ir⟩
    have e3 := e2.trans e23
    have hq0 := ih.get (.nat .klimbs_div) (by nat_lt_calls) ev_div a m rfl
      (good.sub fun x hx => by simp [hx]) na nm (repLimbs_mono e3 ha) (repLimbs_mono e3 hm)
    have e34 := ObsFn.heap_extends ev_div
    have ⟨hq, e45⟩ : RepLimbs m5 qNat v_q ∧ Heap.Extends m4 m5 := by
      cases sg_q with
      | n1 m_r y_sr y_ir cs_ir cs_sq ev_ir op_sr op_mr ev_sq hc_q =>
        subst hc_q
        have hir := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_ir v_r0 rfl
          (good.sub fun x hx => by simp [hx]) (na % nm) (repLimbs_mono (e23.trans e34) (toLimbs hr0))
        subst hir
        have hsr := field_sub_eq op_sr; subst hsr
        have hmr := Value.field.inj (field_mul_eq op_mr).symm
        have hsa1 : sa = 1 := hsa.resolve_left (fun h0 => by rw [h0] at hmr; simp at hmr)
        have hrnz : na % nm ≠ 0 := by intro hr; rw [hsa1, hr] at hmr; simp at hmr
        have hsq := (ih.get (.nat .klimbs_succ) (by nat_lt_calls) ev_sq v_q0 rfl
          (good.sub fun x hx => by simp [hx]) (na / nm)).1
          (repLimbs_mono (ObsFn.heap_extends ev_ir) (toLimbs hq0))
        refine ⟨by simpa [qNat, hsa1, hrnz] using hsq,
          (ObsFn.heap_extends ev_ir).trans (ObsFn.heap_extends ev_sq)⟩
      | other v_c m_r y_sr y_ir cs_ir ev_ir op_sr op_mr hne_mr he_q he_m5 hc_q =>
        subst hc_q he_q he_m5
        have hir := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_ir v_r0 rfl
          (good.sub fun x hx => by simp [hx]) (na % nm) (repLimbs_mono (e23.trans e34) (toLimbs hr0))
        subst hir
        have hsr := field_sub_eq op_sr; subst hsr
        have hmr := field_mul_eq op_mr; subst hmr
        have hnot : ¬ (sa = 1 ∧ na % nm ≠ 0) := fun ⟨hs1, hrnz⟩ => hne_mr (by simp [hs1, hrnz])
        refine ⟨by simpa [qNat, hnot] using repLimbs_mono (ObsFn.heap_extends ev_ir) (toLimbs hq0),
          ObsFn.heap_extends ev_ir⟩
    have hizq := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_izq v_q rfl
      (good.sub fun x hx => by simp [hx]) qNat hq
    subst hizq
    have hnz := field_sub_eq op_nz; subst hnz
    have hqs := field_mul_eq op_qs; subst hqs
    have e56 := ObsFn.heap_extends ev_izq
    have e_two := (PrimStrAux.ext_of_eq_snoc hm_nil2).trans (PrimStrAux.ext_of_eq_snoc hm_two)
    have htwo : RepLimbs m_two 2 (.ptr (.enum limbListEnum) m_nil2.length) :=
      repLimbs_two hm_nil2 hm_two
    have e3_two := e34.trans (e45.trans (e56.trans e_two))
    have hm1 := (ih.get (.nat .klimbs_succ) (by nat_lt_calls) ev_succ m rfl
      (good.sub fun x hx => by simp [hx]) nm).1 (repLimbs_mono (e3.trans e3_two) hm)
    have e_s := ObsFn.heap_extends ev_succ
    have hhalf := ih.get (.nat .klimbs_div) (by nat_lt_calls) ev_div2 v_m1 _ rfl
      (good.sub fun x hx => by simp [hx]) (nm + 1) 2 hm1 (repLimbs_mono e_s htwo)
    have e_d := ObsFn.heap_extends ev_div2
    have hle_f := ih.get (.nat .klimbs_le) (by nat_lt_calls) ev_le v_half v_r rfl
      (good.sub fun x hx => by simp [hx]) ((nm + 1) / 2) rNat (toLimbs hhalf)
      (repLimbs_mono (e3_two.trans (e_s.trans e_d)) hr)
    have hle : (nm + 1) / 2 ≤ rNat := by
      by_contra hlt; exact hne_le (by rw [hle_f, ite_eq_right hlt])
    have e_one := (PrimStrAux.ext_of_eq_snoc hm_nil1).trans (PrimStrAux.ext_of_eq_snoc hm_one)
    have hone : RepLimbs m_one 1 (.ptr (.enum limbListEnum) m_nil1.length) :=
      repLimbs_one hm_nil1 hm_one
    have e5_one := e56.trans (e_two.trans (e_s.trans (e_d.trans ((ObsFn.heap_extends ev_le).trans e_one))))
    have hbit : (sa * (1 - if qNat = 0 then (1 : F) else 0) = 0) ∨
        (sa * (1 - if qNat = 0 then (1 : F) else 0) = 1) :=
      bit_mul_bit hsa (bit_sub_self_zero (bit_ite_zero_one (qNat = 0)))
    have hadd := ih.get (.nat .int_add_prim) (by nat_lt_calls) ev_add rc _ v_q 0 _ rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono (e3.trans (e34.trans (e45.trans e5_one))) hrc)
      hprim hbit (.inl rfl) qNat 1 (repLimbs_mono e5_one hq) hone
    have hbd := intOfSignMag_bdiv_pos (na := na) hsa hmnz
    simpa [rNat, qNat, hle, hbd, intOfSignMag_zero] using hadd

/-- `KernelNatPrim::try_int_unop_dispatch(rc, op, a0, post, types)`. -/
theorem try_int_unop_dispatch_step (c : ScopedCtx) (hc : ScopedCoreBase c)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::try_int_unop_dispatch" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.try_int_unop_dispatch c args h r h' calls := by
  intro rc o a0 post types hargs good hrc ho headAddr hop d Γ htypes A₀ Ps hA₀ hPs t x hr ht
  subst hargs
  rcases Obs.«KernelNatPrim::try_int_unop_dispatch».obs ev with
    ⟨v_w0, m1, cs1, m2, cs2, x_s, x_a, v_res, m3, cs3, v_out, m4, cs4,
      ev_whnf, ev_ext, sg_op, he_r, ev_app, he_h, hc_c⟩ |
    ⟨_, _, _, _, _, _, _, _, _, he_r, _, _, _⟩
  · subst hc_c he_h
    rw [he_r] at hr
    obtain rfl : x = v_out := PrimNat.tag_snd hr.symm
    obtain ⟨W₀, hW₀, hred0⟩ := ih.get (.whnf .whnf) (by nat_lt_calls) ev_whnf rc a0 types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A₀ hA₀
    have e1 := ObsFn.heap_extends ev_whnf
    obtain ⟨s, na, rfl, hs, _, hna, hred1⟩ := ih.get (.nat .try_extract_int_prim) (by nat_lt_calls)
      ev_ext rc v_w0 types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ
      (types_mono e1 htypes) W₀ hW₀ x_s x_a rfl
    have e2 := e1.trans (ObsFn.heap_extends ev_ext)
    have hprim := primEqn_of_intOpAt hc hop
    obtain ⟨ro, hro, haddr, hforce⟩ := hop
    have hkey := intOpAt_key_eq hc hro haddr hforce
    cases sg_op with
    | n2 cs_lit hv2 ev_lit hc_s =>
      subst hc_s
      have ho2 : ZMod.val o = 2 := field_val_eq_nat (by omega) (Value.field.inj hv2)
      obtain rfl : ro = .intNatAbs := (intPrimOp_eq_of_val hro).2.1 ho2
      have hlit := ih.get (.nat .mk_nat_lit) (by nat_lt_calls) ev_lit x_a rfl
        (good.sub fun x hx => by simp [hx]) na hna
      have e3 := e2.trans (ObsFn.heap_extends ev_lit)
      have happ := ih.get (.nat .np_apply_spine) (by nat_lt_calls) ev_app v_res post rfl
        (good.sub fun x hx => by simp [hx]) d Γ (Specs.Nat.natLit na) Ps (hlit d Γ) (TmL.mono e3 hPs)
      refine ⟨Ix.Kernel.Expr.mkAppN (Specs.Nat.natLit na) Ps, happ, ?_⟩
      rw [hkey]
      have hstep : Red c.env d (.app (.const (.role .intNatAbs) []) (intLitExpr (Specs.Nat.intOfSignMag s na)))
          (Specs.Nat.natLit na) := by
        simpa [intOfSignMag_natAbs s na hs] using hprim.intNatAbs d (Specs.Nat.intOfSignMag s na)
      exact PrimNat.red_mkAppN Ps (.trans (.appArg (.trans hred0 hred1)) hstep)
    | other cs_mk v_ns m_iz x_1s y_nz y_iz cs_iz hne2 op_1s ev_iz op_nz op_ns ev_mk hc_s =>
      subst hc_s
      have ho1 : ZMod.val o = 1 := by
        rcases ho with h1 | h2
        · exact h1
        · exfalso
          apply hne2
          have h2' : ((ZMod.val o : Nat) : F) = (2 : F) := by rw [h2]; norm_num
          rw [ZMod.natCast_zmod_val] at h2'
          exact congrArg Value.field h2'
      obtain rfl : ro = .intNeg := (intPrimOp_eq_of_val hro).1 ho1
      have h1s := field_sub_eq op_1s; subst h1s
      have hiz := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_iz x_a rfl
        (good.sub fun x hx => by simp [hx]) na (toLimbs hna)
      subst hiz
      have hnz := field_sub_eq op_nz; subst hnz
      have hns := field_mul_eq op_ns; subst hns
      have e_iz := ObsFn.heap_extends ev_iz
      have hbit := bit_mul_bit (bit_sub_self_zero hs)
        (bit_sub_self_zero (bit_ite_zero_one (na = 0)))
      have hmk := ih.get (.nat .mk_int_prim) (by nat_lt_calls) ev_mk rc _ x_a rfl
        (good.sub fun x hx => by simp [hx]) (RCRep.mono (e2.trans e_iz) hrc) hprim hbit na
        (repLimbs_mono e_iz (toLimbs hna))
      have e3 := e2.trans (e_iz.trans (ObsFn.heap_extends ev_mk))
      rw [intOfSignMag_neg s na hs] at hmk
      have happ := ih.get (.nat .np_apply_spine) (by nat_lt_calls) ev_app v_res post rfl
        (good.sub fun x hx => by simp [hx]) d Γ (intLitExpr (-(Specs.Nat.intOfSignMag s na))) Ps
        (hmk d Γ) (TmL.mono e3 hPs)
      refine ⟨Ix.Kernel.Expr.mkAppN (intLitExpr (-(Specs.Nat.intOfSignMag s na))) Ps, happ, ?_⟩
      rw [hkey]
      exact PrimNat.red_mkAppN Ps (.trans (.appArg (.trans hred0 hred1))
        (hprim.intNeg d (Specs.Nat.intOfSignMag s na)))
  · exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht

/-- `KernelNatPrim::try_int_nat_arg_prim(rc, op, sa, a, b)`. -/
theorem try_int_nat_arg_prim_step (c : ScopedCtx) (hc : ScopedCoreBase c)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::try_int_nat_arg_prim" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.try_int_nat_arg_prim c args h r h' calls := by
  intro rc o sa a b hargs good hrc hprim hsa na nb ha hb headAddr hop x hr
  subst hargs
  obtain ⟨ro, hro, haddr, hforce⟩ := hop
  have hkey := intOpAt_key_eq hc hro haddr hforce
  rcases Obs.«KernelNatPrim::try_int_nat_arg_prim».obs ev with
    ⟨v_res, m1, cs1, hv3, he_r, ev_bmod, he_h, hc_c⟩ |
    ⟨v_res, m1, cs1, _, hv4, he_r, ev_bdiv, he_h, hc_c⟩ |
    ⟨m_cap, m_nilc, m1, cs1, m_two, m_nil2, v_odd, m2, y_ev, cs2, v_mod, m3, cs3,
      v_res, m4, cs4, v_rs, v_pow, m5, cs5,
      _, _, hv5, hm_cap, hm_nilc, ev_le, hm_two, hm_nil2, ev_mod, ev_iz, op_odd,
      he_r, op_rs, ev_pow, ev_mk, he_h, hc_c⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, he_r, _, _, _⟩ |
    ⟨_, _, _, _, he_r, _, _, _⟩
  · -- `Int.bmod`
    subst hc_c he_h
    obtain rfl : x = v_res := PrimNat.tag_snd (hr.symm.trans he_r)
    have ho3 : ZMod.val o = 3 := field_val_eq_nat (by omega) (Value.field.inj hv3)
    obtain rfl : ro = .intBmod := (intPrimOp_eq_of_val hro).2.2.1 ho3
    have hbm := ih.get (.nat .int_bmod_prim) (by nat_lt_calls) ev_bmod rc sa a b rfl
      (good.sub fun x hx => by simp [hx]) hrc hprim hsa na nb ha hb
    exact ⟨_, hbm, fun d => by rw [hkey]; exact hprim.intBmod d _ _⟩
  · -- `Int.bdiv`
    subst hc_c he_h
    obtain rfl : x = v_res := PrimNat.tag_snd (hr.symm.trans he_r)
    have ho4 : ZMod.val o = 4 := field_val_eq_nat (by omega) (Value.field.inj hv4)
    obtain rfl : ro = .intBdiv := (intPrimOp_eq_of_val hro).2.2.2.1 ho4
    have hbd := ih.get (.nat .int_bdiv_prim) (by nat_lt_calls) ev_bdiv rc sa a b rfl
      (good.sub fun x hx => by simp [hx]) hrc hprim hsa na nb ha hb
    exact ⟨_, hbd, fun d => by rw [hkey]; exact hprim.intBdiv d _ _⟩
  · -- `Int.pow` (`nb ≤ 2^24`)
    subst hc_c he_h
    obtain rfl : x = v_res := PrimNat.tag_snd (hr.symm.trans he_r)
    have ho5 : ZMod.val o = 5 := field_val_eq_nat (by omega) (Value.field.inj hv5)
    obtain rfl : ro = .intPow := (intPrimOp_eq_of_val hro).2.2.2.2.1 ho5
    have e_cap := (PrimStrAux.ext_of_eq_snoc hm_nilc).trans (PrimStrAux.ext_of_eq_snoc hm_cap)
    have hcap : RepLimbs m_cap (2 ^ 24) (.ptr (.enum limbListEnum) m_nilc.length) :=
      repLimbs_pow24 hm_nilc hm_cap
    have hle_f := ih.get (.nat .klimbs_le) (by nat_lt_calls) ev_le b _ rfl
      (good.sub fun x hx => by simp [hx]) nb (2 ^ 24) (repLimbs_mono e_cap hb) hcap
    have hle : nb ≤ 2 ^ 24 := by
      by_contra hgt; rw [ite_eq_right hgt] at hle_f; exact field_one_ne_zero hle_f
    have e1 := e_cap.trans (ObsFn.heap_extends ev_le)
    have e_two := (PrimStrAux.ext_of_eq_snoc hm_nil2).trans (PrimStrAux.ext_of_eq_snoc hm_two)
    have htwo : RepLimbs m_two 2 (.ptr (.enum limbListEnum) m_nil2.length) :=
      repLimbs_two hm_nil2 hm_two
    have hmod := ih.get (.nat .klimbs_mod) (by nat_lt_calls) ev_mod b _ rfl
      (good.sub fun x hx => by simp [hx]) nb 2 (repLimbs_mono (e1.trans e_two) hb) htwo
    have hiz := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_iz v_mod rfl
      (good.sub fun x hx => by simp [hx]) (nb % 2) (toLimbs hmod)
    subst hiz
    have hodd := field_sub_eq op_odd; subst hodd
    have hrs := field_mul_eq op_rs; subst hrs
    have e2 := e1.trans (e_two.trans ((ObsFn.heap_extends ev_mod).trans (ObsFn.heap_extends ev_iz)))
    have hpow := ih.get (.nat .klimbs_pow) (by nat_lt_calls) ev_pow a b rfl
      (good.sub fun x hx => by simp [hx]) na nb (repLimbs_mono e2 ha) (repLimbs_mono e2 hb)
    have hbit := bit_mul_bit hsa (bit_sub_self_zero (bit_ite_zero_one (nb % 2 = 0)))
    have hmk := ih.get (.nat .mk_int_prim) (by nat_lt_calls) ev_mk rc _ v_pow rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono (e2.trans (ObsFn.heap_extends ev_pow)) hrc)
      hprim hbit (na ^ nb) hpow
    rw [intOfSignMag_pow sa na nb hsa] at hmk
    exact ⟨_, hmk, fun d => by rw [hkey]; exact hprim.intPow d _ _ hle⟩
  · exact (tag_tuple2_ne (hr.symm.trans he_r)).elim
  · exact (tag_tuple2_ne (hr.symm.trans he_r)).elim

/-- `KernelNatPrim::try_int_int_arg_prim(rc, op, sa, a, sb, b)`. -/
theorem try_int_int_arg_prim_step (c : ScopedCtx) (hc : ScopedCoreBase c)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::try_int_int_arg_prim" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.try_int_int_arg_prim c args h r h' calls := by
  intro rc o sa a sb b hargs good hrc hprim hsa hsb na nb ha hb headAddr hop x hr
  subst hargs
  obtain ⟨ro, hro, haddr, hforce⟩ := hop
  have hkey := intOpAt_key_eq hc hro haddr hforce
  rcases Obs.«KernelNatPrim::try_int_int_arg_prim».obs ev with
    ⟨v_res, m1, cs1, hv6, he_r, ev_add, he_h, hc_c⟩ |
    ⟨v_res, m1, cs1, v_nsb, m2, x_1sb, y_nz, y_iz, cs2, _, hv7, he_r, op_1sb, ev_iz, op_nz, op_nsb,
      ev_add, he_h, hc_c⟩ |
    ⟨v_res, m1, cs1, v_rs, v_mul, m2, x_1, y_2, m3, x_xor, y_1, x_sum, y_2ab, x_2a, y_iza, cs2,
      y_izb, cs3, m4, cs4, _, _, hv8, he_r, op_sum, op_2a, op_2ab, op_xor, ev_iza, op_nza, op_t1,
      ev_izb, op_nzb, op_rs, ev_mul, ev_mk, he_h, hc_c⟩ |
    ⟨v_res, m1, cs1, _, _, _, hv9, he_r, ev_emod, he_h, hc_c⟩ |
    ⟨v_res, m1, cs1, _, _, _, _, hv10, he_r, ev_ediv, he_h, hc_c⟩ |
    ⟨_, _, _, _, _, _, he_r, _, _, _⟩
  · -- `Int.add`
    subst hc_c he_h
    obtain rfl : x = v_res := PrimNat.tag_snd (hr.symm.trans he_r)
    have ho6 : ZMod.val o = 6 := field_val_eq_nat (by omega) (Value.field.inj hv6)
    obtain rfl : ro = .intAdd := (intPrimOp_eq_of_val hro).2.2.2.2.2.1 ho6
    have hadd := ih.get (.nat .int_add_prim) (by nat_lt_calls) ev_add rc sa a sb b rfl
      (good.sub fun x hx => by simp [hx]) hrc hprim hsa hsb na nb ha hb
    exact ⟨_, hadd, fun d => by rw [hkey]; exact hprim.intAdd d _ _⟩
  · -- `Int.sub`
    subst hc_c he_h
    obtain rfl : x = v_res := PrimNat.tag_snd (hr.symm.trans he_r)
    have ho7 : ZMod.val o = 7 := field_val_eq_nat (by omega) (Value.field.inj hv7)
    obtain rfl : ro = .intSub := (intPrimOp_eq_of_val hro).2.2.2.2.2.2.1 ho7
    have h1sb := field_sub_eq op_1sb; subst h1sb
    have hiz := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_iz b rfl
      (good.sub fun x hx => by simp [hx]) nb hb
    subst hiz
    have hnz := field_sub_eq op_nz; subst hnz
    have hnsb := field_mul_eq op_nsb; subst hnsb
    have e1 := ObsFn.heap_extends ev_iz
    have hbit := bit_mul_bit (bit_sub_self_zero hsb)
      (bit_sub_self_zero (bit_ite_zero_one (nb = 0)))
    have hadd := ih.get (.nat .int_add_prim) (by nat_lt_calls) ev_add rc sa a _ b rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) hprim hsa hbit na nb
      (repLimbs_mono e1 ha) (repLimbs_mono e1 hb)
    rw [intOfSignMag_neg sb nb hsb, ← Int.sub_eq_add_neg] at hadd
    exact ⟨_, hadd, fun d => by rw [hkey]; exact hprim.intSub d _ _⟩
  · -- `Int.mul`
    subst hc_c he_h
    obtain rfl : x = v_res := PrimNat.tag_snd (hr.symm.trans he_r)
    have ho8 : ZMod.val o = 8 := field_val_eq_nat (by omega) (Value.field.inj hv8)
    obtain rfl : ro = .intMul := (intPrimOp_eq_of_val hro).2.2.2.2.2.2.2.1 ho8
    have hsum := field_add_eq op_sum; subst hsum
    have h2a := field_mul_eq op_2a; subst h2a
    have h2ab := field_mul_eq op_2ab; subst h2ab
    have hxor := field_sub_eq op_xor; subst hxor
    have hiza := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_iza a rfl
      (good.sub fun x hx => by simp [hx]) na ha
    subst hiza
    have hnza := field_sub_eq op_nza; subst hnza
    have ht1 := field_mul_eq op_t1; subst ht1
    have e1 := ObsFn.heap_extends ev_iza
    have hizb := ih.get (.nat .klimbs_is_zero) (by nat_lt_calls) ev_izb b rfl
      (good.sub fun x hx => by simp [hx]) nb (repLimbs_mono e1 hb)
    subst hizb
    have hnzb := field_sub_eq op_nzb; subst hnzb
    have hrs := field_mul_eq op_rs; subst hrs
    have e2 := e1.trans (ObsFn.heap_extends ev_izb)
    have hmul := ih.get (.nat .klimbs_mul) (by nat_lt_calls) ev_mul a b rfl
      (good.sub fun x hx => by simp [hx]) na nb (repLimbs_mono e2 ha) (repLimbs_mono e2 hb)
    have hbit := bit_mul_bit
      (bit_mul_bit (bit_xor_bit hsa hsb) (bit_sub_self_zero (bit_ite_zero_one (na = 0))))
      (bit_sub_self_zero (bit_ite_zero_one (nb = 0)))
    have hmk := ih.get (.nat .mk_int_prim) (by nat_lt_calls) ev_mk rc _ v_mul rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono (e2.trans (ObsFn.heap_extends ev_mul)) hrc)
      hprim hbit (na * nb) hmul
    rw [intOfSignMag_mul sa sb na nb hsa hsb] at hmk
    exact ⟨_, hmk, fun d => by rw [hkey]; exact hprim.intMul d _ _⟩
  · -- `Int.emod`
    subst hc_c he_h
    obtain rfl : x = v_res := PrimNat.tag_snd (hr.symm.trans he_r)
    have ho9 : ZMod.val o = 9 := field_val_eq_nat (by omega) (Value.field.inj hv9)
    obtain rfl : ro = .intEmod := (intPrimOp_eq_of_val hro).2.2.2.2.2.2.2.2.1 ho9
    have hem := ih.get (.nat .int_emod_prim) (by nat_lt_calls) ev_emod rc sa a b rfl
      (good.sub fun x hx => by simp [hx]) hrc hprim hsa na nb ha hb
    rw [← intOfSignMag_emod_sign_indep sa sb na nb hsb] at hem
    exact ⟨_, hem, fun d => by rw [hkey]; exact hprim.intEmod d _ _⟩
  · -- `Int.ediv`
    subst hc_c he_h
    obtain rfl : x = v_res := PrimNat.tag_snd (hr.symm.trans he_r)
    have ho10 : ZMod.val o = 10 := field_val_eq_nat (by omega) (Value.field.inj hv10)
    obtain rfl : ro = .intEdiv := (intPrimOp_eq_of_val hro).2.2.2.2.2.2.2.2.2 ho10
    have hed := ih.get (.nat .int_ediv_prim) (by nat_lt_calls) ev_ediv rc sa a sb b rfl
      (good.sub fun x hx => by simp [hx]) hrc hprim hsa hsb na nb ha hb
    exact ⟨_, hed, fun d => by rw [hkey]; exact hprim.intEdiv d _ _⟩
  · exact (tag_tuple2_ne (hr.symm.trans he_r)).elim

/-- `KernelNatPrim::try_int_binop_second(rc, op, a1, post, types, sa, a)`. -/
theorem try_int_binop_second_step (c : ScopedCtx) (hc : ScopedCoreBase c)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::try_int_binop_second" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.try_int_binop_second c args h r h' calls := by
  intro rc o a1 post types sa a hargs good hrc hsa headAddr hop d Γ htypes A₀ A₁ Ps na ha
    hred0 hA₁ hPs t x hr ht
  subst hargs
  have hprim := primEqn_of_intOpAt hc hop
  rcases Obs.«KernelNatPrim::try_int_binop_second».obs ev with
    ⟨v_w1, m1, cs1, m2, x_34, y_5, m3, x_3, y_4, m4, cs_z3, v_d3, cs_z4, v_d4, cs_z5, v_d5,
      m5, cs_ext, x_sb, x_b, m6, cs_op, x_v, v_out, m7, cs_app,
      ev_whnf, op_d3, ev_z3, op_d4, ev_z4, op_34, op_d5, ev_z5, op_345,
      ev_ext, ev_op, he_r, ev_app, he_h, hc_c⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, he_r, _, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, he_r, _, _, _⟩ |
    ⟨v_w1, m1, cs1, v_sum, m2, x_34, y_5, m3, x_3, y_4, m4, cs_z3, v_d3, cs_z4, v_d4, cs_z5, v_d5,
      m5, cs_ext, x_b, m6, cs_op, v_bn, m7, cs_norm, x_v, v_out, m8, cs_app,
      ev_whnf, op_d3, ev_z3, op_d4, ev_z4, op_34, op_d5, ev_z5, op_345, hne_sum,
      ev_ext, ev_norm, ev_op, he_r, ev_app, he_h, hc_c⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _, he_r, _, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, he_r, _, _, _⟩
  · -- `Int × Int` op
    subst hc_c he_h
    rw [he_r] at hr
    obtain rfl : x = v_out := PrimNat.tag_snd hr.symm
    obtain ⟨W₁, hW₁, hred1⟩ := ih.get (.whnf .whnf) (by nat_lt_calls) ev_whnf rc a1 types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A₁ hA₁
    have e1 := ObsFn.heap_extends ev_whnf
    obtain ⟨_, hm4⟩ := is_zero_sub_field op_d3 ev_z3; subst hm4
    obtain ⟨_, hm3⟩ := is_zero_sub_field op_d4 ev_z4; subst hm3
    obtain ⟨_, hm2⟩ := is_zero_sub_field op_d5 ev_z5; subst hm2
    obtain ⟨sb, nb, rfl, hsb, _, hnb, hred1'⟩ := ih.get (.nat .try_extract_int_prim) (by nat_lt_calls)
      ev_ext rc v_w1 types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ
      (types_mono e1 htypes) W₁ hW₁ x_sb x_b rfl
    have e2 := e1.trans (ObsFn.heap_extends ev_ext)
    obtain ⟨E', hE', hredOp⟩ := ih.get (.nat .try_int_int_arg_prim) (by nat_lt_calls) ev_op
      rc o sa a sb x_b rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e2 hrc) hprim hsa hsb
      na nb (repLimbs_mono e2 ha) (toLimbs hnb) headAddr hop x_v rfl
    have e3 := e2.trans (ObsFn.heap_extends ev_op)
    have happ := ih.get (.nat .np_apply_spine) (by nat_lt_calls) ev_app x_v post rfl
      (good.sub fun x hx => by simp [hx]) d Γ E' Ps (hE' d Γ) (TmL.mono e3 hPs)
    refine ⟨Ix.Kernel.Expr.mkAppN E' Ps, happ, ?_⟩
    have h2 : Red c.env d
        (.app (.app (.const (c.κ (ixAddr headAddr)) []) A₀) A₁) E' :=
      .trans (.appFn (.appArg hred0)) (.trans (.appArg (.trans hred1 hred1')) (hredOp d))
    exact PrimNat.red_mkAppN Ps h2
  · exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht
  · exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht
  · -- `Int × Nat` op
    subst hc_c he_h
    rw [he_r] at hr
    obtain rfl : x = v_out := PrimNat.tag_snd hr.symm
    obtain ⟨W₁, hW₁, hred1⟩ := ih.get (.whnf .whnf) (by nat_lt_calls) ev_whnf rc a1 types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A₁ hA₁
    have e1 := ObsFn.heap_extends ev_whnf
    obtain ⟨_, hm4⟩ := is_zero_sub_field op_d3 ev_z3; subst hm4
    obtain ⟨_, hm3⟩ := is_zero_sub_field op_d4 ev_z4; subst hm3
    obtain ⟨_, hm2⟩ := is_zero_sub_field op_d5 ev_z5; subst hm2
    obtain ⟨nb, hnb, hred1'⟩ := ih.get (.nat .try_extract_nat) (by nat_lt_calls) ev_ext rc v_w1 rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ W₁ hW₁ x_b rfl
    have e2 := e1.trans (ObsFn.heap_extends ev_ext)
    have hnbn := ih.get (.nat .klimbs_normalize) (by nat_lt_calls) ev_norm x_b rfl
      (good.sub fun x hx => by simp [hx]) nb (toLimbs hnb)
    have e3 := e2.trans (ObsFn.heap_extends ev_norm)
    obtain ⟨E', hE', hredOp⟩ := ih.get (.nat .try_int_nat_arg_prim) (by nat_lt_calls) ev_op
      rc o sa a v_bn rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e3 hrc) hprim hsa
      na nb (repLimbs_mono e3 ha) (toLimbs hnbn) headAddr hop x_v rfl
    have e4 := e3.trans (ObsFn.heap_extends ev_op)
    have happ := ih.get (.nat .np_apply_spine) (by nat_lt_calls) ev_app x_v post rfl
      (good.sub fun x hx => by simp [hx]) d Γ E' Ps (hE' d Γ) (TmL.mono e4 hPs)
    refine ⟨Ix.Kernel.Expr.mkAppN E' Ps, happ, ?_⟩
    have h2 : Red c.env d
        (.app (.app (.const (c.κ (ixAddr headAddr)) []) A₀) A₁) E' :=
      .trans (.appFn (.appArg hred0)) (.trans (.appArg (.trans hred1 hred1')) (hredOp d))
    exact PrimNat.red_mkAppN Ps h2
  · exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht
  · exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht

/-- `KernelNatPrim::try_int_prim_dispatch(rc, op, spine, types)`. -/
theorem try_int_prim_dispatch_step (c : ScopedCtx)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::try_int_prim_dispatch" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.try_int_prim_dispatch c args h r h' calls := by
  intro rc o sp types hargs good hrc headAddr hop d Γ htypes As hAs t x hr ht
  subst hargs
  rcases Obs.«KernelNatPrim::try_int_prim_dispatch».obs ev with
    ⟨_, _, he_r, _, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he_r, _, _, _⟩ |
    ⟨x_a0, x_rest0, m2, x_z1, y_z2, m1, cs_z1, v_d1, cs_z2, v_d2, x_a1, x_post,
      v_w0, m3, cs_w0, m4, cs_ext, x_sa, x_a, cs_bin,
      ld_sp, op_d1, ev_z1, op_d2, ev_z2, op_add, ld_rest, ev_w0, ev_ext, ev_bin, hc_c⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, he_r, _, _, _⟩ |
    ⟨x_a0, x_rest0, v_sum, m2, x_z1, y_z2, m1, cs_z1, v_d1, cs_z2, v_d2, cs_un,
      ld_sp, op_d1, ev_z1, op_d2, ev_z2, op_add, hne_sum, ev_un, hc_c⟩
  · exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht
  · exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht
  · -- binary `Int` op
    subst hc_c
    obtain ⟨A₀, rest, rfl, hA₀, hrest⟩ := RepList.cons_of_load hAs ld_sp
    obtain ⟨_, hm1⟩ := is_zero_sub_field op_d1 ev_z1; subst hm1
    obtain ⟨_, hm2⟩ := is_zero_sub_field op_d2 ev_z2; subst hm2
    obtain ⟨A₁, Ps, rfl, hA₁, hPs⟩ := RepList.cons_of_load hrest ld_rest
    obtain ⟨W₀, hW₀, hred0⟩ := ih.get (.whnf .whnf) (by nat_lt_calls) ev_w0 rc x_a0 types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A₀ hA₀
    have e1 := ObsFn.heap_extends ev_w0
    obtain ⟨sa, na, rfl, hsa, _, hna, hred0'⟩ := ih.get (.nat .try_extract_int_prim) (by nat_lt_calls)
      ev_ext rc v_w0 types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ
      (types_mono e1 htypes) W₀ hW₀ x_sa x_a rfl
    have e2 := e1.trans (ObsFn.heap_extends ev_ext)
    exact ih.get (.nat .try_int_binop_second) (by nat_lt_calls) ev_bin rc o x_a1 x_post types sa x_a rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e2 hrc) hsa headAddr hop d Γ
      (types_mono e2 htypes) A₀ A₁ Ps na (toLimbs hna) (.trans hred0 hred0') (Tm.mono e2 hA₁)
      (TmL.mono e2 hPs) t x hr ht
  · exact absurd (PrimNat.tag_eq_zero (hr.symm.trans he_r)) ht
  · -- unary `Int` op (`o = 1` or `o = 2`)
    subst hc_c
    obtain ⟨A₀, Ps, rfl, hA₀, hPs⟩ := RepList.cons_of_load hAs ld_sp
    obtain ⟨hz1, hm1⟩ := is_zero_sub_field op_d1 ev_z1; subst hm1 hz1
    obtain ⟨hz2, hm2⟩ := is_zero_sub_field op_d2 ev_z2; subst hm2 hz2
    have hsum := field_add_eq op_add; subst hsum
    have ho12 : ZMod.val o = 1 ∨ ZMod.val o = 2 := by
      by_cases h1 : o = 1
      · exact .inl (field_val_eq_nat (by omega) h1)
      · by_cases h2 : o = 2
        · exact .inr (field_val_eq_nat (by omega) h2)
        · exact absurd (by simp [h1, h2]) hne_sum
    exact ih.get (.nat .try_int_unop_dispatch) (by nat_lt_calls) ev_un rc o x_a0 x_rest0 types rfl
      (good.sub fun x hx => by simp [hx]) hrc ho12 headAddr hop d Γ htypes A₀ Ps hA₀ hPs t x hr ht

end IxVM.Refinement.Core
