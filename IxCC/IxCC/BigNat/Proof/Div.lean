import IxCC.BigNat.Div
import IxCC.BigNat.Proof.InvDiv

/-! # Layer-1 Proofs for `IxCC.BigNat.Div` (`IxCC.BigNat.Proof.Div`)

Formal correctness and canonical normal-form preservation for:
- Single-limb division (`divMod1` via Möller–Granlund `divMod1Inv`)
- Knuth's Algorithm D multi-limb division (`divMod`, `div`, `mod`), including
  Möller–Granlund `trialQhatInv` / `knuthLoopInv`, fused 1-carry `subMulCarryLoop`,
  O(1) `divQuick1` fast path, Knuth's Theorem B (`q_true ≤ q̂ ≤ q_true + 1`), and
  exact correctness of the rare `q̂ - 1` add-back step.

All theorems depend strictly on `[propext, Classical.choice, Quot.sound]`.
-/

namespace IxCC.BigNat

/-! ### Fast Single-Limb Division (`divMod1`) -/

theorem wf_divMod1 (a : Array UInt64) (d : UInt64) : WF (divMod1 a d).1 :=
  wf_divMod1Inv a d

theorem divMod1_spec (a : Array UInt64) (d : UInt64) (hd : d ≠ 0) :
    WF (divMod1 a d).1 ∧
    toNat (divMod1 a d).1 = toNat a / d.toNat ∧
    (divMod1 a d).2.toNat = toNat a % d.toNat ∧
    (divMod1 a d).2 < d :=
  divMod1Inv_spec a d hd

theorem toNat_divMod1_lt (a : Array UInt64) (d : UInt64) (ha : WF a) (hsz : a.size ≠ 0)
    (hd : 1 < d.toNat) :
    toNat (divMod1 a d).1 < toNat a := by
  have hdne : d ≠ 0 := fun hz => by subst hz; simp at hd
  have ⟨_, hdiv, _, _⟩ := divMod1_spec a d hdne
  rw [hdiv]
  exact Nat.div_lt_self (toNat_pos_of_ne_zero a ha hsz) hd

/-! ### Knuth Algorithm D: Trial Quotient Refinement and Theorem B -/

private theorem cmpWideGt_iff (hi1 lo1 hi2 lo2 : UInt64) :
    cmpWideGt hi1 lo1 hi2 lo2 = true ↔
      hi2.toNat * 2 ^ 64 + lo2.toNat < hi1.toNat * 2 ^ 64 + lo1.toNat := by
  unfold cmpWideGt
  have hlo1 : lo1.toNat < 2 ^ 64 := uint64_toNat_lt lo1
  have hlo2 : lo2.toNat < 2 ^ 64 := uint64_toNat_lt lo2
  constructor
  · intro h
    rcases Bool.or_eq_true_iff.mp h with hhi | hboth
    · have hlt : hi2.toNat < hi1.toNat := UInt64.lt_iff_toNat_lt.mp (of_decide_eq_true hhi)
      have h1 : (hi2.toNat + 1) * 2 ^ 64 ≤ hi1.toNat * 2 ^ 64 := Nat.mul_le_mul_right _ hlt
      omega
    · rcases Bool.and_eq_true_iff.mp hboth with ⟨heq, hlo⟩
      have h1 : hi1 = hi2 := eq_of_beq heq
      have h2 : lo2.toNat < lo1.toNat := UInt64.lt_iff_toNat_lt.mp (of_decide_eq_true hlo)
      rw [h1]
      omega
  · intro hlt
    rw [Bool.or_eq_true_iff]
    by_cases hhi : hi2.toNat < hi1.toNat
    · left
      exact decide_eq_true (UInt64.lt_iff_toNat_lt.mpr hhi)
    · right
      rw [Bool.and_eq_true_iff]
      have hnotgt : ¬ hi1.toNat < hi2.toNat := by
        intro hgt
        have h1 : (hi1.toNat + 1) * 2 ^ 64 ≤ hi2.toNat * 2 ^ 64 := Nat.mul_le_mul_right _ hgt
        omega
      have heqN : hi1.toNat = hi2.toNat := by omega
      have heq : hi1 = hi2 := UInt64.toNat_inj.mp heqN
      have hlo : lo2.toNat < lo1.toNat := by omega
      exact ⟨beq_iff_eq.mpr heq, decide_eq_true (UInt64.lt_iff_toNat_lt.mpr hlo)⟩

private theorem refine_upper_arith {B q v1 v2 r u2 u1 u0 : Nat}
    (heq : q * v1 + r = u2 * B + u1) (hle : q * v2 ≤ r * B + u0) :
    q * (v1 * B + v2) ≤ u2 * (B * B) + u1 * B + u0 := by
  have hm := congrArg (· * B) heq
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc] at hm ⊢
  omega

private theorem refine_lower_arith {B Q q v1 v2 r u2 u1 u0 : Nat}
    (heq : q * v1 + r = u2 * B + u1) (hgt : r * B + u0 < q * v2)
    (hQ : Q * (v1 * B + v2) ≤ u2 * (B * B) + u1 * B + u0) :
    Q ≤ q - 1 := by
  have hm := congrArg (· * B) heq
  simp only [Nat.add_mul, Nat.mul_assoc] at hm
  have hgtQ : u2 * (B * B) + u1 * B + u0 < q * (v1 * B + v2) := by
    simp only [Nat.mul_add]
    omega
  have hltQ : Q < q := by
    apply Classical.byContradiction; intro hge
    have hle' : q * (v1 * B + v2) ≤ Q * (v1 * B + v2) := Nat.mul_le_mul_right _ (by omega)
    omega
  omega

private theorem refineQhat_spec (qh rh vn1 vn2 u0 u2 u1 : UInt64)
    (hnorm : 2 ^ 63 ≤ vn1.toNat)
    (heq : qh.toNat * vn1.toNat + rh.toNat = u2.toNat * 2 ^ 64 + u1.toNat) :
    let qhat := refineQhat qh rh vn1 vn2 u0
    qhat.toNat * (vn1.toNat * 2 ^ 64 + vn2.toNat) ≤
      u2.toNat * (2 ^ 64 * 2 ^ 64) + u1.toNat * 2 ^ 64 + u0.toNat ∧
    ∀ Q : Nat, Q ≤ qh.toNat →
      Q * (vn1.toNat * 2 ^ 64 + vn2.toNat) ≤
        u2.toNat * (2 ^ 64 * 2 ^ 64) + u1.toNat * 2 ^ 64 + u0.toNat →
      Q ≤ qhat.toNat := by
  unfold refineQhat
  have hmul0 := mulWide64_spec qh vn2
  rcases hm0 : mulWide64 qh vn2 with ⟨pLo, pHi⟩
  rw [hm0] at hmul0
  dsimp only at hmul0 ⊢
  cases hcmp1 : cmpWideGt pHi pLo rh u0
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hle1 : qh.toNat * vn2.toNat ≤ rh.toNat * 2 ^ 64 + u0.toNat := by
      apply Classical.byContradiction; intro hgt
      have htrue := (cmpWideGt_iff pHi pLo rh u0).mpr (by omega)
      rw [hcmp1] at htrue
      exact Bool.false_ne_true htrue
    exact ⟨refine_upper_arith heq hle1, fun Q hQ _ => hQ⟩
  · simp only [↓reduceIte]
    have hgt1 : rh.toNat * 2 ^ 64 + u0.toNat < qh.toNat * vn2.toNat := by
      have := (cmpWideGt_iff pHi pLo rh u0).mp hcmp1
      omega
    have hqh_pos : 1 ≤ qh.toNat := by
      apply Classical.byContradiction; intro h0
      have hz : qh.toNat = 0 := by omega
      rw [hz, Nat.zero_mul] at hgt1
      omega
    have hqh1_toNat : (qh - 1).toNat = qh.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; exact hqh_pos)]
      rfl
    have hQ_lt1 : ∀ Q : Nat,
        Q * (vn1.toNat * 2 ^ 64 + vn2.toNat) ≤
          u2.toNat * (2 ^ 64 * 2 ^ 64) + u1.toNat * 2 ^ 64 + u0.toNat →
        Q ≤ (qh - 1).toNat := by
      intro Q hQineq
      rw [hqh1_toNat]
      exact refine_lower_arith heq hgt1 hQineq
    have hadd1 := addCarry64_spec rh vn1 false
    rcases ha1 : addCarry64 rh vn1 false with ⟨rh1, ov1⟩
    rw [ha1] at hadd1
    dsimp only at hadd1 ⊢
    simp only [Bool.toNat_false, Nat.add_zero] at hadd1
    have heq1_full : (qh - 1).toNat * vn1.toNat + (rh.toNat + vn1.toNat) =
        u2.toNat * 2 ^ 64 + u1.toNat := by
      rw [hqh1_toNat]
      have h1 : (qh.toNat - 1) * vn1.toNat + vn1.toNat = qh.toNat * vn1.toNat := by
        calc (qh.toNat - 1) * vn1.toNat + vn1.toNat
            = (qh.toNat - 1 + 1) * vn1.toNat := by rw [Nat.add_mul, Nat.one_mul]
          _ = qh.toNat * vn1.toNat := by rw [Nat.sub_add_cancel hqh_pos]
      omega
    cases ov1
    · simp only [Bool.false_eq_true, ↓reduceIte]
      simp only [Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at hadd1
      have heq1 : (qh - 1).toNat * vn1.toNat + rh1.toNat = u2.toNat * 2 ^ 64 + u1.toNat := by
        rw [hadd1]; exact heq1_full
      have hmul1 := mulWide64_spec (qh - 1) vn2
      rcases hm1 : mulWide64 (qh - 1) vn2 with ⟨pLo1, pHi1⟩
      rw [hm1] at hmul1
      dsimp only at hmul1 ⊢
      cases hcmp2 : cmpWideGt pHi1 pLo1 rh1 u0
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hle2 : (qh - 1).toNat * vn2.toNat ≤ rh1.toNat * 2 ^ 64 + u0.toNat := by
          apply Classical.byContradiction; intro hgt
          have hgt' : rh1.toNat * 2 ^ 64 + u0.toNat < pHi1.toNat * 2 ^ 64 + pLo1.toNat := by
            rw [Nat.add_comm (pHi1.toNat * 2 ^ 64), hmul1]; exact Nat.lt_of_not_le hgt
          have htrue := (cmpWideGt_iff pHi1 pLo1 rh1 u0).mpr hgt'
          rw [hcmp2] at htrue
          exact Bool.false_ne_true htrue
        exact ⟨refine_upper_arith heq1 hle2, fun Q _ hQineq => hQ_lt1 Q hQineq⟩
      · simp only [↓reduceIte]
        have hgt2 : rh1.toNat * 2 ^ 64 + u0.toNat < (qh - 1).toNat * vn2.toNat := by
          have h := (cmpWideGt_iff pHi1 pLo1 rh1 u0).mp hcmp2
          rw [Nat.add_comm (pHi1.toNat * 2 ^ 64), hmul1] at h
          exact h
        have hqh1_pos : 1 ≤ (qh - 1).toNat := by
          apply Classical.byContradiction; intro h0
          have hz : (qh - 1).toNat = 0 := by omega
          rw [hz, Nat.zero_mul] at hgt2
          omega
        have hqh2_toNat : (qh - 1 - 1).toNat = (qh - 1).toNat - 1 := by
          rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; exact hqh1_pos)]
          rfl
        have hrh2_ge : 2 ^ 64 ≤ rh1.toNat + vn1.toNat := by rw [hadd1]; omega
        have heq2 : (qh - 1 - 1).toNat * vn1.toNat + (rh1.toNat + vn1.toNat) =
            u2.toNat * 2 ^ 64 + u1.toNat := by
          rw [hqh2_toNat]
          have h1 : ((qh - 1).toNat - 1) * vn1.toNat + vn1.toNat = (qh - 1).toNat * vn1.toNat := by
            calc ((qh - 1).toNat - 1) * vn1.toNat + vn1.toNat
                = ((qh - 1).toNat - 1 + 1) * vn1.toNat := by rw [Nat.add_mul, Nat.one_mul]
              _ = (qh - 1).toNat * vn1.toNat := by rw [Nat.sub_add_cancel hqh1_pos]
          omega
        have hprod_le : (qh - 1 - 1).toNat * vn2.toNat ≤ (rh1.toNat + vn1.toNat) * 2 ^ 64 + u0.toNat := by
          have h1 : (qh - 1 - 1).toNat < 2 ^ 64 := uint64_toNat_lt _
          have h2 : vn2.toNat < 2 ^ 64 := uint64_toNat_lt _
          have h3 : (qh - 1 - 1).toNat * vn2.toNat < 2 ^ 64 * 2 ^ 64 :=
            Nat.mul_lt_mul_of_lt_of_lt h1 h2
          have h4 : 2 ^ 64 * 2 ^ 64 ≤ (rh1.toNat + vn1.toNat) * 2 ^ 64 :=
            Nat.mul_le_mul_right _ hrh2_ge
          exact Nat.le_trans (Nat.le_of_lt (Nat.lt_of_lt_of_le h3 h4)) (Nat.le_add_right _ _)
        refine ⟨refine_upper_arith heq2 hprod_le, fun Q _ hQineq => ?_⟩
        rw [hqh2_toNat]
        exact refine_lower_arith heq1 hgt2 hQineq
    · simp only [↓reduceIte]
      simp only [Bool.toNat_true, Nat.one_mul] at hadd1
      have hrh_ge : 2 ^ 64 ≤ rh.toNat + vn1.toNat := by omega
      have hprod_le : (qh - 1).toNat * vn2.toNat ≤ (rh.toNat + vn1.toNat) * 2 ^ 64 + u0.toNat := by
        have h1 : (qh - 1).toNat < 2 ^ 64 := uint64_toNat_lt _
        have h2 : vn2.toNat < 2 ^ 64 := uint64_toNat_lt _
        have h3 : (qh - 1).toNat * vn2.toNat < 2 ^ 64 * 2 ^ 64 :=
          Nat.mul_lt_mul_of_lt_of_lt h1 h2
        have h4 : 2 ^ 64 * 2 ^ 64 ≤ (rh.toNat + vn1.toNat) * 2 ^ 64 :=
          Nat.mul_le_mul_right _ hrh_ge
        exact Nat.le_trans (Nat.le_of_lt (Nat.lt_of_lt_of_le h3 h4)) (Nat.le_add_right _ _)
      exact ⟨refine_upper_arith heq1_full hprod_le, fun Q _ hQineq => hQ_lt1 Q hQineq⟩

/-- Helper: decompose `toNat xs` at the top 3 limbs `p + 2, p + 1, p` when `toNat xs < B^(p + 3)`. -/
private theorem toNat_top3 (xs : Array UInt64) (p : Nat)
    (hlt : toNat xs < (2 ^ 64) ^ (p + 3)) :
    let u2 := getLimb xs (p + 2)
    let u1 := getLimb xs (p + 1)
    let u0 := getLimb xs p
    (u2.toNat * (2 ^ 64 * 2 ^ 64) + u1.toNat * 2 ^ 64 + u0.toNat) * (2 ^ 64) ^ p ≤ toNat xs ∧
    toNat xs < (u2.toNat * (2 ^ 64 * 2 ^ 64) + u1.toNat * 2 ^ 64 + u0.toNat + 1) * (2 ^ 64) ^ p := by
  have hzero_above : ∀ k, p + 3 ≤ k → getLimb xs k = 0 := by
    intro k hk
    apply Classical.byContradiction; intro hne
    have hpos : 1 ≤ (getLimb xs k).toNat := by
      have : (getLimb xs k).toNat ≠ 0 := fun h0 => hne (UInt64.toNat_inj.mp (by simpa using h0))
      omega
    have hge := toNat_ge_limb xs k
    have hpow : (2 ^ 64) ^ (p + 3) ≤ (2 ^ 64) ^ k :=
      Nat.pow_le_pow_right (Nat.two_pow_pos 64) hk
    have h1 : (2 ^ 64) ^ k ≤ (getLimb xs k).toNat * (2 ^ 64) ^ k :=
      Nat.le_mul_of_pos_left _ hpos
    omega
  have hto : toNat xs = toNatPrefix xs (p + 3) := by
    rw [← toNatPrefix_eq_toNat_of_le xs (Nat.le_max_left xs.size (p + 3))]
    have hstep : ∀ d, toNatPrefix xs (p + 3 + d) = toNatPrefix xs (p + 3) := by
      intro d
      induction d with
      | zero => rfl
      | succ d ih =>
        rw [show p + 3 + (d + 1) = (p + 3 + d) + 1 by omega, toNatPrefix_succ, ih,
            hzero_above (p + 3 + d) (by omega), UInt64.toNat_zero, Nat.zero_mul, Nat.add_zero]
    have hM : max xs.size (p + 3) = p + 3 + (max xs.size (p + 3) - (p + 3)) := by omega
    rw [hM, hstep]
  dsimp only
  rw [hto]
  rw [toNatPrefix_succ xs (p + 2), toNatPrefix_succ xs (p + 1), toNatPrefix_succ xs p]
  have hpref : toNatPrefix xs p < (2 ^ 64) ^ p := toNatPrefix_lt xs p
  have hp1 : (2 ^ 64) ^ (p + 1) = 2 ^ 64 * (2 ^ 64) ^ p := by
    rw [Nat.pow_succ (2 ^ 64), Nat.mul_comm]
  have hp2 : (2 ^ 64) ^ (p + 2) = (2 ^ 64 * 2 ^ 64) * (2 ^ 64) ^ p := by
    rw [Nat.pow_succ (2 ^ 64), Nat.pow_succ (2 ^ 64), Nat.mul_assoc, Nat.mul_comm ((2 ^ 64) ^ p)]
  rw [hp1, hp2]
  have hcomb : (getLimb xs (p + 2)).toNat * ((2 ^ 64 * 2 ^ 64) * (2 ^ 64) ^ p) +
      (getLimb xs (p + 1)).toNat * (2 ^ 64 * (2 ^ 64) ^ p) +
      (getLimb xs p).toNat * (2 ^ 64) ^ p =
      ((getLimb xs (p + 2)).toNat * (2 ^ 64 * 2 ^ 64) +
       (getLimb xs (p + 1)).toNat * 2 ^ 64 + (getLimb xs p).toNat) * (2 ^ 64) ^ p := by
    simp only [Nat.add_mul, Nat.mul_assoc]
  constructor
  · omega
  · rw [Nat.add_mul, Nat.one_mul]; omega

/-- Helper: decompose `toNat vn` at its top 2 limbs `n - 1, n - 2` when `2 ≤ n` and `vn.size = n`. -/
private theorem toNat_top2 (vn : Array UInt64) (n : Nat) (hn : 2 ≤ n) (hsz : vn.size = n) :
    let vn1 := getLimb vn (n - 1)
    let vn2 := getLimb vn (n - 2)
    (vn1.toNat * 2 ^ 64 + vn2.toNat) * (2 ^ 64) ^ (n - 2) ≤ toNat vn ∧
    toNat vn < (vn1.toNat * 2 ^ 64 + vn2.toNat + 1) * (2 ^ 64) ^ (n - 2) := by
  dsimp only
  have h1 : n = (n - 2) + 2 := by omega
  have h2 : n - 1 = (n - 2) + 1 := by omega
  have hto : toNat vn = toNatPrefix vn ((n - 2) + 2) := by unfold toNat; rw [hsz, ← h1]
  rw [hto, toNatPrefix_succ vn ((n - 2) + 1), toNatPrefix_succ vn (n - 2), ← h2]
  have hpref : toNatPrefix vn (n - 2) < (2 ^ 64) ^ (n - 2) := toNatPrefix_lt vn (n - 2)
  have hp1 : (2 ^ 64) ^ (n - 1) = 2 ^ 64 * (2 ^ 64) ^ (n - 2) := by
    rw [h2, Nat.pow_succ (2 ^ 64), Nat.mul_comm]
  rw [hp1]
  have hcomb : (getLimb vn (n - 1)).toNat * (2 ^ 64 * (2 ^ 64) ^ (n - 2)) +
      (getLimb vn (n - 2)).toNat * (2 ^ 64) ^ (n - 2) =
      ((getLimb vn (n - 1)).toNat * 2 ^ 64 + (getLimb vn (n - 2)).toNat) * (2 ^ 64) ^ (n - 2) := by
    rw [Nat.add_mul, Nat.mul_assoc]
  constructor
  · omega
  · rw [Nat.add_mul, Nat.one_mul]; omega

/-- **Knuth's Theorem B** (TAOCP Vol. 2, §4.3.1): for a normalized divisor (`vn1 ≥ 2^63`),
the trial quotient `qhat` satisfies `q_true ≤ qhat ≤ q_true + 1`, i.e.:
1. `toNat rem < (qhat.toNat + 1) * toNat vn * B^j` (`q_true ≤ qhat`), and
2. `(qhat.toNat - 1) * toNat vn * B^j ≤ toNat rem` (`qhat ≤ q_true + 1`). -/
theorem trialQhat_theorem_B (rem vn : Array UInt64) (j n : Nat)
    (hn : 2 ≤ n) (hsz : vn.size = n)
    (hnorm : 2 ^ 63 ≤ (getLimb vn (n - 1)).toNat)
    (hrem_lt : toNat rem < toNat vn * (2 ^ 64) ^ (j + 1)) :
    let vn1 := getLimb vn (n - 1)
    let vn2 := getLimb vn (n - 2)
    let u2 := getLimb rem (j + n)
    let u1 := getLimb rem (j + n - 1)
    let u0 := getLimb rem (j + n - 2)
    let qhat := trialQhat u2 u1 u0 vn1 vn2
    toNat rem < (qhat.toNat + 1) * toNat vn * (2 ^ 64) ^ j ∧
    (qhat.toNat - 1) * toNat vn * (2 ^ 64) ^ j ≤ toNat rem := by
  dsimp only
  let vn1 := getLimb vn (n - 1)
  let vn2 := getLimb vn (n - 2)
  let u2 := getLimb rem (j + n)
  let u1 := getLimb rem (j + n - 1)
  let u0 := getLimb rem (j + n - 2)
  let p := j + n - 2
  have hp1 : p + 1 = j + n - 1 := by omega
  have hp2 : p + 2 = j + n := by omega
  have hp3 : p + 3 = j + n + 1 := by omega
  have hvn_lt : toNat vn < (2 ^ 64) ^ n := by rw [← hsz]; exact toNat_lt vn
  have hrem_pow : toNat rem < (2 ^ 64) ^ (p + 3) := by
    have h1 : toNat vn * (2 ^ 64) ^ (j + 1) ≤ (2 ^ 64) ^ n * (2 ^ 64) ^ (j + 1) :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt hvn_lt)
    have h2 : (2 ^ 64) ^ n * (2 ^ 64) ^ (j + 1) = (2 ^ 64) ^ (p + 3) := by
      rw [← Nat.pow_add]; congr 1; omega
    omega
  have ⟨hrem_lo3, hrem_hi3⟩ := toNat_top3 rem p hrem_pow
  rw [hp2, hp1] at hrem_lo3 hrem_hi3
  have ⟨hvn_lo2, hvn_hi2⟩ := toNat_top2 vn n hn hsz
  have hpow_split : (2 ^ 64) ^ (n - 2) * (2 ^ 64) ^ j = (2 ^ 64) ^ p := by
    rw [← Nat.pow_add]; congr 1; omega
  have hpow_pos : 0 < (2 ^ 64) ^ p := Nat.pow_pos (Nat.two_pow_pos 64)
  have hvn_pos : 0 < toNat vn := by
    have h1 : 1 ≤ (getLimb vn (n - 1)).toNat := by omega
    have h2 := toNat_ge_limb vn (n - 1)
    have h3 : 0 < (2 ^ 64) ^ (n - 1) := Nat.pow_pos (Nat.two_pow_pos 64)
    have h4 : (2 ^ 64) ^ (n - 1) ≤ (getLimb vn (n - 1)).toNat * (2 ^ 64) ^ (n - 1) :=
      Nat.le_mul_of_pos_left _ h1
    omega
  let denom := toNat vn * (2 ^ 64) ^ j
  have hdenom_pos : 0 < denom := Nat.mul_pos hvn_pos (Nat.pow_pos (Nat.two_pow_pos 64))
  let Q := toNat rem / denom
  have hQ_ltB : Q < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul hdenom_pos]
    have : denom * 2 ^ 64 = toNat vn * (2 ^ 64) ^ (j + 1) := by
      rw [Nat.pow_succ (2 ^ 64), Nat.mul_assoc]
    omega
  have hQ_mul_le : Q * denom ≤ toNat rem := by
    rw [Nat.mul_comm]; exact Nat.mul_div_le _ _
  have hQ_top3 : Q * (vn1.toNat * 2 ^ 64 + vn2.toNat) ≤
      u2.toNat * (2 ^ 64 * 2 ^ 64) + u1.toNat * 2 ^ 64 + u0.toNat := by
    have h1 : Q * (vn1.toNat * 2 ^ 64 + vn2.toNat) * (2 ^ 64) ^ p ≤ toNat rem := by
      calc Q * (vn1.toNat * 2 ^ 64 + vn2.toNat) * (2 ^ 64) ^ p
          = Q * ((vn1.toNat * 2 ^ 64 + vn2.toNat) * (2 ^ 64) ^ (n - 2)) * (2 ^ 64) ^ j := by
            rw [← hpow_split, ← Nat.mul_assoc, Nat.mul_assoc Q]
        _ ≤ Q * toNat vn * (2 ^ 64) ^ j :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left Q hvn_lo2)
        _ = Q * denom := Nat.mul_assoc _ _ _
        _ ≤ toNat rem := hQ_mul_le
    have h2 : Q * (vn1.toNat * 2 ^ 64 + vn2.toNat) * (2 ^ 64) ^ p <
        (u2.toNat * (2 ^ 64 * 2 ^ 64) + u1.toNat * 2 ^ 64 + u0.toNat + 1) * (2 ^ 64) ^ p :=
      Nat.lt_of_le_of_lt h1 hrem_hi3
    have h3 : Q * (vn1.toNat * 2 ^ 64 + vn2.toNat) <
        u2.toNat * (2 ^ 64 * 2 ^ 64) + u1.toNat * 2 ^ 64 + u0.toNat + 1 :=
      Nat.lt_of_mul_lt_mul_right h2
    omega
  -- Establish the two key properties of qhat: (1) qhat * (vn1*B + vn2) ≤ u2*B^2 + u1*B + u0, (2) Q ≤ qhat
  have hqhat_core :
      (trialQhat u2 u1 u0 vn1 vn2).toNat * (vn1.toNat * 2 ^ 64 + vn2.toNat) ≤
        u2.toNat * (2 ^ 64 * 2 ^ 64) + u1.toNat * 2 ^ 64 + u0.toNat ∧
      Q ≤ (trialQhat u2 u1 u0 vn1 vn2).toNat := by
    unfold trialQhat
    split
    · rename_i hlt
      have hdiv := divWide64_spec u2 u1 vn1 hlt
      rcases hd : divWide64 u2 u1 vn1 hlt with ⟨qh, rh⟩
      rw [hd] at hdiv
      dsimp only at hdiv ⊢
      have ⟨hup, hlo⟩ := refineQhat_spec qh rh vn1 vn2 u0 u2 u1 hnorm hdiv.1
      refine ⟨hup, hlo Q ?_ hQ_top3⟩
      -- Show Q ≤ qh.toNat
      have hQ_vn1 : Q * vn1.toNat ≤ u2.toNat * 2 ^ 64 + u1.toNat := by
        have h1 : Q * vn1.toNat * 2 ^ 64 ≤ Q * (vn1.toNat * 2 ^ 64 + vn2.toNat) := by
          rw [Nat.mul_add, ← Nat.mul_assoc]; exact Nat.le_add_right _ _
        have h2 : Q * vn1.toNat * 2 ^ 64 < (u2.toNat * 2 ^ 64 + u1.toNat + 1) * 2 ^ 64 := by
          have hu0 : u0.toNat < 2 ^ 64 := uint64_toNat_lt u0
          have hle := Nat.le_trans h1 hQ_top3
          have heqR : (u2.toNat * 2 ^ 64 + u1.toNat + 1) * 2 ^ 64 =
              u2.toNat * (2 ^ 64 * 2 ^ 64) + u1.toNat * 2 ^ 64 + 2 ^ 64 := by
            rw [Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
          rw [heqR]
          exact Nat.lt_of_le_of_lt hle (Nat.add_lt_add_left hu0 _)
        have h3 := Nat.lt_of_mul_lt_mul_right h2
        omega
      apply Classical.byContradiction; intro hgt
      have h1 : (qh.toNat + 1) * vn1.toNat ≤ Q * vn1.toNat := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega
    · rename_i hge
      have hu2_ge : vn1.toNat ≤ u2.toNat := by
        have : ¬ u2.toNat < vn1.toNat := fun h => hge (UInt64.lt_iff_toNat_lt.mpr h)
        omega
      have hu2_le : u2.toNat ≤ vn1.toNat := by
        have hvn_hi1 : toNat vn < (vn1.toNat + 1) * (2 ^ 64) ^ (n - 1) := by
          have h1 : toNat vn < (vn1.toNat * 2 ^ 64 + vn2.toNat + 1) * (2 ^ 64) ^ (n - 2) := hvn_hi2
          have hvn2 : vn2.toNat < 2 ^ 64 := uint64_toNat_lt vn2
          have h2 : vn1.toNat * 2 ^ 64 + vn2.toNat + 1 ≤ (vn1.toNat + 1) * 2 ^ 64 := by
            rw [Nat.add_mul, Nat.one_mul]; omega
          have h3 := Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_right _ h2)
          rw [Nat.mul_assoc] at h3
          have h4 : 2 ^ 64 * (2 ^ 64) ^ (n - 2) = (2 ^ 64) ^ (n - 1) := by
            have heq : n - 1 = (n - 2) + 1 := by omega
            conv => rhs; rw [heq]
            rw [Nat.pow_succ (2 ^ 64), Nat.mul_comm]
          rwa [h4] at h3
        have hrem_u2 : u2.toNat * (2 ^ 64) ^ (j + n) ≤ toNat rem := toNat_ge_limb rem (j + n)
        have hpow_eq : (2 ^ 64) ^ (n - 1) * (2 ^ 64) ^ (j + 1) = (2 ^ 64) ^ (j + n) := by
          rw [← Nat.pow_add]; congr 1; omega
        have hlt_u2 : u2.toNat * (2 ^ 64) ^ (j + n) < (vn1.toNat + 1) * (2 ^ 64) ^ (j + n) := by
          calc u2.toNat * (2 ^ 64) ^ (j + n) ≤ toNat rem := hrem_u2
            _ < toNat vn * (2 ^ 64) ^ (j + 1) := hrem_lt
            _ < (vn1.toNat + 1) * (2 ^ 64) ^ (n - 1) * (2 ^ 64) ^ (j + 1) :=
                Nat.mul_lt_mul_of_pos_right hvn_hi1 (Nat.pow_pos (Nat.two_pow_pos 64))
            _ = (vn1.toNat + 1) * (2 ^ 64) ^ (j + n) := by rw [Nat.mul_assoc, hpow_eq]
        have := Nat.lt_of_mul_lt_mul_right hlt_u2
        omega
      have hu2_eq : u2.toNat = vn1.toNat := by omega
      have hadd := addCarry64_spec u1 vn1 false
      rcases ha : addCarry64 u1 vn1 false with ⟨rh, ov⟩
      rw [ha] at hadd
      dsimp only at hadd ⊢
      simp only [Bool.toNat_false, Nat.add_zero] at hadd
      have hQ_le_max : Q ≤ maxWord64.toNat := by rw [maxWord64_toNat]; omega
      cases ov
      · simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at hadd
        have heqM : maxWord64.toNat * vn1.toNat + rh.toNat = u2.toNat * 2 ^ 64 + u1.toNat := by
          rw [maxWord64_toNat, hadd, hu2_eq]
          have hpos : 1 ≤ 2 ^ 64 := Nat.two_pow_pos 64
          have h1 : (2 ^ 64 - 1) * vn1.toNat + vn1.toNat = 2 ^ 64 * vn1.toNat := by
            calc (2 ^ 64 - 1) * vn1.toNat + vn1.toNat
                = (2 ^ 64 - 1 + 1) * vn1.toNat := by rw [Nat.add_mul, Nat.one_mul]
              _ = 2 ^ 64 * vn1.toNat := by rw [Nat.sub_add_cancel hpos]
          rw [Nat.mul_comm vn1.toNat (2 ^ 64)]
          omega
        have ⟨hup, hlo⟩ := refineQhat_spec maxWord64 rh vn1 vn2 u0 u2 u1 hnorm heqM
        exact ⟨hup, hlo Q hQ_le_max hQ_top3⟩
      · simp only [↓reduceIte]
        simp only [Bool.toNat_true, Nat.one_mul] at hadd
        refine ⟨?_, hQ_le_max⟩
        have hgeB : 2 ^ 64 ≤ u1.toNat + vn1.toNat := by omega
        have hvn2 : vn2.toNat < 2 ^ 64 := uint64_toNat_lt vn2
        have hm1 : maxWord64.toNat * vn2.toNat ≤ (u1.toNat + vn1.toNat) * 2 ^ 64 + u0.toNat := by
          have h1 : maxWord64.toNat < 2 ^ 64 := uint64_toNat_lt maxWord64
          have h2 : maxWord64.toNat * vn2.toNat < 2 ^ 64 * 2 ^ 64 :=
            Nat.mul_lt_mul_of_lt_of_lt h1 hvn2
          have h3 : 2 ^ 64 * 2 ^ 64 ≤ (u1.toNat + vn1.toNat) * 2 ^ 64 :=
            Nat.mul_le_mul_right _ hgeB
          exact Nat.le_trans (Nat.le_of_lt (Nat.lt_of_lt_of_le h2 h3)) (Nat.le_add_right _ _)
        have heqM : maxWord64.toNat * vn1.toNat + (u1.toNat + vn1.toNat) =
            u2.toNat * 2 ^ 64 + u1.toNat := by
          rw [maxWord64_toNat, hu2_eq]
          have hpos : 1 ≤ 2 ^ 64 := Nat.two_pow_pos 64
          have h1 : (2 ^ 64 - 1) * vn1.toNat + vn1.toNat = 2 ^ 64 * vn1.toNat := by
            calc (2 ^ 64 - 1) * vn1.toNat + vn1.toNat
                = (2 ^ 64 - 1 + 1) * vn1.toNat := by rw [Nat.add_mul, Nat.one_mul]
              _ = 2 ^ 64 * vn1.toNat := by rw [Nat.sub_add_cancel hpos]
          rw [Nat.mul_comm vn1.toNat (2 ^ 64)]
          omega
        exact refine_upper_arith heqM hm1
  -- Now deduce both halves of Theorem B!
  rcases hqhat_core with ⟨hqhat_up, hQ_le_qhat⟩
  let qhat := trialQhat u2 u1 u0 vn1 vn2
  change toNat rem < (qhat.toNat + 1) * toNat vn * (2 ^ 64) ^ j ∧
    (qhat.toNat - 1) * toNat vn * (2 ^ 64) ^ j ≤ toNat rem
  constructor
  · -- Half 1: toNat rem < (qhat + 1) * toNat vn * B^j
    have hrem_lt_Q : toNat rem < (Q + 1) * denom := by
      have hdm := Nat.div_add_mod (toNat rem) denom
      have hmod := Nat.mod_lt (toNat rem) hdenom_pos
      rw [Nat.add_mul, Nat.one_mul]
      rw [Nat.mul_comm denom (toNat rem / denom)] at hdm
      change toNat rem < (toNat rem / denom) * denom + denom
      omega
    have hle : (Q + 1) * denom ≤ (qhat.toNat + 1) * denom :=
      Nat.mul_le_mul_right _ (Nat.add_le_add_right hQ_le_qhat 1)
    rw [Nat.mul_assoc]
    exact Nat.lt_of_lt_of_le hrem_lt_Q hle
  · -- Half 2: (qhat - 1) * toNat vn * B^j ≤ toNat rem
    by_cases hq0 : qhat.toNat = 0
    · rw [hq0, Nat.zero_sub, Nat.zero_mul, Nat.zero_mul]; exact Nat.zero_le _
    · have hqpos : 1 ≤ qhat.toNat := by omega
      have h1 : qhat.toNat * toNat vn * (2 ^ 64) ^ j <
          qhat.toNat * (vn1.toNat * 2 ^ 64 + vn2.toNat + 1) * (2 ^ 64) ^ p := by
        calc qhat.toNat * toNat vn * (2 ^ 64) ^ j
            < qhat.toNat * ((vn1.toNat * 2 ^ 64 + vn2.toNat + 1) * (2 ^ 64) ^ (n - 2)) * (2 ^ 64) ^ j :=
              Nat.mul_lt_mul_of_pos_right
                (Nat.mul_lt_mul_of_pos_left hvn_hi2 hqpos)
                (Nat.pow_pos (Nat.two_pow_pos 64))
          _ = qhat.toNat * (vn1.toNat * 2 ^ 64 + vn2.toNat + 1) * (2 ^ 64) ^ p := by
              rw [← hpow_split]; simp only [Nat.mul_assoc]
      have h2 : qhat.toNat * (vn1.toNat * 2 ^ 64 + vn2.toNat + 1) * (2 ^ 64) ^ p ≤
          toNat rem + qhat.toNat * (2 ^ 64) ^ p := by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_mul]
        have hle := Nat.mul_le_mul_right ((2 ^ 64) ^ p) hqhat_up
        exact Nat.add_le_add_right (Nat.le_trans hle hrem_lo3) _
      have h3 : qhat.toNat * (2 ^ 64) ^ p ≤ toNat vn * (2 ^ 64) ^ j := by
        have hqlt : qhat.toNat ≤ 2 ^ 64 := Nat.le_of_lt (uint64_toNat_lt qhat)
        have hvn1_pos : 1 ≤ (getLimb vn (n - 1)).toNat := by omega
        have hvn_ge : 2 ^ 64 * (2 ^ 64) ^ (n - 2) ≤ toNat vn := by
          have hge1 : 2 ^ 64 ≤ (getLimb vn (n - 1)).toNat * 2 ^ 64 + (getLimb vn (n - 2)).toNat :=
            Nat.le_trans (Nat.le_mul_of_pos_left (2 ^ 64) hvn1_pos) (Nat.le_add_right _ _)
          exact Nat.le_trans (Nat.mul_le_mul_right _ hge1) hvn_lo2
        calc qhat.toNat * (2 ^ 64) ^ p
            ≤ 2 ^ 64 * (2 ^ 64) ^ p := Nat.mul_le_mul_right _ hqlt
          _ = 2 ^ 64 * (2 ^ 64) ^ (n - 2) * (2 ^ 64) ^ j := by
              rw [← hpow_split, ← Nat.mul_assoc]
          _ ≤ toNat vn * (2 ^ 64) ^ j := Nat.mul_le_mul_right _ hvn_ge
      have hsplit : qhat.toNat * toNat vn * (2 ^ 64) ^ j =
          (qhat.toNat - 1) * toNat vn * (2 ^ 64) ^ j + toNat vn * (2 ^ 64) ^ j := by
        calc qhat.toNat * toNat vn * (2 ^ 64) ^ j
            = ((qhat.toNat - 1) + 1) * (toNat vn * (2 ^ 64) ^ j) := by
              rw [Nat.sub_add_cancel hqpos, Nat.mul_assoc]
          _ = (qhat.toNat - 1) * toNat vn * (2 ^ 64) ^ j + toNat vn * (2 ^ 64) ^ j := by
              rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
      have hcomb := Nat.lt_of_lt_of_le h1 (Nat.le_trans h2 (Nat.add_le_add_left h3 _))
      rw [hsplit] at hcomb
      exact Nat.le_of_lt (Nat.lt_of_add_lt_add_right hcomb)

/-! ### Knuth Algorithm D: Multiply-Subtract (`subMulShiftLoop`) and Add-Back (`addShiftLoop`) -/

private theorem mul_add_lt_sq {B a b c : Nat} (ha : a < B) (hb : b < B) (hc : c < B) :
    a * b + c < B * B := by
  have h1 : a * b + c < a * B + B := by
    have hab : a * b ≤ a * (B - 1) := Nat.mul_le_mul_left a (by omega)
    have hmul : a * (B - 1) + a = a * B := by
      calc a * (B - 1) + a = a * (B - 1 + 1) := by rw [Nat.mul_add, Nat.mul_one]
        _ = a * B := by rw [Nat.sub_add_cancel (by omega)]
    omega
  have h2 : (a + 1) * B ≤ B * B := Nat.mul_le_mul_right B (by omega)
  rw [Nat.add_mul, Nat.one_mul] at h2
  omega

private theorem subMulShiftLoop_props (rem vn : Array UInt64) (j n k : Nat)
    (qhat mulCarry : UInt64) (borrow : Bool)
    (hk : k ≤ n) (hsz : j + n < rem.size) (hvn : vn.size = n) :
    let res := subMulShiftLoop rem vn j n k qhat mulCarry borrow
    res.1.size = rem.size ∧
    (∀ idx, j + n < idx → getLimb res.1 idx = getLimb rem idx) ∧
    toNat res.1 + qhat.toNat * toNat vn * (2 ^ 64) ^ j +
      mulCarry.toNat * (2 ^ 64) ^ (j + k) + borrow.toNat * (2 ^ 64) ^ (j + k) =
      toNat rem + qhat.toNat * toNatPrefix vn k * (2 ^ 64) ^ j +
      res.2.toNat * (2 ^ 64) ^ (j + n + 1) := by
  induction hd : n - k generalizing rem k mulCarry borrow with
  | zero =>
    have hkn : k = n := by omega
    rw [hkn]
    unfold subMulShiftLoop
    simp only [Nat.lt_irrefl, ↓reduceDIte]
    have hsb := subBorrow64_spec (getLimb rem (j + n)) mulCarry borrow
    rcases hs : subBorrow64 (getLimb rem (j + n)) mulCarry borrow with ⟨diffTop, finalBorrow⟩
    rw [hs] at hsb
    dsimp only at hsb ⊢
    refine ⟨size_setLimb _ _ _, ?_, ?_⟩
    · intro idx hidx
      rw [getLimb_setLimb rem (j + n) diffTop hsz idx]
      have hne : idx ≠ j + n := by omega
      simp [hne]
    · have hto := toNat_setLimb rem (j + n) diffTop hsz
      have hvn_eq : toNatPrefix vn n = toNat vn := by unfold toNat; rw [hvn]
      rw [hvn_eq, Nat.pow_succ (2 ^ 64)]
      have hmul := congrArg (· * (2 ^ 64) ^ (j + n)) hsb
      repeat rw [Nat.add_mul] at hmul
      have hpow : finalBorrow.toNat * ((2 ^ 64) ^ (j + n) * 2 ^ 64) =
          finalBorrow.toNat * 2 ^ 64 * (2 ^ 64) ^ (j + n) := by
        rw [Nat.mul_comm ((2 ^ 64) ^ (j + n)) (2 ^ 64), ← Nat.mul_assoc]
      rw [hpow]
      omega
  | succ d ih =>
    have hlt : k < n := by omega
    unfold subMulShiftLoop
    simp only [hlt, ↓reduceDIte]
    have hmul := mulWide64_spec qhat (getLimb vn k)
    rcases hm : mulWide64 qhat (getLimb vn k) with ⟨pLo, pHi⟩
    rw [hm] at hmul
    have hac1 := addCarry64_spec pLo mulCarry false
    rcases h1 : addCarry64 pLo mulCarry false with ⟨prod, c1⟩
    rw [h1] at hac1
    have hac2 := addCarry64_spec pHi 0 c1
    rcases h2 : addCarry64 pHi 0 c1 with ⟨nextMulCarry, ov2⟩
    rw [h2] at hac2
    have hsb := subBorrow64_spec (getLimb rem (j + k)) prod borrow
    rcases h3 : subBorrow64 (getLimb rem (j + k)) prod borrow with ⟨diff, borrow'⟩
    rw [h3] at hsb
    dsimp only at hmul hac1 hac2 hsb ⊢
    -- Prove ov2 = false because qhat * vn[k] + mulCarry < 2^128
    have h0N : (0 : UInt64).toNat = 0 := rfl
    have hfN : false.toNat = 0 := rfl
    rw [hfN, Nat.add_zero] at hac1
    rw [h0N, Nat.add_zero] at hac2
    have hnoov : ov2.toNat = 0 := by
      have hqlt : qhat.toNat < 2 ^ 64 := uint64_toNat_lt qhat
      have hvlt : (getLimb vn k).toNat < 2 ^ 64 := uint64_toNat_lt _
      have hclt : mulCarry.toNat < 2 ^ 64 := uint64_toNat_lt mulCarry
      have hbound : qhat.toNat * (getLimb vn k).toNat + mulCarry.toNat < 2 ^ 64 * 2 ^ 64 :=
        mul_add_lt_sq hqlt hvlt hclt
      have htot : prod.toNat + nextMulCarry.toNat * 2 ^ 64 + ov2.toNat * (2 ^ 64 * 2 ^ 64) =
          qhat.toNat * (getLimb vn k).toNat + mulCarry.toNat := by
        suffices ∀ B q v mc pLo pHi pr c1 nmc ov : Nat,
            pLo + pHi * B = q * v → pr + c1 * B = pLo + mc → nmc + ov * B = pHi + c1 →
            pr + nmc * B + ov * (B * B) = q * v + mc from
          this (2 ^ 64) _ _ _ _ _ _ _ _ _ hmul hac1 hac2
        intro B q v mc pLo pHi pr c1 nmc ov h1 h2 h3
        have hs := congrArg (· * B) h3
        simp only [Nat.add_mul, Nat.mul_assoc] at hs
        omega
      cases ov2
      · rfl
      · simp only [Bool.toNat_true, Nat.one_mul] at htot
        have hge : 2 ^ 64 * 2 ^ 64 ≤ prod.toNat + nextMulCarry.toNat * 2 ^ 64 + 2 ^ 64 * 2 ^ 64 :=
          Nat.le_add_left _ _
        rw [htot] at hge
        exact absurd (Nat.lt_of_le_of_lt hge hbound) (Nat.lt_irrefl _)
    rw [hnoov, Nat.zero_mul, Nat.add_zero] at hac2
    have hcomb : diff.toNat + qhat.toNat * (getLimb vn k).toNat + mulCarry.toNat + borrow.toNat =
        (getLimb rem (j + k)).toNat + nextMulCarry.toNat * 2 ^ 64 + borrow'.toNat * 2 ^ 64 := by
      have hstep := congrArg (· * 2 ^ 64) hac2
      rw [Nat.add_mul] at hstep
      omega
    have hjk : j + k < rem.size := by omega
    have ⟨hsz', hhi', heq'⟩ := ih (setLimb rem (j + k) diff) (k + 1) nextMulCarry borrow'
      (by omega) (by rw [size_setLimb]; exact hsz) (by omega)
    refine ⟨by rw [hsz', size_setLimb], ?_, ?_⟩
    · intro idx hidx
      rw [hhi' idx hidx, getLimb_setLimb rem (j + k) diff hjk idx]
      have hne : idx ≠ j + k := by omega
      simp [hne]
    · have hto := toNat_setLimb rem (j + k) diff hjk
      rw [toNatPrefix_succ vn k] at heq'
      have hpow1 : (2 ^ 64) ^ (j + (k + 1)) = 2 ^ 64 * (2 ^ 64) ^ (j + k) := by
        rw [← Nat.add_assoc, Nat.pow_succ (2 ^ 64), Nat.mul_comm]
      have hpow2 : (2 ^ 64) ^ k * (2 ^ 64) ^ j = (2 ^ 64) ^ (j + k) := by
        rw [← Nat.pow_add, Nat.add_comm]
      have hmcomb := congrArg (· * (2 ^ 64) ^ (j + k)) hcomb
      repeat rw [Nat.add_mul] at hmcomb
      have hr1 : nextMulCarry.toNat * (2 ^ 64) ^ (j + (k + 1)) =
          nextMulCarry.toNat * 2 ^ 64 * (2 ^ 64) ^ (j + k) := by
        rw [hpow1, Nat.mul_assoc]
      have hr2 : borrow'.toNat * (2 ^ 64) ^ (j + (k + 1)) =
          borrow'.toNat * 2 ^ 64 * (2 ^ 64) ^ (j + k) := by
        rw [hpow1, Nat.mul_assoc]
      have hr3 : qhat.toNat * (toNatPrefix vn k + (getLimb vn k).toNat * (2 ^ 64) ^ k) * (2 ^ 64) ^ j =
          qhat.toNat * toNatPrefix vn k * (2 ^ 64) ^ j +
          qhat.toNat * (getLimb vn k).toNat * (2 ^ 64) ^ (j + k) := by
        rw [Nat.mul_add, Nat.add_mul]
        congr 1
        calc qhat.toNat * ((getLimb vn k).toNat * (2 ^ 64) ^ k) * (2 ^ 64) ^ j
            = qhat.toNat * (getLimb vn k).toNat * (2 ^ 64) ^ k * (2 ^ 64) ^ j := by rw [← Nat.mul_assoc]
          _ = qhat.toNat * (getLimb vn k).toNat * ((2 ^ 64) ^ k * (2 ^ 64) ^ j) := Nat.mul_assoc _ _ _
          _ = qhat.toNat * (getLimb vn k).toNat * (2 ^ 64) ^ (j + k) := by rw [hpow2]
      rw [hr1, hr2, hr3] at heq'
      omega

private theorem addShiftLoop_props (rem vn : Array UInt64) (j n k : Nat) (carry : Bool)
    (hk : k ≤ n) (hsz : j + n < rem.size) (hvn : vn.size = n) :
    let res := addShiftLoop rem vn j n k carry
    res.size = rem.size ∧
    (∀ idx, j + n < idx → getLimb res idx = getLimb rem idx) ∧
    ∃ cOut : Bool,
      toNat res + cOut.toNat * (2 ^ 64) ^ (j + n + 1) + toNatPrefix vn k * (2 ^ 64) ^ j =
        toNat rem + carry.toNat * (2 ^ 64) ^ (j + k) + toNat vn * (2 ^ 64) ^ j := by
  induction hd : n - k generalizing rem k carry with
  | zero =>
    have hkn : k = n := by omega
    rw [hkn]
    unfold addShiftLoop
    simp only [Nat.lt_irrefl, ↓reduceDIte]
    have hac := addCarry64_spec (getLimb rem (j + n)) 0 carry
    rcases ha : addCarry64 (getLimb rem (j + n)) 0 carry with ⟨sTop, cOut⟩
    rw [ha] at hac
    dsimp only at hac ⊢
    have h0N : (0 : UInt64).toNat = 0 := rfl
    rw [h0N, Nat.add_zero] at hac
    refine ⟨size_setLimb _ _ _, ?_, cOut, ?_⟩
    · intro idx hidx
      rw [getLimb_setLimb rem (j + n) sTop hsz idx]
      have hne : idx ≠ j + n := by omega
      simp [hne]
    · have hto := toNat_setLimb rem (j + n) sTop hsz
      have hvn_eq : toNatPrefix vn n = toNat vn := by unfold toNat; rw [hvn]
      rw [hvn_eq, Nat.pow_succ (2 ^ 64)]
      have hm := congrArg (· * (2 ^ 64) ^ (j + n)) hac
      repeat rw [Nat.add_mul] at hm
      have hpow : cOut.toNat * ((2 ^ 64) ^ (j + n) * 2 ^ 64) =
          cOut.toNat * 2 ^ 64 * (2 ^ 64) ^ (j + n) := by
        rw [Nat.mul_comm ((2 ^ 64) ^ (j + n)) (2 ^ 64), ← Nat.mul_assoc]
      rw [hpow]
      omega
  | succ d ih =>
    have hlt : k < n := by omega
    unfold addShiftLoop
    simp only [hlt, ↓reduceDIte]
    have hac := addCarry64_spec (getLimb rem (j + k)) (getLimb vn k) carry
    rcases ha : addCarry64 (getLimb rem (j + k)) (getLimb vn k) carry with ⟨s, c'⟩
    rw [ha] at hac
    dsimp only at hac ⊢
    have hjk : j + k < rem.size := by omega
    have ⟨hsz', hhi', cOut, heq'⟩ := ih (setLimb rem (j + k) s) (k + 1) c'
      (by omega) (by rw [size_setLimb]; exact hsz) (by omega)
    refine ⟨by rw [hsz', size_setLimb], ?_, cOut, ?_⟩
    · intro idx hidx
      rw [hhi' idx hidx, getLimb_setLimb rem (j + k) s hjk idx]
      have hne : idx ≠ j + k := by omega
      simp [hne]
    · have hto := toNat_setLimb rem (j + k) s hjk
      rw [toNatPrefix_succ vn k] at heq'
      have hpow1 : (2 ^ 64) ^ (j + (k + 1)) = 2 ^ 64 * (2 ^ 64) ^ (j + k) := by
        rw [← Nat.add_assoc, Nat.pow_succ (2 ^ 64), Nat.mul_comm]
      have hpow2 : (2 ^ 64) ^ k * (2 ^ 64) ^ j = (2 ^ 64) ^ (j + k) := by
        rw [← Nat.pow_add, Nat.add_comm]
      have hm := congrArg (· * (2 ^ 64) ^ (j + k)) hac
      repeat rw [Nat.add_mul] at hm
      have hr1 : c'.toNat * (2 ^ 64) ^ (j + (k + 1)) = c'.toNat * 2 ^ 64 * (2 ^ 64) ^ (j + k) := by
        rw [hpow1, Nat.mul_assoc]
      have hr2 : (toNatPrefix vn k + (getLimb vn k).toNat * (2 ^ 64) ^ k) * (2 ^ 64) ^ j =
          toNatPrefix vn k * (2 ^ 64) ^ j + (getLimb vn k).toNat * (2 ^ 64) ^ (j + k) := by
        rw [Nat.add_mul, Nat.mul_assoc, hpow2]
      rw [hr1, hr2] at heq'
      omega

private theorem toNat_lt_of_upper_zero (xs : Array UInt64) (p : Nat)
    (h : ∀ idx, p ≤ idx → getLimb xs idx = 0) :
    toNat xs < (2 ^ 64) ^ p := by
  have heq : toNat xs = toNatPrefix xs p := by
    rw [← toNatPrefix_eq_toNat_of_le xs (Nat.le_max_left xs.size p)]
    have hstep : ∀ d, toNatPrefix xs (p + d) = toNatPrefix xs p := by
      intro d
      induction d with
      | zero => rfl
      | succ d ih =>
        rw [show p + (d + 1) = (p + d) + 1 by omega, toNatPrefix_succ, ih, h (p + d) (by omega),
            UInt64.toNat_zero, Nat.zero_mul, Nat.add_zero]
    have hM : max xs.size p = p + (max xs.size p - p) := by omega
    rw [hM, hstep]
  rw [heq]
  exact toNatPrefix_lt xs p

/-! ### Knuth Algorithm D: Fused 1-Carry Multiply-Subtract (`subMulCarryLoop`) & Möller–Granlund Bridge -/

theorem trialQhatInv_eq_trialQhat (u2 u1 u0 vn1 vn2 : UInt64) (hvn1 : 2 ^ 63 ≤ vn1.toNat) :
    trialQhatInv u2 u1 u0 vn1 vn2 (invert21 vn1 hvn1) = trialQhat u2 u1 u0 vn1 vn2 := by
  unfold trialQhatInv trialQhat
  split
  · rename_i hlt
    rw [divRem21_eq_divWide64 u2 u1 vn1 hvn1 hlt]
  · rfl

private theorem subMulCarryLoop_props (rem vn : Array UInt64) (j k count : Nat)
    (qhat carry : UInt64)
    (hsz : j + k + count < rem.size) :
    let res := subMulCarryLoop rem vn j k qhat carry count
    res.1.size = rem.size ∧
    (∀ idx, j + k + count < idx → getLimb res.1 idx = getLimb rem idx) ∧
    toNat res.1 + qhat.toNat * toNatPrefix vn (k + count) * (2 ^ 64) ^ j +
      carry.toNat * (2 ^ 64) ^ (j + k) =
      toNat rem + qhat.toNat * toNatPrefix vn k * (2 ^ 64) ^ j +
      res.2.toNat * (2 ^ 64) ^ (j + k + count + 1) := by
  induction count generalizing rem k carry with
  | zero =>
    unfold subMulCarryLoop
    simp only [Nat.add_zero]
    have hsb := subBorrow64_spec (getLimb rem (j + k)) carry false
    rcases hs : subBorrow64 (getLimb rem (j + k)) carry false with ⟨diffTop, finalBorrow⟩
    rw [hs] at hsb
    dsimp only at hsb ⊢
    have hf : false.toNat = 0 := rfl
    rw [hf, Nat.add_zero] at hsb
    refine ⟨size_setLimb _ _ _, ?_, ?_⟩
    · intro idx hidx
      rw [getLimb_setLimb rem (j + k) diffTop hsz idx]
      have hne : idx ≠ j + k := by omega
      simp [hne]
    · have hto := toNat_setLimb rem (j + k) diffTop hsz
      rw [Nat.pow_succ (2 ^ 64)]
      have hmul := congrArg (· * (2 ^ 64) ^ (j + k)) hsb
      repeat rw [Nat.add_mul] at hmul
      have hpow : finalBorrow.toNat * ((2 ^ 64) ^ (j + k) * 2 ^ 64) =
          finalBorrow.toNat * 2 ^ 64 * (2 ^ 64) ^ (j + k) := by
        rw [Nat.mul_comm ((2 ^ 64) ^ (j + k)) (2 ^ 64), ← Nat.mul_assoc]
      rw [hpow]
      omega
  | succ count ih =>
    unfold subMulCarryLoop
    dsimp only
    have hspec := subMulCarry64_spec (getLimb rem (j + k)) (getLimb vn k) qhat carry
    rcases hm : subMulCarry64 (getLimb rem (j + k)) (getLimb vn k) qhat carry with ⟨diff, carry'⟩
    rw [hm] at hspec
    dsimp only at hspec ⊢
    have hlt : j + k < rem.size := by omega
    have hih := ih (setLimb rem (j + k) diff) (k + 1) carry' (by rw [size_setLimb]; omega)
    rw [size_setLimb] at hih
    have ⟨hsz', hhi', heq'⟩ := hih
    have hidx1 : j + (k + 1) + count = j + k + (count + 1) := by omega
    have hidx2 : k + 1 + count = k + (count + 1) := by omega
    rw [hidx1] at hhi' heq'
    rw [hidx2] at heq'
    refine ⟨hsz', ?_, ?_⟩
    · intro idx hidx
      rw [hhi' idx hidx, getLimb_setLimb rem (j + k) diff hlt idx]
      have hne : idx ≠ j + k := by omega
      simp [hne]
    · have hset := toNat_setLimb rem (j + k) diff hlt
      rw [toNatPrefix_succ vn k, Nat.mul_add, Nat.add_mul] at heq'
      have hpow1 : (2 ^ 64) ^ (j + (k + 1)) = 2 ^ 64 * (2 ^ 64) ^ (j + k) := by
        rw [← Nat.add_assoc, Nat.pow_succ (2 ^ 64), Nat.mul_comm]
      have hpow2 : (2 ^ 64) ^ k * (2 ^ 64) ^ j = (2 ^ 64) ^ (j + k) := by
        rw [← Nat.pow_add, Nat.add_comm]
      have hmul := congrArg (· * (2 ^ 64) ^ (j + k)) hspec
      rw [Nat.add_mul, Nat.add_mul, Nat.add_mul] at hmul
      have hr1 : carry'.toNat * (2 ^ 64) ^ (j + (k + 1)) = carry'.toNat * 2 ^ 64 * (2 ^ 64) ^ (j + k) := by
        rw [hpow1, Nat.mul_assoc]
      have hr2 : qhat.toNat * ((getLimb vn k).toNat * (2 ^ 64) ^ k) * (2 ^ 64) ^ j =
          qhat.toNat * (getLimb vn k).toNat * (2 ^ 64) ^ (j + k) := by
        calc qhat.toNat * ((getLimb vn k).toNat * (2 ^ 64) ^ k) * (2 ^ 64) ^ j
            = (qhat.toNat * (getLimb vn k).toNat) * ((2 ^ 64) ^ k * (2 ^ 64) ^ j) := by ac_rfl
          _ = qhat.toNat * (getLimb vn k).toNat * (2 ^ 64) ^ (j + k) := by rw [hpow2]
      rw [hr1, hr2] at heq'
      omega

private theorem knuthStepInv_eq_knuthStep (rem vn q : Array UInt64) (j n : Nat)
    (vn1 vn2 : UInt64) (hvn1 : 2 ^ 63 ≤ vn1.toNat) :
    knuthStepInv rem vn q j n vn1 vn2 (invert21 vn1 hvn1) =
      knuthStep rem vn q j n vn1 vn2 := by
  unfold knuthStepInv knuthStep
  dsimp only
  rw [trialQhatInv_eq_trialQhat _ _ _ vn1 vn2 hvn1]

private theorem knuthLoopInv_eq_knuthLoop (rem vn q : Array UInt64)
    (vn1 vn2 : UInt64) (hvn1 : 2 ^ 63 ≤ vn1.toNat) (steps : Nat) :
    knuthLoopInv rem vn q vn1 vn2 (invert21 vn1 hvn1) steps =
      knuthLoop rem vn q vn.size vn1 vn2 steps := by
  induction steps generalizing rem q with
  | zero => rfl
  | succ j ih =>
    unfold knuthLoopInv knuthLoop
    dsimp only
    rw [knuthStepInv_eq_knuthStep rem vn q j vn.size vn1 vn2 hvn1]
    exact ih _ _

/-! ### Knuth Algorithm D: Main Loop and Top-Level `divMod` -/

private theorem knuthStep_spec (rem vn q : Array UInt64) (j n : Nat)
    (hn : 2 ≤ n) (hvn_sz : vn.size = n)
    (hnorm : 2 ^ 63 ≤ (getLimb vn (n - 1)).toNat)
    (hrem_sz : j + n < rem.size) (hq_sz : j < q.size)
    (hrem_lt : toNat rem < toNat vn * (2 ^ 64) ^ (j + 1))
    (hq_lo : ∀ k ≤ j, getLimb q k = 0) :
    let res := knuthStep rem vn q j n (getLimb vn (n - 1)) (getLimb vn (n - 2))
    res.1.size = q.size ∧
    res.2.size = rem.size ∧
    toNat res.1 * toNat vn + toNat res.2 = toNat q * toNat vn + toNat rem ∧
    toNat res.2 < toNat vn * (2 ^ 64) ^ j ∧
    (∀ k < j, getLimb res.1 k = 0) := by
  unfold knuthStep
  dsimp only
  have ⟨hthB_hi, hthB_lo⟩ := trialQhat_theorem_B rem vn j n hn hvn_sz hnorm hrem_lt
  generalize trialQhat (getLimb rem (j + n)) (getLimb rem (j + n - 1)) (getLimb rem (j + n - 2))
      (getLimb vn (n - 1)) (getLimb vn (n - 2)) = qhat at hthB_hi hthB_lo ⊢
  by_cases hq0_case : qhat == 0
  · simp only [hq0_case, ↓reduceIte]
    have hqz : qhat = 0 := eq_of_beq hq0_case
    subst hqz
    simp only [UInt64.toNat_zero, Nat.zero_add, Nat.one_mul] at hthB_hi
    exact ⟨trivial, trivial, trivial, hthB_hi, fun k hk => hq_lo k (Nat.le_of_lt hk)⟩
  · simp only [hq0_case, Bool.false_eq_true, ↓reduceIte]
    have hvn_lt : toNat vn < (2 ^ 64) ^ n := by rw [← hvn_sz]; exact toNat_lt vn
    have hrem_pow : toNat rem < (2 ^ 64) ^ (j + n + 1) := by
      have h1 : toNat vn * (2 ^ 64) ^ (j + 1) ≤ (2 ^ 64) ^ n * (2 ^ 64) ^ (j + 1) :=
        Nat.mul_le_mul_right _ (Nat.le_of_lt hvn_lt)
      have h2 : (2 ^ 64) ^ n * (2 ^ 64) ^ (j + 1) = (2 ^ 64) ^ (j + n + 1) := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [h2] at h1
      exact Nat.lt_of_lt_of_le hrem_lt h1
    have hrem_zero_hi : ∀ idx, j + n < idx → getLimb rem idx = 0 := by
      intro idx hidx
      apply Classical.byContradiction; intro hne
      have hpos : 1 ≤ (getLimb rem idx).toNat := by
        have : (getLimb rem idx).toNat ≠ 0 := fun h0 => hne (UInt64.toNat_inj.mp (by simpa using h0))
        omega
      have hge := toNat_ge_limb rem idx
      have hpow : (2 ^ 64) ^ (j + n + 1) ≤ (2 ^ 64) ^ idx :=
        Nat.pow_le_pow_right (Nat.two_pow_pos 64) (by omega)
      have h1 : (2 ^ 64) ^ idx ≤ (getLimb rem idx).toNat * (2 ^ 64) ^ idx :=
        Nat.le_mul_of_pos_left _ hpos
      exact Nat.not_lt_of_ge (Nat.le_trans hpow (Nat.le_trans h1 hge)) hrem_pow
    have ⟨hsub_sz, hsub_hi, hsub_eq⟩ := subMulCarryLoop_props rem vn j 0 n qhat 0 (by omega)
    rcases hsub : subMulCarryLoop rem vn j 0 qhat 0 n with ⟨rem1, borrow⟩
    rw [hsub] at hsub_sz hsub_hi hsub_eq
    dsimp only at hsub_sz hsub_hi hsub_eq ⊢
    have hvn_to : toNatPrefix vn n = toNat vn := by unfold toNat; rw [hvn_sz]
    simp only [Nat.add_zero, Nat.zero_add, toNatPrefix_zero, UInt64.toNat_zero,
      Nat.mul_zero, Nat.zero_mul, Nat.add_zero] at hsub_hi hsub_eq
    rw [hvn_to] at hsub_eq
    have hrem1_lt_pow : toNat rem1 < (2 ^ 64) ^ (j + n + 1) :=
      toNat_lt_of_upper_zero rem1 (j + n + 1) (fun idx hidx => by
        rw [hsub_hi idx hidx, hrem_zero_hi idx hidx])
    have hq0 : getLimb q j = 0 := hq_lo j (Nat.le_refl j)
    cases borrow
    · simp only [Bool.false_eq_true, ↓reduceIte]
      simp only [Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at hsub_eq
      refine ⟨size_setLimb _ _ _, hsub_sz, ?_, ?_, ?_⟩
      · rw [toNat_setLimb_of_zero q j qhat hq_sz hq0, Nat.add_mul]
        have hcomm : qhat.toNat * (2 ^ 64) ^ j * toNat vn = qhat.toNat * toNat vn * (2 ^ 64) ^ j := by
          rw [Nat.mul_assoc, Nat.mul_comm ((2 ^ 64) ^ j) (toNat vn), ← Nat.mul_assoc]
        rw [hcomm, Nat.add_assoc, Nat.add_comm (qhat.toNat * toNat vn * (2 ^ 64) ^ j), hsub_eq]
      · rw [Nat.add_mul, Nat.one_mul, Nat.add_mul] at hthB_hi
        rw [← hsub_eq, Nat.add_comm (toNat rem1)] at hthB_hi
        exact Nat.lt_of_add_lt_add_left hthB_hi
      · intro k hk
        rw [getLimb_setLimb q j qhat hq_sz k]
        simp [Nat.ne_of_lt hk, hq_lo k (Nat.le_of_lt hk)]
    · simp only [↓reduceIte]
      simp only [Bool.toNat_true, Nat.one_mul] at hsub_eq
      have hqpos : 1 ≤ qhat.toNat := by
        apply Classical.byContradiction; intro h0
        have hz : qhat.toNat = 0 := Nat.eq_zero_of_not_pos (fun hp => h0 hp)
        rw [hz, Nat.zero_mul, Nat.zero_mul, Nat.add_zero] at hsub_eq
        have hge : (2 ^ 64) ^ (j + n + 1) ≤ toNat rem1 := by
          rw [hsub_eq]; exact Nat.le_add_left _ _
        exact Nat.not_lt_of_ge hge hrem1_lt_pow
      have hqdec : (qhat - 1).toNat = qhat.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; exact hqpos)]
        rfl
      have hrem_lt_qhat : toNat rem < qhat.toNat * toNat vn * (2 ^ 64) ^ j := by
        have hlt : toNat rem1 + qhat.toNat * toNat vn * (2 ^ 64) ^ j >
            toNat rem1 + toNat rem := by
          rw [hsub_eq, Nat.add_comm (toNat rem1)]
          exact Nat.add_lt_add_left hrem1_lt_pow _
        exact Nat.lt_of_add_lt_add_left hlt
      have ⟨hadd_sz, hadd_hi, cOut, hadd_eq⟩ := addShiftLoop_props rem1 vn j n 0 false
        (Nat.zero_le n) (hsub_sz.symm ▸ hrem_sz) hvn_sz
      rw [toNatPrefix_zero, Nat.zero_mul, Nat.add_zero, Bool.toNat_false, Nat.zero_mul,
          Nat.add_zero (toNat rem1)] at hadd_eq
      generalize addShiftLoop rem1 vn j n 0 false = rem2 at hadd_sz hadd_hi hadd_eq ⊢
      have hrem2_lt_pow : toNat rem2 < (2 ^ 64) ^ (j + n + 1) :=
        toNat_lt_of_upper_zero rem2 (j + n + 1) (fun idx hidx => by
          rw [hadd_hi idx hidx, hsub_hi idx hidx, hrem_zero_hi idx hidx])
      have hsplit_q : qhat.toNat * toNat vn * (2 ^ 64) ^ j =
          (qhat.toNat - 1) * toNat vn * (2 ^ 64) ^ j + toNat vn * (2 ^ 64) ^ j := by
        calc qhat.toNat * toNat vn * (2 ^ 64) ^ j
            = ((qhat.toNat - 1) + 1) * (toNat vn * (2 ^ 64) ^ j) := by
              rw [Nat.sub_add_cancel hqpos, Nat.mul_assoc]
          _ = (qhat.toNat - 1) * toNat vn * (2 ^ 64) ^ j + toNat vn * (2 ^ 64) ^ j := by
              rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
      have hsum : toNat rem2 + cOut.toNat * (2 ^ 64) ^ (j + n + 1) +
          (qhat.toNat - 1) * toNat vn * (2 ^ 64) ^ j =
          toNat rem + (2 ^ 64) ^ (j + n + 1) := by
        have h1 : toNat rem2 + cOut.toNat * (2 ^ 64) ^ (j + n + 1) +
            (qhat.toNat - 1) * toNat vn * (2 ^ 64) ^ j =
            toNat rem1 + (toNat vn * (2 ^ 64) ^ j + (qhat.toNat - 1) * toNat vn * (2 ^ 64) ^ j) := by
          rw [hadd_eq, Nat.add_assoc]
        rw [h1, Nat.add_comm (toNat vn * (2 ^ 64) ^ j), ← hsplit_q, hsub_eq]
      have hcOut : cOut.toNat = 1 := by
        cases cOut
        · simp only [Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at hsum
          have hlt : toNat rem2 + (qhat.toNat - 1) * toNat vn * (2 ^ 64) ^ j <
              (2 ^ 64) ^ (j + n + 1) + toNat rem :=
            Nat.add_lt_add_of_lt_of_le hrem2_lt_pow hthB_lo
          rw [hsum, Nat.add_comm] at hlt
          exact absurd hlt (Nat.lt_irrefl _)
        · rfl
      rw [hcOut, Nat.one_mul] at hsum
      have hrem2_eq : toNat rem2 + (qhat.toNat - 1) * toNat vn * (2 ^ 64) ^ j = toNat rem := by
        apply Nat.add_right_cancel (m := (2 ^ 64) ^ (j + n + 1))
        calc toNat rem2 + (qhat.toNat - 1) * toNat vn * (2 ^ 64) ^ j + (2 ^ 64) ^ (j + n + 1)
            = toNat rem2 + (2 ^ 64) ^ (j + n + 1) + (qhat.toNat - 1) * toNat vn * (2 ^ 64) ^ j := by
              rw [Nat.add_assoc, Nat.add_comm ((qhat.toNat - 1) * toNat vn * (2 ^ 64) ^ j), ← Nat.add_assoc]
          _ = toNat rem + (2 ^ 64) ^ (j + n + 1) := hsum
      refine ⟨size_setLimb _ _ _, by rw [hadd_sz, hsub_sz], ?_, ?_, ?_⟩
      · rw [toNat_setLimb_of_zero q j (qhat - 1) hq_sz hq0, hqdec, Nat.add_mul]
        have hcomm : (qhat.toNat - 1) * (2 ^ 64) ^ j * toNat vn =
            (qhat.toNat - 1) * toNat vn * (2 ^ 64) ^ j := by
          rw [Nat.mul_assoc, Nat.mul_comm ((2 ^ 64) ^ j) (toNat vn), ← Nat.mul_assoc]
        rw [hcomm, Nat.add_assoc, Nat.add_comm ((qhat.toNat - 1) * toNat vn * (2 ^ 64) ^ j), hrem2_eq]
      · rw [← hrem2_eq, hsplit_q, Nat.add_comm (toNat rem2)] at hrem_lt_qhat
        exact Nat.lt_of_add_lt_add_left hrem_lt_qhat
      · intro k hk
        rw [getLimb_setLimb q j (qhat - 1) hq_sz k]
        simp [Nat.ne_of_lt hk, hq_lo k (Nat.le_of_lt hk)]

private theorem knuthLoop_spec (rem vn q : Array UInt64) (n steps : Nat)
    (hn : 2 ≤ n) (hvn_sz : vn.size = n)
    (hnorm : 2 ^ 63 ≤ (getLimb vn (n - 1)).toNat)
    (hrem_sz : steps + n ≤ rem.size) (hq_sz : steps ≤ q.size)
    (hrem_lt : toNat rem < toNat vn * (2 ^ 64) ^ steps)
    (hq_lo : ∀ k < steps, getLimb q k = 0) :
    let res := knuthLoop rem vn q n (getLimb vn (n - 1)) (getLimb vn (n - 2)) steps
    toNat res.1 * toNat vn + toNat res.2 = toNat q * toNat vn + toNat rem ∧
    toNat res.2 < toNat vn := by
  induction steps generalizing rem q with
  | zero =>
    unfold knuthLoop
    simp only [Nat.pow_zero, Nat.mul_one] at hrem_lt ⊢
    exact ⟨trivial, hrem_lt⟩
  | succ j ih =>
    unfold knuthLoop
    dsimp only
    have ⟨hq'_sz, hrem'_sz, hstep_eq, hrem'_lt, hq'_lo⟩ :=
      knuthStep_spec rem vn q j n hn hvn_sz hnorm (by omega) (by omega) hrem_lt
        (fun k hk => hq_lo k (by omega))
    rcases hs : knuthStep rem vn q j n (getLimb vn (n - 1)) (getLimb vn (n - 2)) with ⟨q', rem'⟩
    rw [hs] at hq'_sz hrem'_sz hstep_eq hrem'_lt hq'_lo
    dsimp only at hq'_sz hrem'_sz hstep_eq hrem'_lt hq'_lo ⊢
    have ⟨hloop_eq, hloop_lt⟩ := ih rem' q' (by omega) (by omega) hrem'_lt hq'_lo
    exact ⟨by omega, hloop_lt⟩

private theorem divModKnuthRaw_eq_knuthLoop (u v : Array UInt64)
    (hvn_sz : (shiftLeftSmall v (clz64 (getLimb v (v.size - 1))).toNat).size = v.size)
    (hnorm : 2 ^ 63 ≤ (getLimb (shiftLeftSmall v (clz64 (getLimb v (v.size - 1))).toNat) (v.size - 1)).toNat) :
    let n := v.size
    let m := u.size - n
    let s := (clz64 (getLimb v (n - 1))).toNat
    let vn := shiftLeftSmall v s
    let un := padZeros (shiftLeftSmall u s) (m + n + 1)
    let vn1 := getLimb vn (n - 1)
    let vn2 := getLimb vn (n - 2)
    let raw := divModKnuthRaw u v
    (raw.1, raw.2.1) = knuthLoop un vn (mkZeros (m + 1)) n vn1 vn2 (m + 1) ∧
    raw.2.2 = s := by
  unfold divModKnuthRaw
  dsimp only
  have hshr_ne : (getLimb (shiftLeftSmall v (clz64 (getLimb v (v.size - 1))).toNat) (v.size - 1) >>> (63 : UInt64)) ≠ 0 := by
    intro h0
    have hto := congrArg UInt64.toNat h0
    rw [UInt64.toNat_shiftRight, show (63 : UInt64).toNat % 64 = 63 from rfl,
        Nat.shiftRight_eq_div_pow, UInt64.toNat_zero] at hto
    have : 1 ≤ (getLimb (shiftLeftSmall v (clz64 (getLimb v (v.size - 1))).toNat) (v.size - 1)).toNat / 2 ^ 63 :=
      (Nat.le_div_iff_mul_le (Nat.two_pow_pos 63)).mpr (by omega)
    omega
  split
  · refine ⟨?_, rfl⟩
    rw [knuthLoopInv_eq_knuthLoop, hvn_sz]
  · rename_i hnot
    exact absurd hshr_ne hnot

theorem divModKnuth_spec (u v : Array UInt64)
    (_hu : WF u) (hv : WF v) (hge2 : 2 ≤ v.size) (hle : v.size ≤ u.size) :
    let res := divModKnuth u v
    WF res.1 ∧ WF res.2 ∧
    toNat res.1 = toNat u / toNat v ∧
    toNat res.2 = toNat u % toNat v := by
  unfold divModKnuth
  let n := v.size
  let m := u.size - n
  let vTop := getLimb v (n - 1)
  have hvTop_ne : vTop ≠ 0 := by
    rcases hv with h0 | hne
    · omega
    · exact hne
  let s := (clz64 vTop).toNat
  have hs_lt : s < 64 := clz64_lt_64 vTop hvTop_ne
  have ⟨hnorm_lo, hnorm_hi⟩ := clz64_shift_norm vTop hvTop_ne
  let vn := shiftLeftSmall v s
  let un := padZeros (shiftLeftSmall u s) (m + n + 1)
  have hvn_wf : WF vn := wf_shiftLeftSmall v s
  have hvn_toNat : toNat vn = toNat v * 2 ^ s := toNat_shiftLeftSmall v s hs_lt
  have hun_toNat : toNat un = toNat u * 2 ^ s := by
    rw [toNat_padZeros, toNat_shiftLeftSmall u s hs_lt]
  -- Prove vn.size = n and 2^63 ≤ (getLimb vn (n - 1)).toNat
  have hv_decomp : toNat v = toNatPrefix v (n - 1) + vTop.toNat * (2 ^ 64) ^ (n - 1) := by
    have hn1 : n = (n - 1) + 1 := by omega
    unfold toNat
    conv => lhs; rw [show v.size = (n - 1) + 1 from hn1]
    rw [toNatPrefix_succ]
  have hv_pref_lt : toNatPrefix v (n - 1) < (2 ^ 64) ^ (n - 1) := toNatPrefix_lt v (n - 1)
  have hvn_lt : toNat vn < (2 ^ 64) ^ n := by
    rw [hvn_toNat]
    have ⟨_, hvTop_hi⟩ := clz64_spec vTop hvTop_ne
    have h5 : (vTop.toNat + 1) * 2 ^ s ≤ 2 ^ 64 := by
      have := Nat.mul_le_mul_right (2 ^ s) hvTop_hi
      rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hs_lt)] at this
      exact this
    have h6 : toNat v < (vTop.toNat + 1) * (2 ^ 64) ^ (n - 1) := by
      rw [hv_decomp, Nat.add_mul, Nat.one_mul]; omega
    have h7 : toNat v * 2 ^ s < (vTop.toNat + 1) * (2 ^ 64) ^ (n - 1) * 2 ^ s :=
      Nat.mul_lt_mul_of_pos_right h6 (Nat.two_pow_pos s)
    have h8 : (vTop.toNat + 1) * (2 ^ 64) ^ (n - 1) * 2 ^ s ≤ (2 ^ 64) ^ n := by
      calc (vTop.toNat + 1) * (2 ^ 64) ^ (n - 1) * 2 ^ s
          = (vTop.toNat + 1) * 2 ^ s * (2 ^ 64) ^ (n - 1) := by
            rw [Nat.mul_assoc, Nat.mul_comm ((2 ^ 64) ^ (n - 1)) (2 ^ s), ← Nat.mul_assoc]
        _ ≤ 2 ^ 64 * (2 ^ 64) ^ (n - 1) := Nat.mul_le_mul_right _ h5
        _ = (2 ^ 64) ^ n := by
            have hn1 : n = (n - 1) + 1 := by omega
            conv => rhs; rw [hn1]
            rw [Nat.pow_succ (2 ^ 64), Nat.mul_comm]
    exact Nat.lt_of_lt_of_le h7 h8
  have hvn_ge : 2 ^ 63 * (2 ^ 64) ^ (n - 1) ≤ toNat vn := by
    rw [hvn_toNat]
    have h1 : vTop.toNat * (2 ^ 64) ^ (n - 1) ≤ toNat v := toNat_ge_limb v (n - 1)
    calc 2 ^ 63 * (2 ^ 64) ^ (n - 1)
        ≤ vTop.toNat * 2 ^ s * (2 ^ 64) ^ (n - 1) := Nat.mul_le_mul_right _ hnorm_lo
      _ = vTop.toNat * (2 ^ 64) ^ (n - 1) * 2 ^ s := by
          rw [Nat.mul_assoc, Nat.mul_comm (2 ^ s), ← Nat.mul_assoc]
      _ ≤ toNat v * 2 ^ s := Nat.mul_le_mul_right _ h1
  have hvn_sz : vn.size = n := by
    apply Classical.byContradiction; intro hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : toNat vn < (2 ^ 64) ^ vn.size := toNat_lt vn
      have h2 : (2 ^ 64) ^ vn.size ≤ (2 ^ 64) ^ (n - 1) :=
        Nat.pow_le_pow_right (Nat.two_pow_pos 64) (by omega)
      have h3 : (2 ^ 64) ^ (n - 1) ≤ 2 ^ 63 * (2 ^ 64) ^ (n - 1) :=
        Nat.le_mul_of_pos_left _ (Nat.two_pow_pos 63)
      omega
    · have h1 : (2 ^ 64) ^ (vn.size - 1) ≤ toNat vn := toNat_ge_top vn hvn_wf (by omega)
      have h2 : (2 ^ 64) ^ n ≤ (2 ^ 64) ^ (vn.size - 1) :=
        Nat.pow_le_pow_right (Nat.two_pow_pos 64) (by omega)
      omega
  have hnorm : 2 ^ 63 ≤ (getLimb vn (n - 1)).toNat := by
    have hvn_top : toNat vn < ((getLimb vn (n - 1)).toNat + 1) * (2 ^ 64) ^ (n - 1) := by
      have hn1 : vn.size = (n - 1) + 1 := by omega
      have hto : toNat vn = toNatPrefix vn (n - 1) + (getLimb vn (n - 1)).toNat * (2 ^ 64) ^ (n - 1) := by
        unfold toNat
        conv => lhs; rw [hn1]
        rw [toNatPrefix_succ]
      have hp := toNatPrefix_lt vn (n - 1)
      rw [hto, Nat.add_mul, Nat.one_mul]; omega
    have hlt := Nat.lt_of_le_of_lt hvn_ge hvn_top
    have hlt' := Nat.lt_of_mul_lt_mul_right hlt
    omega
  have ⟨hraw_eq, hraw_s⟩ := divModKnuthRaw_eq_knuthLoop u v hvn_sz hnorm
  dsimp only at hraw_eq hraw_s ⊢
  rcases hraw : divModKnuthRaw u v with ⟨q, rem, sRaw⟩
  rw [hraw] at hraw_eq hraw_s
  dsimp only at hraw_eq hraw_s ⊢
  subst hraw_s
  have hun_lt : toNat un < toNat vn * (2 ^ 64) ^ (m + 1) := by
    rw [hun_toNat, hvn_toNat]
    have hu_lt : toNat u < (2 ^ 64) ^ u.size := toNat_lt u
    have hv_ge : (2 ^ 64) ^ (n - 1) ≤ toNat v := toNat_ge_top v hv (by omega)
    have h1 : (2 ^ 64) ^ u.size = (2 ^ 64) ^ (n - 1) * (2 ^ 64) ^ (m + 1) := by
      rw [← Nat.pow_add]; congr 1; omega
    have h2 : toNat u < toNat v * (2 ^ 64) ^ (m + 1) := by
      calc toNat u < (2 ^ 64) ^ u.size := hu_lt
        _ = (2 ^ 64) ^ (n - 1) * (2 ^ 64) ^ (m + 1) := h1
        _ ≤ toNat v * (2 ^ 64) ^ (m + 1) := Nat.mul_le_mul_right _ hv_ge
    calc toNat u * 2 ^ s
        < toNat v * (2 ^ 64) ^ (m + 1) * 2 ^ s := Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos s)
      _ = toNat v * 2 ^ s * (2 ^ 64) ^ (m + 1) := by
          rw [Nat.mul_assoc, Nat.mul_comm ((2 ^ 64) ^ (m + 1)) (2 ^ s), ← Nat.mul_assoc]
  have hun_sz : m + 1 + n ≤ un.size := by
    rw [size_padZeros]; omega
  have ⟨hloop_eq, hloop_lt⟩ := knuthLoop_spec un vn (mkZeros (m + 1)) n (m + 1)
    hge2 hvn_sz hnorm hun_sz (by rw [size_mkZeros]; exact Nat.le_refl _) hun_lt (fun k _ => getLimb_mkZeros _ k)
  rw [← hraw_eq] at hloop_eq hloop_lt
  dsimp only at hloop_eq hloop_lt ⊢
  rw [toNat_mkZeros, Nat.zero_mul, Nat.zero_add, hun_toNat, hvn_toNat] at hloop_eq
  rw [hvn_toNat] at hloop_lt
  -- Unnormalize: divide hloop_eq by 2^s
  have h2s_pos : 0 < 2 ^ s := Nat.two_pow_pos s
  have hrem_div_lt : toNat rem / 2 ^ s < toNat v := by
    rw [Nat.div_lt_iff_lt_mul h2s_pos]
    exact hloop_lt
  have hrem_dvd : 2 ^ s ∣ toNat rem := by
    have h1 : toNat rem = (toNat u - toNat q * toNat v) * 2 ^ s := by
      have hmul : toNat q * (toNat v * 2 ^ s) = (toNat q * toNat v) * 2 ^ s :=
        (Nat.mul_assoc _ _ _).symm
      rw [hmul] at hloop_eq
      rw [Nat.sub_mul]
      omega
    exact ⟨toNat u - toNat q * toNat v, by rw [h1, Nat.mul_comm]⟩
  have hrem_exact : (toNat rem / 2 ^ s) * 2 ^ s = toNat rem := by
    rw [Nat.mul_comm]; exact Nat.mul_div_cancel' hrem_dvd
  have hdecomp : toNat q * toNat v + toNat rem / 2 ^ s = toNat u := by
    have h1 : (toNat q * toNat v + toNat rem / 2 ^ s) * 2 ^ s = toNat u * 2 ^ s := by
      rw [Nat.add_mul, Nat.mul_assoc, hrem_exact]
      exact hloop_eq
    exact Nat.eq_of_mul_eq_mul_right h2s_pos h1
  have hv_pos : 0 < toNat v := toNat_pos_of_ne_zero v hv (by omega)
  refine ⟨wf_normalize q, wf_shiftRightSmall rem s, ?_, ?_⟩
  · rw [toNat_normalize]
    have h1 : (toNat q * toNat v + toNat rem / 2 ^ s) / toNat v = toNat q := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hv_pos, Nat.div_eq_of_lt hrem_div_lt, Nat.zero_add]
    rw [← h1, hdecomp]
  · rw [toNat_shiftRightSmall rem s hs_lt]
    have h1 : (toNat q * toNat v + toNat rem / 2 ^ s) % toNat v = toNat rem / 2 ^ s := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrem_div_lt]
    rw [← h1, hdecomp]

theorem wf_divMod (u v : Array UInt64) : WF (divMod u v).1 ∧ WF (divMod u v).2 := by
  unfold divMod
  dsimp only
  split
  · exact ⟨Or.inl rfl, wf_normalize u⟩
  · split
    · exact ⟨Or.inl rfl, wf_normalize u⟩
    · split
      · exact ⟨wf_divMod1 _ _, wf_ofUInt64 _⟩
      · rename_i hne0 hnotlt hne1
        have hu := wf_normalize u
        have hv := wf_normalize v
        have hge2 : 2 ≤ (normalize v).size := by
          have h0 : (normalize v).size ≠ 0 := fun h => hne0 (by simp [h])
          have h1 : (normalize v).size ≠ 1 := fun h => hne1 (by simp [h])
          omega
        have hle : (normalize v).size ≤ (normalize u).size := by
          apply Classical.byContradiction; intro hlt
          have hltNat : toNat (normalize u) < toNat (normalize v) := by
            have h1 : toNat (normalize u) < (2 ^ 64) ^ (normalize u).size := toNat_lt _
            have h2 : (2 ^ 64) ^ ((normalize v).size - 1) ≤ toNat (normalize v) :=
              toNat_ge_top _ hv (by omega)
            have h3 : (2 ^ 64) ^ (normalize u).size ≤ (2 ^ 64) ^ ((normalize v).size - 1) :=
              Nat.pow_le_pow_right (Nat.two_pow_pos 64) (by omega)
            omega
          have hcmp := cmp_spec hu hv
          rw [show compare (toNat (normalize u)) (toNat (normalize v)) = .lt by
            simp [compare, compareOfLessAndEq, hltNat]] at hcmp
          exact hnotlt (by rw [hcmp]; rfl)
        have ⟨h1, h2, _, _⟩ := divModKnuth_spec _ _ hu hv hge2 hle
        exact ⟨h1, h2⟩

theorem divMod_spec (u v : Array UInt64) :
    WF (divMod u v).1 ∧ WF (divMod u v).2 ∧
    toNat (divMod u v).1 = toNat u / toNat v ∧
    toNat (divMod u v).2 = toNat u % toNat v := by
  unfold divMod
  dsimp only
  have hu := wf_normalize u
  have hv := wf_normalize v
  have htu : toNat (normalize u) = toNat u := toNat_normalize u
  have htv : toNat (normalize v) = toNat v := toNat_normalize v
  split
  · rename_i hv0
    have hsz0 : (normalize v).size = 0 := eq_of_beq hv0
    have hvz : toNat v = 0 := by rw [← htv, toNat, hsz0]; rfl
    rw [hvz, Nat.div_zero, Nat.mod_zero]
    exact ⟨Or.inl rfl, hu, rfl, htu⟩
  · rename_i hvne0
    split
    · rename_i hcmp
      have hlt : cmp (normalize u) (normalize v) = .lt := eq_of_beq hcmp
      rw [cmp_spec hu hv, htu, htv] at hlt
      have hnat : toNat u < toNat v := by
        simp only [compare, compareOfLessAndEq] at hlt
        split at hlt
        · assumption
        · split at hlt <;> simp at hlt
      exact ⟨Or.inl rfl, hu, by simp [Nat.div_eq_of_lt hnat], by rw [htu, Nat.mod_eq_of_lt hnat]⟩
    · rename_i hnotlt
      split
      · rename_i hv1
        have hsz1 : (normalize v).size = 1 := eq_of_beq hv1
        have hd_ne : getLimb (normalize v) 0 ≠ 0 := by
          rcases hv with h0 | hne
          · omega
          · rw [hsz1] at hne; simpa using hne
        have htv1 : toNat v = (getLimb (normalize v) 0).toNat := by
          rw [← htv, toNat, hsz1, toNatPrefix_succ, toNatPrefix_zero]
          simp only [Nat.pow_zero, Nat.mul_one, Nat.zero_add]
        have ⟨hwf1, hdiv1, hmod1, _⟩ := divMod1_spec (normalize u) (getLimb (normalize v) 0) hd_ne
        rw [htu, ← htv1] at hdiv1 hmod1
        refine ⟨hwf1, wf_ofUInt64 _, hdiv1, ?_⟩
        rw [toNat_ofUInt64, hmod1]
      · rename_i hvne1
        have hge2 : 2 ≤ (normalize v).size := by
          have h0 : (normalize v).size ≠ 0 := fun h => hvne0 (by simp [h])
          have h1 : (normalize v).size ≠ 1 := fun h => hvne1 (by simp [h])
          omega
        have hle : (normalize v).size ≤ (normalize u).size := by
          apply Classical.byContradiction; intro hlt
          have hltNat : toNat (normalize u) < toNat (normalize v) := by
            have h1 : toNat (normalize u) < (2 ^ 64) ^ (normalize u).size := toNat_lt _
            have h2 : (2 ^ 64) ^ ((normalize v).size - 1) ≤ toNat (normalize v) :=
              toNat_ge_top _ hv (by omega)
            have h3 : (2 ^ 64) ^ (normalize u).size ≤ (2 ^ 64) ^ ((normalize v).size - 1) :=
              Nat.pow_le_pow_right (Nat.two_pow_pos 64) (by omega)
            omega
          have hcmp := cmp_spec hu hv
          rw [show compare (toNat (normalize u)) (toNat (normalize v)) = .lt by
            simp [compare, compareOfLessAndEq, hltNat]] at hcmp
          exact hnotlt (by rw [hcmp]; rfl)
        have ⟨h1, h2, h3, h4⟩ := divModKnuth_spec _ _ hu hv hge2 hle
        rw [htu, htv] at h3 h4
        exact ⟨h1, h2, h3, h4⟩

/-! ### O(1) Single-Limb Quotient Fast Path (`divQuick1`) and `div` / `mod` -/

private theorem div_eq_of_bracket {U V q : Nat} (hV : 0 < V)
    (hlo : q * V ≤ U) (hhi : U < (q + 1) * V) : U / V = q := by
  have h1 : q ≤ U / V := (Nat.le_div_iff_mul_le hV).mpr hlo
  have h2 : U / V < q + 1 := (Nat.div_lt_iff_lt_mul hV).mpr hhi
  omega

private theorem divQuick1_bracket {U V Utop Vtop P qh rh : Nat}
    (hP : 0 < P) (hVtop : 0 < Vtop)
    (hUlo : Utop * P ≤ U) (hUhi : U < (Utop + 1) * P)
    (hVlo : Vtop * P ≤ V) (hVhi : V < (Vtop + 1) * P)
    (hdm : qh * Vtop + rh = Utop) (hrh : rh < Vtop) (hqle : qh ≤ rh) :
    U / V = qh := by
  have hVpos : 0 < V := by
    have : 0 < Vtop * P := Nat.mul_pos hVtop hP
    omega
  apply div_eq_of_bracket hVpos
  · have hq1 : qh * (Vtop + 1) ≤ Utop := by rw [Nat.mul_add, Nat.mul_one]; omega
    have h1 : qh * V ≤ qh * ((Vtop + 1) * P) := Nat.mul_le_mul_left qh (Nat.le_of_lt hVhi)
    have h2 : qh * ((Vtop + 1) * P) = (qh * (Vtop + 1)) * P := (Nat.mul_assoc _ _ _).symm
    have h3 : (qh * (Vtop + 1)) * P ≤ Utop * P := Nat.mul_le_mul_right P hq1
    omega
  · have hq2 : Utop + 1 ≤ (qh + 1) * Vtop := by rw [Nat.add_mul, Nat.one_mul]; omega
    have h1 : (Utop + 1) * P ≤ ((qh + 1) * Vtop) * P := Nat.mul_le_mul_right P hq2
    have h2 : ((qh + 1) * Vtop) * P = (qh + 1) * (Vtop * P) := Nat.mul_assoc _ _ _
    have h3 : (qh + 1) * (Vtop * P) ≤ (qh + 1) * V := Nat.mul_le_mul_left _ hVlo
    omega

theorem divQuick1_spec (u v q : Array UInt64) (hq : divQuick1 u v = some q) :
    WF q ∧ toNat q = toNat u / toNat v := by
  unfold divQuick1 at hq
  dsimp only at hq
  split at hq
  · cases hq
  · rename_i hguard
    have hbounds : 2 ≤ v.size ∧ v.size ≤ u.size ∧ u.size ≤ v.size + 1 := by
      have h1 : ¬ v.size < 2 := fun h => hguard (by simp [h])
      have h2 : ¬ u.size < v.size := fun h => hguard (by simp [h])
      have h3 : ¬ v.size + 1 < u.size := fun h => hguard (by simp [h])
      omega
    let n := v.size
    let vTop := getLimb v (n - 1)
    split at hq
    · cases hq
    · rename_i hvTop0
      have hvTop_ne : vTop ≠ 0 := fun h => hvTop0 (by simp [vTop, n, h])
      have hvTop_pos : 0 < vTop.toNat := by
        have : vTop.toNat ≠ 0 := fun h0 => hvTop_ne (UInt64.toNat_inj.mp (by simpa using h0))
        omega
      let s := clz64 vTop
      have hs_lt : s.toNat < 64 := clz64_lt_64 vTop hvTop_ne
      have hP_pos : 0 < (2 ^ 64) ^ (n - 1) := Nat.pow_pos (Nat.two_pow_pos 64)
      have hu_decomp : toNat u = ((getLimb u n).toNat * 2 ^ 64 + (getLimb u (n - 1)).toNat) * (2 ^ 64) ^ (n - 1) +
          toNatPrefix u (n - 1) := by
        have hle : u.size ≤ n + 1 := hbounds.2.2
        have hto : toNat u = toNatPrefix u (n + 1) := (toNatPrefix_eq_toNat_of_le u hle).symm
        rw [hto, toNatPrefix_succ u n]
        have hn1 : n = (n - 1) + 1 := by omega
        conv => lhs; rw [show toNatPrefix u n = toNatPrefix u ((n - 1) + 1) by rw [← hn1]]
        rw [toNatPrefix_succ u (n - 1)]
        have hpow : (2 ^ 64) ^ n = 2 ^ 64 * (2 ^ 64) ^ (n - 1) := by
          conv => lhs; rw [hn1]
          rw [Nat.pow_succ (2 ^ 64), Nat.mul_comm]
        rw [hpow, Nat.add_mul, Nat.mul_assoc]
        omega
      have hv_decomp : toNat v = vTop.toNat * (2 ^ 64) ^ (n - 1) + toNatPrefix v (n - 1) := by
        have hn1 : n = (n - 1) + 1 := by omega
        unfold toNat
        conv => lhs; rw [show v.size = (n - 1) + 1 from hn1]
        rw [toNatPrefix_succ, Nat.add_comm]
      split at hq
      · cases hq
      · rename_i hnoOv
        by_cases hs0 : (clz64 (getLimb v (v.size - 1)) == 0) = true
        · -- s == 0: already normalized
          simp only [hs0, ↓reduceIte] at hq
          split at hq
          · rename_i hlt
            split at hq
            · rename_i hqle
              cases hq
              have ⟨hdm, hrh⟩ := divWide64_spec (getLimb u n) (getLimb u (n - 1)) vTop hlt
              refine ⟨wf_ofUInt64 _, ?_⟩
              rw [toNat_ofUInt64]
              have hupref := toNatPrefix_lt u (n - 1)
              have hvpref := toNatPrefix_lt v (n - 1)
              exact (divQuick1_bracket hP_pos hvTop_pos
                (by omega) (by rw [Nat.add_mul, Nat.one_mul]; omega)
                (by omega) (by rw [Nat.add_mul, Nat.one_mul]; omega)
                hdm hrh (UInt64.le_iff_toNat_le.mp hqle)).symm
            · cases hq
          · cases hq
        · -- s > 0: shift top 3 limbs of u and top 2 limbs of v by s in O(1)
          have hs0f : (clz64 (getLimb v (v.size - 1)) == 0) = false := Bool.eq_false_iff.mpr hs0
          simp only [hs0f, Bool.false_eq_true, ↓reduceIte] at hq
          have hsne : s ≠ 0 := fun h => hs0 (by dsimp only [s, vTop, n] at h; simp [h])
          have hs_pos : 0 < s.toNat := by
            have : s.toNat ≠ 0 := fun h0 => hsne (UInt64.toNat_inj.mp (by simpa using h0))
            omega
          have hinv_val : ((64 : UInt64) - s).toNat = 64 - s.toNat := by
            rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; exact Nat.le_of_lt hs_lt)]
            rfl
          have huTop_shr0 : getLimb u n >>> ((64 : UInt64) - s) = 0 := by
            apply Classical.byContradiction; intro hne
            have h1 : (s != 0) = true := bne_iff_ne.mpr hsne
            have h2 : (getLimb u n >>> ((64 : UInt64) - s) != 0) = true := bne_iff_ne.mpr hne
            exact hnoOv (by dsimp only [s, vTop, n] at h1 h2; simp [h1, h2])
          have huTop_mul_lt : (getLimb u n).toNat * 2 ^ s.toNat < 2 ^ 64 := by
            have h0 := congrArg UInt64.toNat huTop_shr0
            rw [UInt64.toNat_shiftRight, hinv_val, Nat.mod_eq_of_lt (by omega),
                Nat.shiftRight_eq_div_pow, UInt64.toNat_zero] at h0
            have hlt_inv : (getLimb u n).toNat < 2 ^ (64 - s.toNat) :=
              Nat.lt_of_not_ge fun hge => by
                have : 1 ≤ (getLimb u n).toNat / 2 ^ (64 - s.toNat) :=
                  (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by omega)
                omega
            have hpow : 2 ^ (64 - s.toNat) * 2 ^ s.toNat = 2 ^ 64 := by
              rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hs_lt)]
            rw [← hpow]
            exact Nat.mul_lt_mul_of_pos_right hlt_inv (Nat.two_pow_pos _)
          have hvTop_mul_lt : vTop.toNat * 2 ^ s.toNat < 2 ^ 64 := (clz64_shift_norm vTop hvTop_ne).2
          have hpow64 : 2 ^ 64 = 2 ^ (64 - s.toNat) * 2 ^ s.toNat := by
            rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hs_lt)]
          -- Helper: x * 2^s = (x / 2^(64-s)) * 2^64 + (x * 2^s) % 2^64
          have hsplit_word : ∀ x : UInt64,
              x.toNat * 2 ^ s.toNat = (x.toNat / 2 ^ (64 - s.toNat)) * 2 ^ 64 + (x.toNat * 2 ^ s.toNat) % 2 ^ 64 := by
            intro x
            have hdm := Nat.div_add_mod x.toNat (2 ^ (64 - s.toNat))
            have hltm : x.toNat % 2 ^ (64 - s.toNat) < 2 ^ (64 - s.toNat) :=
              Nat.mod_lt _ (Nat.two_pow_pos _)
            have hmul_lt : (x.toNat % 2 ^ (64 - s.toNat)) * 2 ^ s.toNat < 2 ^ 64 := by
              rw [hpow64]; exact Nat.mul_lt_mul_of_pos_right hltm (Nat.two_pow_pos _)
            have hdecomp : x.toNat * 2 ^ s.toNat =
                (x.toNat / 2 ^ (64 - s.toNat)) * 2 ^ 64 + (x.toNat % 2 ^ (64 - s.toNat)) * 2 ^ s.toNat := by
              calc x.toNat * 2 ^ s.toNat
                  = (2 ^ (64 - s.toNat) * (x.toNat / 2 ^ (64 - s.toNat)) + x.toNat % 2 ^ (64 - s.toNat)) * 2 ^ s.toNat := by
                    rw [hdm]
                _ = 2 ^ (64 - s.toNat) * (x.toNat / 2 ^ (64 - s.toNat)) * 2 ^ s.toNat +
                    x.toNat % 2 ^ (64 - s.toNat) * 2 ^ s.toNat := by rw [Nat.add_mul]
                _ = (x.toNat / 2 ^ (64 - s.toNat)) * (2 ^ (64 - s.toNat) * 2 ^ s.toNat) +
                    x.toNat % 2 ^ (64 - s.toNat) * 2 ^ s.toNat := by
                    rw [Nat.mul_comm (2 ^ (64 - s.toNat)) (x.toNat / 2 ^ (64 - s.toNat)), Nat.mul_assoc]
                _ = (x.toNat / 2 ^ (64 - s.toNat)) * 2 ^ 64 + x.toNat % 2 ^ (64 - s.toNat) * 2 ^ s.toNat := by
                    rw [← hpow64]
            have hmod : (x.toNat * 2 ^ s.toNat) % 2 ^ 64 = (x.toNat % 2 ^ (64 - s.toNat)) * 2 ^ s.toNat := by
              rw [hdecomp, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hmul_lt]
            rw [hmod]; exact hdecomp
          have hmod_le_top : ∀ x : UInt64, (x.toNat * 2 ^ s.toNat) % 2 ^ 64 + 2 ^ s.toNat ≤ 2 ^ 64 := by
            intro x
            have hdm := Nat.div_add_mod x.toNat (2 ^ (64 - s.toNat))
            have hltm : x.toNat % 2 ^ (64 - s.toNat) < 2 ^ (64 - s.toNat) :=
              Nat.mod_lt _ (Nat.two_pow_pos _)
            have hle1 : (x.toNat % 2 ^ (64 - s.toNat) + 1) * 2 ^ s.toNat ≤ 2 ^ 64 := by
              rw [hpow64]; exact Nat.mul_le_mul_right _ hltm
            rw [Nat.add_mul, Nat.one_mul] at hle1
            have hmul_lt : (x.toNat % 2 ^ (64 - s.toNat)) * 2 ^ s.toNat < 2 ^ 64 := by
              have : 0 < 2 ^ s.toNat := Nat.two_pow_pos _; omega
            have h1 : (x.toNat * 2 ^ s.toNat) % 2 ^ 64 = (x.toNat % 2 ^ (64 - s.toNat)) * 2 ^ s.toNat := by
              have hdec : x.toNat * 2 ^ s.toNat =
                  (x.toNat / 2 ^ (64 - s.toNat)) * 2 ^ 64 + (x.toNat % 2 ^ (64 - s.toNat)) * 2 ^ s.toNat := by
                calc x.toNat * 2 ^ s.toNat
                    = (2 ^ (64 - s.toNat) * (x.toNat / 2 ^ (64 - s.toNat)) + x.toNat % 2 ^ (64 - s.toNat)) * 2 ^ s.toNat := by
                      rw [hdm]
                  _ = 2 ^ (64 - s.toNat) * (x.toNat / 2 ^ (64 - s.toNat)) * 2 ^ s.toNat +
                      x.toNat % 2 ^ (64 - s.toNat) * 2 ^ s.toNat := by rw [Nat.add_mul]
                  _ = (x.toNat / 2 ^ (64 - s.toNat)) * (2 ^ (64 - s.toNat) * 2 ^ s.toNat) +
                      x.toNat % 2 ^ (64 - s.toNat) * 2 ^ s.toNat := by
                      rw [Nat.mul_comm (2 ^ (64 - s.toNat)) (x.toNat / 2 ^ (64 - s.toNat)), Nat.mul_assoc]
                  _ = (x.toNat / 2 ^ (64 - s.toNat)) * 2 ^ 64 + x.toNat % 2 ^ (64 - s.toNat) * 2 ^ s.toNat := by
                      rw [← hpow64]
              rw [hdec, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hmul_lt]
            rw [h1]; exact hle1
          split at hq
          · rename_i hlt
            split at hq
            · rename_i hqle
              cases hq
              let vn1 := (vTop <<< s) ||| (getLimb v (n - 2) >>> ((64 : UInt64) - s))
              let u2 := (getLimb u n <<< s) ||| (getLimb u (n - 1) >>> ((64 : UInt64) - s))
              let u1 := (getLimb u (n - 1) <<< s) ||| (getLimb u (n - 2) >>> ((64 : UInt64) - s))
              have hvn1_val : vn1.toNat = vTop.toNat * 2 ^ s.toNat + (getLimb v (n - 2)).toNat / 2 ^ (64 - s.toNat) := by
                rw [shift_or_toNat vTop (getLimb v (n - 2)) s hs_pos hs_lt, Nat.mod_eq_of_lt hvTop_mul_lt]
              have hu2_val : u2.toNat = (getLimb u n).toNat * 2 ^ s.toNat + (getLimb u (n - 1)).toNat / 2 ^ (64 - s.toNat) := by
                rw [shift_or_toNat (getLimb u n) (getLimb u (n - 1)) s hs_pos hs_lt, Nat.mod_eq_of_lt huTop_mul_lt]
              have hu1_val : u1.toNat = ((getLimb u (n - 1)).toNat * 2 ^ s.toNat) % 2 ^ 64 +
                  (getLimb u (n - 2)).toNat / 2 ^ (64 - s.toNat) :=
                shift_or_toNat (getLimb u (n - 1)) (getLimb u (n - 2)) s hs_pos hs_lt
              have hvn1_pos : 0 < vn1.toNat := by
                have h1 : 2 ^ 63 ≤ vTop.toNat * 2 ^ s.toNat := (clz64_shift_norm vTop hvTop_ne).1
                rw [hvn1_val]
                exact Nat.lt_of_lt_of_le (Nat.two_pow_pos 63) (Nat.le_trans h1 (Nat.le_add_right _ _))
              -- Decompose toNatPrefix _ (n - 1) = toNatPrefix _ (n - 2) + limb (n - 2) * B^(n - 2)
              have hn2 : n - 1 = (n - 2) + 1 := by omega
              have hpow_n1 : (2 ^ 64) ^ (n - 1) = 2 ^ 64 * (2 ^ 64) ^ (n - 2) := by
                conv => lhs; rw [hn2]
                rw [Nat.pow_succ (2 ^ 64), Nat.mul_comm]
              have hu_pref : toNatPrefix u (n - 1) =
                  toNatPrefix u (n - 2) + (getLimb u (n - 2)).toNat * (2 ^ 64) ^ (n - 2) := by
                conv => lhs; rw [hn2]
                rw [toNatPrefix_succ]
              have hv_pref : toNatPrefix v (n - 1) =
                  toNatPrefix v (n - 2) + (getLimb v (n - 2)).toNat * (2 ^ 64) ^ (n - 2) := by
                conv => lhs; rw [hn2]
                rw [toNatPrefix_succ]
              -- Bracket toNat u * 2^s and toNat v * 2^s by (u2 * B + u1) * B^(n - 1) and vn1 * B^(n - 1)
              have hu_shift_eq : toNat u * 2 ^ s.toNat =
                  (u2.toNat * 2 ^ 64 + u1.toNat) * (2 ^ 64) ^ (n - 1) +
                  (((getLimb u (n - 2)).toNat * 2 ^ s.toNat) % 2 ^ 64 * (2 ^ 64) ^ (n - 2) +
                    toNatPrefix u (n - 2) * 2 ^ s.toNat) := by
                have hs1 := hsplit_word (getLimb u (n - 1))
                have hs2 := hsplit_word (getLimb u (n - 2))
                rw [hu_decomp, hu_pref, Nat.add_mul]
                rw [hu2_val, hu1_val]
                have ha : ((getLimb u n).toNat * 2 ^ 64 + (getLimb u (n - 1)).toNat) * (2 ^ 64) ^ (n - 1) * 2 ^ s.toNat =
                    ((getLimb u n).toNat * 2 ^ s.toNat * 2 ^ 64 + (getLimb u (n - 1)).toNat * 2 ^ s.toNat) * (2 ^ 64) ^ (n - 1) := by
                  rw [Nat.add_mul, Nat.add_mul, Nat.add_mul]
                  congr 1 <;> ac_rfl
                have hb : (getLimb u (n - 2)).toNat * (2 ^ 64) ^ (n - 2) * 2 ^ s.toNat =
                    ((getLimb u (n - 2)).toNat * 2 ^ s.toNat) * (2 ^ 64) ^ (n - 2) := by ac_rfl
                conv => lhs; rw [ha, Nat.add_mul, Nat.add_mul, hb, hs1, hs2]
                rw [hpow_n1]
                repeat rw [Nat.add_mul]
                repeat rw [Nat.mul_assoc]
                ac_rfl
              have hv_shift_eq : toNat v * 2 ^ s.toNat =
                  vn1.toNat * (2 ^ 64) ^ (n - 1) +
                  (((getLimb v (n - 2)).toNat * 2 ^ s.toNat) % 2 ^ 64 * (2 ^ 64) ^ (n - 2) +
                    toNatPrefix v (n - 2) * 2 ^ s.toNat) := by
                have hs2 := hsplit_word (getLimb v (n - 2))
                rw [hv_decomp, hv_pref, Nat.add_mul, Nat.add_mul, hvn1_val]
                have ha : vTop.toNat * (2 ^ 64) ^ (n - 1) * 2 ^ s.toNat =
                    vTop.toNat * 2 ^ s.toNat * (2 ^ 64) ^ (n - 1) := by ac_rfl
                have hb : (getLimb v (n - 2)).toNat * (2 ^ 64) ^ (n - 2) * 2 ^ s.toNat =
                    ((getLimb v (n - 2)).toNat * 2 ^ s.toNat) * (2 ^ 64) ^ (n - 2) := by ac_rfl
                conv => lhs; rw [ha, hb, hs2]
                rw [hpow_n1]
                repeat rw [Nat.add_mul]
                repeat rw [Nat.mul_assoc]
                ac_rfl
              have hremU_lt : ((getLimb u (n - 2)).toNat * 2 ^ s.toNat) % 2 ^ 64 * (2 ^ 64) ^ (n - 2) +
                  toNatPrefix u (n - 2) * 2 ^ s.toNat < (2 ^ 64) ^ (n - 1) := by
                have hp := toNatPrefix_lt u (n - 2)
                have h1 : toNatPrefix u (n - 2) * 2 ^ s.toNat < (2 ^ 64) ^ (n - 2) * 2 ^ s.toNat :=
                  Nat.mul_lt_mul_of_pos_right hp (Nat.two_pow_pos _)
                have h2 := Nat.mul_le_mul_right ((2 ^ 64) ^ (n - 2)) (hmod_le_top (getLimb u (n - 2)))
                rw [Nat.add_mul, ← hpow_n1, Nat.mul_comm (2 ^ s.toNat)] at h2
                omega
              have hremV_lt : ((getLimb v (n - 2)).toNat * 2 ^ s.toNat) % 2 ^ 64 * (2 ^ 64) ^ (n - 2) +
                  toNatPrefix v (n - 2) * 2 ^ s.toNat < (2 ^ 64) ^ (n - 1) := by
                have hp := toNatPrefix_lt v (n - 2)
                have h1 : toNatPrefix v (n - 2) * 2 ^ s.toNat < (2 ^ 64) ^ (n - 2) * 2 ^ s.toNat :=
                  Nat.mul_lt_mul_of_pos_right hp (Nat.two_pow_pos _)
                have h2 := Nat.mul_le_mul_right ((2 ^ 64) ^ (n - 2)) (hmod_le_top (getLimb v (n - 2)))
                rw [Nat.add_mul, ← hpow_n1, Nat.mul_comm (2 ^ s.toNat)] at h2
                omega
              have ⟨hdm, hrh⟩ := divWide64_spec u2 u1 vn1 hlt
              have hdivS : (toNat u * 2 ^ s.toNat) / (toNat v * 2 ^ s.toNat) =
                  (divWide64 u2 u1 vn1 hlt).1.toNat :=
                divQuick1_bracket hP_pos hvn1_pos
                  (by omega) (by rw [Nat.add_mul, Nat.one_mul]; omega)
                  (by omega) (by rw [Nat.add_mul, Nat.one_mul]; omega)
                  hdm hrh (UInt64.le_iff_toNat_le.mp hqle)
              rw [Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _)] at hdivS
              refine ⟨wf_ofUInt64 _, ?_⟩
              rw [toNat_ofUInt64, hdivS]
            · cases hq
          · cases hq

theorem div_eq_divMod_fst (u v : Array UInt64) :
    WF (div u v) ∧ toNat (div u v) = toNat u / toNat v := by
  unfold div
  dsimp only
  have hu := wf_normalize u
  have hv := wf_normalize v
  have htu : toNat (normalize u) = toNat u := toNat_normalize u
  have htv : toNat (normalize v) = toNat v := toNat_normalize v
  split
  · rename_i hv0
    have hsz0 : (normalize v).size = 0 := eq_of_beq hv0
    have hvz : toNat v = 0 := by rw [← htv, toNat, hsz0]; rfl
    rw [hvz, Nat.div_zero]
    exact ⟨Or.inl rfl, rfl⟩
  · rename_i hvne0
    split
    · rename_i hcmp
      have hlt : cmp (normalize u) (normalize v) = .lt := eq_of_beq hcmp
      rw [cmp_spec hu hv, htu, htv] at hlt
      have hnat : toNat u < toNat v := by
        simp only [compare, compareOfLessAndEq] at hlt
        split at hlt
        · assumption
        · split at hlt <;> simp at hlt
      exact ⟨Or.inl rfl, by simp [Nat.div_eq_of_lt hnat]⟩
    · rename_i hnotlt
      split
      · rename_i hv1
        have hsz1 : (normalize v).size = 1 := eq_of_beq hv1
        have hd_ne : getLimb (normalize v) 0 ≠ 0 := by
          rcases hv with h0 | hne
          · omega
          · rw [hsz1] at hne; simpa using hne
        have htv1 : toNat v = (getLimb (normalize v) 0).toNat := by
          rw [← htv, toNat, hsz1, toNatPrefix_succ, toNatPrefix_zero]
          simp only [Nat.pow_zero, Nat.mul_one, Nat.zero_add]
        have ⟨hwf1, hdiv1, _, _⟩ := divMod1_spec (normalize u) (getLimb (normalize v) 0) hd_ne
        rw [htu, ← htv1] at hdiv1
        exact ⟨hwf1, hdiv1⟩
      · rename_i hvne1
        match hq : divQuick1 (normalize u) (normalize v) with
        | some q =>
          have ⟨hwf, hdiv⟩ := divQuick1_spec (normalize u) (normalize v) q hq
          rw [htu, htv] at hdiv
          exact ⟨hwf, hdiv⟩
        | none =>
          have hge2 : 2 ≤ (normalize v).size := by
            have h0 : (normalize v).size ≠ 0 := fun h => hvne0 (by simp [h])
            have h1 : (normalize v).size ≠ 1 := fun h => hvne1 (by simp [h])
            omega
          have hle : (normalize v).size ≤ (normalize u).size := by
            apply Classical.byContradiction; intro hlt
            have hltNat : toNat (normalize u) < toNat (normalize v) := by
              have h1 : toNat (normalize u) < (2 ^ 64) ^ (normalize u).size := toNat_lt _
              have h2 : (2 ^ 64) ^ ((normalize v).size - 1) ≤ toNat (normalize v) :=
                toNat_ge_top _ hv (by omega)
              have h3 : (2 ^ 64) ^ (normalize u).size ≤ (2 ^ 64) ^ ((normalize v).size - 1) :=
                Nat.pow_le_pow_right (Nat.two_pow_pos 64) (by omega)
              omega
            have hcmp := cmp_spec hu hv
            rw [show compare (toNat (normalize u)) (toNat (normalize v)) = .lt by
              simp [compare, compareOfLessAndEq, hltNat]] at hcmp
            exact hnotlt (by rw [hcmp]; rfl)
          have ⟨h1, _, h3, _⟩ := divModKnuth_spec (normalize u) (normalize v) hu hv hge2 hle
          unfold divModKnuth at h1 h3
          dsimp only at h1 h3
          rw [htu, htv] at h3
          exact ⟨h1, h3⟩

theorem wf_div (u v : Array UInt64) : WF (div u v) := (div_eq_divMod_fst u v).1

theorem toNat_div (u v : Array UInt64) : toNat (div u v) = toNat u / toNat v :=
  (div_eq_divMod_fst u v).2

theorem wf_mod (u v : Array UInt64) : WF (mod u v) := (divMod_spec u v).2.1

theorem toNat_mod (u v : Array UInt64) : toNat (mod u v) = toNat u % toNat v :=
  (divMod_spec u v).2.2.2

theorem toNat_mod_lt (u v : Array UInt64) (hv : WF v) (hne : v.size ≠ 0) :
    toNat (mod u v) < toNat v := by
  rw [toNat_mod]
  exact Nat.mod_lt _ (toNat_pos_of_ne_zero v hv hne)

end IxCC.BigNat
