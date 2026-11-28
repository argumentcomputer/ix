import IxCC.BigNat.Lehmer
import IxCC.BigNat.Proof.Div

/-! # Layer-1 Proofs for `IxCC.BigNat.Lehmer` (`IxCC.BigNat.Proof.Lehmer`)

Formal correctness and canonical normal-form preservation for 128-bit Lehmer–Jebelean
GCD (`gcdWord64`, `linCombSub`, `lehmer128Loop`, `lehmerStep`, `gcdLehmer`).

All theorems depend strictly on `[propext, Classical.choice, Quot.sound]`.
-/

namespace IxCC.BigNat

/-! ### Single-Limb Euclidean GCD (`gcdWord64`) -/

private theorem two_mul_mod_lt {a b : Nat} (hle : b ≤ a) (hb : 0 < b) :
    2 * (a % b) < a := by
  have hdm := Nat.div_add_mod a b
  have hmod : a % b < b := Nat.mod_lt a hb
  have hq : 1 ≤ a / b := (Nat.le_div_iff_mul_le hb).mpr (by omega)
  have hbm : b ≤ b * (a / b) := Nat.le_mul_of_pos_right b hq
  omega

private theorem gcdWord64Loop_spec (a b : UInt64) (fuel : Nat)
    (hle : b.toNat ≤ a.toNat) (hfuel : b.toNat = 0 ∨ a.toNat * b.toNat < 2 ^ fuel) :
    (gcdWord64Loop a b fuel).toNat = Nat.gcd a.toNat b.toNat := by
  induction fuel generalizing a b with
  | zero =>
    unfold gcdWord64Loop
    have hb0 : b.toNat = 0 := by
      rcases hfuel with h0 | hlt
      · exact h0
      · simp only [Nat.pow_zero] at hlt
        have hmul0 : a.toNat * b.toNat = 0 := by omega
        rcases Nat.mul_eq_zero.mp hmul0 with ha0 | hb0
        · omega
        · exact hb0
    rw [hb0, Nat.gcd_zero_right]
  | succ fuel ih =>
    unfold gcdWord64Loop
    split
    · rename_i hz
      have hbz : b = 0 := eq_of_beq hz
      subst hbz
      rw [UInt64.toNat_zero, Nat.gcd_zero_right]
    · rename_i hne
      have hbne : b ≠ 0 := fun h => hne (by simp [h])
      have hbpos : 0 < b.toNat := by
        have : b.toNat ≠ 0 := fun h0 => hbne (UInt64.toNat_inj.mp (by simpa using h0))
        omega
      have hmod_lt : (a % b).toNat < b.toNat := by
        rw [UInt64.toNat_mod]; exact Nat.mod_lt _ hbpos
      have hfuel' : (a % b).toNat = 0 ∨ b.toNat * (a % b).toNat < 2 ^ fuel := by
        rcases hfuel with h0 | hlt
        · omega
        · right
          have h2 : 2 * (a.toNat % b.toNat) < a.toNat := two_mul_mod_lt hle hbpos
          have hmul : 2 * (b.toNat * (a % b).toNat) < 2 * 2 ^ fuel := by
            rw [UInt64.toNat_mod]
            have h1 : b.toNat * (2 * (a.toNat % b.toNat)) < b.toNat * a.toNat :=
              Nat.mul_lt_mul_of_pos_left h2 hbpos
            have hc1 : 2 * (b.toNat * (a.toNat % b.toNat)) = b.toNat * (2 * (a.toNat % b.toNat)) := by ac_rfl
            have hc2 : b.toNat * a.toNat = a.toNat * b.toNat := Nat.mul_comm _ _
            have hpow : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by rw [Nat.pow_succ, Nat.mul_comm]
            omega
          exact Nat.lt_of_mul_lt_mul_left hmul
      rw [ih b (a % b) (Nat.le_of_lt hmod_lt) hfuel', UInt64.toNat_mod]
      rw [Nat.gcd_comm a.toNat b.toNat, Nat.gcd_rec b.toNat a.toNat, Nat.gcd_comm]

theorem gcdWord64_spec (a b : UInt64) :
    (gcdWord64 a b).toNat = Nat.gcd a.toNat b.toNat := by
  have ha : a.toNat < 2 ^ 64 := uint64_toNat_lt a
  have hb : b.toNat < 2 ^ 64 := uint64_toNat_lt b
  have hprod : a.toNat * b.toNat < 2 ^ 130 := by
    have h1 : a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul_of_lt_of_lt ha hb
    have h2 : 2 ^ 64 * 2 ^ 64 < 2 ^ 130 := by decide
    exact Nat.lt_trans h1 h2
  unfold gcdWord64
  split
  · rename_i hlt
    have hle : a.toNat ≤ b.toNat := Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp hlt)
    rw [gcdWord64Loop_spec b a 130 hle (Or.inr (by rw [Nat.mul_comm]; exact hprod)), Nat.gcd_comm]
  · rename_i hge
    have hle : b.toNat ≤ a.toNat := Nat.le_of_not_lt fun h => hge (UInt64.lt_iff_toNat_lt.mpr h)
    exact gcdWord64Loop_spec a b 130 hle (Or.inr hprod)

/-! ### Single-Pass Fused Linear Combination Subtract (`linCombSub`) -/

private theorem wf_linCombSubLoop (x y : Array UInt64) (u v : UInt64)
    (i : Nat) (mc sc : UInt64) (acc : Array UInt64) (rem : Nat) {r : Array UInt64}
    (hr : linCombSubLoop x y u v i mc sc acc rem = some r) : WF r := by
  induction rem generalizing i mc sc acc with
  | zero =>
    unfold linCombSubLoop at hr
    split at hr
    · cases hr
    · dsimp only at hr
      simp only [Option.some.injEq] at hr
      rw [← hr]
      exact wf_normalize _
  | succ rem ih =>
    unfold linCombSubLoop at hr
    dsimp only at hr
    exact ih _ _ _ _ hr

theorem wf_linCombSub {u : UInt64} {x : Array UInt64} {v : UInt64} {y r : Array UInt64}
    (hr : linCombSub u x v y = some r) : WF r :=
  wf_linCombSubLoop x y u v 0 0 0 _ _ hr

private theorem linCombSubLoop_spec (x y : Array UInt64) (u v : UInt64) (i rem : Nat)
    (mc sc : UInt64) (acc : Array UInt64) (hsz : acc.size = i)
    {r : Array UInt64} (hr : linCombSubLoop x y u v i mc sc acc rem = some r) :
    toNat r + toNatPrefix x i * u.toNat + toNatPrefix y (i + rem) * v.toNat + sc.toNat * (2 ^ 64) ^ i =
      toNat acc + toNatPrefix y i * v.toNat + toNatPrefix x (i + rem) * u.toNat + mc.toNat * (2 ^ 64) ^ i := by
  induction rem generalizing i mc sc acc with
  | zero =>
    unfold linCombSubLoop at hr
    simp only [Nat.add_zero]
    split at hr
    · cases hr
    · rename_i hge
      dsimp only at hr
      simp only [Option.some.injEq] at hr
      rw [← hr, toNat_normalize]
      have hle : sc.toNat ≤ mc.toNat := by
        have hnot : ¬ mc.toNat < sc.toNat := fun hlt => hge (UInt64.lt_iff_toNat_lt.mpr hlt)
        exact Nat.le_of_not_lt hnot
      have hsub : (mc - sc).toNat = mc.toNat - sc.toNat :=
        UInt64.toNat_sub_of_le mc sc (UInt64.le_iff_toNat_le.mpr hle)
      split
      · rename_i htop0
        have htop : mc - sc = 0 := eq_of_beq htop0
        have heq : mc.toNat = sc.toNat := by
          have := congrArg UInt64.toNat htop
          rw [hsub, UInt64.toNat_zero] at this
          omega
        rw [heq]
        omega
      · rw [toNat_push, hsz, hsub]
        have hmul : (mc.toNat - sc.toNat) * (2 ^ 64) ^ i + sc.toNat * (2 ^ 64) ^ i =
            mc.toNat * (2 ^ 64) ^ i := by
          rw [← Nat.add_mul, Nat.sub_add_cancel hle]
        omega
  | succ rem ih =>
    unfold linCombSubLoop at hr
    dsimp only at hr
    have hmul := mulWide64_spec u (getLimb x i)
    rcases hm : mulWide64 u (getLimb x i) with ⟨pLo, pHi⟩
    rw [hm] at hmul
    have hadd := addCarry64_spec pLo mc false
    rcases ha : addCarry64 pLo mc false with ⟨sLo, c1⟩
    rw [ha] at hadd
    have hsub := subMulCarry64_spec sLo (getLimb y i) v sc
    rcases hs : subMulCarry64 sLo (getLimb y i) v sc with ⟨diff, sc'⟩
    rw [hs] at hsub
    rw [hm, ha, hs] at hr
    dsimp only at hmul hadd hsub hr
    have hf : false.toNat = 0 := rfl
    rw [hf, Nat.add_zero] at hadd
    have hmc'_lt : pHi.toNat + c1.toNat < 2 ^ 64 := by
      have hu_lt : u.toNat < 2 ^ 64 := uint64_toNat_lt u
      have hx_lt : (getLimb x i).toNat < 2 ^ 64 := uint64_toNat_lt _
      have hmc_lt : mc.toNat < 2 ^ 64 := uint64_toNat_lt mc
      have hprod : u.toNat * (getLimb x i).toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      have htot : sLo.toNat + (pHi.toNat + c1.toNat) * 2 ^ 64 = u.toNat * (getLimb x i).toNat + mc.toNat := by
        calc sLo.toNat + (pHi.toNat + c1.toNat) * 2 ^ 64
            = sLo.toNat + (pHi.toNat * 2 ^ 64 + c1.toNat * 2 ^ 64) := by rw [Nat.add_mul]
          _ = (sLo.toNat + c1.toNat * 2 ^ 64) + pHi.toNat * 2 ^ 64 := by ac_rfl
          _ = (pLo.toNat + mc.toNat) + pHi.toNat * 2 ^ 64 := by rw [hadd]
          _ = (pLo.toNat + pHi.toNat * 2 ^ 64) + mc.toNat := by ac_rfl
          _ = u.toNat * (getLimb x i).toNat + mc.toNat := by rw [hmul]
      have hbound : (2 ^ 64 - 1) * (2 ^ 64 - 1) + (2 ^ 64 - 1) < 2 ^ 64 * 2 ^ 64 := by decide
      have hlt2 : (pHi.toNat + c1.toNat) * 2 ^ 64 < 2 ^ 64 * 2 ^ 64 := by
        have h1 : (pHi.toNat + c1.toNat) * 2 ^ 64 ≤ u.toNat * (getLimb x i).toNat + mc.toNat := by
          rw [← htot]; exact Nat.le_add_left _ _
        have h2 : u.toNat * (getLimb x i).toNat + mc.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) + (2 ^ 64 - 1) :=
          Nat.add_le_add hprod (by omega)
        exact Nat.lt_of_le_of_lt (Nat.le_trans h1 h2) hbound
      exact Nat.lt_of_mul_lt_mul_right hlt2
    let mc' : UInt64 := if c1 then pHi + 1 else pHi
    have hmc'_toNat : mc'.toNat = pHi.toNat + c1.toNat := by
      dsimp only [mc']
      cases c1
      · simp
      · simp only [↓reduceIte, Bool.toNat_true]
        rw [UInt64.toNat_add]
        have h1 : (1 : UInt64).toNat = 1 := rfl
        rw [h1, Nat.mod_eq_of_lt (by simpa using hmc'_lt)]
    have hmul_step : sLo.toNat + mc'.toNat * 2 ^ 64 = (getLimb x i).toNat * u.toNat + mc.toNat := by
      calc sLo.toNat + mc'.toNat * 2 ^ 64
          = sLo.toNat + (pHi.toNat + c1.toNat) * 2 ^ 64 := by rw [hmc'_toNat]
        _ = (sLo.toNat + c1.toNat * 2 ^ 64) + pHi.toNat * 2 ^ 64 := by rw [Nat.add_mul]; ac_rfl
        _ = (pLo.toNat + mc.toNat) + pHi.toNat * 2 ^ 64 := by rw [hadd]
        _ = (pLo.toNat + pHi.toNat * 2 ^ 64) + mc.toNat := by ac_rfl
        _ = u.toNat * (getLimb x i).toNat + mc.toNat := by rw [hmul]
        _ = (getLimb x i).toNat * u.toNat + mc.toNat := by rw [Nat.mul_comm]
    rw [Nat.mul_comm v.toNat (getLimb y i).toNat] at hsub
    have hstep1 : diff.toNat + (getLimb y i).toNat * v.toNat + sc.toNat + mc'.toNat * 2 ^ 64 =
        (getLimb x i).toNat * u.toNat + mc.toNat + sc'.toNat * 2 ^ 64 := by
      calc diff.toNat + (getLimb y i).toNat * v.toNat + sc.toNat + mc'.toNat * 2 ^ 64
          = (sLo.toNat + sc'.toNat * 2 ^ 64) + mc'.toNat * 2 ^ 64 := by rw [hsub]
        _ = (sLo.toNat + mc'.toNat * 2 ^ 64) + sc'.toNat * 2 ^ 64 := by ac_rfl
        _ = (getLimb x i).toNat * u.toNat + mc.toNat + sc'.toNat * 2 ^ 64 := by rw [hmul_step]
    have hstep := congrArg (· * (2 ^ 64) ^ i) hstep1
    repeat rw [Nat.add_mul] at hstep
    have hih := ih (i + 1) mc' sc' (acc.push diff) (by simp [hsz]) hr
    have hidx : i + 1 + rem = i + (rem + 1) := by omega
    rw [hidx, toNat_push, hsz, toNatPrefix_succ x i, toNatPrefix_succ y i,
        Nat.add_mul, Nat.add_mul, Nat.pow_succ (2 ^ 64) i] at hih
    have hr1 : sc'.toNat * ((2 ^ 64) ^ i * 2 ^ 64) = sc'.toNat * 2 ^ 64 * (2 ^ 64) ^ i := by
      rw [Nat.mul_comm ((2 ^ 64) ^ i) (2 ^ 64), ← Nat.mul_assoc]
    have hr2 : mc'.toNat * ((2 ^ 64) ^ i * 2 ^ 64) = mc'.toNat * 2 ^ 64 * (2 ^ 64) ^ i := by
      rw [Nat.mul_comm ((2 ^ 64) ^ i) (2 ^ 64), ← Nat.mul_assoc]
    have hr3 : (getLimb x i).toNat * (2 ^ 64) ^ i * u.toNat = (getLimb x i).toNat * u.toNat * (2 ^ 64) ^ i := by
      rw [Nat.mul_assoc, Nat.mul_comm ((2 ^ 64) ^ i) u.toNat, ← Nat.mul_assoc]
    have hr4 : (getLimb y i).toNat * (2 ^ 64) ^ i * v.toNat = (getLimb y i).toNat * v.toNat * (2 ^ 64) ^ i := by
      rw [Nat.mul_assoc, Nat.mul_comm ((2 ^ 64) ^ i) v.toNat, ← Nat.mul_assoc]
    rw [hr1, hr2, hr3, hr4] at hih
    clear hm ha hs hmul hadd hsub hmc'_lt hmc'_toNat hmul_step hstep1 hr1 hr2 hr3 hr4
    omega

theorem linCombSub_spec {u : UInt64} {x : Array UInt64} {v : UInt64} {y r : Array UInt64}
    (hr : linCombSub u x v y = some r) :
    WF r ∧ toNat r + v.toNat * toNat y = u.toNat * toNat x := by
  refine ⟨wf_linCombSub hr, ?_⟩
  unfold linCombSub at hr
  dsimp only at hr
  let n := if x.size ≤ y.size then y.size else x.size
  have hxle : x.size ≤ n := by dsimp [n]; split <;> omega
  have hyle : y.size ≤ n := by dsimp [n]; split <;> omega
  have h := linCombSubLoop_spec x y u v 0 n 0 0 (Array.mkEmpty (n + 1)) (by simp) hr
  simp only [toNatPrefix_zero, toNat_mkEmpty, UInt64.toNat_zero, Nat.zero_mul, Nat.zero_add,
    Nat.add_zero] at h
  rw [toNatPrefix_eq_toNat_of_le x hxle, toNatPrefix_eq_toNat_of_le y hyle] at h
  rw [Nat.mul_comm v.toNat (toNat y), Nat.mul_comm u.toNat (toNat x)]
  exact h

/-! ### Unimodularity Invariant for `lehmer128Loop` -/

/-- Exact unimodular determinant invariant for a `LehmerMat`. -/
def LehmerMat.Unimod (m : LehmerMat) : Prop :=
  if m.even then m.u00.toNat * m.u11.toNat = m.u01.toNat * m.u10.toNat + 1
  else m.u01.toNat * m.u10.toNat = m.u00.toNat * m.u11.toNat + 1

private theorem lehmer128Loop_unimod (ah al bh bl u00 u01 u10 u11 : UInt64)
    (even : Bool) (fuel : Nat)
    (huni : LehmerMat.Unimod { u00, u01, u10, u11, even }) :
    (lehmer128Loop ah al bh bl u00 u01 u10 u11 even fuel).Unimod := by
  induction fuel generalizing ah al bh bl u00 u01 u10 u11 even with
  | zero => exact huni
  | succ fuel ih =>
    unfold lehmer128Loop
    split
    · exact huni
    · cases lehmerQuotRem128 ah al bh bl with
      | none => exact huni
      | some qrr =>
        rcases qrr with ⟨q, rh, rl⟩
        dsimp only
        split
        · exact huni
        · have hm10 := mulAddCarry64_spec q u10 u00 0
          rcases h10 : mulAddCarry64 q u10 u00 0 with ⟨new10, hi10⟩
          rw [h10] at hm10
          have hm11 := mulAddCarry64_spec q u11 u01 0
          rcases h11 : mulAddCarry64 q u11 u01 0 with ⟨new11, hi11⟩
          rw [h11] at hm11
          dsimp only at hm10 hm11 ⊢
          split
          · exact huni
          · rename_i hnoovf
            have hhi10 : hi10 = 0 := by
              by_cases h0 : hi10 == 0
              · exact eq_of_beq h0
              · exfalso; apply hnoovf; simp [bne, h0]
            have hhi11 : hi11 = 0 := by
              by_cases h0 : hi11 == 0
              · exact eq_of_beq h0
              · exfalso; apply hnoovf; simp [bne, h0]
            subst hhi10; subst hhi11
            have h0 : (0 : UInt64).toNat = 0 := rfl
            rw [h0, Nat.zero_mul, Nat.add_zero, Nat.add_zero] at hm10 hm11
            split
            · exact huni
            · have hstep : LehmerMat.Unimod { u00 := u10, u01 := u11, u10 := new10, u11 := new11, even := !even } := by
                unfold LehmerMat.Unimod at huni ⊢
                have hprod1 : u11.toNat * new10.toNat =
                    q.toNat * (u10.toNat * u11.toNat) + u00.toNat * u11.toNat := by
                  rw [hm10, Nat.mul_add]
                  have ha : u11.toNat * (q.toNat * u10.toNat) = q.toNat * (u10.toNat * u11.toNat) := by ac_rfl
                  have hb : u11.toNat * u00.toNat = u00.toNat * u11.toNat := Nat.mul_comm _ _
                  rw [ha, hb]
                have hprod2 : u10.toNat * new11.toNat =
                    q.toNat * (u10.toNat * u11.toNat) + u01.toNat * u10.toNat := by
                  rw [hm11, Nat.mul_add]
                  have ha : u10.toNat * (q.toNat * u11.toNat) = q.toNat * (u10.toNat * u11.toNat) := by ac_rfl
                  have hb : u10.toNat * u01.toNat = u01.toNat * u10.toNat := Nat.mul_comm _ _
                  rw [ha, hb]
                cases even
                · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false] at huni ⊢
                  rw [hprod2, hprod1]; omega
                · simp only [↓reduceIte, Bool.not_true, Bool.false_eq_true] at huni ⊢
                  rw [hprod1, hprod2]; omega
              split <;> split
              · exact ih _ _ _ _ _ _ _ _ _ hstep
              · exact huni
              · exact ih _ _ _ _ _ _ _ _ _ hstep
              · exact huni

/-! ### Unimodular GCD Preservation (`Nat.gcd`) -/

private theorem gcd_unimodular_even {u00 u01 u10 u11 a b a' b' : Nat}
    (hdet : u00 * u11 = u01 * u10 + 1)
    (ha' : a' + u01 * b = u00 * a)
    (hb' : b' + u10 * a = u11 * b) :
    Nat.gcd a' b' = Nat.gcd a b := by
  have hinv_a : u11 * a' + u01 * b' = a := by
    have h1 : u11 * a' + u11 * (u01 * b) = u11 * (u00 * a) := by
      rw [← Nat.mul_add, ha']
    have h2 : u01 * b' + u01 * (u10 * a) = u01 * (u11 * b) := by
      rw [← Nat.mul_add, hb']
    have hc1 : u11 * (u01 * b) = u01 * (u11 * b) := by ac_rfl
    have hc2 : u11 * (u00 * a) = (u00 * u11) * a := by ac_rfl
    have hc3 : u01 * (u10 * a) = (u01 * u10) * a := by ac_rfl
    rw [hc1, hc2, hdet, Nat.add_mul, Nat.one_mul] at h1
    rw [hc3] at h2
    omega
  have hinv_b : u10 * a' + u00 * b' = b := by
    have h1 : u10 * a' + u10 * (u01 * b) = u10 * (u00 * a) := by
      rw [← Nat.mul_add, ha']
    have h2 : u00 * b' + u00 * (u10 * a) = u00 * (u11 * b) := by
      rw [← Nat.mul_add, hb']
    have hc1 : u10 * (u00 * a) = u00 * (u10 * a) := by ac_rfl
    have hc2 : u00 * (u11 * b) = (u00 * u11) * b := by ac_rfl
    have hc3 : u10 * (u01 * b) = (u01 * u10) * b := by ac_rfl
    rw [hc1, hc3] at h1
    rw [hc2, hdet, Nat.add_mul, Nat.one_mul] at h2
    omega
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · rw [← hinv_a]
      exact Nat.dvd_add (Nat.dvd_trans (Nat.gcd_dvd_left a' b') (Nat.dvd_mul_left a' u11))
        (Nat.dvd_trans (Nat.gcd_dvd_right a' b') (Nat.dvd_mul_left b' u01))
    · rw [← hinv_b]
      exact Nat.dvd_add (Nat.dvd_trans (Nat.gcd_dvd_left a' b') (Nat.dvd_mul_left a' u10))
        (Nat.dvd_trans (Nat.gcd_dvd_right a' b') (Nat.dvd_mul_left b' u00))
  · apply Nat.dvd_gcd
    · have h1 : Nat.gcd a b ∣ a' + u01 * b := by
        rw [ha']; exact Nat.dvd_trans (Nat.gcd_dvd_left a b) (Nat.dvd_mul_left a u00)
      have h2 : Nat.gcd a b ∣ u01 * b :=
        Nat.dvd_trans (Nat.gcd_dvd_right a b) (Nat.dvd_mul_left b u01)
      exact (Nat.dvd_add_left h2).mp h1
    · have h1 : Nat.gcd a b ∣ b' + u10 * a := by
        rw [hb']; exact Nat.dvd_trans (Nat.gcd_dvd_right a b) (Nat.dvd_mul_left b u11)
      have h2 : Nat.gcd a b ∣ u10 * a :=
        Nat.dvd_trans (Nat.gcd_dvd_left a b) (Nat.dvd_mul_left a u10)
      exact (Nat.dvd_add_left h2).mp h1

private theorem lehmerApply_gcd {mat : LehmerMat} (huni : mat.Unimod)
    {a b hi lo : Array UInt64} (h : lehmerApply mat a b = some (hi, lo)) :
    Nat.gcd (toNat hi) (toNat lo) = Nat.gcd (toNat a) (toNat b) := by
  unfold lehmerApply at h
  dsimp only at h
  cases hev : mat.even with
  | true =>
    simp only [hev, ↓reduceIte] at h
    unfold LehmerMat.Unimod at huni
    simp only [hev, ↓reduceIte] at huni
    cases hA : linCombSub mat.u00 a mat.u01 b with
    | none => rw [hA] at h; cases h
    | some a' =>
      rw [hA] at h; dsimp only at h
      cases hB : linCombSub mat.u11 b mat.u10 a with
      | none => rw [hB] at h; cases h
      | some b' =>
        rw [hB] at h; dsimp only at h
        have ha' := (linCombSub_spec hA).2
        have hb' := (linCombSub_spec hB).2
        have hgcd := gcd_unimodular_even huni ha' hb'
        by_cases hab : blt a' b' = true
        · simp only [hab, ↓reduceIte] at h
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            rw [Nat.gcd_comm, hgcd]
          · cases h
        · simp only [hab, Bool.false_eq_true, ↓reduceIte] at h
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            exact hgcd
          · cases h
  | false =>
    simp only [hev, Bool.false_eq_true, ↓reduceIte] at h
    unfold LehmerMat.Unimod at huni
    simp only [hev, Bool.false_eq_true, ↓reduceIte] at huni
    cases hA : linCombSub mat.u01 b mat.u00 a with
    | none => rw [hA] at h; cases h
    | some a' =>
      rw [hA] at h; dsimp only at h
      cases hB : linCombSub mat.u10 a mat.u11 b with
      | none => rw [hB] at h; cases h
      | some b' =>
        rw [hB] at h; dsimp only at h
        have ha' := (linCombSub_spec hA).2
        have hb' := (linCombSub_spec hB).2
        have hgcd := gcd_unimodular_even huni ha' hb'
        rw [Nat.gcd_comm (toNat b) (toNat a)] at hgcd
        by_cases hab : blt a' b' = true
        · simp only [hab, ↓reduceIte] at h
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            rw [Nat.gcd_comm, hgcd]
          · cases h
        · simp only [hab, Bool.false_eq_true, ↓reduceIte] at h
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            exact hgcd
          · cases h

theorem lehmerStep_gcd {a b hi lo : Array UInt64} (h : lehmerStep a b = some (hi, lo)) :
    Nat.gcd (toNat hi) (toNat lo) = Nat.gcd (toNat a) (toNat b) := by
  unfold lehmerStep at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · have huni := lehmer128Loop_unimod (extractTop128 a b).1 (extractTop128 a b).2.1
        (extractTop128 a b).2.2.1 (extractTop128 a b).2.2.2 1 0 0 1 true 100 (by
          unfold LehmerMat.Unimod; simp)
      exact lehmerApply_gcd huni h

/-! ### Bit-Length Decrease & Top-Level Lehmer GCD Correctness (`gcdLehmer`) -/

private theorem lt_of_blt {a b : Array UInt64} (ha : WF a) (hb : WF b) (h : blt a b = true) :
    toNat a < toNat b :=
  of_decide_eq_true (by rw [← blt_spec ha hb]; exact h)

private theorem le_of_not_blt {a b : Array UInt64} (ha : WF a) (hb : WF b) (h : ¬ blt a b = true) :
    toNat b ≤ toNat a :=
  Nat.le_of_not_lt fun hlt => h (by rw [blt_spec ha hb]; exact decide_eq_true hlt)

private theorem lehmerApply_decrease {mat : LehmerMat} {a b hi lo : Array UInt64}
    (h : lehmerApply mat a b = some (hi, lo)) :
    WF hi ∧ WF lo ∧ toNat lo ≤ toNat hi ∧ (lo.size = 0 ∨ log2 hi + log2 lo < log2 a + log2 b) := by
  unfold lehmerApply at h
  dsimp only at h
  rcases hpA : (if mat.even then (mat.u00, a, mat.u01, b) else (mat.u01, b, mat.u00, a)) with ⟨uA, xA, vA, yA⟩
  rw [hpA] at h
  dsimp only at h
  cases hA : linCombSub uA xA vA yA with
  | none => rw [hA] at h; cases h
  | some a' =>
    rw [hA] at h
    dsimp only at h
    have hwfA : WF a' := wf_linCombSub hA
    rcases hpB : (if mat.even then (mat.u11, b, mat.u10, a) else (mat.u10, a, mat.u11, b)) with ⟨uB, xB, vB, yB⟩
    rw [hpB] at h
    dsimp only at h
    cases hB : linCombSub uB xB vB yB with
    | none => rw [hB] at h; cases h
    | some b' =>
      rw [hB] at h
      dsimp only at h
      have hwfB : WF b' := wf_linCombSub hB
      by_cases hab : blt a' b' = true
      · simp only [hab, ↓reduceIte] at h
        split at h
        · rename_i hcond
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          have hdec : a'.size = 0 ∨ log2 b' + log2 a' < log2 a + log2 b := by
            rcases Bool.or_eq_true_iff.mp hcond with hz | hlt
            · exact Or.inl (eq_of_beq hz)
            · exact Or.inr (of_decide_eq_true hlt)
          exact ⟨hwfB, hwfA, Nat.le_of_lt (lt_of_blt hwfA hwfB hab), hdec⟩
        · cases h
      · simp only [hab, Bool.false_eq_true, ↓reduceIte] at h
        split at h
        · rename_i hcond
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          have hdec : b'.size = 0 ∨ log2 a' + log2 b' < log2 a + log2 b := by
            rcases Bool.or_eq_true_iff.mp hcond with hz | hlt
            · exact Or.inl (eq_of_beq hz)
            · exact Or.inr (of_decide_eq_true hlt)
          exact ⟨hwfA, hwfB, le_of_not_blt hwfA hwfB hab, hdec⟩
        · cases h

theorem lehmerStep_decrease {a b hi lo : Array UInt64}
    (h : lehmerStep a b = some (hi, lo)) :
    WF hi ∧ WF lo ∧ toNat lo ≤ toNat hi ∧ (lo.size = 0 ∨ log2 hi + log2 lo < log2 a + log2 b) := by
  unfold lehmerStep at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact lehmerApply_decrease h

private theorem toNat_of_size_le_one {a : Array UInt64} (h : a.size ≤ 1) :
    toNat a = (getLimb a 0).toNat := by
  cases hsz : a.size with
  | zero =>
    have h0 : getLimb a 0 = 0 := by unfold getLimb; simp [hsz]
    rw [h0, toNat, hsz]; rfl
  | succ k =>
    have hk0 : k = 0 := by omega
    subst hk0
    rw [toNat, hsz, toNatPrefix_succ, toNatPrefix_zero]
    simp only [Nat.pow_zero, Nat.mul_one, Nat.zero_add]

private theorem log2_le_64_mul_size {a : Array UInt64} (ha : WF a) :
    log2 a ≤ 64 * a.size := by
  rw [log2_spec ha]
  by_cases h0 : toNat a = 0
  · rw [h0]; simp
  · have hlt : toNat a < 2 ^ (64 * a.size) := by
      rw [Nat.pow_mul]; exact toNat_lt a
    exact Nat.le_of_lt ((Nat.log2_lt h0).mpr hlt)

private theorem log2_mod_lt {a b : Array UInt64} (ha : WF a) (hb : WF b)
    (hle : toNat b ≤ toNat a) (hbne : b.size ≠ 0) (hrne : (mod a b).size ≠ 0) :
    log2 (mod a b) < log2 a := by
  rw [log2_spec (wf_mod a b), log2_spec ha, toNat_mod]
  have hrpos : 0 < toNat a % toNat b := by
    rw [← toNat_mod]; exact toNat_pos_of_ne_zero _ (wf_mod a b) hrne
  have hbpos : 0 < toNat b := toNat_pos_of_ne_zero b hb hbne
  have h2 : 2 * (toNat a % toNat b) < toNat a := two_mul_mod_lt hle hbpos
  have hrne0 : toNat a % toNat b ≠ 0 := by omega
  have hane0 : toNat a ≠ 0 := by omega
  have h1 : 2 ^ Nat.log2 (toNat a % toNat b) ≤ toNat a % toNat b :=
    (Nat.le_log2 hrne0).mp (Nat.le_refl _)
  have hpow : 2 ^ (Nat.log2 (toNat a % toNat b) + 1) ≤ toNat a := by
    rw [Nat.pow_succ, Nat.mul_comm]; omega
  have hge : Nat.log2 (toNat a % toNat b) + 1 ≤ Nat.log2 (toNat a) :=
    (Nat.le_log2 hane0).mpr hpow
  omega

private theorem gcdLehmerLoop_spec (a b : Array UInt64) (fuel : Nat) (ha : WF a) (hb : WF b)
    (hle : toNat b ≤ toNat a) (hfuel : b.size = 0 ∨ log2 a + log2 b + 1 ≤ fuel) :
    WF (gcdLehmerLoop a b fuel) ∧
    toNat (gcdLehmerLoop a b fuel) = Nat.gcd (toNat a) (toNat b) := by
  induction fuel generalizing a b with
  | zero =>
    unfold gcdLehmerLoop
    have hz : b.size = 0 := by
      rcases hfuel with h0 | hle0
      · exact h0
      · omega
    have hb0 : toNat b = 0 := by rw [toNat, hz]; rfl
    rw [hb0, Nat.gcd_zero_right]
    exact ⟨ha, rfl⟩
  | succ fuel ih =>
    unfold gcdLehmerLoop
    split
    · rename_i hz
      have hbz : b.size = 0 := eq_of_beq hz
      have hb0 : toNat b = 0 := by rw [toNat, hbz]; rfl
      rw [hb0, Nat.gcd_zero_right]
      exact ⟨ha, rfl⟩
    · rename_i hne_beq
      have hne : b.size ≠ 0 := fun h => hne_beq (by simp [h])
      have hlog_le : log2 a + log2 b ≤ fuel := by
        rcases hfuel with h0 | hle'
        · exact absurd h0 hne
        · omega
      split
      · rename_i ha1
        have hb1 : b.size ≤ 1 := by
          by_cases hgt : 1 < b.size
          · exfalso
            have hge : 2 ^ 64 ≤ toNat b := by
              have hlo := toNat_ge_top b hb (by omega)
              have hpow : (2 ^ 64) ^ 1 ≤ (2 ^ 64) ^ (b.size - 1) :=
                Nat.pow_le_pow_right (by decide) (by omega)
              simp only [Nat.pow_one] at hpow
              exact Nat.le_trans hpow hlo
            have hlt : toNat a < 2 ^ 64 := by
              have := toNat_lt a
              have hpow : (2 ^ 64) ^ a.size ≤ (2 ^ 64) ^ 1 :=
                Nat.pow_le_pow_right (by decide) ha1
              simp only [Nat.pow_one] at hpow
              exact Nat.lt_of_lt_of_le this hpow
            omega
          · exact Nat.le_of_not_lt hgt
        refine ⟨wf_ofUInt64 _, ?_⟩
        rw [toNat_ofUInt64, gcdWord64_spec, toNat_of_size_le_one ha1, toNat_of_size_le_one hb1]
      · split
        · rename_i hb1b
          have hb1 : b.size = 1 := eq_of_beq hb1b
          have hbv_ne : getLimb b 0 ≠ 0 := by
            rcases hb with h0 | htop
            · omega
            · rw [hb1] at htop; simpa using htop
          have htb : toNat b = (getLimb b 0).toNat := toNat_of_size_le_one (by omega)
          have hrem := (divMod1_spec a (getLimb b 0) hbv_ne).2.2.1
          refine ⟨wf_ofUInt64 _, ?_⟩
          rw [toNat_ofUInt64, gcdWord64_spec, hrem, ← htb,
              Nat.gcd_comm (toNat a) (toNat b), Nat.gcd_rec (toNat b) (toNat a), Nat.gcd_comm]
        · rename_i hnot_b1
          have hb_ge2 : 2 ≤ b.size := by
            have hb1ne : b.size ≠ 1 := fun h => hnot_b1 (by simp [h])
            omega
          have hba_sz : b.size ≤ a.size := by
            apply Classical.byContradiction; intro hgt
            have h1 : toNat a < (2 ^ 64) ^ a.size := toNat_lt a
            have h2 : (2 ^ 64) ^ (b.size - 1) ≤ toNat b := toNat_ge_top b hb (by omega)
            have h3 : (2 ^ 64) ^ a.size ≤ (2 ^ 64) ^ (b.size - 1) :=
              Nat.pow_le_pow_right (Nat.two_pow_pos 64) (by omega)
            omega
          have hknuth := divModKnuth_spec a b ha hb hb_ge2 hba_sz
          have hmod_step : WF (gcdLehmerLoop b (divModKnuth a b).2 fuel) ∧
              toNat (gcdLehmerLoop b (divModKnuth a b).2 fuel) = Nat.gcd (toNat a) (toNat b) := by
            have hrmod : toNat (divModKnuth a b).2 < toNat b := by
              rw [hknuth.2.2.2]
              exact Nat.mod_lt _ (toNat_pos_of_ne_zero b hb hne)
            have hfuel' : (divModKnuth a b).2.size = 0 ∨ log2 b + log2 (divModKnuth a b).2 + 1 ≤ fuel := by
              by_cases hrz : (divModKnuth a b).2.size = 0
              · exact Or.inl hrz
              · right
                have hlog_eq : log2 (divModKnuth a b).2 = log2 (mod a b) := by
                  rw [log2_spec hknuth.2.1, log2_spec (wf_mod a b), hknuth.2.2.2, toNat_mod]
                have hrz_mod : (mod a b).size ≠ 0 := by
                  intro hz
                  have h0 : toNat (mod a b) = 0 := by simp [toNat, hz]
                  rw [toNat_mod, ← hknuth.2.2.2] at h0
                  have := (toNat_eq_zero_iff (divModKnuth a b).2 hknuth.2.1).mp h0
                  exact hrz this
                have hlt := log2_mod_lt ha hb hle hne hrz_mod
                omega
            have ⟨hwf, hto⟩ := ih b (divModKnuth a b).2 hb hknuth.2.1 (Nat.le_of_lt hrmod) hfuel'
            refine ⟨hwf, ?_⟩
            rw [hto, hknuth.2.2.2, Nat.gcd_comm (toNat a) (toNat b),
                Nat.gcd_rec (toNat b) (toNat a), Nat.gcd_comm]
          cases hnext : (if a.size - b.size ≤ 1 then lehmerStep a b else none) with
          | none => exact hmod_step
          | some hl =>
            rcases hl with ⟨hi, lo⟩
            have hstep : lehmerStep a b = some (hi, lo) := by
              split at hnext
              · exact hnext
              · cases hnext
            have hdec := lehmerStep_decrease hstep
            have hfuel' : lo.size = 0 ∨ log2 hi + log2 lo + 1 ≤ fuel := by
              rcases hdec.2.2.2 with h0 | hlt
              · exact Or.inl h0
              · exact Or.inr (by omega)
            have ⟨hwf, hto⟩ := ih hi lo hdec.1 hdec.2.1 hdec.2.2.1 hfuel'
            exact ⟨hwf, by rw [hto, lehmerStep_gcd hstep]⟩

private theorem gcdLehmer_spec (a b : Array UInt64) :
    WF (gcdLehmer a b) ∧ toNat (gcdLehmer a b) = Nat.gcd (toNat a) (toNat b) := by
  unfold gcdLehmer
  dsimp only
  have hwa := wf_normalize a
  have hwb := wf_normalize b
  have hlogA := log2_le_64_mul_size hwa
  have hlogB := log2_le_64_mul_size hwb
  by_cases hlt : blt (normalize a) (normalize b) = true
  · simp only [hlt, ↓reduceIte]
    have hab : toNat (normalize a) < toNat (normalize b) := lt_of_blt hwa hwb hlt
    have hlogAB : log2 (normalize a) ≤ log2 (normalize b) := by
      rw [log2_spec hwa, log2_spec hwb]
      by_cases h0 : toNat (normalize a) = 0
      · rw [h0]; simp
      · have hb0 : toNat (normalize b) ≠ 0 := by omega
        exact (Nat.le_log2 hb0).mpr (Nat.le_trans ((Nat.le_log2 h0).mp (Nat.le_refl _)) (Nat.le_of_lt hab))
    have ⟨hwf, hto⟩ := gcdLehmerLoop_spec (normalize b) (normalize a)
      ((normalize b).size * 128 + 2) hwb hwa (Nat.le_of_lt hab) (Or.inr (by omega))
    rw [toNat_normalize, toNat_normalize, Nat.gcd_comm] at hto
    exact ⟨hwf, hto⟩
  · simp only [hlt, Bool.false_eq_true, ↓reduceIte]
    have hba : toNat (normalize b) ≤ toNat (normalize a) := le_of_not_blt hwa hwb hlt
    have hlogBA : log2 (normalize b) ≤ log2 (normalize a) := by
      rw [log2_spec hwa, log2_spec hwb]
      by_cases h0 : toNat (normalize b) = 0
      · rw [h0]; simp
      · have ha0 : toNat (normalize a) ≠ 0 := by omega
        exact (Nat.le_log2 ha0).mpr (Nat.le_trans ((Nat.le_log2 h0).mp (Nat.le_refl _)) hba)
    have ⟨hwf, hto⟩ := gcdLehmerLoop_spec (normalize a) (normalize b)
      ((normalize a).size * 128 + 2) hwa hwb hba (Or.inr (by omega))
    rw [toNat_normalize, toNat_normalize] at hto
    exact ⟨hwf, hto⟩

theorem wf_gcdLehmer (a b : Array UInt64) : WF (gcdLehmer a b) :=
  (gcdLehmer_spec a b).1

theorem toNat_gcdLehmer (a b : Array UInt64) :
    toNat (gcdLehmer a b) = Nat.gcd (toNat a) (toNat b) :=
  (gcdLehmer_spec a b).2

end IxCC.BigNat
