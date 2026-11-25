import IxCC.BigNat.InvDiv
import IxCC.BigNat.Proof.Linear

/-! # Layer-1 Proofs for `IxCC.BigNat.InvDiv` (`IxCC.BigNat.Proof.InvDiv`)

Complete formal correctness proof of Möller–Granlund 2-by-1 precomputed-reciprocal
division (`invert21`, `divRem21`, `divMod1Inv`) following Möller & Granlund (2011),
*Improved Division by Invariant Integers*, Algorithm 4 & Lemma 3.

All theorems depend strictly on `[propext, Classical.choice, Quot.sound]`. -/

namespace IxCC.BigNat

/-! ### Reciprocal Specification (`invert21`) -/

theorem invert21_spec (d : UInt64) (hd : 2 ^ 63 ≤ d.toNat) :
    (2 ^ 64 + (invert21 d hd).toNat) * d.toNat < 2 ^ 128 ∧
    2 ^ 128 ≤ (2 ^ 64 + (invert21 d hd).toNat + 1) * d.toNat := by
  unfold invert21
  have hlt_d : d.toNat < 2 ^ 64 := uint64_toNat_lt d
  have hlt : maxWord64 - d < d := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le]
    · rw [maxWord64_toNat]; omega
    · rw [UInt64.le_iff_toNat_le, maxWord64_toNat]; omega
  have ⟨heq, hrem⟩ := divWide64_spec (maxWord64 - d) maxWord64 d hlt
  have hsub : (maxWord64 - d).toNat = 2 ^ 64 - 1 - d.toNat := by
    rw [UInt64.toNat_sub_of_le]
    · rw [maxWord64_toNat]
    · rw [UInt64.le_iff_toNat_le, maxWord64_toNat]; omega
  rw [hsub, maxWord64_toNat] at heq
  have hsq : 2 ^ 64 * 2 ^ 64 = 2 ^ 128 := by rw [← Nat.pow_add]
  have hpos64 : 1 ≤ 2 ^ 64 := Nat.two_pow_pos 64
  have hpos128 : 1 ≤ 2 ^ 128 := Nat.two_pow_pos 128
  have hnum : (2 ^ 64 - 1 - d.toNat) * 2 ^ 64 + (2 ^ 64 - 1) + 2 ^ 64 * d.toNat = 2 ^ 128 - 1 := by
    have h1 : (2 ^ 64 - 1 - d.toNat) * 2 ^ 64 + d.toNat * 2 ^ 64 = (2 ^ 64 - 1) * 2 ^ 64 := by
      rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_sub_one_of_lt hlt_d)]
    have h2 : (2 ^ 64 - 1) * 2 ^ 64 + 2 ^ 64 = 2 ^ 128 := by
      calc (2 ^ 64 - 1) * 2 ^ 64 + 2 ^ 64
          = (2 ^ 64 - 1 + 1) * 2 ^ 64 := by rw [Nat.add_mul, Nat.one_mul]
        _ = 2 ^ 64 * 2 ^ 64 := by rw [Nat.sub_add_cancel hpos64]
        _ = 2 ^ 128 := hsq
    have h3 : (2 ^ 64 - 1) * 2 ^ 64 + (2 ^ 64 - 1) = 2 ^ 128 - 1 := by
      apply Nat.eq_sub_of_add_eq
      rw [Nat.add_assoc, Nat.sub_add_cancel hpos64, h2]
    calc (2 ^ 64 - 1 - d.toNat) * 2 ^ 64 + (2 ^ 64 - 1) + 2 ^ 64 * d.toNat
        = ((2 ^ 64 - 1 - d.toNat) * 2 ^ 64 + d.toNat * 2 ^ 64) + (2 ^ 64 - 1) := by ac_rfl
      _ = (2 ^ 64 - 1) * 2 ^ 64 + (2 ^ 64 - 1) := by rw [h1]
      _ = 2 ^ 128 - 1 := h3
  have hcomb : (2 ^ 64 + (divWide64 (maxWord64 - d) maxWord64 d hlt).1.toNat) * d.toNat +
      (divWide64 (maxWord64 - d) maxWord64 d hlt).2.toNat = 2 ^ 128 - 1 := by
    calc (2 ^ 64 + (divWide64 (maxWord64 - d) maxWord64 d hlt).1.toNat) * d.toNat +
          (divWide64 (maxWord64 - d) maxWord64 d hlt).2.toNat
        = ((divWide64 (maxWord64 - d) maxWord64 d hlt).1.toNat * d.toNat +
            (divWide64 (maxWord64 - d) maxWord64 d hlt).2.toNat) + 2 ^ 64 * d.toNat := by
          rw [Nat.add_mul]; ac_rfl
      _ = (2 ^ 64 - 1 - d.toNat) * 2 ^ 64 + (2 ^ 64 - 1) + 2 ^ 64 * d.toNat := by rw [heq]
      _ = 2 ^ 128 - 1 := hnum
  constructor
  · have hle : (2 ^ 64 + (divWide64 (maxWord64 - d) maxWord64 d hlt).1.toNat) * d.toNat ≤ 2 ^ 128 - 1 := by
      rw [← hcomb]; exact Nat.le_add_right _ _
    exact Nat.lt_of_le_of_lt hle (Nat.sub_lt hpos128 Nat.one_pos)
  · rw [Nat.add_mul, Nat.one_mul]
    have hlt1 : 2 ^ 128 - 1 <
        (2 ^ 64 + (divWide64 (maxWord64 - d) maxWord64 d hlt).1.toNat) * d.toNat + d.toNat := by
      rw [← hcomb]; exact Nat.add_lt_add_left hrem _
    have hle1 : 2 ^ 128 - 1 + 1 ≤
        (2 ^ 64 + (divWide64 (maxWord64 - d) maxWord64 d hlt).1.toNat) * d.toNat + d.toNat := hlt1
    rwa [Nat.sub_add_cancel hpos128] at hle1

theorem invert21_eq_div (d : UInt64) (hd : 2 ^ 63 ≤ d.toNat) :
    (invert21 d hd).toNat = (2 ^ 128 - 1) / d.toNat - 2 ^ 64 := by
  have ⟨hlo, hhi⟩ := invert21_spec d hd
  have hdpos : 0 < d.toNat := Nat.lt_of_lt_of_le (Nat.two_pow_pos 63) hd
  have hpos128 : 1 ≤ 2 ^ 128 := Nat.two_pow_pos 128
  have hdiv_ge : 2 ^ 64 + (invert21 d hd).toNat ≤ (2 ^ 128 - 1) / d.toNat :=
    (Nat.le_div_iff_mul_le hdpos).mpr (Nat.le_sub_one_of_lt hlo)
  have hdiv_lt : (2 ^ 128 - 1) / d.toNat < 2 ^ 64 + (invert21 d hd).toNat + 1 :=
    (Nat.div_lt_iff_lt_mul hdpos).mpr (Nat.lt_of_lt_of_le (Nat.sub_lt hpos128 Nat.one_pos) hhi)
  have heq : (2 ^ 128 - 1) / d.toNat = 2 ^ 64 + (invert21 d hd).toNat :=
    Nat.le_antisymm (Nat.le_of_lt_succ hdiv_lt) hdiv_ge
  rw [heq, Nat.add_sub_cancel_left]

/-! ### Modular Subtraction Helper for `divRem21` -/

private theorem uint64_sub_mul_toNat {u0 q d : UInt64} {r : Nat}
    (hr : r < 2 ^ 64)
    (hmod : (r + q.toNat * d.toNat) % 2 ^ 64 = u0.toNat) :
    (u0 - q * d).toNat = r := by
  have hu0 : u0.toNat < 2 ^ 64 := uint64_toNat_lt u0
  have hqd : (q * d).toNat = (q.toNat * d.toNat) % 2 ^ 64 := UInt64.toNat_mul q d
  have hsub : (u0 - q * d).toNat = (u0.toNat + (2 ^ 64 - (q * d).toNat)) % 2 ^ 64 := by
    rw [UInt64.toNat_sub, Nat.add_comm]
  rw [hsub, hqd]
  have hqdlt : (q.toNat * d.toNat) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (Nat.two_pow_pos 64)
  have hstep : (r + (q.toNat * d.toNat) % 2 ^ 64) % 2 ^ 64 = u0.toNat := by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    exact hmod
  by_cases hlt : r + (q.toNat * d.toNat) % 2 ^ 64 < 2 ^ 64
  · rw [Nat.mod_eq_of_lt hlt] at hstep
    have heq : u0.toNat + (2 ^ 64 - (q.toNat * d.toNat) % 2 ^ 64) = 2 ^ 64 + r := by omega
    rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt hr]
  · have hge : 2 ^ 64 ≤ r + (q.toNat * d.toNat) % 2 ^ 64 := by omega
    have hlt2 : r + (q.toNat * d.toNat) % 2 ^ 64 - 2 ^ 64 < 2 ^ 64 := by omega
    have hmod2 : (r + (q.toNat * d.toNat) % 2 ^ 64) % 2 ^ 64 =
        r + (q.toNat * d.toNat) % 2 ^ 64 - 2 ^ 64 := by omega
    rw [hmod2] at hstep
    have heq : u0.toNat + (2 ^ 64 - (q.toNat * d.toNat) % 2 ^ 64) = r := by omega
    rw [heq, Nat.mod_eq_of_lt hr]

/-! ### Exact Correctness of Möller–Granlund Algorithm 4 (`divRem21`) -/

private theorem divRem21_rem_bounds {H B D u1 u0 e q0 rem0 : Nat}
    (hBH : B = 2 * H) (hHpos : 0 < H)
    (hDlo : H ≤ D) (hDhi : D < B)
    (hu1 : u1 < D) (hu0 : u0 < B)
    (he : e ≤ D) (hq0 : q0 < B)
    (hrem : rem0 * B = q0 * D + u1 * e + u0 * (B - D)) :
    rem0 < B + D ∧ (D ≤ rem0 → rem0 - D < B ∧ rem0 - D < 2 * D) := by
  have hBpos : 0 < B := by omega
  have h1 : u1 * e ≤ (D - 1) * D := Nat.mul_le_mul (by omega) he
  have h2 : u0 * (B - D) ≤ (B - 1) * (B - D) := Nat.mul_le_mul (by omega) (Nat.le_refl _)
  have hrem_upper : rem0 * B < B * D + D * D + B * (B - D) := by
    have hqD : q0 * D < B * D := Nat.mul_lt_mul_of_pos_right hq0 (by omega)
    have h1' : u1 * e ≤ D * D := Nat.le_trans h1 (Nat.mul_le_mul_right D (by omega))
    have h2' : u0 * (B - D) ≤ B * (B - D) := Nat.le_trans h2 (Nat.mul_le_mul_right _ (by omega))
    omega
  have hDsub : D * D + B * (B - D) < B * B := by
    have hmul1 : B * (B - D) + B * D = B * B := by
      rw [← Nat.mul_add, Nat.sub_add_cancel (Nat.le_of_lt hDhi)]
    have hDD : D * D < B * D := Nat.mul_lt_mul_of_pos_right hDhi (by omega)
    omega
  have hsq : (B - D) * (B - D) < B * D := by
    have hle1 : B - D ≤ H := by omega
    have hprod1 : (B - D) * (B - D) ≤ H * H := Nat.mul_le_mul hle1 hle1
    have hprod2 : B * H ≤ B * D := Nat.mul_le_mul_left B hDlo
    have hstrict : H * H < B * H := Nat.mul_lt_mul_of_pos_right (by omega) hHpos
    omega
  have hDsub2 : D * D + B * (B - D) < 2 * B * D := by
    have hmul1 : B * (B - D) + B * D = B * B := by
      rw [← Nat.mul_add, Nat.sub_add_cancel (Nat.le_of_lt hDhi)]
    have h2BD : 2 * B * D = 2 * (B * D) := Nat.mul_assoc 2 B D
    have hexp : (B - D) * (B - D) + 2 * B * D = B * B + D * D := by
      have hsub1 : (B - D) * (B - D) + (B - D) * D = (B - D) * B := by
        rw [← Nat.mul_add, Nat.sub_add_cancel (Nat.le_of_lt hDhi)]
      have hsub2 : (B - D) * D + D * D = B * D := by
        rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt hDhi)]
      have hcomm : (B - D) * B = B * (B - D) := Nat.mul_comm _ _
      omega
    omega
  constructor
  · have htot : rem0 * B < (B + D) * B := by
      rw [Nat.add_mul, Nat.mul_comm D B]; omega
    exact Nat.lt_of_mul_lt_mul_right htot
  · intro hge
    have hsub : (rem0 - D) * B + D * B = rem0 * B := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hge]
    have hBD : D * B = B * D := Nat.mul_comm D B
    constructor
    · have hltB : (rem0 - D) * B < B * B := by omega
      exact Nat.lt_of_mul_lt_mul_right hltB
    · have hlt2D : (rem0 - D) * B < (2 * D) * B := by
        have hcomm : (2 * D) * B = 2 * B * D := by
          rw [Nat.mul_assoc, Nat.mul_comm D B, ← Nat.mul_assoc]
        omega
      exact Nat.lt_of_mul_lt_mul_right hlt2D

private theorem divRem21_case1_gt {B D u1 u0 e q0 rem0 : Nat}
    (hDlt : D < B) (hq0 : q0 < B)
    (hrem0_B : rem0 * B = q0 * D + u1 * e + u0 * (B - D)) :
    q0 < B + rem0 - D := by
  have h1 : (B + rem0 - D) * B = (B - D) * B + rem0 * B := by
    have hsplit : B + rem0 - D = (B - D) + rem0 := by omega
    rw [hsplit, Nat.add_mul]
  have h2 : (B - D) * B + q0 * D + u0 * (B - D) =
      q0 * B + (B - D) * (B + u0 - q0) := by
    have ha : (B - D) * (B + u0 - q0) + (B - D) * q0 = (B - D) * (B + u0) := by
      rw [← Nat.mul_add, Nat.sub_add_cancel (by omega)]
    have hb : (B - D) * q0 + D * q0 = B * q0 := by
      rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt hDlt)]
    have hc : (B - D) * (B + u0) = (B - D) * B + (B - D) * u0 := Nat.mul_add _ _ _
    have hd1 : q0 * B = B * q0 := Nat.mul_comm _ _
    have hd2 : q0 * D = D * q0 := Nat.mul_comm _ _
    have hd3 : u0 * (B - D) = (B - D) * u0 := Nat.mul_comm _ _
    omega
  have hpos : 0 < (B - D) * (B + u0 - q0) := Nat.mul_pos (by omega) (by omega)
  have hltB : q0 * B < (B + rem0 - D) * B := by
    rw [h1, hrem0_B]; omega
  exact Nat.lt_of_mul_lt_mul_right hltB

private theorem uint64_add_one_sub_one (x : UInt64) : (x + 1) - 1 = x := by
  have hx : x.toNat < 2 ^ 64 := uint64_toNat_lt x
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub, UInt64.toNat_add]
  have h1 : (1 : UInt64).toNat = 1 := rfl
  rw [h1]
  by_cases hmax : x.toNat + 1 < 2 ^ 64
  · rw [Nat.mod_eq_of_lt hmax]
    have : 2 ^ 64 - 1 + (x.toNat + 1) = 2 ^ 64 + x.toNat := by omega
    rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt hx]
  · have hxmax : x.toNat = 2 ^ 64 - 1 := by omega
    have h1p : x.toNat + 1 = 2 ^ 64 := by omega
    rw [h1p, Nat.mod_self, Nat.add_zero, ← hxmax, Nat.mod_eq_of_lt hx]

private theorem divRem21_false_trigger_bound {B D u1 u0 e q0 rem1 : Nat}
    (hDhi : D < B) (hu1 : u1 < D) (hu0 : u0 < B) (he : e ≤ D) (hq0 : q0 < rem1)
    (hrem1 : rem1 * B + B * D = q0 * D + u1 * e + u0 * (B - D)) :
    rem1 < B - D := by
  have h1 : u1 * e ≤ (D - 1) * D := Nat.mul_le_mul (by omega) he
  have h2 : u0 * (B - D) ≤ (B - 1) * (B - D) := Nat.mul_le_mul (by omega) (Nat.le_refl _)
  have h3 : q0 * D + D ≤ rem1 * D := by
    have : (q0 + 1) * D ≤ rem1 * D := Nat.mul_le_mul_right D hq0
    rw [Nat.add_mul, Nat.one_mul] at this; exact this
  have h4 : rem1 * (B - D) + rem1 * D = rem1 * B := by
    rw [← Nat.mul_add, Nat.sub_add_cancel (Nat.le_of_lt hDhi)]
  have h5 : (D - 1) * D + D = D * D := by
    have : (D - 1 + 1) * D = D * D := by rw [Nat.sub_add_cancel (by omega)]
    rw [Nat.add_mul, Nat.one_mul] at this; exact this
  have h6 : (B - 1) * (B - D) + (B - D) = B * (B - D) := by
    have : (B - 1 + 1) * (B - D) = B * (B - D) := by rw [Nat.sub_add_cancel (by omega)]
    rw [Nat.add_mul, Nat.one_mul] at this; exact this
  have h7 : (B - D) * (B - D) + B * D = B * (B - D) + D * D := by
    have ha : (B - D) * (B - D) + (B - D) * D = (B - D) * B := by
      rw [← Nat.mul_add, Nat.sub_add_cancel (Nat.le_of_lt hDhi)]
    have hb : (B - D) * D + D * D = B * D := by
      rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt hDhi)]
    have hc : (B - D) * B = B * (B - D) := Nat.mul_comm _ _
    omega
  have hlt : rem1 * (B - D) < (B - D) * (B - D) := by omega
  exact Nat.lt_of_mul_lt_mul_right hlt

private theorem divRem21_spec_aux (u1 u0 d v : UInt64) (hd : 2 ^ 63 ≤ d.toNat) (hu1 : u1 < d)
    (hv_lo : (2 ^ 64 + v.toNat) * d.toNat < 2 ^ 128)
    (hv_hi : 2 ^ 128 ≤ (2 ^ 64 + v.toNat + 1) * d.toNat) :
    let res := divRem21 u1 u0 d v
    res.1.toNat = (u1.toNat * 2 ^ 64 + u0.toNat) / d.toNat ∧
    res.2.toNat = (u1.toNat * 2 ^ 64 + u0.toNat) % d.toNat ∧
    res.2 < d := by
  have hDlt : d.toNat < 2 ^ 64 := uint64_toNat_lt d
  have hu1_lt : u1.toNat < d.toNat := UInt64.lt_iff_toNat_lt.mp hu1
  have hu0_lt : u0.toNat < 2 ^ 64 := uint64_toNat_lt u0
  have hd_pos : 0 < d.toNat := Nat.lt_of_lt_of_le (Nat.two_pow_pos 63) hd
  have hB2 : 2 ^ 64 * 2 ^ 64 = 2 ^ 128 := by rw [← Nat.pow_add]
  have hBH : (2 ^ 64 : Nat) = 2 * 2 ^ 63 := by rw [Nat.mul_comm, ← Nat.pow_succ]
  have hvd_lt : (2 ^ 64 + v.toNat) * d.toNat < 2 ^ 64 * 2 ^ 64 := by
    rw [hB2]; exact hv_lo
  let e : Nat := 2 ^ 64 * 2 ^ 64 - (2 ^ 64 + v.toNat) * d.toNat
  have he_eq : (2 ^ 64 + v.toNat) * d.toNat + e = 2 ^ 64 * 2 ^ 64 :=
    Nat.add_sub_of_le (Nat.le_of_lt hvd_lt)
  have he_le : e ≤ d.toNat := by
    have h2 : 2 ^ 64 * 2 ^ 64 ≤ (2 ^ 64 + v.toNat) * d.toNat + d.toNat := by
      rw [hB2]; rw [Nat.add_mul, Nat.one_mul] at hv_hi; exact hv_hi
    exact Nat.sub_le_iff_le_add'.mpr h2
  -- Unfold divRem21 directly with opaque `v` (no `change` unfolding `invert21`)
  unfold divRem21
  have hmul := mulWide64_spec v u1
  rcases hmw : mulWide64 v u1 with ⟨pLo, pHi⟩
  rw [hmw] at hmul
  dsimp only at hmul ⊢
  have hadd0 := addCarry64_spec pLo u0 false
  rcases ha0 : addCarry64 pLo u0 false with ⟨q0, c0⟩
  rw [ha0] at hadd0
  dsimp only at hadd0 ⊢
  have hadd1 := addCarry64_spec pHi u1 c0
  rcases ha1 : addCarry64 pHi u1 c0 with ⟨q1_init, c1⟩
  rw [ha1] at hadd1
  dsimp only at hadd1 ⊢
  have hf : false.toNat = 0 := rfl
  rw [hf, Nat.add_zero] at hadd0
  have hq0_lt : q0.toNat < 2 ^ 64 := uint64_toNat_lt q0
  -- Prove (q1_init + c1 * 2^64) * 2^64 + q0 = (2^64 + v) * u1 + u0, and c1 = 0
  have hqcomb : (q1_init.toNat + c1.toNat * 2 ^ 64) * 2 ^ 64 + q0.toNat =
      (2 ^ 64 + v.toNat) * u1.toNat + u0.toNat := by
    rw [hadd1, Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.mul_comm (2 ^ 64) u1.toNat]
    calc pHi.toNat * 2 ^ 64 + u1.toNat * 2 ^ 64 + c0.toNat * 2 ^ 64 + q0.toNat
        = u1.toNat * 2 ^ 64 + (pHi.toNat * 2 ^ 64 + (q0.toNat + c0.toNat * 2 ^ 64)) := by ac_rfl
      _ = u1.toNat * 2 ^ 64 + (pHi.toNat * 2 ^ 64 + (pLo.toNat + u0.toNat)) := by rw [hadd0]
      _ = u1.toNat * 2 ^ 64 + ((pLo.toNat + pHi.toNat * 2 ^ 64) + u0.toNat) := by ac_rfl
      _ = u1.toNat * 2 ^ 64 + (v.toNat * u1.toNat + u0.toNat) := by rw [hmul]
      _ = u1.toNat * 2 ^ 64 + v.toNat * u1.toNat + u0.toNat := by ac_rfl
  have hc1_zero : c1.toNat = 0 := by
    have hbound : (2 ^ 64 + v.toNat) * u1.toNat + u0.toNat < 2 ^ 64 * 2 ^ 64 := by
      have h1 : (2 ^ 64 + v.toNat) * (u1.toNat + 1) ≤ (2 ^ 64 + v.toNat) * d.toNat :=
        Nat.mul_le_mul_left _ hu1_lt
      rw [Nat.mul_add, Nat.mul_one] at h1
      have h3 : u0.toNat < 2 ^ 64 + v.toNat := Nat.lt_of_lt_of_le hu0_lt (Nat.le_add_right _ _)
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left h3 _) (Nat.le_trans h1 (Nat.le_of_lt hvd_lt))
    cases c1
    · rfl
    · simp only [Bool.toNat_true, Nat.one_mul, Nat.add_mul] at hqcomb
      have hge : 2 ^ 64 * 2 ^ 64 ≤ (q1_init.toNat * 2 ^ 64 + 2 ^ 64 * 2 ^ 64) + q0.toNat :=
        Nat.le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _)
      rw [hqcomb] at hge
      rw [Nat.add_mul] at hbound
      exact absurd hbound (Nat.not_lt_of_ge hge)
  rw [hc1_zero, Nat.zero_mul, Nat.add_zero] at hqcomb
  -- Fundamental identity: U * 2^64 = q1_init * d * 2^64 + (q0 * d + u1 * e + u0 * (2^64 - d))
  let U : Nat := u1.toNat * 2 ^ 64 + u0.toNat
  have hU_lt : U < d.toNat * 2 ^ 64 := by
    have h1 : (u1.toNat + 1) * 2 ^ 64 ≤ d.toNat * 2 ^ 64 := Nat.mul_le_mul_right _ hu1_lt
    rw [Nat.add_mul, Nat.one_mul] at h1
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hu0_lt _) h1
  have hfund : U * 2 ^ 64 = q1_init.toNat * d.toNat * 2 ^ 64 +
      (q0.toNat * d.toNat + u1.toNat * e + u0.toNat * (2 ^ 64 - d.toNat)) := by
    have h1 : U * 2 ^ 64 = u1.toNat * (2 ^ 64 * 2 ^ 64) + u0.toNat * 2 ^ 64 := by
      rw [Nat.add_mul, Nat.mul_assoc]
    have h2 : u1.toNat * (2 ^ 64 * 2 ^ 64) = u1.toNat * ((2 ^ 64 + v.toNat) * d.toNat) + u1.toNat * e := by
      rw [← he_eq, Nat.mul_add]
    have h3 : u0.toNat * 2 ^ 64 = u0.toNat * d.toNat + u0.toNat * (2 ^ 64 - d.toNat) := by
      rw [← Nat.mul_add, Nat.add_sub_of_le (Nat.le_of_lt hDlt)]
    have h4 : q1_init.toNat * 2 ^ 64 * d.toNat + q0.toNat * d.toNat =
        (2 ^ 64 + v.toNat) * u1.toNat * d.toNat + u0.toNat * d.toNat := by
      rw [← Nat.add_mul, ← Nat.add_mul]; exact congrArg (· * d.toNat) hqcomb
    have h5 : q1_init.toNat * 2 ^ 64 * d.toNat = q1_init.toNat * d.toNat * 2 ^ 64 := by ac_rfl
    have h6 : (2 ^ 64 + v.toNat) * u1.toNat * d.toNat = u1.toNat * ((2 ^ 64 + v.toNat) * d.toNat) := by ac_rfl
    rw [h5, h6] at h4
    calc U * 2 ^ 64
        = u1.toNat * ((2 ^ 64 + v.toNat) * d.toNat) + u1.toNat * e + (u0.toNat * d.toNat + u0.toNat * (2 ^ 64 - d.toNat)) := by
          rw [h1, h2, h3]
      _ = (u1.toNat * ((2 ^ 64 + v.toNat) * d.toNat) + u0.toNat * d.toNat) + (u1.toNat * e + u0.toNat * (2 ^ 64 - d.toNat)) := by ac_rfl
      _ = (q1_init.toNat * d.toNat * 2 ^ 64 + q0.toNat * d.toNat) + (u1.toNat * e + u0.toNat * (2 ^ 64 - d.toNat)) := by rw [← h4]
      _ = q1_init.toNat * d.toNat * 2 ^ 64 + (q0.toNat * d.toNat + u1.toNat * e + u0.toNat * (2 ^ 64 - d.toNat)) := by ac_rfl
  have hq1_le : q1_init.toNat * d.toNat ≤ U := by
    have : q1_init.toNat * d.toNat * 2 ^ 64 ≤ U * 2 ^ 64 := by rw [hfund]; exact Nat.le_add_right _ _
    exact Nat.le_of_mul_le_mul_right this (Nat.two_pow_pos 64)
  let rem0 : Nat := U - q1_init.toNat * d.toNat
  have hU_eq : q1_init.toNat * d.toNat + rem0 = U := Nat.add_sub_of_le hq1_le
  have hrem0_B : rem0 * 2 ^ 64 = q0.toNat * d.toNat + u1.toNat * e + u0.toNat * (2 ^ 64 - d.toNat) := by
    have h1 : q1_init.toNat * d.toNat * 2 ^ 64 + rem0 * 2 ^ 64 = U * 2 ^ 64 := by
      rw [← Nat.add_mul, hU_eq]
    rw [hfund] at h1
    exact Nat.add_left_cancel h1
  have ⟨_, hrem0_ge_bounds⟩ :=
    divRem21_rem_bounds hBH (Nat.two_pow_pos 63) hd hDlt hu1_lt hu0_lt he_le hq0_lt hrem0_B
  generalize hq1_def : q1_init + 1 = q1
  generalize hr_def : u0 - q1 * d = r
  have hq1_mod : q1.toNat = (q1_init.toNat + 1) % 2 ^ 64 := by
    rw [← hq1_def, UInt64.toNat_add]; rfl
  have hUmod : U % 2 ^ 64 = u0.toNat := by
    show (u1.toNat * 2 ^ 64 + u0.toNat) % 2 ^ 64 = u0.toNat
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu0_lt]
  -- Helper: given final (qf, rf) with qf * D + rf = U and rf < D, conclude div/mod goal
  have finish : ∀ (qf rf : UInt64),
      qf.toNat * d.toNat + rf.toNat = U → rf.toNat < d.toNat →
      qf.toNat = U / d.toNat ∧ rf.toNat = U % d.toNat ∧ rf < d := by
    intro qf rf hdecomp hlt
    refine ⟨?_, ?_, UInt64.lt_iff_toNat_lt.mpr hlt⟩
    · rw [← hdecomp, Nat.add_comm, Nat.add_mul_div_right _ _ hd_pos, Nat.div_eq_of_lt hlt, Nat.zero_add]
    · rw [← hdecomp, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
  by_cases hcase : rem0 < d.toNat
  · -- Case 1: rem0 < d => q1_init is exact, r = 2^64 + rem0 - d > q0, Step 5 fixes back to (q1_init, rem0)
    have hd_le_Br : d.toNat ≤ 2 ^ 64 + rem0 := Nat.le_trans (Nat.le_of_lt hDlt) (Nat.le_add_right _ _)
    have hr_lt_B : 2 ^ 64 + rem0 - d.toNat < 2 ^ 64 := by
      apply Nat.sub_lt_left_of_lt_add hd_le_Br
      rw [Nat.add_comm d.toNat (2 ^ 64)]
      exact Nat.add_lt_add_left hcase (2 ^ 64)
    have hr_val : r.toNat = 2 ^ 64 + rem0 - d.toNat := by
      rw [← hr_def]
      apply uint64_sub_mul_toNat hr_lt_B
      have h1 : (2 ^ 64 + rem0 - d.toNat) + (q1_init.toNat + 1) * d.toNat = 2 ^ 64 + U := by
        calc (2 ^ 64 + rem0 - d.toNat) + (q1_init.toNat + 1) * d.toNat
            = (2 ^ 64 + rem0 - d.toNat) + (q1_init.toNat * d.toNat + d.toNat) := by
              rw [Nat.add_mul, Nat.one_mul]
          _ = ((2 ^ 64 + rem0 - d.toNat) + d.toNat) + q1_init.toNat * d.toNat := by ac_rfl
          _ = (2 ^ 64 + rem0) + q1_init.toNat * d.toNat := by rw [Nat.sub_add_cancel hd_le_Br]
          _ = 2 ^ 64 + (q1_init.toNat * d.toNat + rem0) := by ac_rfl
          _ = 2 ^ 64 + U := by rw [hU_eq]
      have h2 : ((2 ^ 64 + rem0 - d.toNat) + q1.toNat * d.toNat) % 2 ^ 64 =
          ((2 ^ 64 + rem0 - d.toNat) + (q1_init.toNat + 1) * d.toNat) % 2 ^ 64 := by
        rw [hq1_mod, Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
      rw [h2, h1, Nat.add_mod_left]
      exact hUmod
    have hr_gt_q0 : r > q0 := by
      rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, hr_val]
      exact divRem21_case1_gt hDlt hq0_lt hrem0_B
    have hq_back : q1 - 1 = q1_init := by rw [← hq1_def]; exact uint64_add_one_sub_one q1_init
    have hr_back : (r + d).toNat = rem0 := by
      rw [UInt64.toNat_add, hr_val, Nat.sub_add_cancel hd_le_Br, Nat.add_mod_left,
          Nat.mod_eq_of_lt (Nat.lt_trans hcase hDlt)]
    have hnotge : ¬ (r + d ≥ d) := by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, hr_back]
      exact Nat.not_le_of_lt hcase
    simp only [hr_gt_q0, ↓reduceIte, hnotge, hq_back]
    exact finish q1_init (r + d) (by rw [hr_back]; exact hU_eq) (by rw [hr_back]; exact hcase)
  · -- Case 2: d ≤ rem0 => rem1 = rem0 - d < min(2^64, 2*d)
    have hge_d : d.toNat ≤ rem0 := Nat.le_of_not_lt hcase
    have ⟨hrem1_lt_B, hrem1_lt_2d⟩ := hrem0_ge_bounds hge_d
    let rem1 : Nat := rem0 - d.toNat
    have hU_eq1 : (q1_init.toNat + 1) * d.toNat + rem1 = U := by
      calc (q1_init.toNat + 1) * d.toNat + rem1
          = q1_init.toNat * d.toNat + d.toNat + (rem0 - d.toNat) := by
            rw [Nat.add_mul, Nat.one_mul]
        _ = q1_init.toNat * d.toNat + (d.toNat + (rem0 - d.toNat)) := Nat.add_assoc _ _ _
        _ = q1_init.toNat * d.toNat + rem0 := by rw [Nat.add_sub_of_le hge_d]
        _ = U := hU_eq
    have hq1_lt_B : q1_init.toNat + 1 < 2 ^ 64 := by
      have hleU : (q1_init.toNat + 1) * d.toNat ≤ U := by
        rw [← hU_eq1]; exact Nat.le_add_right _ _
      have h1 : (q1_init.toNat + 1) * d.toNat < 2 ^ 64 * d.toNat := by
        rw [Nat.mul_comm (2 ^ 64) d.toNat]; exact Nat.lt_of_le_of_lt hleU hU_lt
      exact Nat.lt_of_mul_lt_mul_right h1
    have hq1_val : q1.toNat = q1_init.toNat + 1 := by
      rw [hq1_mod, Nat.mod_eq_of_lt hq1_lt_B]
    have hr_val : r.toNat = rem1 := by
      rw [← hr_def]
      apply uint64_sub_mul_toNat hrem1_lt_B
      rw [hq1_val, Nat.add_comm rem1, hU_eq1]
      exact hUmod
    by_cases hgt : r > q0
    · -- Subcase 2b: false trigger (rem1 > q0) => rem1 < 2^64 - d ≤ d, Step 5 adds d, Step 6 subtracts d back!
      have hq0_lt_rem1 : q0.toNat < rem1 := by
        have := UInt64.lt_iff_toNat_lt.mp hgt
        rw [hr_val] at this; exact this
      have hrem1_eq : rem1 * 2 ^ 64 + 2 ^ 64 * d.toNat =
          q0.toNat * d.toNat + u1.toNat * e + u0.toNat * (2 ^ 64 - d.toNat) := by
        have h1 : rem1 * 2 ^ 64 + d.toNat * 2 ^ 64 = rem0 * 2 ^ 64 := by
          rw [← Nat.add_mul, Nat.sub_add_cancel hge_d]
        rw [Nat.mul_comm d.toNat (2 ^ 64), hrem0_B] at h1
        exact h1
      have hrem1_lt_sub : rem1 < 2 ^ 64 - d.toNat :=
        divRem21_false_trigger_bound hDlt hu1_lt hu0_lt he_le hq0_lt_rem1 hrem1_eq
      have hsub_le_d : 2 ^ 64 - d.toNat ≤ d.toNat := by
        apply Nat.sub_le_iff_le_add.mpr
        have h2d : 2 ^ 64 ≤ 2 * d.toNat := by rw [hBH]; exact Nat.mul_le_mul_left 2 hd
        rw [Nat.two_mul] at h2d; exact h2d
      have hrem1_lt_d : rem1 < d.toNat := Nat.lt_of_lt_of_le hrem1_lt_sub hsub_le_d
      have hrem1_add_lt : rem1 + d.toNat < 2 ^ 64 :=
        Nat.lt_of_lt_of_le (Nat.add_lt_add_right hrem1_lt_sub d.toNat)
          (by rw [Nat.sub_add_cancel (Nat.le_of_lt hDlt)]; exact Nat.le_refl _)
      have hadd_noovf : (r + d).toNat = rem1 + d.toNat := by
        rw [UInt64.toNat_add, hr_val, Nat.mod_eq_of_lt hrem1_add_lt]
      have hge_step6 : r + d ≥ d := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hadd_noovf]
        exact Nat.le_add_left _ _
      have hq_restore : q1 - 1 + 1 = q1 := by
        rw [← hq1_def, uint64_add_one_sub_one]
      have hr_restore : (r + d - d).toNat = rem1 := by
        rw [UInt64.toNat_sub_of_le _ _ hge_step6, hadd_noovf, Nat.add_sub_cancel]
      simp only [hgt, ↓reduceIte, hge_step6, hq_restore]
      exact finish q1 (r + d - d) (by rw [hq1_val, hr_restore]; exact hU_eq1) (by rw [hr_restore]; exact hrem1_lt_d)
    · -- Subcase 2a: r ≤ q0 => Step 5 skipped, Step 6 adjusts if r ≥ d
      simp only [hgt, ↓reduceIte]
      by_cases hge6 : r ≥ d
      · simp only [hge6, ↓reduceIte]
        have hrem1_ge_d : d.toNat ≤ rem1 := by
          have := UInt64.le_iff_toNat_le.mp hge6
          rw [hr_val] at this; exact this
        have hq2_mul : (q1_init.toNat + 2) * d.toNat = (q1_init.toNat + 1) * d.toNat + d.toNat := by
          have h2 : q1_init.toNat + 2 = (q1_init.toNat + 1) + 1 := rfl
          rw [h2, Nat.add_mul, Nat.one_mul]
        have hq2_decomp : (q1_init.toNat + 2) * d.toNat + (rem1 - d.toNat) = U := by
          calc (q1_init.toNat + 2) * d.toNat + (rem1 - d.toNat)
              = ((q1_init.toNat + 1) * d.toNat + d.toNat) + (rem1 - d.toNat) := by rw [hq2_mul]
            _ = (q1_init.toNat + 1) * d.toNat + (d.toNat + (rem1 - d.toNat)) := Nat.add_assoc _ _ _
            _ = (q1_init.toNat + 1) * d.toNat + rem1 := by rw [Nat.add_sub_of_le hrem1_ge_d]
            _ = U := hU_eq1
        have hq2_lt_B : q1_init.toNat + 2 < 2 ^ 64 := by
          have h1 : (q1_init.toNat + 2) * d.toNat ≤ U := by
            rw [← hq2_decomp]; exact Nat.le_add_right _ _
          have h2 : (q1_init.toNat + 2) * d.toNat < 2 ^ 64 * d.toNat := by
            rw [Nat.mul_comm (2 ^ 64) d.toNat]; exact Nat.lt_of_le_of_lt h1 hU_lt
          exact Nat.lt_of_mul_lt_mul_right h2
        have hq2_val : (q1 + 1).toNat = q1_init.toNat + 2 := by
          rw [UInt64.toNat_add, hq1_val]
          have h1 : (1 : UInt64).toNat = 1 := rfl
          rw [h1, Nat.add_assoc, Nat.mod_eq_of_lt hq2_lt_B]
        have hr2_val : (r - d).toNat = rem1 - d.toNat := by
          rw [UInt64.toNat_sub_of_le _ _ hge6, hr_val]
        have hr2_lt_d : rem1 - d.toNat < d.toNat := by
          apply Nat.sub_lt_left_of_lt_add hrem1_ge_d
          rw [← Nat.two_mul]; exact hrem1_lt_2d
        exact finish (q1 + 1) (r - d) (by rw [hq2_val, hr2_val]; exact hq2_decomp) (by rw [hr2_val]; exact hr2_lt_d)
      · simp only [hge6, ↓reduceIte]
        have hrem1_lt_d : rem1 < d.toNat := by
          have hnot : ¬ d.toNat ≤ r.toNat := fun h => hge6 (UInt64.le_iff_toNat_le.mpr h)
          rw [hr_val] at hnot
          exact Nat.lt_of_not_ge hnot
        exact finish q1 r (by rw [hq1_val, hr_val]; exact hU_eq1) (by rw [hr_val]; exact hrem1_lt_d)

theorem divRem21_spec (u1 u0 d : UInt64) (hd : 2 ^ 63 ≤ d.toNat) (hu1 : u1 < d) :
    let res := divRem21 u1 u0 d (invert21 d hd)
    res.1.toNat = (u1.toNat * 2 ^ 64 + u0.toNat) / d.toNat ∧
    res.2.toNat = (u1.toNat * 2 ^ 64 + u0.toNat) % d.toNat ∧
    res.2 < d := by
  have ⟨hlo, hhi⟩ := invert21_spec d hd
  exact divRem21_spec_aux u1 u0 d (invert21 d hd) hd hu1 hlo hhi

theorem divRem21_eq_divWide64 (u1 u0 d : UInt64) (hd : 2 ^ 63 ≤ d.toNat) (hu1 : u1 < d) :
    divRem21 u1 u0 d (invert21 d hd) = divWide64 u1 u0 d hu1 := by
  have ⟨hq, hr, _⟩ := divRem21_spec u1 u0 d hd hu1
  apply Prod.ext
  · apply UInt64.toNat_inj.mp
    rw [hq, divWide64_fst]
  · apply UInt64.toNat_inj.mp
    rw [hr, divWide64_snd]

/-! ### Single-Limb Möller–Granlund Division (`divMod1Inv`) -/

private theorem divRem21_mul_add_spec (u1 u0 d : UInt64) (hd : 2 ^ 63 ≤ d.toNat) (hu1 : u1 < d) :
    let res := divRem21 u1 u0 d (invert21 d hd)
    res.1.toNat * d.toNat + res.2.toNat = u1.toNat * 2 ^ 64 + u0.toNat ∧ res.2 < d := by
  have ⟨hq, hr, hlt⟩ := divRem21_spec u1 u0 d hd hu1
  refine ⟨?_, hlt⟩
  rw [hq, hr, Nat.mul_comm]
  exact Nat.div_add_mod _ _

private theorem divMod1NormLoop_spec (a : Array UInt64) (d v : UInt64)
    (hv : ∀ u1 u0, u1 < d →
      let res := divRem21 u1 u0 d v
      res.1.toNat * d.toNat + res.2.toNat = u1.toNat * 2 ^ 64 + u0.toNat ∧ res.2 < d)
    (k : Nat) (rem : UInt64) (hrem : rem < d) (q : Array UInt64)
    (hk : k ≤ a.size) (hsz : k ≤ q.size) (hlo : ∀ j < k, getLimb q j = 0) :
    let res := divMod1NormLoop a d v k rem q
    WF res.1 ∧ res.2 < d ∧
    toNat res.1 * d.toNat + res.2.toNat =
      toNat q * d.toNat + rem.toNat * (2 ^ 64) ^ k + toNatPrefix a k := by
  induction k generalizing rem q with
  | zero =>
    unfold divMod1NormLoop
    simp only [toNat_normalize, Nat.pow_zero, Nat.mul_one, toNatPrefix_zero, Nat.add_zero]
    exact ⟨wf_normalize q, hrem, trivial⟩
  | succ k ih =>
    unfold divMod1NormLoop
    dsimp only
    have hspec := hv rem (getLimb a k) hrem
    dsimp only at hspec
    let resW := divRem21 rem (getLimb a k) d v
    have hklt : k < q.size := by omega
    have hq0 : getLimb q k = 0 := hlo k (by omega)
    have hlo' : ∀ j < k, getLimb (setLimb q k resW.1) j = 0 := by
      intro j hj
      rw [getLimb_setLimb q k resW.1 hklt j]
      simp [Nat.ne_of_lt hj, hlo j (by omega)]
    have ⟨hwf, hlt, heq⟩ := ih resW.2 hspec.2 (setLimb q k resW.1) (by omega)
      (by rw [size_setLimb]; omega) hlo'
    refine ⟨hwf, hlt, ?_⟩
    rw [heq, toNat_setLimb_of_zero q k resW.1 hklt hq0, toNatPrefix_succ a k, Nat.pow_succ (2 ^ 64) k]
    have hmul : (resW.1.toNat * d.toNat + resW.2.toNat) * (2 ^ 64) ^ k =
        (rem.toNat * 2 ^ 64 + (getLimb a k).toNat) * (2 ^ 64) ^ k := by
      rw [hspec.1]
    rw [Nat.add_mul, Nat.add_mul] at hmul
    rw [Nat.add_mul]
    have ha1 : resW.1.toNat * (2 ^ 64) ^ k * d.toNat = resW.1.toNat * d.toNat * (2 ^ 64) ^ k := by
      rw [Nat.mul_assoc, Nat.mul_comm ((2 ^ 64) ^ k) d.toNat, ← Nat.mul_assoc]
    have ha2 : rem.toNat * ((2 ^ 64) ^ k * 2 ^ 64) = rem.toNat * 2 ^ 64 * (2 ^ 64) ^ k := by
      rw [Nat.mul_comm ((2 ^ 64) ^ k) (2 ^ 64), ← Nat.mul_assoc]
    rw [ha1, ha2]
    omega

theorem shift_or_toNat (hi lo s : UInt64) (hs1 : 0 < s.toNat) (hs2 : s.toNat < 64) :
    ((hi <<< s) ||| (lo >>> ((64 : UInt64) - s))).toNat =
      (hi.toNat * 2 ^ s.toNat) % 2 ^ 64 + lo.toNat / 2 ^ (64 - s.toNat) := by
  have hinv : ((64 : UInt64) - s).toNat = 64 - s.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; exact Nat.le_of_lt hs2)]
    rfl
  have hshl : (hi <<< s).toNat = (hi.toNat * 2 ^ s.toNat) % 2 ^ 64 := by
    rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hs2, Nat.shiftLeft_eq]
  have hshr : (lo >>> ((64 : UInt64) - s)).toNat = lo.toNat / 2 ^ (64 - s.toNat) := by
    rw [UInt64.toNat_shiftRight, hinv, Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]
  have hlo_lt : lo.toNat < 2 ^ 64 := uint64_toNat_lt lo
  have hshr_lt : lo.toNat / 2 ^ (64 - s.toNat) < 2 ^ s.toNat := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_lt hs2)]
    exact hlo_lt
  have hdvd : 2 ^ s.toNat ∣ (hi.toNat * 2 ^ s.toNat) % 2 ^ 64 := by
    have hpow : 2 ^ s.toNat ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (Nat.le_of_lt hs2)
    have hmul : 2 ^ s.toNat ∣ hi.toNat * 2 ^ s.toNat := Nat.dvd_mul_left _ _
    exact (Nat.dvd_mod_iff hpow).mpr hmul
  rw [UInt64.toNat_or, hshl, hshr]
  apply Nat.eq_of_testBit_eq
  intro bit
  rw [Nat.testBit_or]
  rcases hdvd with ⟨q, hq⟩
  rw [hq]
  have hdiv : (2 ^ s.toNat * q + lo.toNat / 2 ^ (64 - s.toNat)) / 2 ^ s.toNat = q := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt hshr_lt, Nat.zero_add]
  have hmod : (2 ^ s.toNat * q + lo.toNat / 2 ^ (64 - s.toNat)) % 2 ^ s.toNat =
      lo.toNat / 2 ^ (64 - s.toNat) := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hshr_lt]
  by_cases hlt : bit < s.toNat
  · have hq0 : (2 ^ s.toNat * q).testBit bit = false := by
      rw [Nat.mul_comm, ← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
      have hge : ¬ s.toNat ≤ bit := by omega
      simp [hge]
    have hsum : (2 ^ s.toNat * q + lo.toNat / 2 ^ (64 - s.toNat)).testBit bit =
        ((2 ^ s.toNat * q + lo.toNat / 2 ^ (64 - s.toNat)) % 2 ^ s.toNat).testBit bit := by
      rw [Nat.testBit_mod_two_pow]; simp [hlt]
    rw [hq0, Bool.false_or, hsum, hmod]
  · have hlo0 : (lo.toNat / 2 ^ (64 - s.toNat)).testBit bit = false :=
      testBit_eq_false_of_lt_pow (Nat.lt_of_lt_of_le hshr_lt (Nat.pow_le_pow_right (by decide) (by omega)))
    have hsub : bit = s.toNat + (bit - s.toNat) := by omega
    have hsum : (2 ^ s.toNat * q + lo.toNat / 2 ^ (64 - s.toNat)).testBit bit = q.testBit (bit - s.toNat) := by
      conv => lhs; rw [hsub]
      rw [← Nat.testBit_shiftRight, Nat.shiftRight_eq_div_pow, hdiv]
    have hlhs : (2 ^ s.toNat * q).testBit bit = q.testBit (bit - s.toNat) := by
      rw [Nat.mul_comm, ← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
      have hge : s.toNat ≤ bit := by omega
      simp [hge]
    rw [hlo0, Bool.or_false, hsum, hlhs]

private theorem divMod1ShiftLoop_raw (a : Array UInt64) (d s v : UInt64)
    (hd : d ≠ 0) (hs : s = clz64 d) (hsne : s ≠ 0)
    (hv : ∀ u1 u0, u1 < d <<< s →
      let res := divRem21 u1 u0 (d <<< s) v
      res.1.toNat * (d <<< s).toNat + res.2.toNat = u1.toNat * 2 ^ 64 + u0.toNat ∧ res.2 < d <<< s)
    (k : Nat) (rem : UInt64) (hrem : rem < d <<< s) (q : Array UInt64)
    (hk : k ≤ a.size) (hsz : k ≤ q.size) (hlo : ∀ j < k, getLimb q j = 0) :
    let dn := d <<< s
    let invS := (64 : UInt64) - s
    let topCarry := if k = 0 then 0 else (getLimb a (k - 1) >>> invS).toNat
    let res := divMod1ShiftLoop a dn v s k rem q
    WF res.1 ∧
    ∃ rRaw : UInt64, rRaw < dn ∧ res.2 = rRaw >>> s ∧
      toNat res.1 * dn.toNat + rRaw.toNat + topCarry * (2 ^ 64) ^ k =
        toNat q * dn.toNat + rem.toNat * (2 ^ 64) ^ k + toNatPrefix a k * 2 ^ s.toNat := by
  have hs_lt : s.toNat < 64 := by rw [hs]; exact clz64_lt_64 d hd
  have hs_pos : 0 < s.toNat := by
    have : s.toNat ≠ 0 := fun h0 => hsne (UInt64.toNat_inj.mp (by simpa using h0))
    omega
  have hinv_val : ((64 : UInt64) - s).toNat = 64 - s.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; exact Nat.le_of_lt hs_lt)]
    rfl
  induction k generalizing rem q with
  | zero =>
    unfold divMod1ShiftLoop
    simp only [↓reduceIte, Nat.zero_mul, Nat.add_zero, Nat.pow_zero, Nat.mul_one,
      toNatPrefix_zero, toNat_normalize]
    exact ⟨wf_normalize q, rem, hrem, rfl, rfl⟩
  | succ k ih =>
    unfold divMod1ShiftLoop
    dsimp only
    let cur := getLimb a k
    let lo := if k == 0 then cur <<< s else (cur <<< s) ||| (getLimb a (k - 1) >>> ((64 : UInt64) - s))
    have hspec := hv rem lo hrem
    dsimp only at hspec
    let resW := divRem21 rem lo (d <<< s) v
    have hklt : k < q.size := by omega
    have hq0 : getLimb q k = 0 := hlo k (by omega)
    have hlo' : ∀ j < k, getLimb (setLimb q k resW.1) j = 0 := by
      intro j hj
      rw [getLimb_setLimb q k resW.1 hklt j]
      simp [Nat.ne_of_lt hj, hlo j (by omega)]
    have ⟨hwf, rRaw, hrRaw_lt, hrRaw_eq, heq⟩ :=
      ih resW.2 hspec.2 (setLimb q k resW.1) (by omega) (by rw [size_setLimb]; omega) hlo'
    refine ⟨hwf, rRaw, hrRaw_lt, hrRaw_eq, ?_⟩
    rw [toNat_setLimb_of_zero q k resW.1 hklt hq0, Nat.add_mul] at heq
    have hinv_lt : 64 - s.toNat < 64 := by omega
    have hcur_split : (cur >>> ((64 : UInt64) - s)).toNat * 2 ^ 64 + (cur <<< s).toNat = cur.toNat * 2 ^ s.toNat := by
      rw [UInt64.toNat_shiftRight, hinv_val, Nat.mod_eq_of_lt hinv_lt, Nat.shiftRight_eq_div_pow,
          UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hs_lt, Nat.shiftLeft_eq]
      have hpow : 2 ^ 64 = 2 ^ (64 - s.toNat) * 2 ^ s.toNat := by
        rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hs_lt)]
      have hdm := Nat.div_add_mod cur.toNat (2 ^ (64 - s.toNat))
      have hltm : cur.toNat % 2 ^ (64 - s.toNat) < 2 ^ (64 - s.toNat) :=
        Nat.mod_lt _ (Nat.two_pow_pos _)
      have hmul_lt : (cur.toNat % 2 ^ (64 - s.toNat)) * 2 ^ s.toNat < 2 ^ 64 := by
        rw [hpow]; exact Nat.mul_lt_mul_of_pos_right hltm (Nat.two_pow_pos _)
      have hdecomp : cur.toNat * 2 ^ s.toNat =
          (cur.toNat / 2 ^ (64 - s.toNat)) * 2 ^ 64 + (cur.toNat % 2 ^ (64 - s.toNat)) * 2 ^ s.toNat := by
        calc cur.toNat * 2 ^ s.toNat
            = (2 ^ (64 - s.toNat) * (cur.toNat / 2 ^ (64 - s.toNat)) + cur.toNat % 2 ^ (64 - s.toNat)) * 2 ^ s.toNat := by
              rw [hdm]
          _ = 2 ^ (64 - s.toNat) * (cur.toNat / 2 ^ (64 - s.toNat)) * 2 ^ s.toNat +
              cur.toNat % 2 ^ (64 - s.toNat) * 2 ^ s.toNat := by rw [Nat.add_mul]
          _ = (cur.toNat / 2 ^ (64 - s.toNat)) * (2 ^ (64 - s.toNat) * 2 ^ s.toNat) +
              cur.toNat % 2 ^ (64 - s.toNat) * 2 ^ s.toNat := by
              rw [Nat.mul_comm (2 ^ (64 - s.toNat)) (cur.toNat / 2 ^ (64 - s.toNat)), Nat.mul_assoc]
          _ = (cur.toNat / 2 ^ (64 - s.toNat)) * 2 ^ 64 + cur.toNat % 2 ^ (64 - s.toNat) * 2 ^ s.toNat := by
              rw [← hpow]
      have hmul_mod : (cur.toNat * 2 ^ s.toNat) % 2 ^ 64 = (cur.toNat % 2 ^ (64 - s.toNat)) * 2 ^ s.toNat := by
        rw [hdecomp, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hmul_lt]
      rw [hmul_mod]
      exact hdecomp.symm
    have hlo_eq : lo.toNat = (cur <<< s).toNat + (if k = 0 then 0 else (getLimb a (k - 1) >>> ((64 : UInt64) - s)).toNat) := by
      dsimp only [lo]
      cases k with
      | zero => simp
      | succ k' =>
        simp only [beq_iff_eq, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
          Nat.add_sub_cancel]
        rw [shift_or_toNat cur (getLimb a k') s hs_pos hs_lt,
            UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hs_lt, Nat.shiftLeft_eq,
            UInt64.toNat_shiftRight, hinv_val, Nat.mod_eq_of_lt hinv_lt, Nat.shiftRight_eq_div_pow]
    have hmul_spec : (resW.1.toNat * (d <<< s).toNat + resW.2.toNat) * (2 ^ 64) ^ k =
        (rem.toNat * 2 ^ 64 + lo.toNat) * (2 ^ 64) ^ k := congrArg (· * (2 ^ 64) ^ k) hspec.1
    rw [Nat.add_mul, Nat.add_mul, hlo_eq, Nat.add_mul] at hmul_spec
    have hmul_cur : ((cur >>> ((64 : UInt64) - s)).toNat * 2 ^ 64 + (cur <<< s).toNat) * (2 ^ 64) ^ k =
        cur.toNat * 2 ^ s.toNat * (2 ^ 64) ^ k := congrArg (· * (2 ^ 64) ^ k) hcur_split
    rw [Nat.add_mul] at hmul_cur
    rw [toNatPrefix_succ a k, Nat.add_mul, Nat.pow_succ (2 ^ 64) k]
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    have ha1 : resW.1.toNat * (2 ^ 64) ^ k * (d <<< s).toNat = resW.1.toNat * (d <<< s).toNat * (2 ^ 64) ^ k := by
      rw [Nat.mul_assoc, Nat.mul_comm ((2 ^ 64) ^ k) (d <<< s).toNat, ← Nat.mul_assoc]
    have ha2 : rem.toNat * ((2 ^ 64) ^ k * 2 ^ 64) = rem.toNat * 2 ^ 64 * (2 ^ 64) ^ k := by
      rw [Nat.mul_comm ((2 ^ 64) ^ k) (2 ^ 64), ← Nat.mul_assoc]
    have ha3 : (cur >>> ((64 : UInt64) - s)).toNat * ((2 ^ 64) ^ k * 2 ^ 64) =
        (cur >>> ((64 : UInt64) - s)).toNat * 2 ^ 64 * (2 ^ 64) ^ k := by
      rw [Nat.mul_comm ((2 ^ 64) ^ k) (2 ^ 64), ← Nat.mul_assoc]
    have ha4 : cur.toNat * (2 ^ 64) ^ k * 2 ^ s.toNat = cur.toNat * 2 ^ s.toNat * (2 ^ 64) ^ k := by
      rw [Nat.mul_assoc, Nat.mul_comm ((2 ^ 64) ^ k), ← Nat.mul_assoc]
    rw [ha1] at heq
    rw [ha2, ha3, ha4]
    dsimp only [resW, lo, cur] at heq hmul_spec hmul_cur ⊢
    omega

theorem divMod1Inv_spec (a : Array UInt64) (d : UInt64) (hd : d ≠ 0) :
    WF (divMod1Inv a d).1 ∧
    toNat (divMod1Inv a d).1 = toNat a / d.toNat ∧
    (divMod1Inv a d).2.toNat = toNat a % d.toNat ∧
    (divMod1Inv a d).2 < d := by
  have hd_pos : 0 < d.toNat := by
    have : d.toNat ≠ 0 := fun h0 => hd (UInt64.toNat_inj.mp (by simpa using h0))
    omega
  have h0_lt_d : (0 : UInt64) < d := UInt64.lt_iff_toNat_lt.mpr hd_pos
  unfold divMod1Inv
  simp only [hd, ↓reduceDIte]
  split
  · rename_i ha0
    have hz : a.size = 0 := eq_of_beq ha0
    have hto : toNat a = 0 := by rw [toNat, hz]; rfl
    rw [hto, Nat.zero_div, Nat.zero_mod]
    exact ⟨Or.inl rfl, rfl, rfl, h0_lt_d⟩
  · rename_i hane0
    have hasz_pos : 0 < a.size := by
      have : a.size ≠ 0 := fun h => hane0 (by simp [h])
      omega
    split
    · rename_i ha1
      have hsz1 : a.size = 1 := eq_of_beq ha1
      have hto : toNat a = (getLimb a 0).toNat := by
        rw [toNat, hsz1, toNatPrefix_succ, toNatPrefix_zero]
        simp only [Nat.pow_zero, Nat.mul_one, Nat.zero_add]
      rw [hto, toNat_ofUInt64, UInt64.toNat_div, UInt64.toNat_mod]
      refine ⟨wf_ofUInt64 _, rfl, rfl, ?_⟩
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_mod]
      exact Nat.mod_lt _ hd_pos
    · split
      · rename_i hs0b
        have hs0 : clz64 d = 0 := eq_of_beq hs0b
        have hdn_eq : d <<< clz64 d = d := by
          apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_shiftLeft, hs0]; simp
        have hdn_toNat : (d <<< clz64 d).toNat = d.toNat := congrArg UInt64.toNat hdn_eq
        have hge := shiftLeft_clz64_ge d hd
        have h0_lt_dn : (0 : UInt64) < d <<< clz64 d := by rw [hdn_eq]; exact h0_lt_d
        have ⟨hwf, hlt0, heq⟩ := divMod1NormLoop_spec a (d <<< clz64 d) (invert21 (d <<< clz64 d) hge)
          (fun u1 u0 hu1 => divRem21_mul_add_spec u1 u0 (d <<< clz64 d) hge hu1) a.size 0 h0_lt_dn (mkZeros a.size)
          (Nat.le_refl _) (by simp) (fun j _ => getLimb_mkZeros _ j)
        have hlt : (divMod1NormLoop a (d <<< clz64 d) (invert21 (d <<< clz64 d) hge) a.size 0 (mkZeros a.size)).2 < d := by
          rw [UInt64.lt_iff_toNat_lt, ← hdn_toNat]
          exact UInt64.lt_iff_toNat_lt.mp hlt0
        rw [hdn_toNat, toNat_mkZeros, UInt64.toNat_zero, Nat.zero_mul, Nat.zero_mul, Nat.zero_add] at heq
        have hltN : (divMod1NormLoop a (d <<< clz64 d) (invert21 (d <<< clz64 d) hge) a.size 0 (mkZeros a.size)).2.toNat < d.toNat :=
          UInt64.lt_iff_toNat_lt.mp hlt
        refine ⟨hwf, ?_, ?_, hlt⟩
        · have h1 : (toNat (divMod1NormLoop a (d <<< clz64 d) (invert21 (d <<< clz64 d) hge) a.size 0 (mkZeros a.size)).1 * d.toNat +
              (divMod1NormLoop a (d <<< clz64 d) (invert21 (d <<< clz64 d) hge) a.size 0 (mkZeros a.size)).2.toNat) / d.toNat =
              toNat (divMod1NormLoop a (d <<< clz64 d) (invert21 (d <<< clz64 d) hge) a.size 0 (mkZeros a.size)).1 := by
            rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd_pos, Nat.div_eq_of_lt hltN, Nat.zero_add]
          rw [← h1, heq]; rfl
        · have h1 : (toNat (divMod1NormLoop a (d <<< clz64 d) (invert21 (d <<< clz64 d) hge) a.size 0 (mkZeros a.size)).1 * d.toNat +
              (divMod1NormLoop a (d <<< clz64 d) (invert21 (d <<< clz64 d) hge) a.size 0 (mkZeros a.size)).2.toNat) % d.toNat =
              (divMod1NormLoop a (d <<< clz64 d) (invert21 (d <<< clz64 d) hge) a.size 0 (mkZeros a.size)).2.toNat := by
            rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hltN]
          rw [← h1, heq]; rfl
      · rename_i hsneb
        have hsne : clz64 d ≠ 0 := fun h0 => hsneb (by simp [h0])
        let s := clz64 d
        have hs_lt : s.toNat < 64 := clz64_lt_64 d hd
        have hs_pos : 0 < s.toNat := by
          have : s.toNat ≠ 0 := fun h0 => hsne (UInt64.toNat_inj.mp (by simpa using h0))
          omega
        have hinv_val : ((64 : UInt64) - s).toNat = 64 - s.toNat := by
          rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; exact Nat.le_of_lt hs_lt)]
          rfl
        have hdn_val : (d <<< s).toNat = d.toNat * 2 ^ s.toNat := by
          have hnorm := clz64_shift_norm d hd
          rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hs_lt, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hnorm.2]
        have hrem0_lt : getLimb a (a.size - 1) >>> ((64 : UInt64) - s) < d <<< s := by
          rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_shiftRight, hinv_val,
              Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow, hdn_val]
          have hlt2s : (getLimb a (a.size - 1)).toNat / 2 ^ (64 - s.toNat) < 2 ^ s.toNat := by
            rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_lt hs_lt)]
            exact uint64_toNat_lt _
          have hle_d : 2 ^ s.toNat ≤ d.toNat * 2 ^ s.toNat := Nat.le_mul_of_pos_left _ hd_pos
          omega
        have hge := shiftLeft_clz64_ge d hd
        have ⟨hwf, rRaw, hrRaw_lt, hrRaw_eq, heq⟩ :=
          divMod1ShiftLoop_raw a d s (invert21 (d <<< s) hge) hd rfl hsne
            (fun u1 u0 hu1 => divRem21_mul_add_spec u1 u0 (d <<< s) hge hu1) a.size
            (getLimb a (a.size - 1) >>> ((64 : UInt64) - s)) hrem0_lt (mkZeros a.size)
            (Nat.le_refl _) (by simp) (fun j _ => getLimb_mkZeros _ j)
        have hne_sz : a.size ≠ 0 := by omega
        simp only [hne_sz, ↓reduceIte, toNat_mkZeros, Nat.zero_mul, Nat.zero_add] at heq
        have heq_cancel : toNat (divMod1ShiftLoop a (d <<< s) (invert21 (d <<< s) hge) s a.size
              (getLimb a (a.size - 1) >>> ((64 : UInt64) - s)) (mkZeros a.size)).1 * (d <<< s).toNat +
            rRaw.toNat = toNat a * 2 ^ s.toNat := by
          change _ + _ = toNatPrefix a a.size * 2 ^ s.toNat
          omega
        rw [hdn_val] at heq_cancel
        have h2s_pos : 0 < 2 ^ s.toNat := Nat.two_pow_pos _
        have hrRaw_lt_N : rRaw.toNat < d.toNat * 2 ^ s.toNat := by
          rw [← hdn_val]; exact UInt64.lt_iff_toNat_lt.mp hrRaw_lt
        have hrRaw_dvd : 2 ^ s.toNat ∣ rRaw.toNat := by
          have h1 : rRaw.toNat = (toNat a - toNat (divMod1ShiftLoop a (d <<< s) (invert21 (d <<< s) hge) s a.size
              (getLimb a (a.size - 1) >>> ((64 : UInt64) - s)) (mkZeros a.size)).1 * d.toNat) * 2 ^ s.toNat := by
            have hmul : toNat (divMod1ShiftLoop a (d <<< s) (invert21 (d <<< s) hge) s a.size
                (getLimb a (a.size - 1) >>> ((64 : UInt64) - s)) (mkZeros a.size)).1 * (d.toNat * 2 ^ s.toNat) =
                (toNat (divMod1ShiftLoop a (d <<< s) (invert21 (d <<< s) hge) s a.size
                (getLimb a (a.size - 1) >>> ((64 : UInt64) - s)) (mkZeros a.size)).1 * d.toNat) * 2 ^ s.toNat :=
              (Nat.mul_assoc _ _ _).symm
            rw [hmul] at heq_cancel
            rw [Nat.sub_mul]
            omega
          exact ⟨_, by rw [h1, Nat.mul_comm]⟩
        have hr_toNat : (rRaw >>> s).toNat = rRaw.toNat / 2 ^ s.toNat := by
          rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hs_lt, Nat.shiftRight_eq_div_pow]
        have hr_lt_d : (rRaw >>> s).toNat < d.toNat := by
          rw [hr_toNat, Nat.div_lt_iff_lt_mul h2s_pos]; exact hrRaw_lt_N
        have hdecomp : toNat (divMod1ShiftLoop a (d <<< s) (invert21 (d <<< s) hge) s a.size
              (getLimb a (a.size - 1) >>> ((64 : UInt64) - s)) (mkZeros a.size)).1 * d.toNat +
            (rRaw >>> s).toNat = toNat a := by
          have hexact : (rRaw >>> s).toNat * 2 ^ s.toNat = rRaw.toNat := by
            rw [hr_toNat, Nat.mul_comm]; exact Nat.mul_div_cancel' hrRaw_dvd
          have h1 : (toNat (divMod1ShiftLoop a (d <<< s) (invert21 (d <<< s) hge) s a.size
                (getLimb a (a.size - 1) >>> ((64 : UInt64) - s)) (mkZeros a.size)).1 * d.toNat +
              (rRaw >>> s).toNat) * 2 ^ s.toNat = toNat a * 2 ^ s.toNat := by
            rw [Nat.add_mul, Nat.mul_assoc, hexact]
            exact heq_cancel
          exact Nat.eq_of_mul_eq_mul_right h2s_pos h1
        refine ⟨hwf, ?_, ?_, ?_⟩
        · have h1 : (toNat (divMod1ShiftLoop a (d <<< s) (invert21 (d <<< s) hge) s a.size
              (getLimb a (a.size - 1) >>> ((64 : UInt64) - s)) (mkZeros a.size)).1 * d.toNat +
              (rRaw >>> s).toNat) / d.toNat =
              toNat (divMod1ShiftLoop a (d <<< s) (invert21 (d <<< s) hge) s a.size
              (getLimb a (a.size - 1) >>> ((64 : UInt64) - s)) (mkZeros a.size)).1 := by
            rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd_pos, Nat.div_eq_of_lt hr_lt_d, Nat.zero_add]
          rw [← h1, hdecomp]
        · rw [hrRaw_eq]
          have h1 : (toNat (divMod1ShiftLoop a (d <<< s) (invert21 (d <<< s) hge) s a.size
              (getLimb a (a.size - 1) >>> ((64 : UInt64) - s)) (mkZeros a.size)).1 * d.toNat +
              (rRaw >>> s).toNat) % d.toNat = (rRaw >>> s).toNat := by
            rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr_lt_d]
          rw [← h1, hdecomp]
        · rw [hrRaw_eq]
          exact UInt64.lt_iff_toNat_lt.mpr hr_lt_d

theorem wf_divMod1Inv (a : Array UInt64) (d : UInt64) : WF (divMod1Inv a d).1 := by
  by_cases hd : d = 0
  · subst hd; unfold divMod1Inv; simp only [↓reduceDIte]; exact Or.inl rfl
  · exact (divMod1Inv_spec a d hd).1

end IxCC.BigNat
