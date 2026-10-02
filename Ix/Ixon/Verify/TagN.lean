/-
Moved from Ix/Compile/Verify/TagN.lean at Ix revision
22afee6d9245bd5f974ad59019affed034d84615.
-/

import Ix.Ixon.Verify.Basic

/-!
# TagN integer code

Proofs about `Ixon.putTagN` / `Ixon.getTagN` for flag widths `f ∈ {0, 2, 4}`.
The explicit bytes written (`Codec.tagNBytes`), their length
(`Ixon.tagNByteWidth`) and the exact reads (roundtrip) are in
`Ixon.Verify.Codec`, where every wire codec proof uses them. This module
adds the rung ends, monotonicity of the width, and the converse: every successful
read consumed exactly the encoding of the decoded value, so the code is a
bijection between `UInt64` values (per flag) and accepted byte strings.
Invalid codes and overflowing 8-byte payloads are rejected.
-/

namespace Ixon.Verify.TagN

open Ixon.Verify.Codec

/-! ## Rung ends -/

theorem tagNEnd1_eq_0 : Ixon.tagNEnd1 0 = 128 := by decide
theorem tagNEnd2_eq_0 : Ixon.tagNEnd2 0 = 16512 := by decide
theorem tagNEnd3_eq_0 : Ixon.tagNEnd3 0 = 82048 := by decide
theorem tagNEnd4_eq_0 : Ixon.tagNEnd4 0 = 16859264 := by decide
theorem tagNEnd5_eq_0 : Ixon.tagNEnd5 0 = 4311826560 := by decide
theorem tagNEnd1_eq_2 : Ixon.tagNEnd1 2 = 32 := by decide
theorem tagNEnd2_eq_2 : Ixon.tagNEnd2 2 = 4128 := by decide
theorem tagNEnd3_eq_2 : Ixon.tagNEnd3 2 = 69664 := by decide
theorem tagNEnd4_eq_2 : Ixon.tagNEnd4 2 = 16846880 := by decide
theorem tagNEnd5_eq_2 : Ixon.tagNEnd5 2 = 4311814176 := by decide
theorem tagNEnd1_eq_4 : Ixon.tagNEnd1 4 = 8 := by decide
theorem tagNEnd2_eq_4 : Ixon.tagNEnd2 4 = 1032 := by decide
theorem tagNEnd3_eq_4 : Ixon.tagNEnd3 4 = 66568 := by decide
theorem tagNEnd4_eq_4 : Ixon.tagNEnd4 4 = 16843784 := by decide
theorem tagNEnd5_eq_4 : Ixon.tagNEnd5 4 = 4311811080 := by decide

/-- The rung ends increase. -/
theorem tagNEnd_le (f : Nat) :
    Ixon.tagNEnd1 f ≤ Ixon.tagNEnd2 f ∧ Ixon.tagNEnd2 f ≤ Ixon.tagNEnd3 f ∧
      Ixon.tagNEnd3 f ≤ Ixon.tagNEnd4 f ∧ Ixon.tagNEnd4 f ≤ Ixon.tagNEnd5 f ∧
      Ixon.tagNEnd5 f ≤ Ixon.tagNEnd6 f := by
  unfold Ixon.tagNEnd6 Ixon.tagNEnd5 Ixon.tagNEnd4 Ixon.tagNEnd3 Ixon.tagNEnd2
  exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, Nat.le_add_right _ _,
    Nat.le_add_right _ _, Nat.le_add_right _ _⟩

/-- Every `UInt64` lies below the end of rung 6, for every flag width. -/
theorem uint64_lt_tagNEnd6 (f : Nat) (v : UInt64) : v.toNat < Ixon.tagNEnd6 f := by
  unfold Ixon.tagNEnd6
  exact Nat.lt_of_lt_of_le v.toNat_lt (Nat.le_add_left _ _)

/-- The 9-byte rung starts below `2^64` for the supported flag widths. -/
theorem tagNEnd5_lt (f : Nat) (hf : f = 0 ∨ f = 2 ∨ f = 4) :
    Ixon.tagNEnd5 f < 2 ^ 33 := by
  rcases hf with rfl | rfl | rfl <;> decide

/-! ## Width -/

theorem tagNByteWidth_mono (f : Nat) {i j : Nat} (h : i ≤ j) :
    Ixon.tagNByteWidth f i ≤ Ixon.tagNByteWidth f j := by
  have := tagNEnd_le f
  unfold Ixon.tagNByteWidth
  repeat' split
  all_goals omega

theorem tagNByteWidth_pos (f i : Nat) : 1 ≤ Ixon.tagNByteWidth f i := by
  unfold Ixon.tagNByteWidth
  repeat' split
  all_goals omega

/-! ## Inverting successful reads -/

/-- A successful read moved the cursor across exactly `bytes`. -/
def Consumed (s s' : Ixon.GetState) (bytes : ByteArray) : Prop :=
  s' = { idx := s.idx + bytes.size, bytes := s.bytes } ∧
    s.bytes.extract s.idx (s.idx + bytes.size) = bytes

theorem Consumed.empty (s : Ixon.GetState) : Consumed s s ByteArray.empty := by
  exact ⟨by simp, by simp⟩

theorem Consumed.trans {s s1 s2 : Ixon.GetState} {a b : ByteArray}
    (h1 : Consumed s s1 a) (h2 : Consumed s1 s2 b) : Consumed s s2 (a ++ b) := by
  obtain ⟨rfl, hx1⟩ := h1
  obtain ⟨rfl, hx2⟩ := h2
  simp only at hx2
  unfold Consumed
  rw [ByteArray.size_append, ← Nat.add_assoc]
  refine ⟨rfl, ?_⟩
  rw [ByteArray.extract_eq_extract_append_extract (s.idx + a.size)
    (by omega) (by omega), hx1, hx2]

theorem bind_ok_inv {x : Ixon.GetM α} {k : α → Ixon.GetM β} {s s' : Ixon.GetState}
    {v : β} (h : (x >>= k) s = .ok v s') :
    ∃ a s1, x s = .ok a s1 ∧ k a s1 = .ok v s' := by
  change EStateM.bind x k s = _ at h
  unfold EStateM.bind at h
  split at h
  · exact ⟨_, _, by assumption, h⟩
  · cases h

theorem pure_ok_inv {a b : α} {s s' : Ixon.GetState}
    (h : (pure a : Ixon.GetM α) s = .ok b s') : a = b ∧ s' = s := by
  change EStateM.Result.ok a s = _ at h
  cases h
  exact ⟨rfl, rfl⟩

theorem throw_ok_false {e : String} {b : α} {s s' : Ixon.GetState}
    (h : (throw e : Ixon.GetM α) s = .ok b s') : False := by
  change EStateM.Result.error e s = _ at h
  cases h

theorem getU8_ok {s s' : Ixon.GetState} {b : UInt8} (h : Ixon.getU8 s = .ok b s') :
    Consumed s s' [b].toByteArray ∧ s.bytes[s.idx]! = b := by
  unfold Ixon.getU8 at h
  change EStateM.bind EStateM.get _ s = _ at h
  simp only [EStateM.bind, EStateM.get] at h
  split at h
  · rename_i hlt
    change EStateM.Result.ok _ _ = _ at h
    cases h
    refine ⟨⟨by simp, ?_⟩, rfl⟩
    simp only [List.size_toByteArray, List.length_cons, List.length_nil, Nat.zero_add]
    rw [ByteArray.extract_add_one (by omega)]
    simp [getElem!_pos, hlt]
  · cases h

theorem or_shift_toNat (low : UInt8) (high : UInt64) (hh : high.toNat < 2 ^ 56) :
    (low.toUInt64 ||| high <<< 8).toNat = low.toNat + high.toNat * 256 := by
  have hlow := low.toNat_lt
  have hsh : high.toNat * 256 < 2 ^ 64 := by omega
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64,
    UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
  rw [show 2 ^ 8 = 256 from rfl, Nat.mod_eq_of_lt hsh, Nat.or_comm,
    show high.toNat * 256 = high.toNat <<< 8 by rw [Nat.shiftLeft_eq],
    ← Nat.shiftLeft_add_eq_or_of_lt (by simpa using hlow), Nat.shiftLeft_eq]
  omega

theorem getU64TrimmedLEAux_ok {len : Nat} (hlen : len ≤ 8) {s s' : Ixon.GetState}
    {x : UInt64} (h : Ixon.getU64TrimmedLEAux len s = .ok x s') :
    Consumed s s' (trimmedBytes x len) ∧ x.toNat < 2 ^ (8 * len) := by
  induction len generalizing s s' x with
  | zero =>
    obtain ⟨rfl, rfl⟩ := pure_ok_inv h
    exact ⟨Consumed.empty _, by simp⟩
  | succ len ih =>
    obtain ⟨low, s1, hlow, h⟩ := bind_ok_inv h
    obtain ⟨high, s2, hhigh, h⟩ := bind_ok_inv h
    obtain ⟨rfl, rfl⟩ := pure_ok_inv h
    obtain ⟨hc1, -⟩ := getU8_ok hlow
    obtain ⟨hc2, hlt⟩ := ih (by omega) hhigh
    have hlt' : high.toNat < 2 ^ 56 :=
      Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega))
    have hx := or_shift_toNat low high hlt'
    have hlowNat := low.toNat_lt
    have hbyte : (low.toUInt64 ||| high <<< 8).toUInt8 = low := by
      rw [← UInt8.toNat_inj, UInt64.toNat_toUInt8, hx]
      omega
    have hshift : (low.toUInt64 ||| high <<< 8) >>> 8 = high := by
      rw [← UInt64.toNat_inj, UInt64.toNat_shiftRight, hx]
      simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
      omega
    refine ⟨?_, ?_⟩
    · simp only [trimmedBytes, hbyte, hshift]
      exact hc1.trans hc2
    · have hp : 2 ^ (8 * (len + 1)) = 2 ^ (8 * len) * 256 := by
        rw [Nat.mul_succ, Nat.pow_add]
      rw [hx, hp]
      omega

theorem tagNHeader_split (f : Nat) (hf : f = 0 ∨ f = 2 ∨ f = 4) (b : UInt8) :
    Ixon.tagNHeader f (b.toNat / 2 ^ (8 - f)).toUInt8 (b.toNat % 2 ^ (8 - f)) = b ∧
      (b.toNat / 2 ^ (8 - f)).toUInt8.toNat < 2 ^ f := by
  have key : ∀ n : Nat, (n.toUInt8).toNat = n % 256 := fun n => by simp
  have hb := b.toNat_lt
  refine ⟨?_, ?_⟩
  · unfold Ixon.tagNHeader
    rw [← UInt8.toNat_inj, key, key]
    rcases hf with rfl | rfl | rfl <;>
      simp only [Nat.reduceSub, Nat.reducePow] at hb ⊢ <;> omega
  · rw [key]
    rcases hf with rfl | rfl | rfl <;>
      simp only [Nat.reduceSub, Nat.reducePow] at hb ⊢ <;> omega

theorem toUInt64_toNat_of_lt {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

/-- Every successful `getTagN` read consumed exactly the encoding of the value
it returned, and the decoded flag fits in `f` bits. -/
theorem getTagN_consumed (f : Nat) (hf : f = 0 ∨ f = 2 ∨ f = 4)
    {s s' : Ixon.GetState} {t : Ixon.TagN} (h : Ixon.getTagN f s = .ok t s') :
    Consumed s s' (tagNBytes f t.flag t.value) ∧ t.flag.toNat < 2 ^ f := by
  obtain ⟨hR, hlead, hmbit, hE1, hE2, hE3, hE4, hE5, hE5lt⟩ := tagN_consts f hf
  unfold Ixon.getTagN at h
  obtain ⟨b, s1, hb, h⟩ := bind_ok_inv h
  obtain ⟨hc1, -⟩ := getU8_ok hb
  obtain ⟨hhdr, hflag⟩ := tagNHeader_split f hf b
  have hpR : b.toNat % 2 ^ (8 - f) < 2 ^ (8 - f) :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  simp only at h
  generalize b.toNat % 2 ^ (8 - f) = p at h hhdr hpR
  generalize (b.toNat / 2 ^ (8 - f)).toUInt8 = flag at h hhdr hflag
  by_cases h1 : p < 2 ^ (8 - f - 1)
  · rw [ite_eq_left h1] at h
    obtain ⟨rfl, rfl⟩ := pure_ok_inv h
    have hv : p.toUInt64.toNat = p := toUInt64_toNat_of_lt (by omega)
    refine ⟨?_, hflag⟩
    have henc : tagNBytes f flag p.toUInt64 = [b].toByteArray ++ ByteArray.empty := by
      unfold tagNBytes
      simp only
      rw [hv, ite_eq_left (by omega), hhdr, ByteArray.append_empty]
    rw [henc]
    exact hc1.trans (Consumed.empty _)
  rw [ite_eq_right h1] at h
  by_cases h2 : p - 2 ^ (8 - f - 1) < 2 ^ (8 - f - 2)
  · rw [ite_eq_left h2] at h
    obtain ⟨lo, s2, hlo, h⟩ := bind_ok_inv h
    obtain ⟨rfl, rfl⟩ := pure_ok_inv h
    obtain ⟨hc2, -⟩ := getU8_ok hlo
    have hlo' := lo.toNat_lt
    have hv := toUInt64_toNat_of_lt (n := Ixon.tagNEnd1 f +
      (p - 2 ^ (8 - f - 1)) * 256 + lo.toNat) (by omega)
    refine ⟨?_, hflag⟩
    have henc : tagNBytes f flag (Ixon.tagNEnd1 f + (p - 2 ^ (8 - f - 1)) * 256 +
        lo.toNat).toUInt64 = [b].toByteArray ++ [lo].toByteArray := by
      unfold tagNBytes
      simp only
      rw [hv, ite_eq_right (by omega), ite_eq_left (by omega)]
      have e1 : 2 ^ (8 - f - 1) + (Ixon.tagNEnd1 f + (p - 2 ^ (8 - f - 1)) * 256 +
          lo.toNat - Ixon.tagNEnd1 f) / 256 = p := by omega
      have e2 : ((Ixon.tagNEnd1 f + (p - 2 ^ (8 - f - 1)) * 256 + lo.toNat -
          Ixon.tagNEnd1 f) % 256).toUInt8 = lo := by
        rw [← UInt8.toNat_inj]
        simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat']
        omega
      rw [e1, e2, hhdr]
    rw [henc]
    exact hc1.trans hc2
  rw [ite_eq_right h2] at h
  unfold Ixon.getTagNWide at h
  by_cases h3 : p - 2 ^ (8 - f - 1) - 2 ^ (8 - f - 2) = 0
  · rw [ite_eq_left h3] at h
    obtain ⟨x, s2, hx, h⟩ := bind_ok_inv h
    obtain ⟨rfl, rfl⟩ := pure_ok_inv h
    obtain ⟨hc2, hxlt⟩ := getU64TrimmedLEAux_ok (by omega) hx
    simp only [Nat.reduceMul, Nat.reducePow] at hxlt
    have hv := toUInt64_toNat_of_lt (n := Ixon.tagNEnd2 f + x.toNat) (by omega)
    refine ⟨?_, hflag⟩
    have henc : tagNBytes f flag (Ixon.tagNEnd2 f + x.toNat).toUInt64 =
        [b].toByteArray ++ trimmedBytes x 2 := by
      unfold tagNBytes
      simp only
      rw [hv, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
        show 2 ^ (8 - f - 1) + 2 ^ (8 - f - 2) = p by omega, hhdr,
        show Ixon.tagNEnd2 f + x.toNat - Ixon.tagNEnd2 f = x.toNat by omega]
      simp
    rw [henc]
    exact hc1.trans hc2
  rw [ite_eq_right h3] at h
  by_cases h4 : p - 2 ^ (8 - f - 1) - 2 ^ (8 - f - 2) = 1
  · rw [ite_eq_left h4] at h
    obtain ⟨x, s2, hx, h⟩ := bind_ok_inv h
    obtain ⟨rfl, rfl⟩ := pure_ok_inv h
    obtain ⟨hc2, hxlt⟩ := getU64TrimmedLEAux_ok (by omega) hx
    simp only [Nat.reduceMul, Nat.reducePow] at hxlt
    have hv := toUInt64_toNat_of_lt (n := Ixon.tagNEnd3 f + x.toNat) (by omega)
    refine ⟨?_, hflag⟩
    have henc : tagNBytes f flag (Ixon.tagNEnd3 f + x.toNat).toUInt64 =
        [b].toByteArray ++ trimmedBytes x 3 := by
      unfold tagNBytes
      simp only
      rw [hv, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
        show 2 ^ (8 - f - 1) + 2 ^ (8 - f - 2) + 1 = p by omega, hhdr,
        show Ixon.tagNEnd3 f + x.toNat - Ixon.tagNEnd3 f = x.toNat by omega]
      simp
    rw [henc]
    exact hc1.trans hc2
  rw [ite_eq_right h4] at h
  by_cases h5 : p - 2 ^ (8 - f - 1) - 2 ^ (8 - f - 2) = 2
  · rw [ite_eq_left h5] at h
    obtain ⟨x, s2, hx, h⟩ := bind_ok_inv h
    obtain ⟨rfl, rfl⟩ := pure_ok_inv h
    obtain ⟨hc2, hxlt⟩ := getU64TrimmedLEAux_ok (by omega) hx
    simp only [Nat.reduceMul, Nat.reducePow] at hxlt
    have hv := toUInt64_toNat_of_lt (n := Ixon.tagNEnd4 f + x.toNat) (by omega)
    refine ⟨?_, hflag⟩
    have henc : tagNBytes f flag (Ixon.tagNEnd4 f + x.toNat).toUInt64 =
        [b].toByteArray ++ trimmedBytes x 4 := by
      unfold tagNBytes
      simp only
      rw [hv, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_left (by omega),
        show 2 ^ (8 - f - 1) + 2 ^ (8 - f - 2) + 2 = p by omega, hhdr,
        show Ixon.tagNEnd4 f + x.toNat - Ixon.tagNEnd4 f = x.toNat by omega]
      simp
    rw [henc]
    exact hc1.trans hc2
  rw [ite_eq_right h5] at h
  by_cases h6 : p - 2 ^ (8 - f - 1) - 2 ^ (8 - f - 2) = 3
  · rw [ite_eq_left h6] at h
    obtain ⟨x, s2, hx, h⟩ := bind_ok_inv h
    obtain ⟨hc2, hxlt⟩ := getU64TrimmedLEAux_ok (by omega) hx
    by_cases hov : Ixon.tagNEnd5 f + x.toNat < 2 ^ 64
    · rw [ite_eq_left hov] at h
      obtain ⟨rfl, rfl⟩ := pure_ok_inv h
      have hv := toUInt64_toNat_of_lt hov
      refine ⟨?_, hflag⟩
      have henc : tagNBytes f flag (Ixon.tagNEnd5 f + x.toNat).toUInt64 =
          [b].toByteArray ++ trimmedBytes x 8 := by
        unfold tagNBytes
        simp only
        rw [hv, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega),
          show 2 ^ (8 - f - 1) + 2 ^ (8 - f - 2) + 3 = p by omega, hhdr,
          show Ixon.tagNEnd5 f + x.toNat - Ixon.tagNEnd5 f = x.toNat by omega]
        simp
      rw [henc]
      exact hc1.trans hc2
    · rw [ite_eq_right hov] at h
      exact (throw_ok_false h).elim
  rw [ite_eq_right h6] at h
  exact (throw_ok_false h).elim

/-- Every byte string accepted by the full-buffer TagN decoder is the
encoding of the value it decodes to (canonicity). -/
theorem runGetExact_getTagN_eq (f : Nat) (hf : f = 0 ∨ f = 2 ∨ f = 4)
    {bytes : ByteArray} {t : Ixon.TagN}
    (h : Ixon.runGetExact (Ixon.getTagN f) bytes = .ok t) :
    bytes = Ixon.runPut (Ixon.putTagN f t.flag t.value) ∧ t.flag.toNat < 2 ^ f := by
  rw [runPut_putTagN]
  unfold Ixon.runGetExact at h
  split at h
  · rename_i a state hrun
    split at h
    · rename_i hidx
      cases h
      obtain ⟨⟨hs, hx⟩, hflag⟩ := getTagN_consumed f hf hrun
      refine ⟨?_, hflag⟩
      subst hs
      simp only [Nat.zero_add] at hidx hx
      rw [← hx, hidx, ByteArray.extract_zero_size]
    · cases h
  · cases h

/-- The full-buffer TagN decoder accepts exactly the encodings of in-range
flags and `UInt64` values: decoding is a bijection between accepted byte
strings and `{t | t.flag < 2^f}`. -/
theorem runGetExact_getTagN_iff (f : Nat) (hf : f = 0 ∨ f = 2 ∨ f = 4)
    (bytes : ByteArray) (t : Ixon.TagN) :
    Ixon.runGetExact (Ixon.getTagN f) bytes = .ok t ↔
      t.flag.toNat < 2 ^ f ∧ bytes = Ixon.runPut (Ixon.putTagN f t.flag t.value) := by
  constructor
  · intro h
    obtain ⟨hb, hflag⟩ := runGetExact_getTagN_eq f hf h
    exact ⟨hflag, hb⟩
  · rintro ⟨hflag, rfl⟩
    exact runGetExact_getTagN_putTagN f hf t.flag hflag t.value

/-- Decoding is injective on accepted byte strings: no two distinct byte
strings decode to the same flag and value. -/
theorem runGetExact_getTagN_inj (f : Nat) (hf : f = 0 ∨ f = 2 ∨ f = 4)
    {bytes₁ bytes₂ : ByteArray} {t : Ixon.TagN}
    (h₁ : Ixon.runGetExact (Ixon.getTagN f) bytes₁ = .ok t)
    (h₂ : Ixon.runGetExact (Ixon.getTagN f) bytes₂ = .ok t) :
    bytes₁ = bytes₂ := by
  rw [(runGetExact_getTagN_eq f hf h₁).1, (runGetExact_getTagN_eq f hf h₂).1]

/-- Distinct values (or flags) have distinct encodings. -/
theorem putTagN_inj (f : Nat) (hf : f = 0 ∨ f = 2 ∨ f = 4)
    {flag₁ flag₂ : UInt8} (hflag₁ : flag₁.toNat < 2 ^ f) (hflag₂ : flag₂.toNat < 2 ^ f)
    {value₁ value₂ : UInt64}
    (h : Ixon.runPut (Ixon.putTagN f flag₁ value₁) =
      Ixon.runPut (Ixon.putTagN f flag₂ value₂)) :
    flag₁ = flag₂ ∧ value₁ = value₂ := by
  have h₁ := runGetExact_getTagN_putTagN f hf flag₁ hflag₁ value₁
  rw [h, runGetExact_getTagN_putTagN f hf flag₂ hflag₂ value₂] at h₁
  cases h₁
  exact ⟨rfl, rfl⟩

/-! ## Rejection -/

/-- A header whose `L = M = 1` code is 4 or more is rejected, whatever
follows it. Only `f = 0` and `f = 2` have such codes (`tagN4_code_valid`). -/
theorem getTagN_rejects_code (f : Nat) (hf : f = 0 ∨ f = 2 ∨ f = 4)
    {s : Ixon.GetState}
    (hcode : 2 ^ (8 - f - 1) + 2 ^ (8 - f - 2) + 4 ≤
      (s.bytes[s.idx]!).toNat % 2 ^ (8 - f))
    (t : Ixon.TagN) (s' : Ixon.GetState) :
    Ixon.getTagN f s ≠ .ok t s' := by
  intro h
  obtain ⟨hR, hlead, hmbit, -⟩ := tagN_consts f hf
  unfold Ixon.getTagN at h
  obtain ⟨b, s1, hb, h⟩ := bind_ok_inv h
  obtain ⟨-, hbyte⟩ := getU8_ok hb
  rw [hbyte] at hcode
  simp only at h
  generalize b.toNat % 2 ^ (8 - f) = p at h hcode
  rw [ite_eq_right (by omega), ite_eq_right (by omega)] at h
  unfold Ixon.getTagNWide at h
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)] at h
  exact throw_ok_false h

/-- With a 4-bit flag every header code is valid: the `L = M = 1` code has two
bits and selects one of the 3-, 4-, 5- and 9-byte rungs. -/
theorem tagN4_code_valid (b : UInt8) :
    b.toNat % 2 ^ (8 - 4) < 2 ^ (8 - 4 - 1) + 2 ^ (8 - 4 - 2) + 4 := by
  have := Nat.mod_lt b.toNat (show 0 < 2 ^ (8 - 4) by decide)
  simp only [Nat.reduceSub, Nat.reducePow] at this ⊢
  omega

/-- A 9-byte encoding whose value would reach `2^64` is rejected. -/
theorem getTagN_rejects_overflow (f : Nat) (hf : f = 0 ∨ f = 2 ∨ f = 4)
    (flag : UInt8) (hflag : flag.toNat < 2 ^ f) (x : UInt64)
    (hx : 2 ^ 64 ≤ Ixon.tagNEnd5 f + x.toNat) (before after : ByteArray)
    (t : Ixon.TagN) (s' : Ixon.GetState) :
    Ixon.getTagN f {
      idx := before.size
      bytes := before ++
        [Ixon.tagNHeader f flag (2 ^ (8 - f - 1) + 2 ^ (8 - f - 2) + 3)].toByteArray ++
        trimmedBytes x 8 ++ after } ≠ .ok t s' := by
  intro h
  obtain ⟨hR, hlead, hmbit, -⟩ := tagN_consts f hf
  generalize hhdr : Ixon.tagNHeader f flag (2 ^ (8 - f - 1) + 2 ^ (8 - f - 2) + 3) = hdr at h
  obtain ⟨hdiv, hmod⟩ := tagNHeader_fields f hf flag hflag
    (2 ^ (8 - f - 1) + 2 ^ (8 - f - 2) + 3) (by omega)
  rw [hhdr] at hdiv hmod
  unfold Ixon.getTagN at h
  obtain ⟨b, s1, hb, h⟩ := bind_ok_inv h
  rw [show before ++ [hdr].toByteArray ++ trimmedBytes x 8 ++ after =
      before ++ [hdr].toByteArray ++ (trimmedBytes x 8 ++ after) by
    simp [ByteArray.append_assoc], getU8_reads hdr before (trimmedBytes x 8 ++ after)] at hb
  cases hb
  simp only [hdiv, hmod] at h
  rw [ite_eq_right (by omega), ite_eq_right (by omega)] at h
  unfold Ixon.getTagNWide at h
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)] at h
  obtain ⟨y, s2, hy, h⟩ := bind_ok_inv h
  have hr := getU64TrimmedLEAux_reads x 8
    (shiftBytes_eq_zero_of_lt x 8 (by simpa using x.toNat_lt))
    (before ++ [hdr].toByteArray) after
  rw [ByteArray.size_append] at hr
  rw [show before ++ [hdr].toByteArray ++ (trimmedBytes x 8 ++ after) =
      before ++ [hdr].toByteArray ++ trimmedBytes x 8 ++ after by
    simp [ByteArray.append_assoc], hr] at hy
  cases hy
  rw [ite_eq_right (by omega)] at h
  exact throw_ok_false h

end Ixon.Verify.TagN
