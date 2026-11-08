import Ix.IxVM.Refinement.TagN
import IxC.Ixon.Verify.TagN

/-! # The TagN slice: the wide rungs

The multi-byte rungs of IxVM's TagN decoders (`get_tagn_tail`'s wide branch,
`get_tagn_wide`: three, four, five and nine bytes) against IxC's
`getTagNWide`, on the generated mirrors (`Ix.IxVM.Refinement.Mirrors.TagN`),
and the refinements of `Ixon.getTagN 0`, `2` and `4` on every header. -/

namespace IxVM.Refinement.TagN

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM.Checked (F)

set_option linter.unusedSimpArgs false
/-! ## Wide rungs: `get_tagn_wide` -/

theorem fromField_two {hh : Nat} (hhh : hh < 128) (h : Heap F) :
    mapCall IxVM.Checked.source.tables "UInt8::from_field" [.field (2 * (hh : F))] h =
      some (.field (2 * (hh : F)), h) := by
  have := fromField_row (x := 2 * hh) (by omega)
  push_cast at this
  simp [mapCall, this, Constant.toValue, Value.mapAddress]

theorem fromField_one {hh : Nat} (hhh : hh < 256) (h : Heap F) :
    mapCall IxVM.Checked.source.tables "UInt8::from_field" [.field (hh : F)] h =
      some (.field (hh : F), h) := by
  simp [mapCall, fromField_row hhh, Constant.toValue, Value.mapAddress]

/-- How many bytes wide code `c` reads. -/
def wideN : Nat → Nat
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | _ => 8

/-- The value wide code `c` adds, for `h = 2^(6-f)`: the end of the previous rung. Kept folded
in statements, so that no proof compares a symbolic `h` plus a large numeral by evaluation. -/
def wideOff (hh : Nat) : Nat → Nat
  | 0 => 2 * hh + 256 * hh
  | 1 => 2 * hh + 256 * hh + 65536
  | 2 => 2 * hh + 256 * hh + 16842752
  | _ => 2 * hh + 256 * hh + 4311810048

theorem wideOff_lt {hh c : Nat} (hhv : hh = 64 ∨ hh = 16 ∨ hh = 4) :
    wideOff hh c < 4311843072 := by
  rcases hhv with rfl | rfl | rfl <;> rcases c with _ | _ | _ | c <;> simp [wideOff]

/-- The offset bytes of wide code 0. -/
theorem wideOff0_eq {hh : Nat} (hhv : hh = 64 ∨ hh = 16 ∨ hh = 4) :
    (.tuple [.field (2 * (hh : F)), .field (hh : F), .field 0, .field 0, .field 0, .field 0, .field 0,
      .field 0] : SourceValue F) = u64Value (wideOff hh 0) := by
  rcases hhv with rfl | rfl | rfl <;> norm_num [u64Value, wideOff]

/-- **`get_tagn_wide` with code 0** reads 2 bytes and adds the code's offset. -/
theorem wide0_run {hh : Nat} (hhv : hh = 64 ∨ hh = 16 ∨ hh = 4) {heap : Heap F} {bs : List UInt8}
    {stream : SourceValue F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum heap bs stream) (hlen : wideN 0 ≤ bs.length)
    (nov : leValue (bs.take (wideN 0)) + wideOff hh 0 < 18446744073709551616) :
    ∃ restPtr, Aiur.Library.Bytes.RepByteStream byteStreamEnum heap (bs.drop (wideN 0)) restPtr ∧
      ∀ k, 12 ≤ k → Mirrors.«IxonDeserialize::get_tagn_wide» k heap (.field 0) (.field (hh : F)) stream =
        some (.tuple [u64Value (leValue (bs.take (wideN 0)) + wideOff hh 0), restPtr], heap) := by
  have hhh : hh < 128 := by omega
  simp only [wideN] at hlen nov ⊢
  obtain ⟨restPtr, restRep, run⟩ := getU64le_run 2 (by norm_num) hlen rep
  refine ⟨restPtr, restRep, fun k hk => ?_⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 3 := ⟨k - 3, by omega⟩
  have hrun := run (k' + 2) (by omega)
  simp only [Nat.cast_ofNat] at hrun
  have hX : leValue (bs.take 2) < 65536 := by
    have h0 := leValue_lt (bs.take 2)
    rw [show (bs.take 2).length = 2 by simp; omega] at h0
    norm_num at h0
    exact h0
  have hoff := wideOff_lt (c := 0) hhv
  have hadd := u64Add_value (x := leValue (bs.take 2)) (y := wideOff hh 0)
    (lt_of_lt_of_le hX (by norm_num)) (lt_of_lt_of_le hoff (by norm_num)) k' heap
  rw [Nat.mod_eq_of_lt nov, Nat.div_eq_of_lt nov] at hadd
  rw [← wideOff0_eq hhv] at hadd
  simp (config := { decide := true }) [Mirrors.«IxonDeserialize::get_tagn_wide», evalBinOp,
    fromField_two hhh, fromField_one (show hh < 256 by omega), hrun, hadd,
    toField_run, Builtin.apply, evalAssertEq, Value.pointerFree]

/-- The offset bytes of wide code 1. -/
theorem wideOff1_eq {hh : Nat} (hhv : hh = 64 ∨ hh = 16 ∨ hh = 4) :
    (.tuple [.field (2 * (hh : F)), .field (hh : F), .field 1, .field 0, .field 0, .field 0, .field 0,
      .field 0] : SourceValue F) = u64Value (wideOff hh 1) := by
  rcases hhv with rfl | rfl | rfl <;> norm_num [u64Value, wideOff]

/-- **`get_tagn_wide` with code 1** reads 3 bytes and adds the code's offset. -/
theorem wide1_run {hh : Nat} (hhv : hh = 64 ∨ hh = 16 ∨ hh = 4) {heap : Heap F} {bs : List UInt8}
    {stream : SourceValue F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum heap bs stream) (hlen : wideN 1 ≤ bs.length)
    (nov : leValue (bs.take (wideN 1)) + wideOff hh 1 < 18446744073709551616) :
    ∃ restPtr, Aiur.Library.Bytes.RepByteStream byteStreamEnum heap (bs.drop (wideN 1)) restPtr ∧
      ∀ k, 12 ≤ k → Mirrors.«IxonDeserialize::get_tagn_wide» k heap (.field 1) (.field (hh : F)) stream =
        some (.tuple [u64Value (leValue (bs.take (wideN 1)) + wideOff hh 1), restPtr], heap) := by
  have hhh : hh < 128 := by omega
  simp only [wideN] at hlen nov ⊢
  obtain ⟨restPtr, restRep, run⟩ := getU64le_run 3 (by norm_num) hlen rep
  refine ⟨restPtr, restRep, fun k hk => ?_⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 3 := ⟨k - 3, by omega⟩
  have hrun := run (k' + 2) (by omega)
  simp only [Nat.cast_ofNat] at hrun
  have hX : leValue (bs.take 3) < 16777216 := by
    have h0 := leValue_lt (bs.take 3)
    rw [show (bs.take 3).length = 3 by simp; omega] at h0
    norm_num at h0
    exact h0
  have hoff := wideOff_lt (c := 1) hhv
  have hadd := u64Add_value (x := leValue (bs.take 3)) (y := wideOff hh 1)
    (lt_of_lt_of_le hX (by norm_num)) (lt_of_lt_of_le hoff (by norm_num)) k' heap
  rw [Nat.mod_eq_of_lt nov, Nat.div_eq_of_lt nov] at hadd
  rw [← wideOff1_eq hhv] at hadd
  simp (config := { decide := true }) [Mirrors.«IxonDeserialize::get_tagn_wide», evalBinOp,
    fromField_two hhh, fromField_one (show hh < 256 by omega), hrun, hadd,
    toField_run, Builtin.apply, evalAssertEq, Value.pointerFree]

/-- The offset bytes of wide code 2. -/
theorem wideOff2_eq {hh : Nat} (hhv : hh = 64 ∨ hh = 16 ∨ hh = 4) :
    (.tuple [.field (2 * (hh : F)), .field (hh : F), .field 1, .field 1, .field 0, .field 0, .field 0,
      .field 0] : SourceValue F) = u64Value (wideOff hh 2) := by
  rcases hhv with rfl | rfl | rfl <;> norm_num [u64Value, wideOff]

/-- **`get_tagn_wide` with code 2** reads 4 bytes and adds the code's offset. -/
theorem wide2_run {hh : Nat} (hhv : hh = 64 ∨ hh = 16 ∨ hh = 4) {heap : Heap F} {bs : List UInt8}
    {stream : SourceValue F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum heap bs stream) (hlen : wideN 2 ≤ bs.length)
    (nov : leValue (bs.take (wideN 2)) + wideOff hh 2 < 18446744073709551616) :
    ∃ restPtr, Aiur.Library.Bytes.RepByteStream byteStreamEnum heap (bs.drop (wideN 2)) restPtr ∧
      ∀ k, 12 ≤ k → Mirrors.«IxonDeserialize::get_tagn_wide» k heap (.field 2) (.field (hh : F)) stream =
        some (.tuple [u64Value (leValue (bs.take (wideN 2)) + wideOff hh 2), restPtr], heap) := by
  have hhh : hh < 128 := by omega
  simp only [wideN] at hlen nov ⊢
  obtain ⟨restPtr, restRep, run⟩ := getU64le_run 4 (by norm_num) hlen rep
  refine ⟨restPtr, restRep, fun k hk => ?_⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 3 := ⟨k - 3, by omega⟩
  have hrun := run (k' + 2) (by omega)
  simp only [Nat.cast_ofNat] at hrun
  have hX : leValue (bs.take 4) < 4294967296 := by
    have h0 := leValue_lt (bs.take 4)
    rw [show (bs.take 4).length = 4 by simp; omega] at h0
    norm_num at h0
    exact h0
  have hoff := wideOff_lt (c := 2) hhv
  have hadd := u64Add_value (x := leValue (bs.take 4)) (y := wideOff hh 2)
    (lt_of_lt_of_le hX (by norm_num)) (lt_of_lt_of_le hoff (by norm_num)) k' heap
  rw [Nat.mod_eq_of_lt nov, Nat.div_eq_of_lt nov] at hadd
  rw [← wideOff2_eq hhv] at hadd
  simp (config := { decide := true }) [Mirrors.«IxonDeserialize::get_tagn_wide», evalBinOp,
    fromField_two hhh, fromField_one (show hh < 256 by omega), hrun, hadd,
    toField_run, Builtin.apply, evalAssertEq, Value.pointerFree]

/-- The offset bytes of wide code 3. -/
theorem wideOff3_eq {hh : Nat} (hhv : hh = 64 ∨ hh = 16 ∨ hh = 4) :
    (.tuple [.field (2 * (hh : F)), .field (hh : F), .field 1, .field 1, .field 1, .field 0, .field 0,
      .field 0] : SourceValue F) = u64Value (wideOff hh 3) := by
  rcases hhv with rfl | rfl | rfl <;> norm_num [u64Value, wideOff]

/-- **`get_tagn_wide` with code 3** reads 8 bytes and adds the code's offset. -/
theorem wide3_run {hh : Nat} (hhv : hh = 64 ∨ hh = 16 ∨ hh = 4) {heap : Heap F} {bs : List UInt8}
    {stream : SourceValue F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum heap bs stream) (hlen : wideN 3 ≤ bs.length)
    (nov : leValue (bs.take (wideN 3)) + wideOff hh 3 < 18446744073709551616) :
    ∃ restPtr, Aiur.Library.Bytes.RepByteStream byteStreamEnum heap (bs.drop (wideN 3)) restPtr ∧
      ∀ k, 12 ≤ k → Mirrors.«IxonDeserialize::get_tagn_wide» k heap (.field 3) (.field (hh : F)) stream =
        some (.tuple [u64Value (leValue (bs.take (wideN 3)) + wideOff hh 3), restPtr], heap) := by
  have hhh : hh < 128 := by omega
  simp only [wideN] at hlen nov ⊢
  obtain ⟨restPtr, restRep, run⟩ := getU64le_run 8 (by norm_num) hlen rep
  refine ⟨restPtr, restRep, fun k hk => ?_⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 3 := ⟨k - 3, by omega⟩
  have hrun := run (k' + 2) (by omega)
  simp only [Nat.cast_ofNat] at hrun
  have hX : leValue (bs.take 8) < 18446744073709551616 := by
    have h0 := leValue_lt (bs.take 8)
    rw [show (bs.take 8).length = 8 by simp; omega] at h0
    norm_num at h0
    exact h0
  have hoff := wideOff_lt (c := 3) hhv
  have hadd := u64Add_value (x := leValue (bs.take 8)) (y := wideOff hh 3)
    (lt_of_lt_of_le hX (by norm_num)) (lt_of_lt_of_le hoff (by norm_num)) k' heap
  rw [Nat.mod_eq_of_lt nov, Nat.div_eq_of_lt nov] at hadd
  rw [← wideOff3_eq hhv] at hadd
  simp (config := { decide := true }) [Mirrors.«IxonDeserialize::get_tagn_wide», evalBinOp,
    fromField_two hhh, fromField_one (show hh < 256 by omega), hrun, hadd,
    toField_run, Builtin.apply, evalAssertEq, Value.pointerFree]

theorem natCast_ne_of_lt {a b : Nat} (ha : a < 1000) (hb : b < 1000) (hab : a ≠ b) :
    (a : F) ≠ (b : F) := fun h => hab (IxVM.Checked.natCast_inj (by omega) (by omega) h)

/-- **`get_tagn_tail(hh + c, hh, stream)` for a wide code `c < 4`**. -/
theorem tailWide_run {hh c : Nat} (hhv : hh = 64 ∨ hh = 16 ∨ hh = 4) (hc : c < 4) {heap : Heap F}
    {bs : List UInt8} {stream : SourceValue F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum heap bs stream) (hlen : wideN c ≤ bs.length)
    (nov : leValue (bs.take (wideN c)) + wideOff hh c < 18446744073709551616) :
    ∃ restPtr, Aiur.Library.Bytes.RepByteStream byteStreamEnum heap (bs.drop (wideN c)) restPtr ∧
      ∀ k, 14 ≤ k → Mirrors.«IxonDeserialize::get_tagn_tail» k heap (.field ((hh + c : Nat) : F))
          (.field (hh : F)) stream =
        some (.tuple [u64Value (leValue (bs.take (wideN c)) + wideOff hh c), restPtr], heap) := by
  have hhh : hh < 128 := by omega
  obtain rfl | rfl | rfl | rfl : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
  · obtain ⟨restPtr, restRep, run⟩ := wide0_run hhv rep hlen nov
    refine ⟨restPtr, restRep, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hlt := rawLt_run (a := hh + 0) (b := hh) (by omega) (by omega) (k' - 1) heap
    rw [show k' - 1 + 1 = k' by omega] at hlt
    simp only [Nat.add_zero, lt_irrefl, ite_false, Nat.cast_zero] at hlt
    simp (config := { decide := true }) [Mirrors.«IxonDeserialize::get_tagn_tail», hlt, evalBinOp,
      run k' (by omega)]
  · obtain ⟨restPtr, restRep, run⟩ := wide1_run hhv rep hlen nov
    refine ⟨restPtr, restRep, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hlt := rawLt_run (a := hh + 1) (b := hh) (by omega) (by omega) (k' - 1) heap
    rw [show k' - 1 + 1 = k' by omega] at hlt
    simp only [show ¬ hh + 1 < hh by omega, ite_false, Nat.cast_zero, Nat.cast_add, Nat.cast_one] at hlt
    simp (config := { decide := true }) [Mirrors.«IxonDeserialize::get_tagn_tail», hlt, evalBinOp,
      run k' (by omega)]
  · obtain ⟨restPtr, restRep, run⟩ := wide2_run hhv rep hlen nov
    refine ⟨restPtr, restRep, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hlt := rawLt_run (a := hh + 2) (b := hh) (by omega) (by omega) (k' - 1) heap
    rw [show k' - 1 + 1 = k' by omega] at hlt
    simp only [show ¬ hh + 2 < hh by omega, ite_false, Nat.cast_zero, Nat.cast_add,
      Nat.cast_ofNat] at hlt
    simp (config := { decide := true }) [Mirrors.«IxonDeserialize::get_tagn_tail», hlt, evalBinOp,
      run k' (by omega)]
  · obtain ⟨restPtr, restRep, run⟩ := wide3_run hhv rep hlen nov
    refine ⟨restPtr, restRep, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hlt := rawLt_run (a := hh + 3) (b := hh) (by omega) (by omega) (k' - 1) heap
    rw [show k' - 1 + 1 = k' by omega] at hlt
    simp only [show ¬ hh + 3 < hh by omega, ite_false, Nat.cast_zero, Nat.cast_add,
      Nat.cast_ofNat] at hlt
    simp (config := { decide := true }) [Mirrors.«IxonDeserialize::get_tagn_tail», hlt, evalBinOp,
      run k' (by omega)]

/-- **`get_u64_le` on a stream with too few bytes fails.** -/
theorem getU64le_short {heap : Heap F} : ∀ (n : Nat), n ≤ 8 → ∀ {bs : List UInt8} {stream : SourceValue F},
    bs.length < n → Aiur.Library.Bytes.RepByteStream byteStreamEnum heap bs stream →
      ∀ k, Mirrors.«IxonDeserialize::get_u64_le» k heap stream (.field (n : F)) = none
  | 0, _, _, _, hlen, _ => by simp at hlen
  | n + 1, hn, bs, stream, hlen, rep => by
    intro k
    cases k with
    | zero => rfl
    | succ k =>
      have hne := natCast_succ_ne_zero (n := n) (by omega)
      cases rep with
      | nil cell =>
        simp [Mirrors.«IxonDeserialize::get_u64_le», hne, loadValue_cell cell]
      | @cons b tl addr headVal tailPtr cell headRep tailRep =>
        simp only [Aiur.Library.RepU8] at headRep
        subst headRep
        have hrec := getU64le_short n (by omega) (bs := tl) (by simp at hlen; omega) tailRep k
        simp [Mirrors.«IxonDeserialize::get_u64_le», hne, loadValue_cell cell, node_ctor, evalBinOp,
          hrec]


/-! ## Wide rungs: IxC's reader -/

theorem getTrimmed_at {bs : List UInt8} : ∀ (n i : Nat), n ≤ 8 → i + n ≤ bs.length →
    Ixon.getU64TrimmedLEAux n { idx := i, bytes := ⟨bs.toArray⟩ } =
      .ok (leValue ((bs.drop i).take n)).toUInt64 { idx := i + n, bytes := ⟨bs.toArray⟩ }
  | 0, i, _, _ => by simp [Ixon.getU64TrimmedLEAux, leValue, pure, EStateM.pure]
  | n + 1, i, hn, hi => by
    have read := getU8_at (bytes := bs) (i := i) (by omega)
    have ih := getTrimmed_at (bs := bs) n (i + 1) (by omega) (by omega)
    have hdrop : (bs.drop i).take (n + 1) = bs[i] :: (bs.drop (i + 1)).take n := by
      rw [List.drop_eq_getElem_cons (by omega)]
      rfl
    have hlt := leValue_lt ((bs.drop (i + 1)).take n)
    rw [show ((bs.drop (i + 1)).take n).length = n by simp; omega] at hlt
    have hlt' : leValue ((bs.drop (i + 1)).take n) < 2 ^ 56 :=
      lt_of_lt_of_le hlt (le_trans (Nat.pow_le_pow_right (by norm_num) (show n ≤ 7 by omega))
        (by norm_num))
    have htoNat : (leValue ((bs.drop (i + 1)).take n)).toUInt64.toNat =
        leValue ((bs.drop (i + 1)).take n) := by
      simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt (by omega)
    have hbi := (bs[i]'(by omega)).toNat_lt
    have hv : ((bs[i]'(by omega)).toUInt64 ||| (leValue ((bs.drop (i + 1)).take n)).toUInt64 <<< 8) =
        (leValue ((bs[i]'(by omega)) :: (bs.drop (i + 1)).take n)).toUInt64 := by
      apply UInt64.toNat_inj.mp
      rw [Ixon.Verify.TagN.or_shift_toNat _ _ (by rw [htoNat]; exact hlt'), htoNat]
      simp only [leValue, Nat.toUInt64_eq, UInt64.toNat_ofNat']
      rw [Nat.mod_eq_of_lt (by omega)]
      ring
    simp only [Ixon.getU64TrimmedLEAux, bind, EStateM.bind, read, ih, pure, EStateM.pure]
    rw [hdrop, hv, show i + 1 + n = i + (n + 1) by omega]

/-- Where wide code `c` starts for an `f`-bit flag: IxC's rung ends. -/
def wideEnd (f : Nat) : Nat → Nat
  | 0 => Ixon.tagNEnd2 f
  | 1 => Ixon.tagNEnd3 f
  | 2 => Ixon.tagNEnd4 f
  | _ => Ixon.tagNEnd5 f

theorem toUInt64_toNat_small {x : Nat} (hx : x < 18446744073709551616) : x.toUInt64.toNat = x := by
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt hx

/-- **IxC's wide rungs**, after the header: code `c` reads `wideN c` bytes and adds the
rung's start. -/
theorem getTagNWide_at {f : Nat} {flag : UInt8} {c : Nat} (hc : c < 4) {b : UInt8} {tl : List UInt8}
    (hlen : wideN c ≤ tl.length)
    (nov : wideEnd f c + leValue (tl.take (wideN c)) < 18446744073709551616) :
    Ixon.getTagNWide f flag c { idx := 1, bytes := ⟨(b :: tl).toArray⟩ } =
      .ok ⟨flag, (wideEnd f c + leValue (tl.take (wideN c))).toUInt64⟩
        { idx := 1 + wideN c, bytes := ⟨(b :: tl).toArray⟩ } := by
  obtain rfl | rfl | rfl | rfl : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
  all_goals
    simp only [wideN, wideEnd] at hlen nov ⊢
  · have rd := getTrimmed_at (bs := b :: tl) 2 1 (by norm_num) (by simp; omega)
    have hX := leValue_lt (tl.take 2)
    rw [show (tl.take 2).length = 2 by simp; omega] at hX
    simp only [List.drop_one, List.tail_cons] at rd
    simp only [Ixon.getTagNWide, ↓reduceIte, bind, EStateM.bind, rd, pure, EStateM.pure]
    rw [toUInt64_toNat_small (lt_of_lt_of_le hX (by norm_num))]
  · have rd := getTrimmed_at (bs := b :: tl) 3 1 (by norm_num) (by simp; omega)
    have hX := leValue_lt (tl.take 3)
    rw [show (tl.take 3).length = 3 by simp; omega] at hX
    simp only [List.drop_one, List.tail_cons] at rd
    simp only [Ixon.getTagNWide, show (1 : Nat) ≠ 0 by decide, ite_false, ↓reduceIte, bind, EStateM.bind,
      rd, pure, EStateM.pure]
    rw [toUInt64_toNat_small (lt_of_lt_of_le hX (by norm_num))]
  · have rd := getTrimmed_at (bs := b :: tl) 4 1 (by norm_num) (by simp; omega)
    have hX := leValue_lt (tl.take 4)
    rw [show (tl.take 4).length = 4 by simp; omega] at hX
    simp only [List.drop_one, List.tail_cons] at rd
    simp only [Ixon.getTagNWide, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, ite_false,
      ↓reduceIte, bind, EStateM.bind, rd, pure, EStateM.pure]
    rw [toUInt64_toNat_small (lt_of_lt_of_le hX (by norm_num))]
  · have rd := getTrimmed_at (bs := b :: tl) 8 1 (by norm_num) (by simp; omega)
    have hX := leValue_lt (tl.take 8)
    rw [show (tl.take 8).length = 8 by simp; omega] at hX
    simp only [List.drop_one, List.tail_cons] at rd
    have hx : (leValue (tl.take 8)).toUInt64.toNat = leValue (tl.take 8) :=
      toUInt64_toNat_small (lt_of_lt_of_le hX (by norm_num))
    simp only [Ixon.getTagNWide, show (3 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 1 by decide,
      show (3 : Nat) ≠ 2 by decide, ite_false, ↓reduceIte, bind, EStateM.bind, rd, pure, EStateM.pure, hx]
    simp [nov, EStateM.pure]

/-! ## Wide rungs: what the derivation rules out -/

theorem f10 : (1 : F) ≠ 0 := one_ne_zero
theorem f20 : (2 : F) ≠ 0 := by simpa using natCast_ne_of_lt (a := 2) (b := 0) (by norm_num) (by norm_num) (by norm_num)
theorem f21 : (2 : F) ≠ 1 := by simpa using natCast_ne_of_lt (a := 2) (b := 1) (by norm_num) (by norm_num) (by norm_num)
theorem f30 : (3 : F) ≠ 0 := by simpa using natCast_ne_of_lt (a := 3) (b := 0) (by norm_num) (by norm_num) (by norm_num)
theorem f31 : (3 : F) ≠ 1 := by simpa using natCast_ne_of_lt (a := 3) (b := 1) (by norm_num) (by norm_num) (by norm_num)
theorem f32 : (3 : F) ≠ 2 := by simpa using natCast_ne_of_lt (a := 3) (b := 2) (by norm_num) (by norm_num) (by norm_num)

/-- **A code from `4` has no rung.** -/
theorem wide_none_code {hh c : Nat} (hhv : hh = 64 ∨ hh = 16 ∨ hh = 4) (hc : 4 ≤ c) (hc' : c < 200)
    {heap : Heap F} {stream : SourceValue F} (k : Nat) :
    Mirrors.«IxonDeserialize::get_tagn_wide» k heap (.field (c : F)) (.field (hh : F)) stream = none := by
  have hhh : hh < 128 := by omega
  cases k with
  | zero => rfl
  | succ k =>
    have h0 : (c : F) ≠ 0 := by
      simpa using natCast_ne_of_lt (a := c) (b := 0) (by omega) (by norm_num) (by omega)
    have h1 : (c : F) ≠ 1 := by
      simpa using natCast_ne_of_lt (a := c) (b := 1) (by omega) (by norm_num) (by omega)
    have h2 : (c : F) ≠ 2 := by
      simpa using natCast_ne_of_lt (a := c) (b := 2) (by omega) (by norm_num) (by omega)
    have h3 : (c : F) ≠ 3 := by
      simpa using natCast_ne_of_lt (a := c) (b := 3) (by omega) (by norm_num) (by omega)
    simp [Mirrors.«IxonDeserialize::get_tagn_wide», evalBinOp, fromField_two hhh,
      fromField_one (show hh < 256 by omega), h0, h1, h2, h3]

/-- **A wide rung on too few bytes fails.** -/
theorem wide_none_short {hh c : Nat} (hhv : hh = 64 ∨ hh = 16 ∨ hh = 4) (hc : c < 4) {heap : Heap F}
    {bs : List UInt8} {stream : SourceValue F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum heap bs stream) (hshort : bs.length < wideN c)
    (k : Nat) :
    Mirrors.«IxonDeserialize::get_tagn_wide» k heap (.field (c : F)) (.field (hh : F)) stream = none := by
  have hhh : hh < 128 := by omega
  cases k with
  | zero => rfl
  | succ k =>
    obtain rfl | rfl | rfl | rfl : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
    · have hs := getU64le_short 2 (by norm_num) hshort rep k
      simp only [Nat.cast_ofNat] at hs
      simp [Mirrors.«IxonDeserialize::get_tagn_wide», evalBinOp, fromField_two hhh,
        fromField_one (show hh < 256 by omega), hs]
    · have hs := getU64le_short 3 (by norm_num) hshort rep k
      simp only [Nat.cast_ofNat] at hs
      simp [Mirrors.«IxonDeserialize::get_tagn_wide», evalBinOp, fromField_two hhh,
        fromField_one (show hh < 256 by omega), hs, f10]
    · have hs := getU64le_short 4 (by norm_num) hshort rep k
      simp only [Nat.cast_ofNat] at hs
      simp [Mirrors.«IxonDeserialize::get_tagn_wide», evalBinOp, fromField_two hhh,
        fromField_one (show hh < 256 by omega), hs, f20, f21]
    · have hs := getU64le_short 8 (by norm_num) hshort rep k
      simp only [Nat.cast_ofNat] at hs
      simp [Mirrors.«IxonDeserialize::get_tagn_wide», evalBinOp, fromField_two hhh,
        fromField_one (show hh < 256 by omega), hs, f30, f31, f32]

/-- **Code `3` past `2^64` fails** its overflow assertion. -/
theorem wide3_none_overflow {hh : Nat} (hhv : hh = 64 ∨ hh = 16 ∨ hh = 4) {heap : Heap F}
    {bs : List UInt8} {stream : SourceValue F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum heap bs stream) (hlen : 8 ≤ bs.length)
    (ov : 18446744073709551616 ≤ leValue (bs.take 8) + wideOff hh 3) (k : Nat)
    (hk : 12 ≤ k) :
    Mirrors.«IxonDeserialize::get_tagn_wide» k heap (.field 3) (.field (hh : F)) stream = none := by
  have hhh : hh < 128 := by omega
  obtain ⟨restPtr, restRep, run⟩ := getU64le_run 8 (by norm_num) hlen rep
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 3 := ⟨k - 3, by omega⟩
  have hrun := run (k' + 2) (by omega)
  simp only [Nat.cast_ofNat] at hrun
  have hX : leValue (bs.take 8) < 18446744073709551616 := by
    have h0 := leValue_lt (bs.take 8)
    rw [show (bs.take 8).length = 8 by simp; omega] at h0
    simpa using h0
  have hoff := wideOff_lt (c := 3) hhv
  have hadd := u64Add_value (x := leValue (bs.take 8)) (y := wideOff hh 3) hX
    (lt_of_lt_of_le hoff (by norm_num)) k' heap
  rw [show (leValue (bs.take 8) + wideOff hh 3) / 18446744073709551616 = 1 by omega] at hadd
  rw [← wideOff3_eq hhv] at hadd
  simp [Mirrors.«IxonDeserialize::get_tagn_wide», evalBinOp, fromField_two hhh,
    fromField_one (show hh < 256 by omega), hrun, hadd, toField_run, Builtin.apply,
    evalAssertEq, Value.pointerFree, f30, f31, f32, f10]

/-- **`get_tagn_tail(hh + c, hh, stream)` fails** when the wide rung does. -/
theorem tailWide_none {hh c : Nat} (hhv : hh = 64 ∨ hh = 16 ∨ hh = 4) (hc : c < 128) {heap : Heap F}
    {stream : SourceValue F}
    (hnone : ∀ k, 12 ≤ k → Mirrors.«IxonDeserialize::get_tagn_wide» k heap (.field (c : F))
      (.field (hh : F)) stream = none) (k : Nat) (hk : 14 ≤ k) :
    Mirrors.«IxonDeserialize::get_tagn_tail» k heap (.field ((hh : F) + (c : F))) (.field (hh : F))
      stream = none := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hlt := rawLt_run (a := hh + c) (b := hh) (by omega) (by omega) (k' - 1) heap
  rw [show k' - 1 + 1 = k' by omega] at hlt
  simp only [show ¬ hh + c < hh by omega, ite_false, Nat.cast_zero] at hlt
  push_cast at hlt
  simp [Mirrors.«IxonDeserialize::get_tagn_tail», hlt, evalBinOp, hnone k' (by omega), f10]

/-! ## Every header: `getTagN 0` -/

theorem leValue_take_lt {l : List UInt8} {n : Nat} (h : n ≤ l.length) : leValue (l.take n) < 256 ^ n := by
  have := leValue_lt (l.take n)
  rwa [show (l.take n).length = n by simp; omega] at this

/-- **IxC's `getTagN 0` on a wide header** `192 + c`. -/
theorem getTagN0_wide {b : UInt8} {rest : List UInt8} {c : Nat} (hbc : b.toNat = 192 + c)
    (hc4 : c < 4) (hlen : wideN c ≤ rest.length)
    (nov : wideEnd 0 c + leValue (rest.take (wideN c)) < 18446744073709551616) :
    Ixon.getTagN 0 (start (b :: rest)) =
      .ok ⟨0, (wideEnd 0 c + leValue (rest.take (wideN c))).toUInt64⟩
        { idx := 1 + wideN c, bytes := ⟨(b :: rest).toArray⟩ } := by
  have read := getU8_at (bytes := b :: rest) (i := 0) (by simp)
  have hb := b.toNat_lt
  have wide := getTagNWide_at (f := 0) (flag := 0) hc4 (b := b) hlen nov
  simp only [start, Ixon.getTagN, bind, EStateM.bind, read]
  simp [show ¬ b.toNat < 128 by omega, show ¬ b.toNat - 128 < 64 by omega,
    Nat.mod_eq_of_lt (show b.toNat < 256 from hb), Nat.div_eq_of_lt (show b.toNat < 256 from hb),
    show b.toNat - 128 - 64 = c by omega, show b.toNat - 192 = c by omega, wide]

theorem wideEnd0 {c : Nat} (hc : c < 4) : wideEnd 0 c = wideOff 64 c := by
  obtain rfl | rfl | rfl | rfl : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
  all_goals rfl

set_option maxHeartbeats 4000000 in
/-- **IxVM's `get_tagn0` refines IxC's `Ixon.getTagN 0` on every header**: every
derivation of `IxonDeserialize::get_tagn0` on a stream of `bytes` is matched by IxC's
reader on the same bytes: it succeeds with flag `0` and the value the derivation
returns as eight little-endian bytes, and the derivation's rest pointer holds the bytes
IxC's reader did not consume. The heap is unchanged. -/
theorem getTagN0_refines {stream r : SourceValue F} {heap h' : Heap F} {bytes : List UInt8}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum heap bytes stream)
    (ev : EvalFn W "IxonDeserialize::get_tagn0" [stream] heap r h') :
    h' = heap ∧ ∃ (t : Ixon.TagN) (n : Nat) (restPtr : SourceValue F),
      Ixon.getTagN 0 (start bytes) = .ok t { idx := n, bytes := ⟨bytes.toArray⟩ } ∧ t.flag = 0 ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum heap (bytes.drop n) restPtr ∧
      r = .tuple [u64Value t.value.toNat, restPtr] := by
  cases rep with
  | nil cell =>
    exact getTagN0_refines_short (.nil cell) (by simp) ev
  | @cons b rest addr headVal tailPtr cell headRep tailRep =>
    by_cases narrow : b.toNat < 192
    · exact getTagN0_refines_short (.cons cell headRep tailRep) (by simpa using narrow) ev
    obtain ⟨k0, hk0⟩ := Mirrors.«IxonDeserialize::get_tagn0».of_eval getU64le_complete ev
    have run := hk0 (k0 + 20) (by omega)
    simp only [Aiur.Library.RepU8] at headRep
    subst headRep
    have hb := b.toNat_lt
    obtain ⟨c, hbc⟩ : ∃ c, b.toNat = 192 + c := ⟨b.toNat - 192, by omega⟩
    have hlt : Mirrors.«UInt8::less_than» (k0 + 19) heap (.field (b.toNat : F)) (.field 128) =
        some (.field 0, heap) := by
      have := lessThan_run (a := b.toNat) (b := 128) hb (by norm_num) (k0 + 17) heap
      simpa [show ¬ b.toNat < 128 by omega] using this
    have hq : (b.toNat : F) - 128 = (64 : F) + (c : F) := by
      rw [hbc]
      push_cast
      ring
    have hrun : Mirrors.«IxonDeserialize::get_tagn_tail» (k0 + 19) heap (.field ((64 : F) + (c : F)))
        (.field 64) tailPtr = some (r, h') := by
      simpa [Mirrors.«IxonDeserialize::get_tagn0», loadValue_cell cell, node_ctor, hlt, toField_run,
        evalBinOp, hq] using run
    have tailNone : (∀ k, 12 ≤ k → Mirrors.«IxonDeserialize::get_tagn_wide» k heap (.field (c : F))
        (.field ((64 : Nat) : F)) tailPtr = none) → False := by
      intro hnone
      have := tailWide_none (hh := 64) (c := c) (by norm_num) (by omega) hnone (k0 + 19) (by omega)
      simp only [Nat.cast_ofNat] at this
      rw [this] at hrun
      cases hrun
    by_cases hc4 : c < 4
    · by_cases hlen : wideN c ≤ rest.length
      · by_cases nov : leValue (rest.take (wideN c)) + wideOff 64 c < 18446744073709551616
        · obtain ⟨restPtr, restRep, trun⟩ :=
            tailWide_run (hh := 64) (c := c) (by norm_num) hc4 tailRep hlen nov
          have htail := trun (k0 + 19) (by omega)
          push_cast at htail
          rw [htail] at hrun
          simp only [Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl⟩ := hrun
          have hend := wideEnd0 hc4
          refine ⟨rfl, _, 1 + wideN c, restPtr,
            getTagN0_wide hbc hc4 hlen (by rw [hend]; omega), rfl,
            by rw [Nat.add_comm, List.drop_succ_cons]; exact restRep, ?_⟩
          rw [toUInt64_toNat_small (by rw [hend]; omega), hend, Nat.add_comm (wideOff 64 c)]
        · obtain rfl | rfl | rfl | rfl : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
          · exfalso; apply nov
            have := leValue_take_lt hlen
            simp only [wideOff, wideN] at this ⊢
            norm_num at this ⊢
            omega
          · exfalso; apply nov
            have := leValue_take_lt hlen
            simp only [wideOff, wideN] at this ⊢
            norm_num at this ⊢
            omega
          · exfalso; apply nov
            have := leValue_take_lt hlen
            simp only [wideOff, wideN] at this ⊢
            norm_num at this ⊢
            omega
          · exact (tailNone fun k hk => by
              exact wide3_none_overflow (hh := 64) (by norm_num) tailRep hlen (by simpa [wideN] using not_lt.mp nov) k hk).elim
      · exact (tailNone fun k _ => by
          exact wide_none_short (hh := 64) (by norm_num) hc4 tailRep (by omega) k).elim
    · exact (tailNone fun k _ => by
        exact wide_none_code (hh := 64) (by norm_num) (by omega) (by omega) k).elim

/-! ## Every header: `getTagN 4` -/

/-- **IxC's `getTagN 4` on a wide header**: low bits `12 + c`. -/
theorem getTagN4_wide {b : UInt8} {rest : List UInt8} {c : Nat} (hbc : b.toNat % 16 = 12 + c)
    (hc4 : c < 4) (hlen : wideN c ≤ rest.length)
    (nov : wideEnd 4 c + leValue (rest.take (wideN c)) < 18446744073709551616) :
    Ixon.getTagN 4 (start (b :: rest)) =
      .ok ⟨(b.toNat / 16).toUInt8, (wideEnd 4 c + leValue (rest.take (wideN c))).toUInt64⟩
        { idx := 1 + wideN c, bytes := ⟨(b :: rest).toArray⟩ } := by
  have read := getU8_at (bytes := b :: rest) (i := 0) (by simp)
  have wide := getTagNWide_at (f := 4) (flag := (b.toNat / 16).toUInt8) hc4 (b := b) hlen nov
  simp only [start, Ixon.getTagN, bind, EStateM.bind, read]
  simp [show ¬ b.toNat % 16 < 8 by omega, show ¬ b.toNat % 16 - 8 < 4 by omega,
    show b.toNat % 16 - 8 - 4 = c by omega, show b.toNat % 16 - 12 = c by omega, wide]

theorem wideEnd4 {c : Nat} (hc : c < 4) : wideEnd 4 c = wideOff 4 c := by
  obtain rfl | rfl | rfl | rfl : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
  all_goals rfl

set_option maxHeartbeats 4000000 in
/-- **IxVM's `get_tagn4` refines IxC's `Ixon.getTagN 4` on every header**: every
derivation agrees with IxC's reader on the same bytes: the flag, the value as eight
little-endian bytes, the rest pointer at IxC's position, the heap unchanged. -/
theorem getTagN4_refines {stream r : SourceValue F} {heap h' : Heap F} {bytes : List UInt8}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum heap bytes stream)
    (ev : EvalFn W "IxonDeserialize::get_tagn4" [stream] heap r h') :
    h' = heap ∧ ∃ (t : Ixon.TagN) (n : Nat) (restPtr : SourceValue F),
      Ixon.getTagN 4 (start bytes) = .ok t { idx := n, bytes := ⟨bytes.toArray⟩ } ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum heap (bytes.drop n) restPtr ∧
      r = .tuple [.tuple [.field (t.flag.toNat : F), u64Value t.value.toNat], restPtr] := by
  cases rep with
  | nil cell =>
    exact getTagN4_refines_short (.nil cell) (by simp) ev
  | @cons b rest addr headVal tailPtr cell headRep tailRep =>
    by_cases narrow : b.toNat % 16 < 12
    · exact getTagN4_refines_short (.cons cell headRep tailRep) (by simpa using narrow) ev
    obtain ⟨k0, hk0⟩ := Mirrors.«IxonDeserialize::get_tagn4».of_eval getU64le_complete ev
    have run := hk0 (k0 + 20) (by omega)
    simp only [Aiur.Library.RepU8] at headRep
    subst headRep
    have hb := b.toNat_lt
    obtain ⟨c, hbc⟩ : ∃ c, b.toNat % 16 = 12 + c := ⟨b.toNat % 16 - 12, by omega⟩
    have hbits := bitDecomp_run hb (k0 + 18) heap
    have hbit : b.toNat / 8 % 2 = 1 := by omega
    have hlow : ((b.toNat % 2 : Nat) : F) + 2 * ((b.toNat / 2 % 2 : Nat) : F) + 4 * ((b.toNat / 4 % 2 : Nat) : F) = (4 : F) + (c : F) := by
      rw [bits_low]
      rw [show b.toNat % 8 = 4 + c by omega]
      push_cast
      ring
    have hflag : (b.toNat / 16).toUInt8.toNat = b.toNat / 16 := by
      simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat']
      exact Nat.mod_eq_of_lt (by omega)
    have tailNone : (∀ k, 12 ≤ k → Mirrors.«IxonDeserialize::get_tagn_wide» k heap (.field (c : F))
        (.field ((4 : Nat) : F)) tailPtr = none) → False := by
      intro hnone
      have := tailWide_none (hh := 4) (c := c) (by norm_num) (by omega) hnone (k0 + 19) (by omega)
      simp only [Nat.cast_ofNat] at this
      simp (config := { decide := true }) [Mirrors.«IxonDeserialize::get_tagn4», loadValue_cell cell,
        node_ctor, hbits, evalBinOp, bits_high hb, hbit, hlow, this] at run
    by_cases hc4 : c < 4
    · by_cases hlen : wideN c ≤ rest.length
      · by_cases nov : leValue (rest.take (wideN c)) + wideOff 4 c < 18446744073709551616
        · obtain ⟨restPtr, restRep, trun⟩ :=
            tailWide_run (hh := 4) (c := c) (by norm_num) hc4 tailRep hlen nov
          have htail := trun (k0 + 19) (by omega)
          push_cast at htail
          simp (config := { decide := true }) [Mirrors.«IxonDeserialize::get_tagn4», loadValue_cell cell,
            node_ctor, hbits, evalBinOp, bits_high hb, hbit, hlow, htail] at run
          obtain ⟨rfl, rfl⟩ := run
          have hend := wideEnd4 hc4
          refine ⟨rfl, _, 1 + wideN c, restPtr,
            getTagN4_wide hbc hc4 hlen (by rw [hend]; omega),
            by rw [Nat.add_comm, List.drop_succ_cons]; exact restRep, ?_⟩
          rw [hflag, toUInt64_toNat_small (by rw [hend]; omega), hend, Nat.add_comm (wideOff 4 c)]
        · obtain rfl | rfl | rfl | rfl : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
          · exfalso; apply nov
            have := leValue_take_lt hlen
            simp only [wideOff, wideN] at this ⊢
            norm_num at this ⊢
            omega
          · exfalso; apply nov
            have := leValue_take_lt hlen
            simp only [wideOff, wideN] at this ⊢
            norm_num at this ⊢
            omega
          · exfalso; apply nov
            have := leValue_take_lt hlen
            simp only [wideOff, wideN] at this ⊢
            norm_num at this ⊢
            omega
          · exact (tailNone fun k hk => by
              exact wide3_none_overflow (hh := 4) (by norm_num) tailRep hlen
                (by simpa [wideN] using not_lt.mp nov) k hk).elim
      · exact (tailNone fun k _ => by
          exact wide_none_short (hh := 4) (by norm_num) hc4 tailRep (by omega) k).elim
    · exact (tailNone fun k _ => by
        exact wide_none_code (hh := 4) (by norm_num) (by omega) (by omega) k).elim

/-! ## Every header: `getTagN 2` -/

/-- **IxC's `getTagN 2` on a wide header**: low bits `48 + c`. -/
theorem getTagN2_wide {b : UInt8} {rest : List UInt8} {c : Nat} (hbc : b.toNat % 64 = 48 + c)
    (hc4 : c < 4) (hlen : wideN c ≤ rest.length)
    (nov : wideEnd 2 c + leValue (rest.take (wideN c)) < 18446744073709551616) :
    Ixon.getTagN 2 (start (b :: rest)) =
      .ok ⟨(b.toNat / 64).toUInt8, (wideEnd 2 c + leValue (rest.take (wideN c))).toUInt64⟩
        { idx := 1 + wideN c, bytes := ⟨(b :: rest).toArray⟩ } := by
  have read := getU8_at (bytes := b :: rest) (i := 0) (by simp)
  have wide := getTagNWide_at (f := 2) (flag := (b.toNat / 64).toUInt8) hc4 (b := b) hlen nov
  simp only [start, Ixon.getTagN, bind, EStateM.bind, read]
  simp [show ¬ b.toNat % 64 < 32 by omega, show ¬ b.toNat % 64 - 32 < 16 by omega,
    show b.toNat % 64 - 32 - 16 = c by omega, show b.toNat % 64 - 48 = c by omega, wide]

theorem wideEnd2 {c : Nat} (hc : c < 4) : wideEnd 2 c = wideOff 16 c := by
  obtain rfl | rfl | rfl | rfl : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
  all_goals rfl

set_option maxHeartbeats 4000000 in
/-- **IxVM's `get_tagn2` refines IxC's `Ixon.getTagN 2` on every header**: every
derivation agrees with IxC's reader on the same bytes: the flag, the value as eight
little-endian bytes, the rest pointer at IxC's position, the heap unchanged. -/
theorem getTagN2_refines {stream r : SourceValue F} {heap h' : Heap F} {bytes : List UInt8}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum heap bytes stream)
    (ev : EvalFn W "IxonDeserialize::get_tagn2" [stream] heap r h') :
    h' = heap ∧ ∃ (t : Ixon.TagN) (n : Nat) (restPtr : SourceValue F),
      Ixon.getTagN 2 (start bytes) = .ok t { idx := n, bytes := ⟨bytes.toArray⟩ } ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum heap (bytes.drop n) restPtr ∧
      r = .tuple [.tuple [.field (t.flag.toNat : F), u64Value t.value.toNat], restPtr] := by
  cases rep with
  | nil cell =>
    exact getTagN2_refines_short (.nil cell) (by simp) ev
  | @cons b rest addr headVal tailPtr cell headRep tailRep =>
    by_cases narrow : b.toNat % 64 < 48
    · exact getTagN2_refines_short (.cons cell headRep tailRep) (by simpa using narrow) ev
    obtain ⟨k0, hk0⟩ := Mirrors.«IxonDeserialize::get_tagn2».of_eval getU64le_complete ev
    have run := hk0 (k0 + 20) (by omega)
    simp only [Aiur.Library.RepU8] at headRep
    subst headRep
    have hb := b.toNat_lt
    obtain ⟨c, hbc⟩ : ∃ c, b.toNat % 64 = 48 + c := ⟨b.toNat % 64 - 48, by omega⟩
    have hbits := bitDecomp_run hb (k0 + 18) heap
    have hbit : b.toNat / 32 % 2 = 1 := by omega
    have hlow : ((b.toNat % 2 : Nat) : F) + 2 * ((b.toNat / 2 % 2 : Nat) : F) + 4 * ((b.toNat / 4 % 2 : Nat) : F) + 8 * ((b.toNat / 8 % 2 : Nat) : F) + 16 * ((b.toNat / 16 % 2 : Nat) : F) = (16 : F) + (c : F) := by
      rw [bits_low5]
      rw [show b.toNat % 32 = 16 + c by omega]
      push_cast
      ring
    have hflag : (b.toNat / 64).toUInt8.toNat = b.toNat / 64 := by
      simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat']
      exact Nat.mod_eq_of_lt (by omega)
    have tailNone : (∀ k, 12 ≤ k → Mirrors.«IxonDeserialize::get_tagn_wide» k heap (.field (c : F))
        (.field ((16 : Nat) : F)) tailPtr = none) → False := by
      intro hnone
      have := tailWide_none (hh := 16) (c := c) (by norm_num) (by omega) hnone (k0 + 19) (by omega)
      simp only [Nat.cast_ofNat] at this
      simp (config := { decide := true }) [Mirrors.«IxonDeserialize::get_tagn2», loadValue_cell cell,
        node_ctor, hbits, evalBinOp, bits_high2 hb, hbit, hlow, this] at run
    by_cases hc4 : c < 4
    · by_cases hlen : wideN c ≤ rest.length
      · by_cases nov : leValue (rest.take (wideN c)) + wideOff 16 c < 18446744073709551616
        · obtain ⟨restPtr, restRep, trun⟩ :=
            tailWide_run (hh := 16) (c := c) (by norm_num) hc4 tailRep hlen nov
          have htail := trun (k0 + 19) (by omega)
          push_cast at htail
          simp (config := { decide := true }) [Mirrors.«IxonDeserialize::get_tagn2», loadValue_cell cell,
            node_ctor, hbits, evalBinOp, bits_high2 hb, hbit, hlow, htail] at run
          obtain ⟨rfl, rfl⟩ := run
          have hend := wideEnd2 hc4
          refine ⟨rfl, _, 1 + wideN c, restPtr,
            getTagN2_wide hbc hc4 hlen (by rw [hend]; omega),
            by rw [Nat.add_comm, List.drop_succ_cons]; exact restRep, ?_⟩
          rw [hflag, toUInt64_toNat_small (by rw [hend]; omega), hend, Nat.add_comm (wideOff 16 c)]
        · obtain rfl | rfl | rfl | rfl : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
          · exfalso; apply nov
            have := leValue_take_lt hlen
            simp only [wideOff, wideN] at this ⊢
            norm_num at this ⊢
            omega
          · exfalso; apply nov
            have := leValue_take_lt hlen
            simp only [wideOff, wideN] at this ⊢
            norm_num at this ⊢
            omega
          · exfalso; apply nov
            have := leValue_take_lt hlen
            simp only [wideOff, wideN] at this ⊢
            norm_num at this ⊢
            omega
          · exact (tailNone fun k hk => by
              exact wide3_none_overflow (hh := 16) (by norm_num) tailRep hlen
                (by simpa [wideN] using not_lt.mp nov) k hk).elim
      · exact (tailNone fun k _ => by
          exact wide_none_short (hh := 16) (by norm_num) hc4 tailRep (by omega) k).elim
    · exact (tailNone fun k _ => by
        exact wide_none_code (hh := 16) (by norm_num) (by omega) (by omega) k).elim

/-! ## Arbitrary reader offsets -/

theorem getU8_drop {bytes : List UInt8} {i j : Nat} {b : UInt8} {s' : Ixon.GetState}
    (h : Ixon.getU8 { idx := j, bytes := ⟨(bytes.drop i).toArray⟩ } = .ok b s') :
    s' = { idx := j + 1, bytes := ⟨(bytes.drop i).toArray⟩ } ∧
      Ixon.getU8 { idx := i + j, bytes := ⟨bytes.toArray⟩ } =
        .ok b { idx := i + (j + 1), bytes := ⟨bytes.toArray⟩ } := by
  have hj : j < (bytes.drop i).length := by
    unfold Ixon.getU8 at h
    change EStateM.bind EStateM.get _ _ = _ at h
    simp only [EStateM.bind, EStateM.get] at h
    split at h
    · rename_i hlt; simpa [ByteArray.size] using hlt
    · cases h
  rw [getU8_at hj] at h
  cases h
  refine ⟨rfl, ?_⟩
  have hij : i + j < bytes.length := by simp at hj; omega
  simpa [List.getElem_drop, Nat.add_assoc] using getU8_at hij

theorem getTrimmed_drop (len : Nat) {bytes : List UInt8} {i j : Nat} {x : UInt64}
    {s' : Ixon.GetState}
    (h : Ixon.getU64TrimmedLEAux len { idx := j, bytes := ⟨(bytes.drop i).toArray⟩ } = .ok x s') :
    s' = { idx := j + len, bytes := ⟨(bytes.drop i).toArray⟩ } ∧
      Ixon.getU64TrimmedLEAux len { idx := i + j, bytes := ⟨bytes.toArray⟩ } =
        .ok x { idx := i + (j + len), bytes := ⟨bytes.toArray⟩ } := by
  induction len generalizing j x s' with
  | zero =>
    obtain ⟨rfl, rfl⟩ := Ixon.Verify.TagN.pure_ok_inv h
    exact ⟨by simp, by simp [Ixon.getU64TrimmedLEAux, pure, EStateM.pure]⟩
  | succ len ih =>
    obtain ⟨low, s1, hlow, h⟩ := Ixon.Verify.TagN.bind_ok_inv h
    obtain ⟨high, s2, hhigh, h⟩ := Ixon.Verify.TagN.bind_ok_inv h
    obtain ⟨rfl, rfl⟩ := Ixon.Verify.TagN.pure_ok_inv h
    obtain ⟨rfl, hlow'⟩ := getU8_drop hlow
    obtain ⟨rfl, hhigh'⟩ := ih hhigh
    refine ⟨by simp [Nat.add_assoc, Nat.add_comm 1 len], ?_⟩
    simp [Ixon.getU64TrimmedLEAux, bind, EStateM.bind, hlow', hhigh', pure, EStateM.pure,
      Nat.add_assoc, Nat.add_comm 1 len]

theorem getTagNWide_drop {f : Nat} {flag : UInt8} {c : Nat} {bytes : List UInt8} {i j : Nat}
    {t : Ixon.TagN} {s' : Ixon.GetState}
    (h : Ixon.getTagNWide f flag c { idx := j, bytes := ⟨(bytes.drop i).toArray⟩ } = .ok t s') :
    ∃ m, s' = { idx := m, bytes := ⟨(bytes.drop i).toArray⟩ } ∧
      Ixon.getTagNWide f flag c { idx := i + j, bytes := ⟨bytes.toArray⟩ } =
        .ok t { idx := i + m, bytes := ⟨bytes.toArray⟩ } := by
  unfold Ixon.getTagNWide at h ⊢
  by_cases h0 : c = 0
  · rw [ite_eq_left h0] at h ⊢
    obtain ⟨x, s1, hx, h⟩ := Ixon.Verify.TagN.bind_ok_inv h
    obtain ⟨rfl, rfl⟩ := Ixon.Verify.TagN.pure_ok_inv h
    obtain ⟨rfl, hx'⟩ := getTrimmed_drop 2 hx
    exact ⟨j + 2, rfl, by simp [bind, EStateM.bind, hx', pure, EStateM.pure]⟩
  rw [ite_eq_right h0] at h ⊢
  by_cases h1 : c = 1
  · rw [ite_eq_left h1] at h ⊢
    obtain ⟨x, s1, hx, h⟩ := Ixon.Verify.TagN.bind_ok_inv h
    obtain ⟨rfl, rfl⟩ := Ixon.Verify.TagN.pure_ok_inv h
    obtain ⟨rfl, hx'⟩ := getTrimmed_drop 3 hx
    exact ⟨j + 3, rfl, by simp [bind, EStateM.bind, hx', pure, EStateM.pure]⟩
  rw [ite_eq_right h1] at h ⊢
  by_cases h2 : c = 2
  · rw [ite_eq_left h2] at h ⊢
    obtain ⟨x, s1, hx, h⟩ := Ixon.Verify.TagN.bind_ok_inv h
    obtain ⟨rfl, rfl⟩ := Ixon.Verify.TagN.pure_ok_inv h
    obtain ⟨rfl, hx'⟩ := getTrimmed_drop 4 hx
    exact ⟨j + 4, rfl, by simp [bind, EStateM.bind, hx', pure, EStateM.pure]⟩
  rw [ite_eq_right h2] at h ⊢
  by_cases h3 : c = 3
  · rw [ite_eq_left h3] at h ⊢
    obtain ⟨x, s1, hx, h⟩ := Ixon.Verify.TagN.bind_ok_inv h
    obtain ⟨rfl, hx'⟩ := getTrimmed_drop 8 hx
    by_cases hlt : Ixon.tagNEnd5 f + x.toNat < 2 ^ 64
    · rw [ite_eq_left hlt] at h
      obtain ⟨rfl, rfl⟩ := Ixon.Verify.TagN.pure_ok_inv h
      refine ⟨j + 8, rfl, ?_⟩
      simp only [bind, EStateM.bind, hx', hlt, ↓reduceIte, pure, EStateM.pure]
    · rw [ite_eq_right hlt] at h
      exact (Ixon.Verify.TagN.throw_ok_false h).elim
  · rw [ite_eq_right h3] at h
    exact (Ixon.Verify.TagN.throw_ok_false h).elim

/-- **Shifting `Ixon.getTagN` to an arbitrary offset `i`**: a read from `start (bytes.drop i)`
that advances to `n` succeeds from `{ idx := i, bytes := ⟨bytes.toArray⟩ }` and advances to
`i + n`. -/
theorem getTagN_drop {f : Nat} {bytes : List UInt8} {i n : Nat} {t : Ixon.TagN}
    (h : Ixon.getTagN f (start (bytes.drop i)) = .ok t { idx := n, bytes := ⟨(bytes.drop i).toArray⟩ }) :
    Ixon.getTagN f { idx := i, bytes := ⟨bytes.toArray⟩ } =
      .ok t { idx := i + n, bytes := ⟨bytes.toArray⟩ } := by
  unfold start Ixon.getTagN at h
  unfold Ixon.getTagN
  obtain ⟨b, s1, hb, h⟩ := Ixon.Verify.TagN.bind_ok_inv h
  obtain ⟨rfl, hb'⟩ := getU8_drop hb
  rw [Nat.add_zero] at hb'
  simp only at h
  by_cases h1 : b.toNat % 2 ^ (8 - f) < 2 ^ (8 - f - 1)
  · rw [ite_eq_left h1] at h
    obtain ⟨rfl, hidx⟩ := Ixon.Verify.TagN.pure_ok_inv h
    cases hidx
    simp [bind, EStateM.bind, hb', h1, pure, EStateM.pure]
  rw [ite_eq_right h1] at h
  by_cases h2 : b.toNat % 2 ^ (8 - f) - 2 ^ (8 - f - 1) < 2 ^ (8 - f - 2)
  · rw [ite_eq_left h2] at h
    obtain ⟨lo, s2, hlo, h⟩ := Ixon.Verify.TagN.bind_ok_inv h
    obtain ⟨rfl, hidx⟩ := Ixon.Verify.TagN.pure_ok_inv h
    obtain ⟨hs2, hlo'⟩ := getU8_drop hlo
    rw [hs2] at hidx
    cases hidx
    simp [bind, EStateM.bind, hb', h1, h2, hlo', pure, EStateM.pure]
  · rw [ite_eq_right h2] at h
    obtain ⟨m, hm, hw⟩ := getTagNWide_drop h
    cases hm
    simp [bind, EStateM.bind, hb', h1, h2, hw]

/-- **`getTagN0_refines` at an arbitrary reader offset `i`.** -/
theorem getTagN0_refines_at {stream r : SourceValue F} {heap h' : Heap F} {bytes : List UInt8}
    {i : Nat} (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum heap (bytes.drop i) stream)
    (ev : EvalFn W "IxonDeserialize::get_tagn0" [stream] heap r h') :
    h' = heap ∧ ∃ (t : Ixon.TagN) (n : Nat) (restPtr : SourceValue F),
      Ixon.getTagN 0 { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok t { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      t.flag = 0 ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum heap (bytes.drop (i + n)) restPtr ∧
      r = .tuple [u64Value t.value.toNat, restPtr] := by
  obtain ⟨rfl, t, n, restPtr, hok, hflag, hrep, hr⟩ := getTagN0_refines rep ev
  rw [List.drop_drop] at hrep
  exact ⟨rfl, t, n, restPtr, getTagN_drop hok, hflag, hrep, hr⟩

/-- **`getTagN4_refines` at an arbitrary reader offset `i`.** -/
theorem getTagN4_refines_at {stream r : SourceValue F} {heap h' : Heap F} {bytes : List UInt8}
    {i : Nat} (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum heap (bytes.drop i) stream)
    (ev : EvalFn W "IxonDeserialize::get_tagn4" [stream] heap r h') :
    h' = heap ∧ ∃ (t : Ixon.TagN) (n : Nat) (restPtr : SourceValue F),
      Ixon.getTagN 4 { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok t { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum heap (bytes.drop (i + n)) restPtr ∧
      r = .tuple [.tuple [.field (t.flag.toNat : F), u64Value t.value.toNat], restPtr] := by
  obtain ⟨rfl, t, n, restPtr, hok, hrep, hr⟩ := getTagN4_refines rep ev
  rw [List.drop_drop] at hrep
  exact ⟨rfl, t, n, restPtr, getTagN_drop hok, hrep, hr⟩

/-- **`getTagN2_refines` at an arbitrary reader offset `i`.** -/
theorem getTagN2_refines_at {stream r : SourceValue F} {heap h' : Heap F} {bytes : List UInt8}
    {i : Nat} (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum heap (bytes.drop i) stream)
    (ev : EvalFn W "IxonDeserialize::get_tagn2" [stream] heap r h') :
    h' = heap ∧ ∃ (t : Ixon.TagN) (n : Nat) (restPtr : SourceValue F),
      Ixon.getTagN 2 { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok t { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum heap (bytes.drop (i + n)) restPtr ∧
      r = .tuple [.tuple [.field (t.flag.toNat : F), u64Value t.value.toNat], restPtr] := by
  obtain ⟨rfl, t, n, restPtr, hok, hrep, hr⟩ := getTagN2_refines rep ev
  rw [List.drop_drop] at hrep
  exact ⟨rfl, t, n, restPtr, getTagN_drop hok, hrep, hr⟩

end IxVM.Refinement.TagN
