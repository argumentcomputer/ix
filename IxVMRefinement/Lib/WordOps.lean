import IxVMRefinement.Lib.Words
import Aiur.Library.U8Facts

/-! # Word arithmetic and bitwise library functions, over observed derivations

`UInt64::sub_with_borrow`, and the byte and word `xor`, `and`, `or`, as specs over observed
derivations, through their mirrors (`IxVM.Refinement.Mirrors`, `«f».of_eval`) and the
mirrors' computation on represented inputs proved here: the subtraction is a ripple of
`UInt8::split_sum` steps over the complement of the subtrahend (`u64SubBorrow_run`); the
bitwise operations read the byte table `UInt8::raw_xor` (`rawXor_row`), `and`/`or` through
`a + b = (a xor b) + 2 (a and b)` and `2 (a or b) = a + b + (a xor b)`
(`Aiur.Library.U8Facts`), and a word operation is the byte operation at each byte
(`byte_xor` and its siblings). -/

namespace IxVM.Refinement.Lib

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library
open IxVM.Refinement.Obs (W)
open IxVM (F)

set_option linter.unusedVariables false

/-! ## `UInt64::sub_with_borrow` -/

/-- **`UInt64::sub_with_borrow` on bytes**: given the ripple digits `s` and carries `c` of
`a + (2^64 - 1 - b) + 1`, the mirror returns the digits and the borrow `1 - c₈`. -/
theorem u64SubBorrow_run {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    {s0 s1 s2 s3 s4 s5 s6 s7 c1 c2 c3 c4 c5 c6 c7 c8 : Nat}
    (ha0 : a0 < 256) (ha1 : a1 < 256) (ha2 : a2 < 256) (ha3 : a3 < 256)
    (ha4 : a4 < 256) (ha5 : a5 < 256) (ha6 : a6 < 256) (ha7 : a7 < 256)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (hb4 : b4 < 256) (hb5 : b5 < 256) (hb6 : b6 < 256) (hb7 : b7 < 256)
    (hs0 : s0 < 256) (hs1 : s1 < 256) (hs2 : s2 < 256) (hs3 : s3 < 256)
    (hs4 : s4 < 256) (hs5 : s5 < 256) (hs6 : s6 < 256) (hs7 : s7 < 256)
    (h0 : a0 + 256 - b0 = s0 + 256 * c1) (h1 : a1 + 255 - b1 + c1 = s1 + 256 * c2)
    (h2 : a2 + 255 - b2 + c2 = s2 + 256 * c3) (h3 : a3 + 255 - b3 + c3 = s3 + 256 * c4)
    (h4 : a4 + 255 - b4 + c4 = s4 + 256 * c5) (h5 : a5 + 255 - b5 + c5 = s5 + 256 * c6)
    (h6 : a6 + 255 - b6 + c6 = s6 + 256 * c7) (h7 : a7 + 255 - b7 + c7 = s7 + 256 * c8)
    (k : Nat) (h : Heap F) :
    Mirrors.«UInt64::sub_with_borrow» (k + 2) h
        (.tuple [.field (a0 : F), .field (a1 : F), .field (a2 : F), .field (a3 : F), .field (a4 : F),
          .field (a5 : F), .field (a6 : F), .field (a7 : F)])
        (.tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F), .field (b4 : F),
          .field (b5 : F), .field (b6 : F), .field (b7 : F)]) =
      some (.tuple [.tuple [.field (s0 : F), .field (s1 : F), .field (s2 : F), .field (s3 : F),
        .field (s4 : F), .field (s5 : F), .field (s6 : F), .field (s7 : F)],
        .field (1 - (c8 : F))], h) := by
  have e0 : Mirrors.«UInt8::split_sum» (k + 1) h (.field ((a0 : F) + 256 - (b0 : F))) =
      some (.tuple [.field (s0 : F), .field (c1 : F)], h) := by
    have hc : ((a0 : F) + 256 - (b0 : F)) = ((a0 + 256 - b0 : Nat) : F) := by
      rw [Nat.cast_sub (show b0 ≤ a0 + 256 by omega), Nat.cast_add, Nat.cast_ofNat]
    rw [hc, show s0 = (a0 + 256 - b0) % 256 by omega, show c1 = (a0 + 256 - b0) / 256 by omega]
    exact TagN.splitSum_run (by omega) k h
  have e1 : Mirrors.«UInt8::split_sum» (k + 1) h (.field ((a1 : F) + 255 - (b1 : F) + (c1 : F))) =
      some (.tuple [.field (s1 : F), .field (c2 : F)], h) := by
    have hc : ((a1 : F) + 255 - (b1 : F) + (c1 : F)) = ((a1 + 255 - b1 + c1 : Nat) : F) := by
      rw [Nat.cast_add, Nat.cast_sub (show b1 ≤ a1 + 255 by omega), Nat.cast_add, Nat.cast_ofNat]
    rw [hc, show s1 = (a1 + 255 - b1 + c1) % 256 by omega,
      show c2 = (a1 + 255 - b1 + c1) / 256 by omega]
    exact TagN.splitSum_run (by omega) k h
  have e2 : Mirrors.«UInt8::split_sum» (k + 1) h (.field ((a2 : F) + 255 - (b2 : F) + (c2 : F))) =
      some (.tuple [.field (s2 : F), .field (c3 : F)], h) := by
    have hc : ((a2 : F) + 255 - (b2 : F) + (c2 : F)) = ((a2 + 255 - b2 + c2 : Nat) : F) := by
      rw [Nat.cast_add, Nat.cast_sub (show b2 ≤ a2 + 255 by omega), Nat.cast_add, Nat.cast_ofNat]
    rw [hc, show s2 = (a2 + 255 - b2 + c2) % 256 by omega,
      show c3 = (a2 + 255 - b2 + c2) / 256 by omega]
    exact TagN.splitSum_run (by omega) k h
  have e3 : Mirrors.«UInt8::split_sum» (k + 1) h (.field ((a3 : F) + 255 - (b3 : F) + (c3 : F))) =
      some (.tuple [.field (s3 : F), .field (c4 : F)], h) := by
    have hc : ((a3 : F) + 255 - (b3 : F) + (c3 : F)) = ((a3 + 255 - b3 + c3 : Nat) : F) := by
      rw [Nat.cast_add, Nat.cast_sub (show b3 ≤ a3 + 255 by omega), Nat.cast_add, Nat.cast_ofNat]
    rw [hc, show s3 = (a3 + 255 - b3 + c3) % 256 by omega,
      show c4 = (a3 + 255 - b3 + c3) / 256 by omega]
    exact TagN.splitSum_run (by omega) k h
  have e4 : Mirrors.«UInt8::split_sum» (k + 1) h (.field ((a4 : F) + 255 - (b4 : F) + (c4 : F))) =
      some (.tuple [.field (s4 : F), .field (c5 : F)], h) := by
    have hc : ((a4 : F) + 255 - (b4 : F) + (c4 : F)) = ((a4 + 255 - b4 + c4 : Nat) : F) := by
      rw [Nat.cast_add, Nat.cast_sub (show b4 ≤ a4 + 255 by omega), Nat.cast_add, Nat.cast_ofNat]
    rw [hc, show s4 = (a4 + 255 - b4 + c4) % 256 by omega,
      show c5 = (a4 + 255 - b4 + c4) / 256 by omega]
    exact TagN.splitSum_run (by omega) k h
  have e5 : Mirrors.«UInt8::split_sum» (k + 1) h (.field ((a5 : F) + 255 - (b5 : F) + (c5 : F))) =
      some (.tuple [.field (s5 : F), .field (c6 : F)], h) := by
    have hc : ((a5 : F) + 255 - (b5 : F) + (c5 : F)) = ((a5 + 255 - b5 + c5 : Nat) : F) := by
      rw [Nat.cast_add, Nat.cast_sub (show b5 ≤ a5 + 255 by omega), Nat.cast_add, Nat.cast_ofNat]
    rw [hc, show s5 = (a5 + 255 - b5 + c5) % 256 by omega,
      show c6 = (a5 + 255 - b5 + c5) / 256 by omega]
    exact TagN.splitSum_run (by omega) k h
  have e6 : Mirrors.«UInt8::split_sum» (k + 1) h (.field ((a6 : F) + 255 - (b6 : F) + (c6 : F))) =
      some (.tuple [.field (s6 : F), .field (c7 : F)], h) := by
    have hc : ((a6 : F) + 255 - (b6 : F) + (c6 : F)) = ((a6 + 255 - b6 + c6 : Nat) : F) := by
      rw [Nat.cast_add, Nat.cast_sub (show b6 ≤ a6 + 255 by omega), Nat.cast_add, Nat.cast_ofNat]
    rw [hc, show s6 = (a6 + 255 - b6 + c6) % 256 by omega,
      show c7 = (a6 + 255 - b6 + c6) / 256 by omega]
    exact TagN.splitSum_run (by omega) k h
  have e7 : Mirrors.«UInt8::split_sum» (k + 1) h (.field ((a7 : F) + 255 - (b7 : F) + (c7 : F))) =
      some (.tuple [.field (s7 : F), .field (c8 : F)], h) := by
    have hc : ((a7 : F) + 255 - (b7 : F) + (c7 : F)) = ((a7 + 255 - b7 + c7 : Nat) : F) := by
      rw [Nat.cast_add, Nat.cast_sub (show b7 ≤ a7 + 255 by omega), Nat.cast_add, Nat.cast_ofNat]
    rw [hc, show s7 = (a7 + 255 - b7 + c7) % 256 by omega,
      show c8 = (a7 + 255 - b7 + c7) / 256 by omega]
    exact TagN.splitSum_run (by omega) k h
  simp only [Mirrors.«UInt64::sub_with_borrow», projectValue, TagN.toField_run, evalBinOp, e0, e1,
    e2, e3, e4, e5, e6, e7, bind, Except.bind, pure, Except.pure, Option.bind,
    List.getElem?_cons_succ, List.getElem?_cons_zero]

set_option maxHeartbeats 4000000 in
/-- **`UInt64::sub_with_borrow` is 64-bit subtraction with a borrow**: the difference modulo
`2^64`, and `1` exactly when the subtrahend is the larger. -/
theorem u64SubBorrow_value {x y : Nat} (hx : x < 18446744073709551616)
    (hy : y < 18446744073709551616) (k : Nat) (h : Heap F) :
    Mirrors.«UInt64::sub_with_borrow» (k + 2) h (TagN.u64Value x) (TagN.u64Value y) =
      some (.tuple [TagN.u64Value ((x + 18446744073709551616 - y) % 18446744073709551616),
        .field (if x < y then 1 else 0)], h) := by
  have run := u64SubBorrow_run
    (a0 := x % 256) (b0 := y % 256)
    (s0 := (x + 18446744073709551616 - y) % 18446744073709551616 % 256)
    (a1 := x / 256 % 256) (b1 := y / 256 % 256)
    (s1 := (x + 18446744073709551616 - y) % 18446744073709551616 / 256 % 256)
    (a2 := x / 65536 % 256) (b2 := y / 65536 % 256)
    (s2 := (x + 18446744073709551616 - y) % 18446744073709551616 / 65536 % 256)
    (a3 := x / 16777216 % 256) (b3 := y / 16777216 % 256)
    (s3 := (x + 18446744073709551616 - y) % 18446744073709551616 / 16777216 % 256)
    (a4 := x / 4294967296 % 256) (b4 := y / 4294967296 % 256)
    (s4 := (x + 18446744073709551616 - y) % 18446744073709551616 / 4294967296 % 256)
    (a5 := x / 1099511627776 % 256) (b5 := y / 1099511627776 % 256)
    (s5 := (x + 18446744073709551616 - y) % 18446744073709551616 / 1099511627776 % 256)
    (a6 := x / 281474976710656 % 256) (b6 := y / 281474976710656 % 256)
    (s6 := (x + 18446744073709551616 - y) % 18446744073709551616 / 281474976710656 % 256)
    (a7 := x / 72057594037927936 % 256) (b7 := y / 72057594037927936 % 256)
    (s7 := (x + 18446744073709551616 - y) % 18446744073709551616 / 72057594037927936 % 256)
    (c1 := (x % 256 + 256 - y % 256) / 256)
    (c2 := (x % 65536 + 65536 - y % 65536) / 65536)
    (c3 := (x % 16777216 + 16777216 - y % 16777216) / 16777216)
    (c4 := (x % 4294967296 + 4294967296 - y % 4294967296) / 4294967296)
    (c5 := (x % 1099511627776 + 1099511627776 - y % 1099511627776) / 1099511627776)
    (c6 := (x % 281474976710656 + 281474976710656 - y % 281474976710656) / 281474976710656)
    (c7 := (x % 72057594037927936 + 72057594037927936 - y % 72057594037927936) /
      72057594037927936)
    (c8 := (x % 18446744073709551616 + 18446744073709551616 - y % 18446744073709551616) /
      18446744073709551616)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) k h
  have hb : (1 : F) - (((x % 18446744073709551616 + 18446744073709551616 - y % 18446744073709551616) /
      18446744073709551616 : Nat) : F) = if x < y then 1 else 0 := by
    by_cases hxy : x < y
    · rw [show (x % 18446744073709551616 + 18446744073709551616 - y % 18446744073709551616) /
        18446744073709551616 = 0 by omega, ite_eq_left hxy, Nat.cast_zero, sub_zero]
    · rw [show (x % 18446744073709551616 + 18446744073709551616 - y % 18446744073709551616) /
        18446744073709551616 = 1 by omega, ite_eq_right hxy, Nat.cast_one, sub_self]
  rw [hb] at run
  simp only [TagN.u64Value]
  rw [run]

/-- **`UInt64::sub_with_borrow(x, y)`** on two words: the difference modulo `2^64`, and the
borrow, `1` exactly when `y` is the larger; no allocation. -/
theorem u64_sub_with_borrow_spec {x y r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {v w : UInt64} (hx : RepU64 h v x) (hy : RepU64 h w y)
    (ev : ObsFn W "UInt64::sub_with_borrow" [x, y] h r h' cs) :
    r = .tuple [TagN.u64Value ((v.toNat + 18446744073709551616 - w.toNat) % 18446744073709551616),
      .field (if v.toNat < w.toNat then 1 else 0)] ∧ h' = h := by
  obtain rfl := repU64_eq hx
  obtain rfl := repU64_eq hy
  obtain ⟨k0, hk0⟩ := Mirrors.«UInt64::sub_with_borrow».of_eval ev.erase
  have run := hk0 (k0 + 2) (by omega)
  rw [u64SubBorrow_value (u64_toNat_lt v) (u64_toNat_lt w) k0 h, Option.some.injEq,
    Prod.mk.injEq] at run
  exact ⟨run.1.symm, run.2.symm⟩

/-! ## The byte table `UInt8::raw_xor` -/

/-- The static map `UInt8::raw_xor`. -/
def rawXorMap : Aiur.MapDecl := IxVM.coreTables.maps[3]'(by decide)

theorem rawXor_row {a b : Nat} (ha : a < 256) (hb : b < 256) :
    lookupMap IxVM.source.tables "UInt8::raw_xor" ([.field (a : F), .field (b : F)] : List (SourceValue F)) =
      .ok (.field ((Nat.xor a b : Nat) : F)) := by
  have member : rawXorMap ∈ IxVM.coreTables.maps := List.getElem_mem _
  have rows : IxVM.coreTables.mapRows rawXorMap =
      IxVM.pairInputsTTable.rows.zip IxVM.pairXorsTable.rows := by
    simp only [Aiur.Program.mapRows, show rawXorMap.input = "UInt8::pair_inputs" from rfl,
      show rawXorMap.output = "UInt8::pair_xors" from rfl, IxVM.find_pairInputsT,
      IxVM.find_pairXors]
  have row : (⟨[.field (a : F), .field (b : F)], .field ((Nat.xor a b : Nat) : F)⟩ : MapEntry F) ∈
      IxVM.coreTables.mapEntries rawXorMap := by
    apply Aiur.mapEntry_mem_iff.mpr
    rw [rows]
    simp only [IxVM.pairInputsTTable, IxVM.pairXorsTable, List.map_map]
    convert TagN.mem_zip_map (TagN.pair_mem ha hb) using 1
    simp [IxVM.coreRow, IxVM.coreLeaf]
  have looked := Aiur.lookupMap_of_entry (A := Nat) IxVM.tablesChecked member row
  simpa [Constant.toValue, Value.mapAddress, show rawXorMap.name = "UInt8::raw_xor" from rfl,
    IxVM.source] using looked

theorem rawXor_mapCall {a b : Nat} (ha : a < 256) (hb : b < 256) (h : Heap F) :
    mapCall IxVM.source.tables "UInt8::raw_xor" [.field (a : F), .field (b : F)] h =
      some (.field ((Nat.xor a b : Nat) : F), h) := by
  simp [mapCall, rawXor_row ha hb, Constant.toValue, Value.mapAddress]

theorem two_ne_zero' : (2 : F) ≠ 0 := by decide

/-! ## Byte operations -/

theorem u8Xor_run {a b : Nat} (ha : a < 256) (hb : b < 256) (k : Nat) (h : Heap F) :
    Mirrors.«UInt8::xor» (k + 1) h (.field (a : F)) (.field (b : F)) =
      some (.field ((Nat.xor a b : Nat) : F), h) := by
  simp only [Mirrors.«UInt8::xor»]
  exact rawXor_mapCall ha hb h

theorem land_field {a b : Nat} :
    ((a : F) + (b : F) - ((Nat.xor a b : Nat) : F)) / 2 = ((Nat.land a b : Nat) : F) := by
  have e := congrArg (Nat.cast : Nat → F) (Aiur.Library.U8Facts.xor_and_identity a b)
  push_cast at e
  rw [div_eq_iff two_ne_zero']
  linear_combination e

theorem lor_field {a b : Nat} :
    ((a : F) + (b : F) + ((Nat.xor a b : Nat) : F)) / 2 = ((Nat.lor a b : Nat) : F) := by
  have e := congrArg (Nat.cast : Nat → F) (Aiur.Library.U8Facts.xor_or_identity a b)
  push_cast at e
  rw [div_eq_iff two_ne_zero']
  linear_combination -e

theorem u8RawAnd_run {a b : Nat} (ha : a < 256) (hb : b < 256) (k : Nat) (h : Heap F) :
    Mirrors.«UInt8::raw_and» (k + 1) h (.field (a : F)) (.field (b : F)) =
      some (.field ((Nat.land a b : Nat) : F), h) := by
  rw [show Mirrors.«UInt8::raw_and» (k + 1) h (.field (a : F)) (.field (b : F)) =
      some (.field (((a : F) + (b : F) - ((Nat.xor a b : Nat) : F)) / 2), h) by
    simp [Mirrors.«UInt8::raw_and», rawXor_mapCall ha hb h, evalBinOp, two_ne_zero'], land_field]

theorem u8RawOr_run {a b : Nat} (ha : a < 256) (hb : b < 256) (k : Nat) (h : Heap F) :
    Mirrors.«UInt8::raw_or» (k + 1) h (.field (a : F)) (.field (b : F)) =
      some (.field ((Nat.lor a b : Nat) : F), h) := by
  rw [show Mirrors.«UInt8::raw_or» (k + 1) h (.field (a : F)) (.field (b : F)) =
      some (.field (((a : F) + (b : F) + ((Nat.xor a b : Nat) : F)) / 2), h) by
    simp [Mirrors.«UInt8::raw_or», rawXor_mapCall ha hb h, evalBinOp, two_ne_zero'], lor_field]

theorem u8And_run {a b : Nat} (ha : a < 256) (hb : b < 256) (k : Nat) (h : Heap F) :
    Mirrors.«UInt8::and» (k + 2) h (.field (a : F)) (.field (b : F)) =
      some (.field ((Nat.land a b : Nat) : F), h) := by
  simp only [Mirrors.«UInt8::and»]
  exact u8RawAnd_run ha hb k h

theorem u8Or_run {a b : Nat} (ha : a < 256) (hb : b < 256) (k : Nat) (h : Heap F) :
    Mirrors.«UInt8::or» (k + 2) h (.field (a : F)) (.field (b : F)) =
      some (.field ((Nat.lor a b : Nat) : F), h) := by
  simp only [Mirrors.«UInt8::or»]
  exact u8RawOr_run ha hb k h

/-- **`UInt8::xor(x, y)`** on two bytes: their exclusive or; no allocation. -/
theorem u8_xor_spec {x y r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {a b : UInt8} (hx : RepU8 h a x) (hy : RepU8 h b y)
    (ev : ObsFn W "UInt8::xor" [x, y] h r h' cs) :
    RepU8 h (a ^^^ b) r ∧ h' = h := by
  unfold RepU8 at hx hy ⊢
  subst hx hy
  obtain ⟨k0, hk0⟩ := Mirrors.«UInt8::xor».of_eval ev.erase
  have run := hk0 (k0 + 1) (by omega)
  rw [u8Xor_run (show a.toNat < 256 from a.toNat_lt) (show b.toNat < 256 from b.toNat_lt) k0 h,
    Option.some.injEq, Prod.mk.injEq] at run
  refine ⟨run.1.symm.trans ?_, run.2.symm⟩
  rw [UInt8.toNat_xor]
  rfl

/-- **`UInt8::and(x, y)`** on two bytes: their conjunction; no allocation. -/
theorem u8_and_spec {x y r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {a b : UInt8} (hx : RepU8 h a x) (hy : RepU8 h b y)
    (ev : ObsFn W "UInt8::and" [x, y] h r h' cs) :
    RepU8 h (a &&& b) r ∧ h' = h := by
  unfold RepU8 at hx hy ⊢
  subst hx hy
  obtain ⟨k0, hk0⟩ := Mirrors.«UInt8::and».of_eval ev.erase
  have run := hk0 (k0 + 2) (by omega)
  rw [u8And_run (show a.toNat < 256 from a.toNat_lt) (show b.toNat < 256 from b.toNat_lt) k0 h,
    Option.some.injEq, Prod.mk.injEq] at run
  refine ⟨run.1.symm.trans ?_, run.2.symm⟩
  rw [UInt8.toNat_and]
  rfl

/-- **`UInt8::or(x, y)`** on two bytes: their disjunction; no allocation. -/
theorem u8_or_spec {x y r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {a b : UInt8} (hx : RepU8 h a x) (hy : RepU8 h b y)
    (ev : ObsFn W "UInt8::or" [x, y] h r h' cs) :
    RepU8 h (a ||| b) r ∧ h' = h := by
  unfold RepU8 at hx hy ⊢
  subst hx hy
  obtain ⟨k0, hk0⟩ := Mirrors.«UInt8::or».of_eval ev.erase
  have run := hk0 (k0 + 2) (by omega)
  rw [u8Or_run (show a.toNat < 256 from a.toNat_lt) (show b.toNat < 256 from b.toNat_lt) k0 h,
    Option.some.injEq, Prod.mk.injEq] at run
  refine ⟨run.1.symm.trans ?_, run.2.symm⟩
  rw [UInt8.toNat_or]
  rfl

/-! ## A bitwise operation reads each byte -/

theorem byte_xor (a b k : Nat) :
    Nat.xor a b / 2 ^ k % 2 ^ 8 = Nat.xor (a / 2 ^ k % 2 ^ 8) (b / 2 ^ k % 2 ^ 8) := by
  show (a ^^^ b) / 2 ^ k % 2 ^ 8 = (a / 2 ^ k % 2 ^ 8) ^^^ (b / 2 ^ k % 2 ^ 8)
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_xor]
  by_cases hi : i < 8 <;> simp [hi]

theorem byte_land (a b k : Nat) :
    Nat.land a b / 2 ^ k % 2 ^ 8 = Nat.land (a / 2 ^ k % 2 ^ 8) (b / 2 ^ k % 2 ^ 8) := by
  show (a &&& b) / 2 ^ k % 2 ^ 8 = (a / 2 ^ k % 2 ^ 8) &&& (b / 2 ^ k % 2 ^ 8)
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_and]
  by_cases hi : i < 8 <;> simp [hi]

theorem byte_lor (a b k : Nat) :
    Nat.lor a b / 2 ^ k % 2 ^ 8 = Nat.lor (a / 2 ^ k % 2 ^ 8) (b / 2 ^ k % 2 ^ 8) := by
  show (a ||| b) / 2 ^ k % 2 ^ 8 = (a / 2 ^ k % 2 ^ 8) ||| (b / 2 ^ k % 2 ^ 8)
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_or]
  by_cases hi : i < 8 <;> simp [hi]

/-- The eight bytes of a bitwise operation `op` are `op` of the operands' bytes. -/
theorem u64Value_bitwise {op : Nat → Nat → Nat}
    (hop : ∀ a b k, op a b / 2 ^ k % 2 ^ 8 = op (a / 2 ^ k % 2 ^ 8) (b / 2 ^ k % 2 ^ 8))
    (x y : Nat) :
    TagN.u64Value (op x y) =
      .tuple [.field ((op (x % 256) (y % 256) : Nat) : F),
        .field ((op (x / 256 % 256) (y / 256 % 256) : Nat) : F),
        .field ((op (x / 65536 % 256) (y / 65536 % 256) : Nat) : F),
        .field ((op (x / 16777216 % 256) (y / 16777216 % 256) : Nat) : F),
        .field ((op (x / 4294967296 % 256) (y / 4294967296 % 256) : Nat) : F),
        .field ((op (x / 1099511627776 % 256) (y / 1099511627776 % 256) : Nat) : F),
        .field ((op (x / 281474976710656 % 256) (y / 281474976710656 % 256) : Nat) : F),
        .field ((op (x / 72057594037927936 % 256) (y / 72057594037927936 % 256) : Nat) : F)] := by
  have e0 := hop x y 0
  have e1 := hop x y 8
  have e2 := hop x y 16
  have e3 := hop x y 24
  have e4 := hop x y 32
  have e5 := hop x y 40
  have e6 := hop x y 48
  have e7 := hop x y 56
  simp only [Nat.reducePow, Nat.pow_zero, Nat.div_one] at e0 e1 e2 e3 e4 e5 e6 e7
  simp only [TagN.u64Value, e0, e1, e2, e3, e4, e5, e6, e7]

/-! ## Word operations -/

theorem u64Xor_value {x y : Nat} (hx : x < 18446744073709551616) (hy : y < 18446744073709551616)
    (k : Nat) (h : Heap F) :
    Mirrors.«UInt64::xor» (k + 2) h (TagN.u64Value x) (TagN.u64Value y) =
      some (TagN.u64Value (Nat.xor x y), h) := by
  rw [u64Value_bitwise byte_xor]
  simp only [TagN.u64Value, Mirrors.«UInt64::xor», bind, Option.bind,
    u8Xor_run (a := x % 256) (b := y % 256) (by omega) (by omega),
    u8Xor_run (a := x / 256 % 256) (b := y / 256 % 256) (by omega) (by omega),
    u8Xor_run (a := x / 65536 % 256) (b := y / 65536 % 256) (by omega) (by omega),
    u8Xor_run (a := x / 16777216 % 256) (b := y / 16777216 % 256) (by omega) (by omega),
    u8Xor_run (a := x / 4294967296 % 256) (b := y / 4294967296 % 256) (by omega) (by omega),
    u8Xor_run (a := x / 1099511627776 % 256) (b := y / 1099511627776 % 256) (by omega) (by omega),
    u8Xor_run (a := x / 281474976710656 % 256) (b := y / 281474976710656 % 256) (by omega)
      (by omega),
    u8Xor_run (a := x / 72057594037927936 % 256) (b := y / 72057594037927936 % 256) (by omega)
      (by omega)]

theorem u64And_value {x y : Nat} (hx : x < 18446744073709551616) (hy : y < 18446744073709551616)
    (k : Nat) (h : Heap F) :
    Mirrors.«UInt64::and» (k + 3) h (TagN.u64Value x) (TagN.u64Value y) =
      some (TagN.u64Value (Nat.land x y), h) := by
  rw [u64Value_bitwise byte_land]
  simp only [TagN.u64Value, Mirrors.«UInt64::and», bind, Option.bind,
    u8And_run (a := x % 256) (b := y % 256) (by omega) (by omega),
    u8And_run (a := x / 256 % 256) (b := y / 256 % 256) (by omega) (by omega),
    u8And_run (a := x / 65536 % 256) (b := y / 65536 % 256) (by omega) (by omega),
    u8And_run (a := x / 16777216 % 256) (b := y / 16777216 % 256) (by omega) (by omega),
    u8And_run (a := x / 4294967296 % 256) (b := y / 4294967296 % 256) (by omega) (by omega),
    u8And_run (a := x / 1099511627776 % 256) (b := y / 1099511627776 % 256) (by omega) (by omega),
    u8And_run (a := x / 281474976710656 % 256) (b := y / 281474976710656 % 256) (by omega)
      (by omega),
    u8And_run (a := x / 72057594037927936 % 256) (b := y / 72057594037927936 % 256) (by omega)
      (by omega)]

theorem u64Or_value {x y : Nat} (hx : x < 18446744073709551616) (hy : y < 18446744073709551616)
    (k : Nat) (h : Heap F) :
    Mirrors.«UInt64::or» (k + 3) h (TagN.u64Value x) (TagN.u64Value y) =
      some (TagN.u64Value (Nat.lor x y), h) := by
  rw [u64Value_bitwise byte_lor]
  simp only [TagN.u64Value, Mirrors.«UInt64::or», bind, Option.bind,
    u8Or_run (a := x % 256) (b := y % 256) (by omega) (by omega),
    u8Or_run (a := x / 256 % 256) (b := y / 256 % 256) (by omega) (by omega),
    u8Or_run (a := x / 65536 % 256) (b := y / 65536 % 256) (by omega) (by omega),
    u8Or_run (a := x / 16777216 % 256) (b := y / 16777216 % 256) (by omega) (by omega),
    u8Or_run (a := x / 4294967296 % 256) (b := y / 4294967296 % 256) (by omega) (by omega),
    u8Or_run (a := x / 1099511627776 % 256) (b := y / 1099511627776 % 256) (by omega) (by omega),
    u8Or_run (a := x / 281474976710656 % 256) (b := y / 281474976710656 % 256) (by omega)
      (by omega),
    u8Or_run (a := x / 72057594037927936 % 256) (b := y / 72057594037927936 % 256) (by omega)
      (by omega)]

/-- **`UInt64::xor(x, y)`** on two words: their exclusive or; no allocation. -/
theorem u64_xor_spec {x y r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {v w : UInt64} (hx : RepU64 h v x) (hy : RepU64 h w y)
    (ev : ObsFn W "UInt64::xor" [x, y] h r h' cs) :
    RepU64 h (v ^^^ w) r ∧ h' = h := by
  obtain rfl := repU64_eq hx
  obtain rfl := repU64_eq hy
  obtain ⟨k0, hk0⟩ := Mirrors.«UInt64::xor».of_eval ev.erase
  have run := hk0 (k0 + 2) (by omega)
  rw [u64Xor_value (u64_toNat_lt v) (u64_toNat_lt w) k0 h, Option.some.injEq,
    Prod.mk.injEq] at run
  obtain ⟨rfl, rfl⟩ := run
  refine ⟨?_, rfl⟩
  have e := Deserialize.repU64_u64Value h (v ^^^ w)
  rw [UInt64.toNat_xor] at e
  exact e

/-- **`UInt64::and(x, y)`** on two words: their conjunction; no allocation. -/
theorem u64_and_spec {x y r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {v w : UInt64} (hx : RepU64 h v x) (hy : RepU64 h w y)
    (ev : ObsFn W "UInt64::and" [x, y] h r h' cs) :
    RepU64 h (v &&& w) r ∧ h' = h := by
  obtain rfl := repU64_eq hx
  obtain rfl := repU64_eq hy
  obtain ⟨k0, hk0⟩ := Mirrors.«UInt64::and».of_eval ev.erase
  have run := hk0 (k0 + 3) (by omega)
  rw [u64And_value (u64_toNat_lt v) (u64_toNat_lt w) k0 h, Option.some.injEq,
    Prod.mk.injEq] at run
  obtain ⟨rfl, rfl⟩ := run
  refine ⟨?_, rfl⟩
  have e := Deserialize.repU64_u64Value h (v &&& w)
  rw [UInt64.toNat_and] at e
  exact e

/-- **`UInt64::or(x, y)`** on two words: their disjunction; no allocation. -/
theorem u64_or_spec {x y r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {v w : UInt64} (hx : RepU64 h v x) (hy : RepU64 h w y)
    (ev : ObsFn W "UInt64::or" [x, y] h r h' cs) :
    RepU64 h (v ||| w) r ∧ h' = h := by
  obtain rfl := repU64_eq hx
  obtain rfl := repU64_eq hy
  obtain ⟨k0, hk0⟩ := Mirrors.«UInt64::or».of_eval ev.erase
  have run := hk0 (k0 + 3) (by omega)
  rw [u64Or_value (u64_toNat_lt v) (u64_toNat_lt w) k0 h, Option.some.injEq,
    Prod.mk.injEq] at run
  obtain ⟨rfl, rfl⟩ := run
  refine ⟨?_, rfl⟩
  have e := Deserialize.repU64_u64Value h (v ||| w)
  rw [UInt64.toNat_or] at e
  exact e

end IxVM.Refinement.Lib
