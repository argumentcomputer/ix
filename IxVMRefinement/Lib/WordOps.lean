import IxVMRefinement.Lib.Words
import Aiur.Library.U8Facts

/-! # Bitwise byte and word library functions, over observed derivations

The byte and word `xor`, `and`, `or`, as specs over observed derivations, through their
mirrors (`IxVM.Refinement.Mirrors`, `«f».of_eval`) and the mirrors' computation on
represented inputs proved here: the byte operations read the table `UInt8::raw_xor`
(`rawXor_row`), `and`/`or` through `a + b = (a xor b) + 2 (a and b)` and
`2 (a or b) = a + b + (a xor b)` (`Aiur.Library.U8Facts`), and a word operation is the byte
operation at each byte (`byte_xor` and its siblings). -/

namespace IxVM.Refinement.Lib

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library
open IxVM.Refinement.Obs (W)
open IxVM (F)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

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

theorem twoF_ne_zero : (2 : F) ≠ 0 := by decide

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
  rw [div_eq_iff twoF_ne_zero]
  linear_combination e

theorem lor_field {a b : Nat} :
    ((a : F) + (b : F) + ((Nat.xor a b : Nat) : F)) / 2 = ((Nat.lor a b : Nat) : F) := by
  have e := congrArg (Nat.cast : Nat → F) (Aiur.Library.U8Facts.xor_or_identity a b)
  push_cast at e
  rw [div_eq_iff twoF_ne_zero]
  linear_combination -e

theorem u8RawAnd_run {a b : Nat} (ha : a < 256) (hb : b < 256) (k : Nat) (h : Heap F) :
    Mirrors.«UInt8::raw_and» (k + 1) h (.field (a : F)) (.field (b : F)) =
      some (.field ((Nat.land a b : Nat) : F), h) := by
  rw [show Mirrors.«UInt8::raw_and» (k + 1) h (.field (a : F)) (.field (b : F)) =
      some (.field (((a : F) + (b : F) - ((Nat.xor a b : Nat) : F)) / 2), h) by
    simp [Mirrors.«UInt8::raw_and», rawXor_mapCall ha hb h, evalBinOp, twoF_ne_zero], land_field]

theorem u8RawOr_run {a b : Nat} (ha : a < 256) (hb : b < 256) (k : Nat) (h : Heap F) :
    Mirrors.«UInt8::raw_or» (k + 1) h (.field (a : F)) (.field (b : F)) =
      some (.field ((Nat.lor a b : Nat) : F), h) := by
  rw [show Mirrors.«UInt8::raw_or» (k + 1) h (.field (a : F)) (.field (b : F)) =
      some (.field (((a : F) + (b : F) + ((Nat.xor a b : Nat) : F)) / 2), h) by
    simp [Mirrors.«UInt8::raw_or», rawXor_mapCall ha hb h, evalBinOp, twoF_ne_zero], lor_field]

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
  rw [UInt8.toNat_xor] <;> rfl

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
  rw [UInt8.toNat_and] <;> rfl

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
  rw [UInt8.toNat_or] <;> rfl

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
