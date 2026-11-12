import IxVMRefinement.Lib.WordSub
import IxVMRefinement.Obs.UInt64

/-! # `UInt64::mul`, over observed derivations

`UInt64::mul` multiplies two words, each read as four 16-bit limbs (two little-endian bytes
each), by schoolbook columns: column `k` sums the limb products `aᵢ bⱼ` with `i + j = k` and
the previous column's carry, and `UInt64::mul_column` splits the sum, read from a hint
(`bytes_le`), into its low two bytes (the column's digit) and the next three bytes (its carry).
The hint is checked, not trusted: each pair of hint bytes is range-checked
(`UInt8::from_fields`) and the five bytes must recompose to the column sum, so a column has a
derivation only on a sum below `2^40`, and then returns that sum's bytes
(`mulColumn_complete`: every derivation is a run of the column's mirror). The last carry's top
byte is asserted zero.

Over represented words the columns are the long multiplication of their values: the seven
digits and the last carry are the product's sixteen bytes, the low word first
(`u64Mul_value`), and `u64_mul_spec` reads a derivation through the mirror of `UInt64::mul`
(`Mirrors.«UInt64::mul».of_eval`). -/

namespace IxVM.Refinement.NatLib

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library
open IxVM.Refinement.Obs (W)
open IxVM (F)

set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## `UInt64::mul_column` -/

/-- **A column on a natural below `2^40`**: its low two bytes and its next three bytes. -/
theorem mulColumn_run {X : ℕ} (hX : X < 1099511627776) (k : ℕ) (h : Heap F) :
    Mirrors.«UInt64::mul_column» (k + 1) h (.field (X : F)) =
      some (.tuple [.tuple [.field ((X % 256 : ℕ) : F), .field ((X / 256 % 256 : ℕ) : F)],
        .tuple [.field ((X / 65536 % 256 : ℕ) : F), .field ((X / 16777216 % 256 : ℕ) : F),
          .field ((X / 4294967296 % 256 : ℕ) : F)]], h) := by
  have hv : ((X : F)).val = X :=
    ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  simp only [Mirrors.«UInt64::mul_column», hv, hX, ↓reduceIte]

/-- `mulColumn_run` on a field element given as the cast of a natural below `2^40`. -/
theorem mulColumn_of_eq {x : F} {X : ℕ} (hx : x = (X : F)) (hX : X < 1099511627776) (k : ℕ)
    (h : Heap F) :
    Mirrors.«UInt64::mul_column» (k + 1) h (.field x) =
      some (.tuple [.tuple [.field ((X % 256 : ℕ) : F), .field ((X / 256 % 256 : ℕ) : F)],
        .tuple [.field ((X / 65536 % 256 : ℕ) : F), .field ((X / 16777216 % 256 : ℕ) : F),
          .field ((X / 4294967296 % 256 : ℕ) : F)]], h) := by
  subst hx
  exact mulColumn_run hX k h

set_option maxHeartbeats 1000000 in
/-- **Every derivation of `UInt64::mul_column` is a run of its mirror**: the hint's five
bytes are range-checked and must recompose to the column value, which is therefore below
`2^40` and is returned as its low two bytes and next three bytes. -/
theorem mulColumn_complete : Mirrors.«UInt64::mul_column».Complete := by
  intro x h h' r ev
  obtain ⟨cs, ob⟩ := ev.observe
  rcases Obs.«UInt64::mul_column».obs ob with
    ⟨k10, m15, cs25, v28, v29, xr0, xr1, m64, cs74, v77, v78, xc0, xc1, m113, cs123, v126, xc2,
      w147, v170, m179, x184, y185, m186, x192, y193, m194, cs203, y215, cs225, y237, x244, y245,
      m246, x252, y253, m254, cs263, y275, cs285, y297, cs307, ty12, pr38, pr48, ev27, pr87, pr97,
      ev76, pr136, ev125, ev205, ev227, op221, op199, ev265, ev287, op281, op259, ev309, op303,
      op251, op243, op191, heq318, rfl, rfl, -⟩
  -- the hint's bytes, range-checked in pairs
  obtain ⟨hr27, rfl, a0, a1, ha0, ha1, rfl, rfl⟩ := KernelLevels.u8FromFields_eval_inv ev27.erase
  injection hr27 with hr27
  injection hr27 with e0 hr27
  injection hr27 with e1 _
  subst e0 e1
  obtain ⟨hr76, rfl, c0, c1, hc0, hc1, rfl, rfl⟩ := KernelLevels.u8FromFields_eval_inv ev76.erase
  injection hr76 with hr76
  injection hr76 with e2 hr76
  injection hr76 with e3 _
  subst e2 e3
  obtain ⟨hr125, rfl, c2, z, hc2, hz, rfl, -⟩ := KernelLevels.u8FromFields_eval_inv ev125.erase
  injection hr125 with hr125
  injection hr125 with e4 hr125
  injection hr125 with e5 _
  subst e4 e5
  -- the recomposition
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev205
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev227
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev265
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev287
  obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev309
  simp only [evalBinOp, Except.ok.injEq] at op221
  subst op221
  simp only [evalBinOp, Except.ok.injEq] at op199
  subst op199
  simp only [evalBinOp, Except.ok.injEq] at op281
  subst op281
  simp only [evalBinOp, Except.ok.injEq] at op259
  subst op259
  simp only [evalBinOp, Except.ok.injEq] at op303
  subst op303
  simp only [evalBinOp, Except.ok.injEq] at op251
  subst op251
  simp only [evalBinOp, Except.ok.injEq] at op243
  subst op243
  simp only [evalBinOp, Except.ok.injEq] at op191
  subst op191
  subst heq318
  -- the column value is the natural its bytes recompose to, below `2^40`
  have hlt : a0 + 256 * a1 + 65536 * (c0 + 256 * c1 + 65536 * c2) < 1099511627776 := by omega
  have d0 : (a0 + 256 * a1 + 65536 * (c0 + 256 * c1 + 65536 * c2)) % 256 = a0 := by omega
  have d1 : (a0 + 256 * a1 + 65536 * (c0 + 256 * c1 + 65536 * c2)) / 256 % 256 = a1 := by omega
  have d2 : (a0 + 256 * a1 + 65536 * (c0 + 256 * c1 + 65536 * c2)) / 65536 % 256 = c0 := by
    omega
  have d3 : (a0 + 256 * a1 + 65536 * (c0 + 256 * c1 + 65536 * c2)) / 16777216 % 256 = c1 := by
    omega
  have d4 : (a0 + 256 * a1 + 65536 * (c0 + 256 * c1 + 65536 * c2)) / 4294967296 % 256 = c2 := by
    omega
  refine ⟨1, fun k hk => ?_⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [mulColumn_of_eq (X := a0 + 256 * a1 + 65536 * (c0 + 256 * c1 + 65536 * c2)) ?_ hlt,
    d0, d1, d2, d3, d4]
  push_cast <;> ring

/-! ## The columns -/

/-- The low byte of a natural is a byte. -/
theorem byte_lt (n : ℕ) : n % 256 < 256 := Nat.mod_lt _ (by norm_num)

/-- A natural that is `lo + 2^64 hi`, for `lo` the value of eight bytes, splits there. -/
theorem leBytes8_split {L d0 d1 d2 d3 d4 d5 d6 d7 e0 e1 e2 e3 e4 e5 e6 e7 : ℕ}
    (hd0 : d0 < 256) (hd1 : d1 < 256) (hd2 : d2 < 256) (hd3 : d3 < 256) (hd4 : d4 < 256)
    (hd5 : d5 < 256) (hd6 : d6 < 256) (hd7 : d7 < 256)
    (hL : L = Lib.leBytes8 d0 d1 d2 d3 d4 d5 d6 d7 +
      18446744073709551616 * Lib.leBytes8 e0 e1 e2 e3 e4 e5 e6 e7) :
    L % 18446744073709551616 = Lib.leBytes8 d0 d1 d2 d3 d4 d5 d6 d7 ∧
      L / 18446744073709551616 = Lib.leBytes8 e0 e1 e2 e3 e4 e5 e6 e7 := by
  have := Lib.leBytes8_lt hd0 hd1 hd2 hd3 hd4 hd5 hd6 hd7
  constructor <;> omega

set_option maxHeartbeats 4000000 in
/-- **`UInt64::mul` on bytes, column by column**: given the column sums `Xₖ` (each the sum of
the limb products `(a₂ᵢ + 256 a₂ᵢ₊₁)(b₂ⱼ + 256 b₂ⱼ₊₁)` with `i + j = k` and the previous
column's carry `Xₖ₋₁ / 2^16`), all below `2^40`, and the last carry's top byte zero, the mirror
returns each column's low two bytes, then the last carry's low two bytes. -/
theorem u64Mul_run {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : ℕ}
    {X0 X1 X2 X3 X4 X5 X6 : ℕ}
    (hX0 : X0 < 1099511627776) (hX1 : X1 < 1099511627776) (hX2 : X2 < 1099511627776)
    (hX3 : X3 < 1099511627776) (hX4 : X4 < 1099511627776) (hX5 : X5 < 1099511627776)
    (hX6 : X6 < 1099511627776)
    (h0 : (a0 + 256 * a1) * (b0 + 256 * b1) = X0)
    (h1 : (a0 + 256 * a1) * (b2 + 256 * b3) + (a2 + 256 * a3) * (b0 + 256 * b1) + X0 / 65536 = X1)
    (h2 : (a0 + 256 * a1) * (b4 + 256 * b5) + (a2 + 256 * a3) * (b2 + 256 * b3) +
      (a4 + 256 * a5) * (b0 + 256 * b1) + X1 / 65536 = X2)
    (h3 : (a0 + 256 * a1) * (b6 + 256 * b7) + (a2 + 256 * a3) * (b4 + 256 * b5) +
      (a4 + 256 * a5) * (b2 + 256 * b3) + (a6 + 256 * a7) * (b0 + 256 * b1) + X2 / 65536 = X3)
    (h4 : (a2 + 256 * a3) * (b6 + 256 * b7) + (a4 + 256 * a5) * (b4 + 256 * b5) +
      (a6 + 256 * a7) * (b2 + 256 * b3) + X3 / 65536 = X4)
    (h5 : (a4 + 256 * a5) * (b6 + 256 * b7) + (a6 + 256 * a7) * (b4 + 256 * b5) + X4 / 65536 = X5)
    (h6 : (a6 + 256 * a7) * (b6 + 256 * b7) + X5 / 65536 = X6)
    (hc : X6 / 4294967296 % 256 = 0) (k : ℕ) (h : Heap F) :
    Mirrors.«UInt64::mul» (k + 2) h
        (.tuple [.field (a0 : F), .field (a1 : F), .field (a2 : F), .field (a3 : F),
          .field (a4 : F), .field (a5 : F), .field (a6 : F), .field (a7 : F)])
        (.tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F),
          .field (b4 : F), .field (b5 : F), .field (b6 : F), .field (b7 : F)]) =
      some (.tuple [
        .tuple [.field ((X0 % 256 : ℕ) : F), .field ((X0 / 256 % 256 : ℕ) : F),
          .field ((X1 % 256 : ℕ) : F), .field ((X1 / 256 % 256 : ℕ) : F),
          .field ((X2 % 256 : ℕ) : F), .field ((X2 / 256 % 256 : ℕ) : F),
          .field ((X3 % 256 : ℕ) : F), .field ((X3 / 256 % 256 : ℕ) : F)],
        .tuple [.field ((X4 % 256 : ℕ) : F), .field ((X4 / 256 % 256 : ℕ) : F),
          .field ((X5 % 256 : ℕ) : F), .field ((X5 / 256 % 256 : ℕ) : F),
          .field ((X6 % 256 : ℕ) : F), .field ((X6 / 256 % 256 : ℕ) : F),
          .field ((X6 / 65536 % 256 : ℕ) : F), .field ((X6 / 16777216 % 256 : ℕ) : F)]], h) := by
  -- each column sum, with the previous carry as its three bytes
  have n1 : X1 = (a0 + 256 * a1) * (b2 + 256 * b3) + (a2 + 256 * a3) * (b0 + 256 * b1) +
      X0 / 65536 % 256 + 256 * (X0 / 16777216 % 256) + 65536 * (X0 / 4294967296 % 256) := by
    omega
  have n2 : X2 = (a0 + 256 * a1) * (b4 + 256 * b5) + (a2 + 256 * a3) * (b2 + 256 * b3) +
      (a4 + 256 * a5) * (b0 + 256 * b1) +
      X1 / 65536 % 256 + 256 * (X1 / 16777216 % 256) + 65536 * (X1 / 4294967296 % 256) := by
    omega
  have n3 : X3 = (a0 + 256 * a1) * (b6 + 256 * b7) + (a2 + 256 * a3) * (b4 + 256 * b5) +
      (a4 + 256 * a5) * (b2 + 256 * b3) + (a6 + 256 * a7) * (b0 + 256 * b1) +
      X2 / 65536 % 256 + 256 * (X2 / 16777216 % 256) + 65536 * (X2 / 4294967296 % 256) := by
    omega
  have n4 : X4 = (a2 + 256 * a3) * (b6 + 256 * b7) + (a4 + 256 * a5) * (b4 + 256 * b5) +
      (a6 + 256 * a7) * (b2 + 256 * b3) +
      X3 / 65536 % 256 + 256 * (X3 / 16777216 % 256) + 65536 * (X3 / 4294967296 % 256) := by
    omega
  have n5 : X5 = (a4 + 256 * a5) * (b6 + 256 * b7) + (a6 + 256 * a7) * (b4 + 256 * b5) +
      X4 / 65536 % 256 + 256 * (X4 / 16777216 % 256) + 65536 * (X4 / 4294967296 % 256) := by
    omega
  have n6 : X6 = (a6 + 256 * a7) * (b6 + 256 * b7) +
      X5 / 65536 % 256 + 256 * (X5 / 16777216 % 256) + 65536 * (X5 / 4294967296 % 256) := by
    omega
  -- the last carry's top byte is zero
  have ea : ∀ m, Builtin.apply (.assertEq m)
      ([.field ((X6 / 4294967296 % 256 : ℕ) : F), .field 0] : List (SourceValue F)) =
        .ok (.tuple []) := by
    intro m
    rw [hc]
    simp [Builtin.apply, evalAssertEq, Value.pointerFree]
  -- the limbs, up to the first column
  simp (config := { maxSteps := 10000000 }) only [Mirrors.«UInt64::mul», projectValue,
    TagN.toField_run, evalBinOp, Mirrors.bindPair_some, matchTuple_tuple, bindCons_cons, bind,
    Except.bind, pure, Except.pure, List.getElem?_cons_succ, List.getElem?_cons_zero,
    List.length_cons, List.length_nil, eq_self_iff_true, ↓reduceIte]
  rw [mulColumn_of_eq (X := X0) ?_ hX0]
  swap
  · rw [← h0]
    push_cast <;> ring
  simp (config := { maxSteps := 10000000 }) only [projectValue, TagN.toField_run, evalBinOp,
    Mirrors.bindPair_some, matchTuple_tuple, bindCons_cons, bind,
    Except.bind, pure, Except.pure, List.getElem?_cons_succ, List.getElem?_cons_zero,
    List.length_cons, List.length_nil, eq_self_iff_true, ↓reduceIte]
  rw [mulColumn_of_eq (X := X1) ?_ hX1]
  swap
  · rw [n1]
    push_cast <;> ring
  simp (config := { maxSteps := 10000000 }) only [projectValue, TagN.toField_run, evalBinOp,
    Mirrors.bindPair_some, matchTuple_tuple, bindCons_cons, bind,
    Except.bind, pure, Except.pure, List.getElem?_cons_succ, List.getElem?_cons_zero,
    List.length_cons, List.length_nil, eq_self_iff_true, ↓reduceIte]
  rw [mulColumn_of_eq (X := X2) ?_ hX2]
  swap
  · rw [n2]
    push_cast <;> ring
  simp (config := { maxSteps := 10000000 }) only [projectValue, TagN.toField_run, evalBinOp,
    Mirrors.bindPair_some, matchTuple_tuple, bindCons_cons, bind,
    Except.bind, pure, Except.pure, List.getElem?_cons_succ, List.getElem?_cons_zero,
    List.length_cons, List.length_nil, eq_self_iff_true, ↓reduceIte]
  rw [mulColumn_of_eq (X := X3) ?_ hX3]
  swap
  · rw [n3]
    push_cast <;> ring
  simp (config := { maxSteps := 10000000 }) only [projectValue, TagN.toField_run, evalBinOp,
    Mirrors.bindPair_some, matchTuple_tuple, bindCons_cons, bind,
    Except.bind, pure, Except.pure, List.getElem?_cons_succ, List.getElem?_cons_zero,
    List.length_cons, List.length_nil, eq_self_iff_true, ↓reduceIte]
  rw [mulColumn_of_eq (X := X4) ?_ hX4]
  swap
  · rw [n4]
    push_cast <;> ring
  simp (config := { maxSteps := 10000000 }) only [projectValue, TagN.toField_run, evalBinOp,
    Mirrors.bindPair_some, matchTuple_tuple, bindCons_cons, bind,
    Except.bind, pure, Except.pure, List.getElem?_cons_succ, List.getElem?_cons_zero,
    List.length_cons, List.length_nil, eq_self_iff_true, ↓reduceIte]
  rw [mulColumn_of_eq (X := X5) ?_ hX5]
  swap
  · rw [n5]
    push_cast <;> ring
  simp (config := { maxSteps := 10000000 }) only [projectValue, TagN.toField_run, evalBinOp,
    Mirrors.bindPair_some, matchTuple_tuple, bindCons_cons, bind,
    Except.bind, pure, Except.pure, List.getElem?_cons_succ, List.getElem?_cons_zero,
    List.length_cons, List.length_nil, eq_self_iff_true, ↓reduceIte]
  rw [mulColumn_of_eq (X := X6) ?_ hX6]
  swap
  · rw [n6]
    push_cast <;> ring
  -- the assertion and the result
  simp (config := { maxSteps := 10000000 }) only [projectValue, TagN.toField_run, evalBinOp,
    ea, Mirrors.bindPair_some, matchTuple_tuple, bindCons_cons, bind,
    Except.bind, pure, Except.pure, List.getElem?_cons_succ, List.getElem?_cons_zero,
    List.length_cons, List.length_nil, eq_self_iff_true, ↓reduceIte]

set_option maxHeartbeats 4000000 in
/-- **`UInt64::mul` on eight bytes each**: the bytes of the product of their values modulo
`2^64`, and of its quotient by `2^64`. -/
theorem u64Mul_bytes {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : ℕ}
    (ha0 : a0 < 256) (ha1 : a1 < 256) (ha2 : a2 < 256) (ha3 : a3 < 256)
    (ha4 : a4 < 256) (ha5 : a5 < 256) (ha6 : a6 < 256) (ha7 : a7 < 256)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (hb4 : b4 < 256) (hb5 : b5 < 256) (hb6 : b6 < 256) (hb7 : b7 < 256) (k : ℕ) (h : Heap F) :
    Mirrors.«UInt64::mul» (k + 2) h
        (.tuple [.field (a0 : F), .field (a1 : F), .field (a2 : F), .field (a3 : F),
          .field (a4 : F), .field (a5 : F), .field (a6 : F), .field (a7 : F)])
        (.tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F),
          .field (b4 : F), .field (b5 : F), .field (b6 : F), .field (b7 : F)]) =
      some (.tuple [
        TagN.u64Value (Lib.leBytes8 a0 a1 a2 a3 a4 a5 a6 a7 *
          Lib.leBytes8 b0 b1 b2 b3 b4 b5 b6 b7 % 18446744073709551616),
        TagN.u64Value (Lib.leBytes8 a0 a1 a2 a3 a4 a5 a6 a7 *
          Lib.leBytes8 b0 b1 b2 b3 b4 b5 b6 b7 / 18446744073709551616)], h) := by
  -- the 16-bit limbs and their products
  have hA0 : a0 + 256 * a1 ≤ 65535 := by omega
  have hA1 : a2 + 256 * a3 ≤ 65535 := by omega
  have hA2 : a4 + 256 * a5 ≤ 65535 := by omega
  have hA3 : a6 + 256 * a7 ≤ 65535 := by omega
  have hB0 : b0 + 256 * b1 ≤ 65535 := by omega
  have hB1 : b2 + 256 * b3 ≤ 65535 := by omega
  have hB2 : b4 + 256 * b5 ≤ 65535 := by omega
  have hB3 : b6 + 256 * b7 ≤ 65535 := by omega
  have p00 := Nat.mul_le_mul hA0 hB0
  have p01 := Nat.mul_le_mul hA0 hB1
  have p02 := Nat.mul_le_mul hA0 hB2
  have p03 := Nat.mul_le_mul hA0 hB3
  have p10 := Nat.mul_le_mul hA1 hB0
  have p11 := Nat.mul_le_mul hA1 hB1
  have p12 := Nat.mul_le_mul hA1 hB2
  have p13 := Nat.mul_le_mul hA1 hB3
  have p20 := Nat.mul_le_mul hA2 hB0
  have p21 := Nat.mul_le_mul hA2 hB1
  have p22 := Nat.mul_le_mul hA2 hB2
  have p23 := Nat.mul_le_mul hA2 hB3
  have p30 := Nat.mul_le_mul hA3 hB0
  have p31 := Nat.mul_le_mul hA3 hB1
  have p32 := Nat.mul_le_mul hA3 hB2
  have p33 := Nat.mul_le_mul hA3 hB3
  -- the product, column by column
  have hL : Lib.leBytes8 a0 a1 a2 a3 a4 a5 a6 a7 * Lib.leBytes8 b0 b1 b2 b3 b4 b5 b6 b7 =
      (a0 + 256 * a1) * (b0 + 256 * b1) +
      65536 * ((a0 + 256 * a1) * (b2 + 256 * b3) + (a2 + 256 * a3) * (b0 + 256 * b1)) +
      4294967296 * ((a0 + 256 * a1) * (b4 + 256 * b5) + (a2 + 256 * a3) * (b2 + 256 * b3) +
        (a4 + 256 * a5) * (b0 + 256 * b1)) +
      281474976710656 * ((a0 + 256 * a1) * (b6 + 256 * b7) + (a2 + 256 * a3) * (b4 + 256 * b5) +
        (a4 + 256 * a5) * (b2 + 256 * b3) + (a6 + 256 * a7) * (b0 + 256 * b1)) +
      18446744073709551616 * ((a2 + 256 * a3) * (b6 + 256 * b7) +
        (a4 + 256 * a5) * (b4 + 256 * b5) + (a6 + 256 * a7) * (b2 + 256 * b3)) +
      1208925819614629174706176 * ((a4 + 256 * a5) * (b6 + 256 * b7) +
        (a6 + 256 * a7) * (b4 + 256 * b5)) +
      79228162514264337593543950336 * ((a6 + 256 * a7) * (b6 + 256 * b7)) := by
    unfold Lib.leBytes8
    ring
  have hLlt := Nat.mul_lt_mul_of_lt_of_lt (Lib.leBytes8_lt ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7)
    (Lib.leBytes8_lt hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7)
  generalize Lib.leBytes8 a0 a1 a2 a3 a4 a5 a6 a7 * Lib.leBytes8 b0 b1 b2 b3 b4 b5 b6 b7 = L
    at hL hLlt ⊢
  -- the column sums
  obtain ⟨X0, h0⟩ : ∃ X, (a0 + 256 * a1) * (b0 + 256 * b1) = X := ⟨_, rfl⟩
  obtain ⟨X1, h1⟩ : ∃ X, (a0 + 256 * a1) * (b2 + 256 * b3) + (a2 + 256 * a3) * (b0 + 256 * b1) +
      X0 / 65536 = X := ⟨_, rfl⟩
  obtain ⟨X2, h2⟩ : ∃ X, (a0 + 256 * a1) * (b4 + 256 * b5) + (a2 + 256 * a3) * (b2 + 256 * b3) +
      (a4 + 256 * a5) * (b0 + 256 * b1) + X1 / 65536 = X := ⟨_, rfl⟩
  obtain ⟨X3, h3⟩ : ∃ X, (a0 + 256 * a1) * (b6 + 256 * b7) + (a2 + 256 * a3) * (b4 + 256 * b5) +
      (a4 + 256 * a5) * (b2 + 256 * b3) + (a6 + 256 * a7) * (b0 + 256 * b1) +
      X2 / 65536 = X := ⟨_, rfl⟩
  obtain ⟨X4, h4⟩ : ∃ X, (a2 + 256 * a3) * (b6 + 256 * b7) + (a4 + 256 * a5) * (b4 + 256 * b5) +
      (a6 + 256 * a7) * (b2 + 256 * b3) + X3 / 65536 = X := ⟨_, rfl⟩
  obtain ⟨X5, h5⟩ : ∃ X, (a4 + 256 * a5) * (b6 + 256 * b7) + (a6 + 256 * a7) * (b4 + 256 * b5) +
      X4 / 65536 = X := ⟨_, rfl⟩
  obtain ⟨X6, h6⟩ : ∃ X, (a6 + 256 * a7) * (b6 + 256 * b7) + X5 / 65536 = X := ⟨_, rfl⟩
  have hX0 : X0 < 1099511627776 := by omega
  have hX1 : X1 < 1099511627776 := by omega
  have hX2 : X2 < 1099511627776 := by omega
  have hX3 : X3 < 1099511627776 := by omega
  have hX4 : X4 < 1099511627776 := by omega
  have hX5 : X5 < 1099511627776 := by omega
  have hX6 : X6 < 1099511627776 := by omega
  -- the digits and the last carry make up the product
  have hT1 : L = X0 % 65536 + 65536 * (X1 % 65536) + 4294967296 * (X2 % 65536) +
      281474976710656 * (X3 % 65536) + 18446744073709551616 * (X4 % 65536) +
      1208925819614629174706176 * (X5 % 65536) + 79228162514264337593543950336 * (X6 % 65536) +
      5192296858534827628530496329220096 * (X6 / 65536) := by
    omega
  have hC6 : X6 / 65536 < 65536 := by omega
  have hc : X6 / 4294967296 % 256 = 0 := by omega
  have r0 : X0 % 65536 = X0 % 256 + 256 * (X0 / 256 % 256) := by omega
  have r1 : X1 % 65536 = X1 % 256 + 256 * (X1 / 256 % 256) := by omega
  have r2 : X2 % 65536 = X2 % 256 + 256 * (X2 / 256 % 256) := by omega
  have r3 : X3 % 65536 = X3 % 256 + 256 * (X3 / 256 % 256) := by omega
  have r4 : X4 % 65536 = X4 % 256 + 256 * (X4 / 256 % 256) := by omega
  have r5 : X5 % 65536 = X5 % 256 + 256 * (X5 / 256 % 256) := by omega
  have r6 : X6 % 65536 = X6 % 256 + 256 * (X6 / 256 % 256) := by omega
  have c6 : X6 / 65536 = X6 / 65536 % 256 + 256 * (X6 / 16777216 % 256) := by omega
  rw [r0, r1, r2, r3, r4, r5, r6, c6] at hT1
  have hT : L = Lib.leBytes8 (X0 % 256) (X0 / 256 % 256) (X1 % 256) (X1 / 256 % 256)
        (X2 % 256) (X2 / 256 % 256) (X3 % 256) (X3 / 256 % 256) +
      18446744073709551616 * Lib.leBytes8 (X4 % 256) (X4 / 256 % 256) (X5 % 256)
        (X5 / 256 % 256) (X6 % 256) (X6 / 256 % 256) (X6 / 65536 % 256)
        (X6 / 16777216 % 256) := by
    rw [hT1]
    unfold Lib.leBytes8
    ring
  obtain ⟨hlo, hhi⟩ := leBytes8_split (byte_lt X0) (byte_lt (X0 / 256)) (byte_lt X1)
    (byte_lt (X1 / 256)) (byte_lt X2) (byte_lt (X2 / 256)) (byte_lt X3) (byte_lt (X3 / 256)) hT
  rw [u64Mul_run hX0 hX1 hX2 hX3 hX4 hX5 hX6 h0 h1 h2 h3 h4 h5 h6 hc k h, hlo, hhi,
    Lib.u64Value_leBytes8 (byte_lt X0) (byte_lt (X0 / 256)) (byte_lt X1) (byte_lt (X1 / 256))
      (byte_lt X2) (byte_lt (X2 / 256)) (byte_lt X3) (byte_lt (X3 / 256)),
    Lib.u64Value_leBytes8 (byte_lt X4) (byte_lt (X4 / 256)) (byte_lt X5) (byte_lt (X5 / 256))
      (byte_lt X6) (byte_lt (X6 / 256)) (byte_lt (X6 / 65536)) (byte_lt (X6 / 16777216))]

/-- **`UInt64::mul` is the full 64-bit product**: the product modulo `2^64` (the low word) and
its quotient by `2^64` (the high word, itself below `2^64`). -/
theorem u64Mul_value {x y : ℕ} (hx : x < 18446744073709551616) (hy : y < 18446744073709551616)
    (k : ℕ) (h : Heap F) :
    Mirrors.«UInt64::mul» (k + 2) h (TagN.u64Value x) (TagN.u64Value y) =
      some (.tuple [TagN.u64Value (x * y % 18446744073709551616),
        TagN.u64Value (x * y / 18446744073709551616)], h) := by
  have run := u64Mul_bytes
    (a0 := x % 256) (b0 := y % 256)
    (a1 := x / 256 % 256) (b1 := y / 256 % 256)
    (a2 := x / 65536 % 256) (b2 := y / 65536 % 256)
    (a3 := x / 16777216 % 256) (b3 := y / 16777216 % 256)
    (a4 := x / 4294967296 % 256) (b4 := y / 4294967296 % 256)
    (a5 := x / 1099511627776 % 256) (b5 := y / 1099511627776 % 256)
    (a6 := x / 281474976710656 % 256) (b6 := y / 281474976710656 % 256)
    (a7 := x / 72057594037927936 % 256) (b7 := y / 72057594037927936 % 256)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) k h
  rw [Lib.leBytes8_bytes hx, Lib.leBytes8_bytes hy] at run
  simp only [TagN.u64Value] at run ⊢
  exact run

/-! ## `UInt64::mul` -/

/-- **`UInt64::mul(x, y)`** on two words: the low and high words of their full product (the
product modulo `2^64` and its quotient by `2^64`); no allocation. Whatever the column hints, a
derivation computes the product. -/
theorem u64_mul_spec {x y r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {v w : UInt64} (hx : RepU64 h v x) (hy : RepU64 h w y)
    (ev : ObsFn W "UInt64::mul" [x, y] h r h' cs) :
    r = .tuple [TagN.u64Value (v.toNat * w.toNat % 18446744073709551616),
      TagN.u64Value (v.toNat * w.toNat / 18446744073709551616)] ∧ h' = h := by
  obtain rfl := Lib.repU64_eq hx
  obtain rfl := Lib.repU64_eq hy
  obtain ⟨k0, hk0⟩ := Mirrors.«UInt64::mul».of_eval mulColumn_complete ev.erase
  have run := hk0 (k0 + 2) (by omega)
  rw [u64Mul_value (Lib.u64_toNat_lt v) (Lib.u64_toNat_lt w) k0 h, Option.some.injEq,
    Prod.mk.injEq] at run
  exact ⟨run.1.symm, run.2.symm⟩

end IxVM.Refinement.NatLib
