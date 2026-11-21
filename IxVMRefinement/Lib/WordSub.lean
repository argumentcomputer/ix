import IxVMRefinement.Lib.Words

/-! # `UInt64::sub_with_borrow`, over observed derivations

The subtraction is a ripple of `UInt8::split_sum` steps over the bytes: byte `0` splits
`a₀ + 256 - b₀`, byte `i` splits `aᵢ + 255 - bᵢ + cᵢ` with the previous carry, and the borrow
is `1 - c₈`. The digits and carries of that ripple exist for any bytes (`sub_ripple`), and
their value is `a + 2^64 - b` (the weighted sum of the digit equations), so the digits are
the difference modulo `2^64` and the last carry is `0` exactly when the subtrahend is the
larger. `leBytes8` is the value of eight bytes, least significant first. -/

namespace IxVM.Refinement.Lib

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library
open IxVM.Refinement.Obs (W)
open IxVM (F)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## Eight bytes -/

/-- The value of eight bytes, least significant first. -/
def leBytes8 (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) : Nat :=
  b0 + 256 * b1 + 65536 * b2 + 16777216 * b3 + 4294967296 * b4 + 1099511627776 * b5 +
    281474976710656 * b6 + 72057594037927936 * b7

theorem leBytes8_lt {b0 b1 b2 b3 b4 b5 b6 b7 : Nat} (h0 : b0 < 256) (h1 : b1 < 256)
    (h2 : b2 < 256) (h3 : b3 < 256) (h4 : b4 < 256) (h5 : b5 < 256) (h6 : b6 < 256)
    (h7 : b7 < 256) : leBytes8 b0 b1 b2 b3 b4 b5 b6 b7 < 18446744073709551616 := by
  unfold leBytes8
  omega

/-- Eight bytes are the byte tuple of their value. -/
theorem u64Value_leBytes8 {b0 b1 b2 b3 b4 b5 b6 b7 : Nat} (h0 : b0 < 256) (h1 : b1 < 256)
    (h2 : b2 < 256) (h3 : b3 < 256) (h4 : b4 < 256) (h5 : b5 < 256) (h6 : b6 < 256)
    (h7 : b7 < 256) :
    TagN.u64Value (leBytes8 b0 b1 b2 b3 b4 b5 b6 b7) =
      .tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F),
        .field (b4 : F), .field (b5 : F), .field (b6 : F), .field (b7 : F)] := by
  have f0 : leBytes8 b0 b1 b2 b3 b4 b5 b6 b7 % 256 = b0 := by unfold leBytes8; omega
  have f1 : leBytes8 b0 b1 b2 b3 b4 b5 b6 b7 / 256 % 256 = b1 := by unfold leBytes8; omega
  have f2 : leBytes8 b0 b1 b2 b3 b4 b5 b6 b7 / 65536 % 256 = b2 := by unfold leBytes8; omega
  have f3 : leBytes8 b0 b1 b2 b3 b4 b5 b6 b7 / 16777216 % 256 = b3 := by unfold leBytes8; omega
  have f4 : leBytes8 b0 b1 b2 b3 b4 b5 b6 b7 / 4294967296 % 256 = b4 := by unfold leBytes8; omega
  have f5 : leBytes8 b0 b1 b2 b3 b4 b5 b6 b7 / 1099511627776 % 256 = b5 := by
    unfold leBytes8; omega
  have f6 : leBytes8 b0 b1 b2 b3 b4 b5 b6 b7 / 281474976710656 % 256 = b6 := by
    unfold leBytes8; omega
  have f7 : leBytes8 b0 b1 b2 b3 b4 b5 b6 b7 / 72057594037927936 % 256 = b7 := by
    unfold leBytes8; omega
  simp only [TagN.u64Value, f0, f1, f2, f3, f4, f5, f6, f7]

set_option maxHeartbeats 1000000 in
/-- A natural below `2^64` is the value of its eight bytes. -/
theorem leBytes8_bytes {x : Nat} (hx : x < 18446744073709551616) :
    leBytes8 (x % 256) (x / 256 % 256) (x / 65536 % 256) (x / 16777216 % 256)
      (x / 4294967296 % 256) (x / 1099511627776 % 256) (x / 281474976710656 % 256)
      (x / 72057594037927936 % 256) = x := by
  have d2 : x / 65536 = x / 256 / 256 := by omega
  have d3 : x / 16777216 = x / 65536 / 256 := by omega
  have d4 : x / 4294967296 = x / 16777216 / 256 := by omega
  have d5 : x / 1099511627776 = x / 4294967296 / 256 := by omega
  have d6 : x / 281474976710656 = x / 1099511627776 / 256 := by omega
  have d7 : x / 72057594037927936 = x / 281474976710656 / 256 := by omega
  have d8 : x / 72057594037927936 / 256 = 0 := by omega
  unfold leBytes8
  omega

/-! ## The ripple -/


/-- **The ripple of a subtraction**: for any bytes there are digits `s` and carries `c` with
`a₀ + 256 = b₀ + s₀ + 256 c₁` and `aᵢ + 255 + cᵢ = bᵢ + sᵢ + 256 cᵢ₊₁`; their value, with the last
carry, is `a + 2^64 - b`. -/
theorem sub_ripple {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256) (hb4 : b4 < 256) (hb5 : b5 < 256) (hb6 : b6 < 256) (hb7 : b7 < 256) :
    ∃ s0 s1 s2 s3 s4 s5 s6 s7 c1 c2 c3 c4 c5 c6 c7 c8 : Nat,
      s0 < 256 ∧ s1 < 256 ∧ s2 < 256 ∧ s3 < 256 ∧ s4 < 256 ∧ s5 < 256 ∧ s6 < 256 ∧ s7 < 256 ∧
      a0 + 256 = b0 + s0 + 256 * c1 ∧
      a1 + 255 + c1 = b1 + s1 + 256 * c2 ∧
      a2 + 255 + c2 = b2 + s2 + 256 * c3 ∧
      a3 + 255 + c3 = b3 + s3 + 256 * c4 ∧
      a4 + 255 + c4 = b4 + s4 + 256 * c5 ∧
      a5 + 255 + c5 = b5 + s5 + 256 * c6 ∧
      a6 + 255 + c6 = b6 + s6 + 256 * c7 ∧
      a7 + 255 + c7 = b7 + s7 + 256 * c8 ∧
      leBytes8 s0 s1 s2 s3 s4 s5 s6 s7 + 18446744073709551616 * c8 + leBytes8 b0 b1 b2 b3 b4 b5 b6 b7 =
        leBytes8 a0 a1 a2 a3 a4 a5 a6 a7 + 18446744073709551616 := by
  obtain ⟨s0, c1, hs0, h0⟩ : ∃ s c, s < 256 ∧ a0 + 256 = b0 + s + 256 * c :=
    ⟨(a0 + 256 - b0) % 256, (a0 + 256 - b0) / 256, by omega, by omega⟩
  obtain ⟨s1, c2, hs1, h1⟩ : ∃ s c, s < 256 ∧ a1 + 255 + c1 = b1 + s + 256 * c :=
    ⟨(a1 + 255 + c1 - b1) % 256, (a1 + 255 + c1 - b1) / 256, by omega, by omega⟩
  obtain ⟨s2, c3, hs2, h2⟩ : ∃ s c, s < 256 ∧ a2 + 255 + c2 = b2 + s + 256 * c :=
    ⟨(a2 + 255 + c2 - b2) % 256, (a2 + 255 + c2 - b2) / 256, by omega, by omega⟩
  obtain ⟨s3, c4, hs3, h3⟩ : ∃ s c, s < 256 ∧ a3 + 255 + c3 = b3 + s + 256 * c :=
    ⟨(a3 + 255 + c3 - b3) % 256, (a3 + 255 + c3 - b3) / 256, by omega, by omega⟩
  obtain ⟨s4, c5, hs4, h4⟩ : ∃ s c, s < 256 ∧ a4 + 255 + c4 = b4 + s + 256 * c :=
    ⟨(a4 + 255 + c4 - b4) % 256, (a4 + 255 + c4 - b4) / 256, by omega, by omega⟩
  obtain ⟨s5, c6, hs5, h5⟩ : ∃ s c, s < 256 ∧ a5 + 255 + c5 = b5 + s + 256 * c :=
    ⟨(a5 + 255 + c5 - b5) % 256, (a5 + 255 + c5 - b5) / 256, by omega, by omega⟩
  obtain ⟨s6, c7, hs6, h6⟩ : ∃ s c, s < 256 ∧ a6 + 255 + c6 = b6 + s + 256 * c :=
    ⟨(a6 + 255 + c6 - b6) % 256, (a6 + 255 + c6 - b6) / 256, by omega, by omega⟩
  obtain ⟨s7, c8, hs7, h7⟩ : ∃ s c, s < 256 ∧ a7 + 255 + c7 = b7 + s + 256 * c :=
    ⟨(a7 + 255 + c7 - b7) % 256, (a7 + 255 + c7 - b7) / 256, by omega, by omega⟩
  refine ⟨s0, s1, s2, s3, s4, s5, s6, s7, c1, c2, c3, c4, c5, c6, c7, c8, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, h0, h1, h2, h3, h4, h5, h6, h7, ?_⟩
  unfold leBytes8
  omega

set_option maxHeartbeats 1000000 in
/-- **`UInt64::sub_with_borrow` on bytes**: given the ripple's digits `s` and carries `c`, the
mirror returns the digits and the borrow `1 - c₈`. -/
theorem u64SubBorrow_run {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    {s0 s1 s2 s3 s4 s5 s6 s7 c1 c2 c3 c4 c5 c6 c7 c8 : Nat}
    (ha0 : a0 < 256) (ha1 : a1 < 256) (ha2 : a2 < 256) (ha3 : a3 < 256) (ha4 : a4 < 256) (ha5 : a5 < 256) (ha6 : a6 < 256) (ha7 : a7 < 256)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256) (hb4 : b4 < 256) (hb5 : b5 < 256) (hb6 : b6 < 256) (hb7 : b7 < 256)
    (hs0 : s0 < 256) (hs1 : s1 < 256) (hs2 : s2 < 256) (hs3 : s3 < 256) (hs4 : s4 < 256) (hs5 : s5 < 256) (hs6 : s6 < 256) (hs7 : s7 < 256)
    (h0 : a0 + 256 = b0 + s0 + 256 * c1)
    (h1 : a1 + 255 + c1 = b1 + s1 + 256 * c2)
    (h2 : a2 + 255 + c2 = b2 + s2 + 256 * c3)
    (h3 : a3 + 255 + c3 = b3 + s3 + 256 * c4)
    (h4 : a4 + 255 + c4 = b4 + s4 + 256 * c5)
    (h5 : a5 + 255 + c5 = b5 + s5 + 256 * c6)
    (h6 : a6 + 255 + c6 = b6 + s6 + 256 * c7)
    (h7 : a7 + 255 + c7 = b7 + s7 + 256 * c8)
    (k : Nat) (h : Heap F) :
    Mirrors.«UInt64::sub_with_borrow» (k + 2) h
        (.tuple [.field (a0 : F), .field (a1 : F), .field (a2 : F), .field (a3 : F), .field (a4 : F), .field (a5 : F), .field (a6 : F), .field (a7 : F)])
        (.tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F), .field (b4 : F), .field (b5 : F), .field (b6 : F), .field (b7 : F)]) =
      some (.tuple [.tuple [.field (s0 : F), .field (s1 : F), .field (s2 : F), .field (s3 : F), .field (s4 : F), .field (s5 : F), .field (s6 : F), .field (s7 : F)],
        .field (1 - (c8 : F))], h) := by
  have e0 : Mirrors.«UInt8::split_sum» (k + 1) h (.field ((a0 : F) + 256 - (b0 : F))) =
      some (.tuple [.field (s0 : F), .field (c1 : F)], h) := by
    have hc : ((a0 + 256 - b0 : Nat) : F) = (a0 : F) + 256 - (b0 : F) := by
      rw [Nat.cast_sub (show b0 ≤ a0 + 256 by omega), Nat.cast_add, Nat.cast_ofNat]
    rw [← hc, show s0 = (a0 + 256 - b0) % 256 by omega, show c1 = (a0 + 256 - b0) / 256 by omega]
    exact TagN.splitSum_run (by omega) k h
  have e1 : Mirrors.«UInt8::split_sum» (k + 1) h (.field ((a1 : F) + 255 - (b1 : F) + (c1 : F))) =
      some (.tuple [.field (s1 : F), .field (c2 : F)], h) := by
    have hc : ((a1 + 255 - b1 + c1 : Nat) : F) = (a1 : F) + 255 - (b1 : F) + (c1 : F) := by
      rw [Nat.cast_add, Nat.cast_sub (show b1 ≤ a1 + 255 by omega), Nat.cast_add, Nat.cast_ofNat]
    rw [← hc, show s1 = (a1 + 255 - b1 + c1) % 256 by omega,
      show c2 = (a1 + 255 - b1 + c1) / 256 by omega]
    exact TagN.splitSum_run (by omega) k h
  have e2 : Mirrors.«UInt8::split_sum» (k + 1) h (.field ((a2 : F) + 255 - (b2 : F) + (c2 : F))) =
      some (.tuple [.field (s2 : F), .field (c3 : F)], h) := by
    have hc : ((a2 + 255 - b2 + c2 : Nat) : F) = (a2 : F) + 255 - (b2 : F) + (c2 : F) := by
      rw [Nat.cast_add, Nat.cast_sub (show b2 ≤ a2 + 255 by omega), Nat.cast_add, Nat.cast_ofNat]
    rw [← hc, show s2 = (a2 + 255 - b2 + c2) % 256 by omega,
      show c3 = (a2 + 255 - b2 + c2) / 256 by omega]
    exact TagN.splitSum_run (by omega) k h
  have e3 : Mirrors.«UInt8::split_sum» (k + 1) h (.field ((a3 : F) + 255 - (b3 : F) + (c3 : F))) =
      some (.tuple [.field (s3 : F), .field (c4 : F)], h) := by
    have hc : ((a3 + 255 - b3 + c3 : Nat) : F) = (a3 : F) + 255 - (b3 : F) + (c3 : F) := by
      rw [Nat.cast_add, Nat.cast_sub (show b3 ≤ a3 + 255 by omega), Nat.cast_add, Nat.cast_ofNat]
    rw [← hc, show s3 = (a3 + 255 - b3 + c3) % 256 by omega,
      show c4 = (a3 + 255 - b3 + c3) / 256 by omega]
    exact TagN.splitSum_run (by omega) k h
  have e4 : Mirrors.«UInt8::split_sum» (k + 1) h (.field ((a4 : F) + 255 - (b4 : F) + (c4 : F))) =
      some (.tuple [.field (s4 : F), .field (c5 : F)], h) := by
    have hc : ((a4 + 255 - b4 + c4 : Nat) : F) = (a4 : F) + 255 - (b4 : F) + (c4 : F) := by
      rw [Nat.cast_add, Nat.cast_sub (show b4 ≤ a4 + 255 by omega), Nat.cast_add, Nat.cast_ofNat]
    rw [← hc, show s4 = (a4 + 255 - b4 + c4) % 256 by omega,
      show c5 = (a4 + 255 - b4 + c4) / 256 by omega]
    exact TagN.splitSum_run (by omega) k h
  have e5 : Mirrors.«UInt8::split_sum» (k + 1) h (.field ((a5 : F) + 255 - (b5 : F) + (c5 : F))) =
      some (.tuple [.field (s5 : F), .field (c6 : F)], h) := by
    have hc : ((a5 + 255 - b5 + c5 : Nat) : F) = (a5 : F) + 255 - (b5 : F) + (c5 : F) := by
      rw [Nat.cast_add, Nat.cast_sub (show b5 ≤ a5 + 255 by omega), Nat.cast_add, Nat.cast_ofNat]
    rw [← hc, show s5 = (a5 + 255 - b5 + c5) % 256 by omega,
      show c6 = (a5 + 255 - b5 + c5) / 256 by omega]
    exact TagN.splitSum_run (by omega) k h
  have e6 : Mirrors.«UInt8::split_sum» (k + 1) h (.field ((a6 : F) + 255 - (b6 : F) + (c6 : F))) =
      some (.tuple [.field (s6 : F), .field (c7 : F)], h) := by
    have hc : ((a6 + 255 - b6 + c6 : Nat) : F) = (a6 : F) + 255 - (b6 : F) + (c6 : F) := by
      rw [Nat.cast_add, Nat.cast_sub (show b6 ≤ a6 + 255 by omega), Nat.cast_add, Nat.cast_ofNat]
    rw [← hc, show s6 = (a6 + 255 - b6 + c6) % 256 by omega,
      show c7 = (a6 + 255 - b6 + c6) / 256 by omega]
    exact TagN.splitSum_run (by omega) k h
  have e7 : Mirrors.«UInt8::split_sum» (k + 1) h (.field ((a7 : F) + 255 - (b7 : F) + (c7 : F))) =
      some (.tuple [.field (s7 : F), .field (c8 : F)], h) := by
    have hc : ((a7 + 255 - b7 + c7 : Nat) : F) = (a7 : F) + 255 - (b7 : F) + (c7 : F) := by
      rw [Nat.cast_add, Nat.cast_sub (show b7 ≤ a7 + 255 by omega), Nat.cast_add, Nat.cast_ofNat]
    rw [← hc, show s7 = (a7 + 255 - b7 + c7) % 256 by omega,
      show c8 = (a7 + 255 - b7 + c7) / 256 by omega]
    exact TagN.splitSum_run (by omega) k h
  simp only [Mirrors.«UInt64::sub_with_borrow», projectValue, TagN.toField_run, evalBinOp, e0, e1,
    e2, e3, e4, e5, e6, e7, bind, Except.bind, pure, Except.pure, Option.bind,
    List.getElem?_cons_succ, List.getElem?_cons_zero]

/-- **`UInt64::sub_with_borrow` on eight bytes each**: the bytes of the difference of their
values modulo `2^64`, and `1` exactly when the subtrahend is the larger. -/
theorem u64SubBorrow_bytes {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    (ha0 : a0 < 256) (ha1 : a1 < 256) (ha2 : a2 < 256) (ha3 : a3 < 256) (ha4 : a4 < 256) (ha5 : a5 < 256) (ha6 : a6 < 256) (ha7 : a7 < 256)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256) (hb4 : b4 < 256) (hb5 : b5 < 256) (hb6 : b6 < 256) (hb7 : b7 < 256) (k : Nat) (h : Heap F) :
    Mirrors.«UInt64::sub_with_borrow» (k + 2) h
        (.tuple [.field (a0 : F), .field (a1 : F), .field (a2 : F), .field (a3 : F), .field (a4 : F), .field (a5 : F), .field (a6 : F), .field (a7 : F)])
        (.tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F), .field (b4 : F), .field (b5 : F), .field (b6 : F), .field (b7 : F)]) =
      some (.tuple [TagN.u64Value ((leBytes8 a0 a1 a2 a3 a4 a5 a6 a7 + 18446744073709551616 -
          leBytes8 b0 b1 b2 b3 b4 b5 b6 b7) % 18446744073709551616),
        .field (if leBytes8 a0 a1 a2 a3 a4 a5 a6 a7 < leBytes8 b0 b1 b2 b3 b4 b5 b6 b7 then 1 else 0)], h) := by
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, c1, c2, c3, c4, c5, c6, c7, c8, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, h0, h1, h2, h3, h4, h5, h6, h7, hsum⟩ :=
    sub_ripple (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3) (a4 := a4) (a5 := a5) (a6 := a6) (a7 := a7)
      hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  have hX := leBytes8_lt ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
  have hY := leBytes8_lt hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  have hlt := leBytes8_lt hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7
  have hS : leBytes8 s0 s1 s2 s3 s4 s5 s6 s7 =
      (leBytes8 a0 a1 a2 a3 a4 a5 a6 a7 + 18446744073709551616 - leBytes8 b0 b1 b2 b3 b4 b5 b6 b7) % 18446744073709551616 := by
    omega
  have hb : (1 : F) - (c8 : F) =
      if leBytes8 a0 a1 a2 a3 a4 a5 a6 a7 < leBytes8 b0 b1 b2 b3 b4 b5 b6 b7 then 1 else 0 := by
    by_cases hxy : leBytes8 a0 a1 a2 a3 a4 a5 a6 a7 < leBytes8 b0 b1 b2 b3 b4 b5 b6 b7
    · have hc : c8 = 0 := by omega
      rw [hc, ite_eq_left hxy, Nat.cast_zero, sub_zero]
    · have hc : c8 = 1 := by omega
      rw [hc, ite_eq_right hxy, Nat.cast_one, sub_self]
  rw [← hS, u64Value_leBytes8 hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7, ← hb]
  exact u64SubBorrow_run ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 h0 h1 h2 h3 h4 h5 h6 h7 k h

/-- **`UInt64::sub_with_borrow` is 64-bit subtraction with a borrow**: the difference modulo
`2^64`, and `1` exactly when the subtrahend is the larger. -/
theorem u64SubBorrow_value {x y : Nat} (hx : x < 18446744073709551616)
    (hy : y < 18446744073709551616) (k : Nat) (h : Heap F) :
    Mirrors.«UInt64::sub_with_borrow» (k + 2) h (TagN.u64Value x) (TagN.u64Value y) =
      some (.tuple [TagN.u64Value ((x + 18446744073709551616 - y) % 18446744073709551616),
        .field (if x < y then 1 else 0)], h) := by
  have run := u64SubBorrow_bytes
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
  rw [leBytes8_bytes hx, leBytes8_bytes hy] at run
  simp only [TagN.u64Value] at run ⊢
  exact run

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

end IxVM.Refinement.Lib
