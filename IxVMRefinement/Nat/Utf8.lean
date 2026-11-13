import IxVMRefinement.Core.Registry
import IxVMRefinement.Obs.KernelNatPrim
import IxVMRefinement.Lib.Words
import IxVMRefinement.Lib.Lists
import Mathlib.Tactic.Ring

/-! # UTF-8 and string literals: `KernelNatPrim`'s decoder against Lean's `String`

A string literal's bytes are related to the string by `StrBytes` (`String.fromUTF8?`, as the
kernel reader decodes a literal's blob). At this toolchain a `String` is a byte array with a proof
that it is `List.utf8Encode m` for a list of characters `m`, the concatenation of the characters'
encodings (`String.utf8EncodeChar`). This file proves:

* **The encodings the decoder reads** (`encode_one` … `encode_four`): a lead byte and its
  continuation bytes in the ranges `utf8_decode_one` accepts are the encoding of the character
  whose code point the circuit computes.
* **The term seam's string relation** (`strBytes_ofList`, `strBytes_eq_ofList`,
  `exists_strBytes_iff`): bytes decode to a string exactly when they are the concatenated
  encodings of a character list, and the string is then `String.ofList` of it.
* **The constructor form** (`strLitToConstructor_ofList`): the kernel's expansion of
  `String.ofList cs` is `charList` of `cs`.
* **The step lemmas** of `utf8_cont`, `utf8_decode_one`, `utf8_validate` and `build_char_list`
  against their registered specs. The decoder allocates nothing; its code point is computed in
  the field and is the cast of the natural code point (no wrap: every value is below `2^22`). -/

namespace IxVM.Refinement.Core.Utf8Aux

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List

set_option linter.unusedVariables false

/-! ## Characters and their encodings -/

/-- `String.utf8EncodeChar`, read off the code point. -/
theorem utf8EncodeChar_eq (c : Char) : String.utf8EncodeChar c =
    if c.toNat ≤ 127 then [UInt8.ofNat c.toNat]
    else if c.toNat ≤ 2047 then
      [UInt8.ofNat (c.toNat / 64 % 32 + 192), UInt8.ofNat (c.toNat % 64 + 128)]
    else if c.toNat ≤ 65535 then
      [UInt8.ofNat (c.toNat / 4096 % 16 + 224), UInt8.ofNat (c.toNat / 64 % 64 + 128),
        UInt8.ofNat (c.toNat % 64 + 128)]
    else
      [UInt8.ofNat (c.toNat / 262144 % 8 + 240), UInt8.ofNat (c.toNat / 4096 % 64 + 128),
        UInt8.ofNat (c.toNat / 64 % 64 + 128), UInt8.ofNat (c.toNat % 64 + 128)] := rfl

theorem toNat_ofNatAux (n : Nat) (h : n.isValidChar) : (Char.ofNatAux n h).toNat = n := rfl

/-- Every code point is below `0x110000`. -/
theorem char_toNat_lt (ch : Char) : ch.toNat < 1114112 := by
  have hv : ch.val.toNat.isValidChar := ch.valid
  show ch.val.toNat < 1114112
  rcases hv with hv | ⟨-, hv⟩ <;> omega

/-- **One byte**: an ASCII byte is the encoding of the character with that code point. -/
theorem encode_one {b0 : UInt8} (h0 : b0.toNat < 128) :
    ∃ ch : Char, ch.toNat = b0.toNat ∧ String.utf8EncodeChar ch = [b0] := by
  refine ⟨Char.ofNatAux b0.toNat (Or.inl (by omega)), rfl, ?_⟩
  rw [utf8EncodeChar_eq, toNat_ofNatAux, ite_eq_left (show b0.toNat ≤ 127 by omega),
    UInt8.ofNat_toNat]

/-- **Two bytes**: a lead byte in `[0xC2, 0xE0)` and a continuation byte. -/
theorem encode_two {b0 b1 : UInt8} (h0 : 194 ≤ b0.toNat) (h0' : b0.toNat < 224)
    (h1 : 128 ≤ b1.toNat) (h1' : b1.toNat < 192) :
    ∃ ch : Char, ch.toNat = (b0.toNat - 192) * 64 + (b1.toNat - 128) ∧
      String.utf8EncodeChar ch = [b0, b1] := by
  generalize hn : (b0.toNat - 192) * 64 + (b1.toNat - 128) = n
  refine ⟨Char.ofNatAux n (Or.inl (by omega)), rfl, ?_⟩
  rw [utf8EncodeChar_eq, toNat_ofNatAux, ite_eq_right (show ¬ n ≤ 127 by omega),
    ite_eq_left (show n ≤ 2047 by omega), show n / 64 % 32 + 192 = b0.toNat by omega,
    show n % 64 + 128 = b1.toNat by omega, UInt8.ofNat_toNat, UInt8.ofNat_toNat]

/-- **Three bytes**: a lead byte in `[0xE0, 0xF0)`, two continuation bytes, the code point not
overlong (`2048 ≤ cp`) and not a surrogate. -/
theorem encode_three {b0 b1 b2 : UInt8} (h0 : 224 ≤ b0.toNat) (h0' : b0.toNat < 240)
    (h1 : 128 ≤ b1.toNat) (h1' : b1.toNat < 192) (h2 : 128 ≤ b2.toNat) (h2' : b2.toNat < 192)
    (hlo : 2048 ≤ (b0.toNat - 224) * 4096 + (b1.toNat - 128) * 64 + (b2.toNat - 128))
    (hs : (b0.toNat - 224) * 4096 + (b1.toNat - 128) * 64 + (b2.toNat - 128) < 55296 ∨
      57344 ≤ (b0.toNat - 224) * 4096 + (b1.toNat - 128) * 64 + (b2.toNat - 128)) :
    ∃ ch : Char, ch.toNat = (b0.toNat - 224) * 4096 + (b1.toNat - 128) * 64 + (b2.toNat - 128) ∧
      String.utf8EncodeChar ch = [b0, b1, b2] := by
  generalize hn : (b0.toNat - 224) * 4096 + (b1.toNat - 128) * 64 + (b2.toNat - 128) = n
    at hlo hs ⊢
  have hv : n.isValidChar := by
    rcases hs with hs | hs
    · exact Or.inl hs
    · exact Or.inr ⟨by omega, by omega⟩
  refine ⟨Char.ofNatAux n hv, rfl, ?_⟩
  rw [utf8EncodeChar_eq, toNat_ofNatAux, ite_eq_right (show ¬ n ≤ 127 by omega),
    ite_eq_right (show ¬ n ≤ 2047 by omega), ite_eq_left (show n ≤ 65535 by omega),
    show n / 4096 % 16 + 224 = b0.toNat by omega, show n / 64 % 64 + 128 = b1.toNat by omega,
    show n % 64 + 128 = b2.toNat by omega, UInt8.ofNat_toNat, UInt8.ofNat_toNat,
    UInt8.ofNat_toNat]

/-- **Four bytes**: a lead byte from `0xF0`, three continuation bytes, the code point not
overlong (`65536 ≤ cp`) and at most `U+10FFFF`. -/
theorem encode_four {b0 b1 b2 b3 : UInt8} (h0 : 240 ≤ b0.toNat)
    (h1 : 128 ≤ b1.toNat) (h1' : b1.toNat < 192) (h2 : 128 ≤ b2.toNat) (h2' : b2.toNat < 192)
    (h3 : 128 ≤ b3.toNat) (h3' : b3.toNat < 192)
    (hlo : 65536 ≤ (b0.toNat - 240) * 262144 + (b1.toNat - 128) * 4096 + (b2.toNat - 128) * 64 +
      (b3.toNat - 128))
    (hhi : (b0.toNat - 240) * 262144 + (b1.toNat - 128) * 4096 + (b2.toNat - 128) * 64 +
      (b3.toNat - 128) < 1114112) :
    ∃ ch : Char, ch.toNat = (b0.toNat - 240) * 262144 + (b1.toNat - 128) * 4096 +
        (b2.toNat - 128) * 64 + (b3.toNat - 128) ∧
      String.utf8EncodeChar ch = [b0, b1, b2, b3] := by
  generalize hn : (b0.toNat - 240) * 262144 + (b1.toNat - 128) * 4096 + (b2.toNat - 128) * 64 +
    (b3.toNat - 128) = n at hlo hhi ⊢
  refine ⟨Char.ofNatAux n (Or.inr ⟨by omega, hhi⟩), rfl, ?_⟩
  rw [utf8EncodeChar_eq, toNat_ofNatAux, ite_eq_right (show ¬ n ≤ 127 by omega),
    ite_eq_right (show ¬ n ≤ 2047 by omega), ite_eq_right (show ¬ n ≤ 65535 by omega),
    show n / 262144 % 8 + 240 = b0.toNat by omega, show n / 4096 % 64 + 128 = b1.toNat by omega,
    show n / 64 % 64 + 128 = b2.toNat by omega, show n % 64 + 128 = b3.toNat by omega,
    UInt8.ofNat_toNat, UInt8.ofNat_toNat, UInt8.ofNat_toNat, UInt8.ofNat_toNat]

/-! ## Strings and their bytes -/

theorem byteArray_mk (bs : List UInt8) : (⟨bs.toArray⟩ : ByteArray) = bs.toByteArray :=
  ByteArray.ext (by simp)

/-- **The bytes of `String.ofList cs`** are its characters' encodings, concatenated. -/
theorem strBytes_ofList (cs : List Char) :
    StrBytes (String.ofList cs) (cs.flatMap String.utf8EncodeChar) := by
  have e : (⟨(cs.flatMap String.utf8EncodeChar).toArray⟩ : ByteArray) = List.utf8Encode cs :=
    (byteArray_mk _).trans rfl
  have hv : ByteArray.IsValidUTF8 ⟨(cs.flatMap String.utf8EncodeChar).toArray⟩ := ⟨cs, e⟩
  rw [StrBytes, String.fromUTF8?, dite_eq_left hv]
  congr 1
  apply String.toByteArray_inj.mp
  exact e.trans String.toByteArray_ofList.symm

/-- **The string of a literal's bytes** is `String.ofList` of any character list they encode. -/
theorem strBytes_eq_ofList {s : String} {cs : List Char} {bs : List UInt8} (hs : StrBytes s bs)
    (hcs : cs.flatMap String.utf8EncodeChar = bs) : s = String.ofList cs := by
  subst hcs
  have h2 := strBytes_ofList cs
  unfold StrBytes at hs h2
  rw [hs] at h2
  exact Option.some.inj h2

/-- **Bytes decode to a string exactly when they encode a character list.** -/
theorem exists_strBytes_iff {bs : List UInt8} :
    (∃ s, StrBytes s bs) ↔ ∃ cs : List Char, cs.flatMap String.utf8EncodeChar = bs := by
  constructor
  · rintro ⟨s, hs⟩
    unfold StrBytes String.fromUTF8? at hs
    by_cases hv : ByteArray.IsValidUTF8 ⟨bs.toArray⟩
    · obtain ⟨m, hm⟩ := hv
      refine ⟨m, ?_⟩
      have e : (m.flatMap String.utf8EncodeChar).toByteArray = bs.toByteArray :=
        (hm.symm.trans (byteArray_mk bs) : _)
      exact List.toByteArray_inj.mp e
    · rw [dite_eq_right hv] at hs
      cases hs
  · rintro ⟨cs, rfl⟩
    exact ⟨_, strBytes_ofList cs⟩

/-- **The constructor form of `String.ofList cs`** (the right side of `Red.strLit`) is the
character list `charList` of `cs`, under `String.ofList`. -/
theorem strLitToConstructor_ofList (cs : List Char) :
    Ix.Kernel.strLitToConstructor (md := .anon) (String.ofList cs) =
      .app (.const Ix.Kernel.stringOfListName [])
        (Specs.Nat.charList
          (.app (.const Ix.Kernel.listNilName [.zero]) (.const Ix.Kernel.charName []))
          (.app (.const Ix.Kernel.listConsName [.zero]) (.const Ix.Kernel.charName []))
          (.const Ix.Kernel.charOfNatName []) cs) := by
  unfold Ix.Kernel.strLitToConstructor
  rw [String.toList_ofList]
  congr 1
  induction cs with
  | nil => rfl
  | cons ch cs ih => simp only [List.foldr_cons, Specs.Nat.charList, ih]

/-! ## Fields, bytes and comparisons -/

theorem valF {n : Nat} (hn : n < 18446744069414584321) : ((n : Nat) : F).val = n :=
  ZMod.val_natCast_of_lt hn

theorem field_congr {a b : F} (e : a = b) : (Value.field a : SourceValue F) = .field b := by
  rw [e]

theorem tuple_field_congr {a b : F} {x : SourceValue F} (e : a = b) :
    (Value.tuple [.field a, x] : SourceValue F) = .tuple [.field b, x] := by
  rw [e]

theorem tuple2_inj {a b c d : SourceValue F}
    (e : (Value.tuple [a, b] : SourceValue F) = .tuple [c, d]) : a = c ∧ b = d := by
  injection e with e1
  injection e1 with e2 e3
  injection e3 with e4
  exact ⟨e2, e4⟩

theorem binop_add {x y v : SourceValue F} {a b : F} (hx : x = .field a) (hy : y = .field b)
    (op : evalBinOp .add x y = .ok v) : v = .field (a + b) := by
  subst hx hy
  simp only [evalBinOp, Except.ok.injEq] at op
  exact op.symm

theorem binop_sub_lit {x v : SourceValue F} {a b : F} (hx : x = .field a)
    (op : evalBinOp .sub x (.field b) = .ok v) : v = .field (a - b) := by
  subst hx
  simp only [evalBinOp, Except.ok.injEq] at op
  exact op.symm

theorem binop_mul_lit {x v : SourceValue F} {a b : F} (hx : x = .field a)
    (op : evalBinOp .mul x (.field b) = .ok v) : v = .field (a * b) := by
  subst hx
  simp only [evalBinOp, Except.ok.injEq] at op
  exact op.symm

theorem of_field_one {p : Prop} [Decidable p]
    (e : (Value.field (1 : F) : SourceValue F) = .field (if p then 1 else 0)) : p := by
  by_contra hp
  rw [ite_eq_right hp] at e
  exact one_ne_zero (Value.field.inj e)

theorem not_of_field_zero {p : Prop} [Decidable p]
    (e : (Value.field (0 : F) : SourceValue F) = .field (if p then 1 else 0)) : ¬p := by
  intro hp
  rw [ite_eq_left hp] at e
  exact zero_ne_one (Value.field.inj e)

theorem not_of_ne_one {p : Prop} [Decidable p]
    (e : (Value.field (if p then (1 : F) else 0) : SourceValue F) ≠ .field 1) : ¬p := by
  intro hp
  rw [ite_eq_left hp] at e
  exact e rfl

/-- `UInt8::less_than` against a constant byte `k`. -/
theorem u8_lt_lit {x r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {b : UInt8} {c : F}
    (k : Nat) (hk : k < 256) (hc : c = (k : F)) (hx : x = .field (b.toNat : F))
    (ev : ObsFn W "UInt8::less_than" [x, .field c] h r h' cs) :
    r = .field (if b.toNat < k then 1 else 0) ∧ h' = h := by
  have hy : RepU8 h (UInt8.ofNatLT k hk) (.field c) := by
    show Value.field c = .field (((UInt8.ofNatLT k hk).toNat : Nat) : F)
    rw [UInt8.toNat_ofNatLT, hc]
  have := Lib.u8_less_than_spec (a := b) hx hy ev
  rwa [UInt8.toNat_ofNatLT] at this

/-- `UInt32::less_than_fields` of a natural against a constant `k`. -/
theorem ltf_nat (k : Nat) {n : Nat} {c : F} {r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} (hn : n < 4294967296) (hk : k < 4294967296) (hc : c = (k : F))
    (ev : ObsFn W "UInt32::less_than_fields" [.field (n : F), .field c] h r h' cs) :
    (r = .field 1 ↔ n < k) ∧ h' = h := by
  obtain ⟨-, -, hiff, -, hh⟩ := Lib.less_than_fields_field ev
  have hcv : c.val = k := by rw [hc]; exact valF (by omega)
  rw [hcv, valF (n := n) (by omega)] at hiff
  exact ⟨hiff, hh⟩

theorem ltf_zero (k : Nat) {n : Nat} {c : F} {h h' : Heap F} {cs : List (Call F)}
    (hn : n < 4294967296) (hk : k < 4294967296) (hc : c = (k : F))
    (ev : ObsFn W "UInt32::less_than_fields" [.field (n : F), .field c] h (.field 0) h' cs) :
    k ≤ n ∧ h' = h := by
  obtain ⟨hiff, hh⟩ := ltf_nat k hn hk hc ev
  refine ⟨Nat.le_of_not_lt fun hlt => ?_, hh⟩
  exact zero_ne_one (Value.field.inj (hiff.mpr hlt))

theorem ltf_one (k : Nat) {n : Nat} {c : F} {h h' : Heap F} {cs : List (Call F)}
    (hn : n < 4294967296) (hk : k < 4294967296) (hc : c = (k : F))
    (ev : ObsFn W "UInt32::less_than_fields" [.field (n : F), .field c] h (.field 1) h' cs) :
    n < k ∧ h' = h := by
  obtain ⟨hiff, hh⟩ := ltf_nat k hn hk hc ev
  exact ⟨hiff.mp rfl, hh⟩

/-! ## The code point in the field -/

theorem cast1 {b0 : Nat} (h0 : 128 ≤ b0) : (b0 : F) - 128 = ((b0 - 128 : Nat) : F) := by
  push_cast [Nat.cast_sub h0]
  ring

theorem cast2 {b0 c1 : Nat} (h0 : 192 ≤ b0) :
    ((b0 : F) - 192) * 64 + (c1 : F) = (((b0 - 192) * 64 + c1 : Nat) : F) := by
  push_cast [Nat.cast_sub h0]
  ring

theorem cast3 {b0 c1 c2 : Nat} (h0 : 224 ≤ b0) :
    ((b0 : F) - 224) * 4096 + (c1 : F) * 64 + (c2 : F) =
      (((b0 - 224) * 4096 + c1 * 64 + c2 : Nat) : F) := by
  push_cast [Nat.cast_sub h0]
  ring

theorem cast4 {b0 c1 c2 c3 : Nat} (h0 : 240 ≤ b0) :
    ((b0 : F) - 240) * 262144 + (c1 : F) * 4096 + (c2 : F) * 64 + (c3 : F) =
      (((b0 - 240) * 262144 + c1 * 4096 + c2 * 64 + c3 : Nat) : F) := by
  push_cast [Nat.cast_sub h0]
  ring

end IxVM.Refinement.Core.Utf8Aux

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List

set_option linter.unusedVariables false

/-- A callee's derivation has fewer calls than its caller's. -/
macro "utf8_lt_calls" : tactic =>
  `(tactic| (simp only [List.length_cons, List.length_append]; omega))

/-! ## The step lemmas -/

/-- `KernelNatPrim::utf8_cont`: a continuation byte (`128 ≤ b < 192`) and its six payload bits;
no allocation. -/
theorem utf8_cont_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::utf8_cont" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.utf8_cont c args h r h' calls := by
  intro bp hargs good b hb
  subst hargs
  have hbv : bp = .field (b.toNat : F) := hb
  obtain ⟨m2, cs13, m36, cs47, x69, m71, cs80, ev15, ev49, ev82, he91, op76, hc92⟩ :=
    Obs.«KernelNatPrim::utf8_cont».obs ev
  obtain ⟨hv15, hm2⟩ := Utf8Aux.u8_lt_lit 128 (by omega) (by rfl) hbv ev15
  subst m2
  obtain ⟨hv49, hm36⟩ := Utf8Aux.u8_lt_lit 192 (by omega) (by rfl) hbv ev49
  subst m36
  obtain ⟨hx69, hm71⟩ := Lib.u8_to_field_spec ev82
  subst x69 m71 h'
  have l128 : ¬ b.toNat < 128 := Utf8Aux.not_of_field_zero hv15
  have l192 : b.toNat < 192 := Utf8Aux.of_field_one hv49
  refine ⟨by omega, l192, ?_, rfl⟩
  exact (Utf8Aux.binop_sub_lit hbv op76).trans
    (Utf8Aux.field_congr (Utf8Aux.cast1 (by omega)))

/-- `KernelNatPrim::utf8_decode_one`: the bytes start with the encoding of the character whose
code point the result is (one to four bytes, by the lead byte's range), and the rest is returned;
no allocation. -/
theorem utf8_decode_one_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::utf8_decode_one" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.utf8_decode_one c args h r h' calls := by
  intro bp rest hargs good b bs hb hbs
  subst hargs
  have hbv : bp = .field (b.toNat : F) := hb
  have hb256 : b.toNat < 256 := b.toNat_lt_size
  rcases Obs.«KernelNatPrim::utf8_decode_one».obs ev with
    ⟨m2, cs13, v37, m41, cs49, ev15, he39, ev51, he67, hc68⟩ |
    ⟨v1, m2, cs13, m74, cs85, m108, cs119, x_b1, x_r1, v170, m171, x178, y179, x186, x194, m196,
      cs205, cs219, ev15, hne69, ev87, ev121, ld152, ev207, op201, op193, ev221, op185, he234,
      he249, hc250⟩ |
    ⟨v1, m2, cs13, m74, cs85, v107, m108, cs119, m257, cs268, x_b1, x_r1, x_b2, x_r2, v348, m349,
      x356, y357, x364, y365, x372, x380, m382, cs391, x402, m404, cs413, cs427, m439, cs450, m473,
      cs484, ev15, hne69, ev87, ev121, hne252, ev270, ld301, ld330, ev393, op387, op379, ev415,
      op409, op371, ev429, op363, ev452, ev486, he510, he525, hc526⟩ |
    ⟨v1, m2, cs13, m74, cs85, v107, m108, cs119, m257, cs268, x_b1, x_r1, x_b2, x_r2, v348, m349,
      x356, y357, x364, y365, x372, x380, m382, cs391, x402, m404, cs413, cs427, m439, cs450, m473,
      cs484, m533, cs544, ev15, hne69, ev87, ev121, hne252, ev270, ld301, ld330, ev393, op387,
      op379, ev415, op409, op371, ev429, op363, ev452, ev486, ev546, he570, he585, hc586⟩ |
    ⟨v1, m2, cs13, m74, cs85, v107, m108, cs119, v256, m257, cs268, x_b1, x_r1, x_b2, x_r2, x_b3,
      x_r3, v683, m684, x691, y692, x699, y700, x707, y708, x715, x723, m725, cs734, x745, m747,
      cs756, x767, m769, cs778, cs792, m804, cs815, m838, cs849, ev15, hne69, ev87, ev121, hne252,
      ev270, hne592, ld607, ld636, ld665, ev736, op730, op722, ev758, op752, op714, ev780, op774,
      op706, ev794, op698, ev817, ev851, he875, he890, hc891⟩
  · -- one byte: `b < 0x80`
    subst r h'
    obtain ⟨hv15, hm2⟩ := Utf8Aux.u8_lt_lit 128 (by omega) (by rfl) hbv ev15
    subst m2
    obtain ⟨hv37, hm41⟩ := Lib.u8_to_field_spec ev51
    subst v37 m41
    obtain ⟨ch, hch, henc⟩ := Utf8Aux.encode_one (Utf8Aux.of_field_one hv15)
    refine ⟨ch, bs, rest, by simp [henc], ?_, hbs⟩
    rw [hbv]
    exact Utf8Aux.tuple_field_congr (congrArg (Nat.cast : Nat → F) hch.symm)
  · -- two bytes: `0xC2 ≤ b < 0xE0`
    subst calls r h'
    obtain ⟨hv1, hm2⟩ := Utf8Aux.u8_lt_lit 128 (by omega) (by rfl) hbv ev15
    subst v1 m2
    obtain ⟨hv87, hm74⟩ := Utf8Aux.u8_lt_lit 194 (by omega) (by rfl) hbv ev87
    subst m74
    obtain ⟨hv121, hm108⟩ := Utf8Aux.u8_lt_lit 224 (by omega) (by rfl) hbv ev121
    subst m108
    have l194 : ¬ b.toNat < 194 := Utf8Aux.not_of_field_zero hv87
    have l224 : b.toNat < 224 := Utf8Aux.of_field_one hv121
    obtain ⟨b1, bs1, rfl, hb1, hbs1⟩ := RepList.cons_of_load hbs ld152
    obtain ⟨hx194, hm196⟩ := Lib.u8_to_field_spec ev207
    subst x194 m196
    obtain ⟨c1lo, c1hi, hy179, hm171⟩ := ih.get (.nat .utf8_cont) (by utf8_lt_calls) ev221 x_b1
      rfl (good.sub fun x hx => by simp [hx]) b1 hb1
    subst m171
    have e170 : v170 = .field ((((b.toNat - 192) * 64 + (b1.toNat - 128) : Nat)) : F) :=
      (Utf8Aux.binop_add (Utf8Aux.binop_mul_lit (Utf8Aux.binop_sub_lit hbv op201) op193) hy179
        op185).trans (Utf8Aux.field_congr (Utf8Aux.cast2 (by omega)))
    subst v170
    obtain ⟨ch, hch, henc⟩ := Utf8Aux.encode_two (by omega) l224 c1lo c1hi
    refine ⟨ch, bs1, x_r1, by simp [henc], ?_, hbs1⟩
    exact Utf8Aux.tuple_field_congr (congrArg (Nat.cast : Nat → F) hch.symm)
  · -- three bytes, below the surrogates: `0xE0 ≤ b < 0xF0`
    subst calls r h'
    obtain ⟨hv1, hm2⟩ := Utf8Aux.u8_lt_lit 128 (by omega) (by rfl) hbv ev15
    subst v1 m2
    obtain ⟨hv87, hm74⟩ := Utf8Aux.u8_lt_lit 194 (by omega) (by rfl) hbv ev87
    subst m74
    obtain ⟨hv107, hm108⟩ := Utf8Aux.u8_lt_lit 224 (by omega) (by rfl) hbv ev121
    subst v107 m108
    obtain ⟨hv270, hm257⟩ := Utf8Aux.u8_lt_lit 240 (by omega) (by rfl) hbv ev270
    subst m257
    have l224 : ¬ b.toNat < 224 := Utf8Aux.not_of_ne_one hne252
    have l240 : b.toNat < 240 := Utf8Aux.of_field_one hv270
    obtain ⟨b1, bs1, rfl, hb1, hbs1⟩ := RepList.cons_of_load hbs ld301
    obtain ⟨b2, bs2, rfl, hb2, hbs2⟩ := RepList.cons_of_load hbs1 ld330
    obtain ⟨hx380, hm382⟩ := Lib.u8_to_field_spec ev393
    subst x380 m382
    obtain ⟨c1lo, c1hi, hx402, hm404⟩ := ih.get (.nat .utf8_cont) (by utf8_lt_calls) ev415 x_b1
      rfl (good.sub fun x hx => by simp [hx]) b1 hb1
    subst m404
    obtain ⟨c2lo, c2hi, hy357, hm349⟩ := ih.get (.nat .utf8_cont) (by utf8_lt_calls) ev429 x_b2
      rfl (good.sub fun x hx => by simp [hx]) b2 hb2
    subst m349
    have e348 : v348 = .field ((((b.toNat - 224) * 4096 + (b1.toNat - 128) * 64 +
        (b2.toNat - 128) : Nat)) : F) :=
      (Utf8Aux.binop_add (Utf8Aux.binop_add
        (Utf8Aux.binop_mul_lit (Utf8Aux.binop_sub_lit hbv op387) op379)
        (Utf8Aux.binop_mul_lit hx402 op409) op371) hy357 op363).trans
        (Utf8Aux.field_congr (Utf8Aux.cast3 (by omega)))
    subst v348
    obtain ⟨hlo, hm439⟩ := Utf8Aux.ltf_zero 2048 (by omega) (by omega) (by rfl) ev452
    subst m439
    obtain ⟨hhi, hm473⟩ := Utf8Aux.ltf_one 55296 (by omega) (by omega) (by rfl) ev486
    subst m473
    obtain ⟨ch, hch, henc⟩ :=
      Utf8Aux.encode_three (b0 := b) (by omega) l240 c1lo c1hi c2lo c2hi (by omega)
        (.inl (by omega))
    refine ⟨ch, bs2, x_r2, by simp [henc], ?_, hbs2⟩
    exact Utf8Aux.tuple_field_congr (congrArg (Nat.cast : Nat → F) hch.symm)
  · -- three bytes, above the surrogates
    subst calls r h'
    obtain ⟨hv1, hm2⟩ := Utf8Aux.u8_lt_lit 128 (by omega) (by rfl) hbv ev15
    subst v1 m2
    obtain ⟨hv87, hm74⟩ := Utf8Aux.u8_lt_lit 194 (by omega) (by rfl) hbv ev87
    subst m74
    obtain ⟨hv107, hm108⟩ := Utf8Aux.u8_lt_lit 224 (by omega) (by rfl) hbv ev121
    subst v107 m108
    obtain ⟨hv270, hm257⟩ := Utf8Aux.u8_lt_lit 240 (by omega) (by rfl) hbv ev270
    subst m257
    have l224 : ¬ b.toNat < 224 := Utf8Aux.not_of_ne_one hne252
    have l240 : b.toNat < 240 := Utf8Aux.of_field_one hv270
    obtain ⟨b1, bs1, rfl, hb1, hbs1⟩ := RepList.cons_of_load hbs ld301
    obtain ⟨b2, bs2, rfl, hb2, hbs2⟩ := RepList.cons_of_load hbs1 ld330
    obtain ⟨hx380, hm382⟩ := Lib.u8_to_field_spec ev393
    subst x380 m382
    obtain ⟨c1lo, c1hi, hx402, hm404⟩ := ih.get (.nat .utf8_cont) (by utf8_lt_calls) ev415 x_b1
      rfl (good.sub fun x hx => by simp [hx]) b1 hb1
    subst m404
    obtain ⟨c2lo, c2hi, hy357, hm349⟩ := ih.get (.nat .utf8_cont) (by utf8_lt_calls) ev429 x_b2
      rfl (good.sub fun x hx => by simp [hx]) b2 hb2
    subst m349
    have e348 : v348 = .field ((((b.toNat - 224) * 4096 + (b1.toNat - 128) * 64 +
        (b2.toNat - 128) : Nat)) : F) :=
      (Utf8Aux.binop_add (Utf8Aux.binop_add
        (Utf8Aux.binop_mul_lit (Utf8Aux.binop_sub_lit hbv op387) op379)
        (Utf8Aux.binop_mul_lit hx402 op409) op371) hy357 op363).trans
        (Utf8Aux.field_congr (Utf8Aux.cast3 (by omega)))
    subst v348
    obtain ⟨hlo, hm439⟩ := Utf8Aux.ltf_zero 2048 (by omega) (by omega) (by rfl) ev452
    subst m439
    obtain ⟨-, hm473⟩ := Utf8Aux.ltf_zero 55296 (by omega) (by omega) (by rfl) ev486
    subst m473
    obtain ⟨hhi, hm533⟩ := Utf8Aux.ltf_zero 57344 (by omega) (by omega) (by rfl) ev546
    subst m533
    obtain ⟨ch, hch, henc⟩ :=
      Utf8Aux.encode_three (b0 := b) (by omega) l240 c1lo c1hi c2lo c2hi (by omega)
        (.inr (by omega))
    refine ⟨ch, bs2, x_r2, by simp [henc], ?_, hbs2⟩
    exact Utf8Aux.tuple_field_congr (congrArg (Nat.cast : Nat → F) hch.symm)
  · -- four bytes: `0xF0 ≤ b`
    subst calls r h'
    obtain ⟨hv1, hm2⟩ := Utf8Aux.u8_lt_lit 128 (by omega) (by rfl) hbv ev15
    subst v1 m2
    obtain ⟨hv87, hm74⟩ := Utf8Aux.u8_lt_lit 194 (by omega) (by rfl) hbv ev87
    subst m74
    obtain ⟨hv107, hm108⟩ := Utf8Aux.u8_lt_lit 224 (by omega) (by rfl) hbv ev121
    subst v107 m108
    obtain ⟨hv256, hm257⟩ := Utf8Aux.u8_lt_lit 240 (by omega) (by rfl) hbv ev270
    subst v256 m257
    have l240 : ¬ b.toNat < 240 := Utf8Aux.not_of_ne_one hne592
    obtain ⟨b1, bs1, rfl, hb1, hbs1⟩ := RepList.cons_of_load hbs ld607
    obtain ⟨b2, bs2, rfl, hb2, hbs2⟩ := RepList.cons_of_load hbs1 ld636
    obtain ⟨b3, bs3, rfl, hb3, hbs3⟩ := RepList.cons_of_load hbs2 ld665
    obtain ⟨hx723, hm725⟩ := Lib.u8_to_field_spec ev736
    subst x723 m725
    obtain ⟨c1lo, c1hi, hx745, hm747⟩ := ih.get (.nat .utf8_cont) (by utf8_lt_calls) ev758 x_b1
      rfl (good.sub fun x hx => by simp [hx]) b1 hb1
    subst m747
    obtain ⟨c2lo, c2hi, hx767, hm769⟩ := ih.get (.nat .utf8_cont) (by utf8_lt_calls) ev780 x_b2
      rfl (good.sub fun x hx => by simp [hx]) b2 hb2
    subst m769
    obtain ⟨c3lo, c3hi, hy692, hm684⟩ := ih.get (.nat .utf8_cont) (by utf8_lt_calls) ev794 x_b3
      rfl (good.sub fun x hx => by simp [hx]) b3 hb3
    subst m684
    have e683 : v683 = .field ((((b.toNat - 240) * 262144 + (b1.toNat - 128) * 4096 +
        (b2.toNat - 128) * 64 + (b3.toNat - 128) : Nat)) : F) :=
      (Utf8Aux.binop_add (Utf8Aux.binop_add (Utf8Aux.binop_add
        (Utf8Aux.binop_mul_lit (Utf8Aux.binop_sub_lit hbv op730) op722)
        (Utf8Aux.binop_mul_lit hx745 op752) op714)
        (Utf8Aux.binop_mul_lit hx767 op774) op706) hy692 op698).trans
        (Utf8Aux.field_congr (Utf8Aux.cast4 (by omega)))
    subst v683
    obtain ⟨hlo, hm804⟩ :=
      Utf8Aux.ltf_zero 65536 (by omega) (by omega) (by rfl) ev817
    subst m804
    obtain ⟨hhi, hm838⟩ :=
      Utf8Aux.ltf_one 1114112 (by omega) (by omega) (by rfl) ev851
    subst m838
    obtain ⟨ch, hch, henc⟩ :=
      Utf8Aux.encode_four (b0 := b) (by omega) c1lo c1hi c2lo c2hi c3lo c3hi (by omega) (by omega)
    refine ⟨ch, bs3, x_r3, by simp [henc], ?_, hbs3⟩
    exact Utf8Aux.tuple_field_congr (congrArg (Nat.cast : Nat → F) hch.symm)

/-- `KernelNatPrim::utf8_validate`: the bytes are a concatenation of characters' encodings, so
they decode to a string (`StrBytes`). -/
theorem utf8_validate_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::utf8_validate" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.utf8_validate c args h r h' calls := by
  intro bp hargs good bs hbs
  subst hargs
  rcases Obs.«KernelNatPrim::utf8_validate».obs ev with
    ⟨ld12, he22, he23, hc24⟩ |
    ⟨x_b0, x_rest, m43, cs54, w79, x_remaining, cs93, ld12, ev56, ev95, hc104⟩
  · -- `Nil`: the empty string
    obtain rfl := RepList.nil_of_load hbs ld12
    exact Utf8Aux.exists_strBytes_iff.mpr ⟨[], by simp⟩
  · -- `Cons`: one character's encoding, then the rest
    obtain ⟨b0, bs0, rfl, hb0, hbs0⟩ := RepList.cons_of_load hbs ld12
    subst calls
    obtain ⟨ch, bs', rem, hsplit, hr, hrem⟩ :=
      ih.get (.nat .utf8_decode_one) (by utf8_lt_calls) ev56 x_b0 x_rest rfl
        (good.sub fun x hx => by simp [hx]) b0 bs0 hb0 hbs0
    obtain ⟨-, hrm⟩ := Utf8Aux.tuple2_inj hr
    subst x_remaining
    obtain ⟨s, hs⟩ := ih.get (.nat .utf8_validate) (by utf8_lt_calls) ev95 rem rfl
      (good.sub fun x hx => by simp [hx]) bs' hrem
    obtain ⟨cs, hcs⟩ := Utf8Aux.exists_strBytes_iff.mp ⟨s, hs⟩
    exact Utf8Aux.exists_strBytes_iff.mpr
      ⟨ch :: cs, by rw [List.flatMap_cons, hcs, hsplit]⟩

/-- `KernelNatPrim::build_char_list`: the character list of the bytes' decoding, one
`List.cons Char (Char.ofNat (lit cp))` node per character, over the given `List.nil Char`. -/
theorem build_char_list_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelNatPrim::build_char_list" args h r h' calls) (ih : IH c calls) :
    Specs.Nat.build_char_list c args h r h' calls := by
  intro bp n cp k hargs good bs hbs
  subst hargs
  rcases Obs.«KernelNatPrim::build_char_list».obs ev with
    ⟨ld12, he21, he22, hc23⟩ |
    ⟨x_b0, x_rest, m42, cs53, x_cp, x_remaining, v88, m89, cs99, m111, m144, m175, v205, m206,
      cs216, ld12, ev55, ev101, hm121, hm154, hm185, ev218, he255, hm254, hc275⟩
  · -- `Nil => nil_app`
    obtain rfl := RepList.nil_of_load hbs ld12
    subst r h'
    exact ⟨[], List.flatMap_nil, fun d Γ N C K hN _ _ => hN⟩
  · -- `Cons`: decode one character, build its node, recurse on the rest
    obtain ⟨b0, bs0, rfl, hb0, hbs0⟩ := RepList.cons_of_load hbs ld12
    subst calls r h'
    obtain ⟨ch, bs', rem, hsplit, hr, hrem⟩ :=
      ih.get (.nat .utf8_decode_one) (by utf8_lt_calls) ev55 x_b0 x_rest rfl
        (good.sub fun x hx => by simp [hx]) b0 bs0 hb0 hbs0
    obtain ⟨hcp, hrm⟩ := Utf8Aux.tuple2_inj hr
    subst x_cp x_remaining
    obtain ⟨-, limbs, hlimbs, hval, hcanon⟩ :=
      ih.get (.nat .klimbs_from_g) (by utf8_lt_calls) ev101 _ rfl
        (good.sub fun x hx => by simp [hx])
    have hval' : limbsVal limbs = ch.toNat :=
      hval.trans (Utf8Aux.valF (by have := Utf8Aux.char_toNat_lt ch; omega))
    have e1 : Heap.Extends h m42 := ObsFn.heap_extends ev55
    have e2 : Heap.Extends m42 m89 := ObsFn.heap_extends ev101
    have e3 : Heap.Extends m89 m111 := by rw [hm121]; exact Heap.Extends.snoc _ _
    have e4 : Heap.Extends m111 m144 := by rw [hm154]; exact Heap.Extends.snoc _ _
    have e5 : Heap.Extends m144 m175 := by rw [hm185]; exact Heap.Extends.snoc _ _
    have e6 : Heap.Extends m175 m206 := ObsFn.heap_extends ev218
    obtain ⟨cs', hcs', htail⟩ :=
      ih.get (.nat .build_char_list) (by utf8_lt_calls) ev218 rem n cp k rfl
        (good.sub fun x hx => by simp [hx]) bs'
        (Bytes.repByteStream_heapMono₂ _ ((e2.trans e3).trans (e4.trans e5)) hrem)
    refine ⟨ch :: cs', by rw [List.flatMap_cons, hcs', hsplit], ?_⟩
    intro d Γ N C K hN hC hK
    have hlit : c.tm d Γ m111 (.lit (.natVal ch.toNat)) (.ptr (.enum kexprEnum) m89.length) := by
      rw [← hval', hm121]
      exact .litNat (by simp)
        (repList_heapMono₂ _ repU64_heapMono₂ (Heap.Extends.snoc _ _) hlimbs) hcanon
    have hchar : c.tm d Γ m144 (.app K (.lit (.natVal ch.toNat)))
        (.ptr (.enum kexprEnum) m111.length) := by
      rw [hm154]
      exact Tm.store_app (hK.mono ((e1.trans e2).trans e3)) hlit
    have hhead : c.tm d Γ m175 (.app C (.app K (.lit (.natVal ch.toNat))))
        (.ptr (.enum kexprEnum) m144.length) := by
      rw [hm185]
      exact Tm.store_app (hC.mono (((e1.trans e2).trans e3).trans e4)) hchar
    have e15 : Heap.Extends h m175 := (((e1.trans e2).trans e3).trans e4).trans e5
    exact Tm.store_app (hhead.mono e6) (htail d Γ N C K (hN.mono e15) (hC.mono e15) (hK.mono e15))

end IxVM.Refinement.Core
