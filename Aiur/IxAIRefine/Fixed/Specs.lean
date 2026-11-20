import IxAIRefine.Fixed.Obs
import Mathlib.Tactic
import Mathlib.Algebra.Order.Group.Int

/-! # Specs of the leaf functions of `Fixed`

Every observed derivation (`ObsFn`) of a leaf function of the formal `Fixed` program computes
the intended integer fixed-point operation of `IxAICore.Fx`. A fixed-point number is represented
by its raw integer cast into the Goldilocks field (`fxVal`, which is `IxAIAiur.fx`).

* `UInt8` library: `UInt8::to_field` is the identity (`toField_spec`); `UInt8::from_fields`
  returns its two arguments, and they are bytes, because its `range_pair` lookup succeeds only
  on rows of the pair table (`rangePair_spec`, `fromFields_spec`); `UInt8::bit_decomposition`
  of a byte is its row of the bit table (`bitDecomposition_spec`).
* `shr8_spec`: for `|s| < 2^55`, `Fixed::shr8 s` is `⌊s / 256⌋`, which is `s >>> 8`
  (`shr8_eq`). The hinted quotient and remainder are pinned down by the range-checked bytes and
  `256 q + r = s`: both sides are integers far below the characteristic (`int_eq_of_cast_eq`).
* `sign_split_spec`: for `|v| < 2^55`, the flags are `[v ≥ 0]` and `[v ≠ 0]`.
* `bound_spec`: `Fixed::bound x` returns `x`, and `x` is the image of an integer in
  `[-4096, 4320)`.
* `mul_spec`, `relu_spec`, `pos_spec`: `Fx.mul`, `Fx.relu` and `Fx.pos`.
* `dot8_spec`, `dot16_spec`, `dot11_spec`, `dot20_spec`: `Fx.dot`, the exact integer sum of
  products rounded once, when that sum is below `2^55` in magnitude; `sum20_spec`: `Fx.sum`.

The magnitude bounds are hypotheses here; they follow from bounds on the model's weights and
data. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace IxAIStep.Fixed.Specs

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxAIStep.Fixed.Obs

/-- A fixed-point number as a field value: its raw integer, cast into the field. -/
def fxVal (x : IxAICore.Fx) : SourceValue F := .field ((x.raw : ℤ) : F)

theorem fxVal_eq_fx (x : IxAICore.Fx) : fxVal x = IxAIAiur.fx x := rfl

/-! ## Integers in the field -/

/-- Two integers closer than the characteristic are equal when their images in the field
are. -/
theorem int_eq_of_cast_eq {a b : ℤ} (hab : |a - b| < 18446744069414584321)
    (h : (a : F) = (b : F)) : a = b := by
  have h0 : ((a - b : ℤ) : F) = 0 := by rw [Int.cast_sub, h, sub_self]
  have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd (a - b)
    Aiur.Library.U32.Goldilocks.modulus).mp h0
  have h2 : (18446744069414584321 : ℤ) ∣ a - b := by
    first | exact_mod_cast h1 | exact h1 | simpa using h1
  have := Int.eq_zero_of_abs_lt_dvd h2 hab
  omega

/-- `>>> 8` on integers is floor division by `256`. -/
theorem shr8_eq (x : ℤ) : x >>> (8 : ℕ) = x / 256 := by
  first
    | (rw [Int.shiftRight_eq_div_pow]; norm_num)
    | simp [Int.shiftRight_eq_div_pow]

/-! ## Field operations and projections -/

theorem add_ff {x y : F} {c : SourceValue F}
    (h : evalBinOp .add (.field x : SourceValue F) (.field y) = .ok c) : c = .field (x + y) := by
  first
    | exact (Except.ok.inj h).symm
    | (simp only [evalBinOp, Except.ok.injEq] at h; exact h.symm)
    | (simp [evalBinOp] at h; exact h.symm)

theorem sub_ff {x y : F} {c : SourceValue F}
    (h : evalBinOp .sub (.field x : SourceValue F) (.field y) = .ok c) : c = .field (x - y) := by
  first
    | exact (Except.ok.inj h).symm
    | (simp only [evalBinOp, Except.ok.injEq] at h; exact h.symm)
    | (simp [evalBinOp] at h; exact h.symm)

theorem mul_ff {x y : F} {c : SourceValue F}
    (h : evalBinOp .mul (.field x : SourceValue F) (.field y) = .ok c) : c = .field (x * y) := by
  first
    | exact (Except.ok.inj h).symm
    | (simp only [evalBinOp, Except.ok.injEq] at h; exact h.symm)
    | (simp [evalBinOp] at h; exact h.symm)

/-- A successful product with a field on the left has a field on the right. -/
theorem mul_right_field {x : F} {b c : SourceValue F}
    (h : evalBinOp .mul (.field x : SourceValue F) b = .ok c) : ∃ y, b = .field y := by
  cases b
  case field y => exact ⟨y, rfl⟩
  all_goals simp [evalBinOp] at h

theorem proj_ok {items : List (SourceValue F)} {i : ℕ} {v : SourceValue F}
    (h : projectValue (.tuple items : SourceValue F) i = .ok v) : items[i]? = some v := by
  cases found : items[i]? with
  | none => simp [projectValue, found] at h <;> cases h
  | some w =>
    simp [projectValue, found, pure, Except.pure] at h
    simp [h]

theorem mem_zip_map {α β γ : Type} {l : List α} {f : α → β} {g : α → γ} {b : β} {c : γ}
    (hm : (b, c) ∈ (l.map f).zip (l.map g)) : ∃ a ∈ l, f a = b ∧ g a = c := by
  rw [List.zip_map'] at hm
  obtain ⟨a, ha, he⟩ := List.mem_map.mp hm
  simp only [Prod.mk.injEq] at he
  exact ⟨a, ha, he.1, he.2⟩

theorem dotRaw_cons (a b : IxAICore.Fx) (xs ys : List IxAICore.Fx) :
    IxAICore.Fx.dotRaw (a :: xs) (b :: ys) = a.raw * b.raw + IxAICore.Fx.dotRaw xs ys := by
  first | rfl | simp [IxAICore.Fx.dotRaw]

theorem dotRaw_nil : IxAICore.Fx.dotRaw [] [] = 0 := by
  first | rfl | simp [IxAICore.Fx.dotRaw]

theorem sumRaw_cons (a : IxAICore.Fx) (xs : List IxAICore.Fx) :
    IxAICore.Fx.sumRaw (a :: xs) = a.raw + IxAICore.Fx.sumRaw xs := by
  first | rfl | simp [IxAICore.Fx.sumRaw]

theorem sumRaw_nil : IxAICore.Fx.sumRaw [] = 0 := by
  first | rfl | simp [IxAICore.Fx.sumRaw]

/-- A list of length 8 is a literal of 8 elements. -/
theorem list_eq8 {α : Type} {l : List α} (h : l.length = 8) :
    ∃ x0 x1 x2 x3 x4 x5 x6 x7,
      l = [x0, x1, x2, x3, x4, x5, x6, x7] := by
  rcases l with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, _ | ⟨x6, _ | ⟨x7, _ | ⟨x8,
      l⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals first
    | exact ⟨_, _, _, _, _, _, _, _, rfl⟩
    | (simp only [List.length_cons, List.length_nil] at h <;> omega)

/-- A list of length 11 is a literal of 11 elements. -/
theorem list_eq11 {α : Type} {l : List α} (h : l.length = 11) :
    ∃ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10,
      l = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10] := by
  rcases l with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, _ | ⟨x6, _ | ⟨x7, _ | ⟨x8,
      _ | ⟨x9, _ | ⟨x10, _ | ⟨x11, l⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals first
    | exact ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩
    | (simp only [List.length_cons, List.length_nil] at h <;> omega)

/-- A list of length 16 is a literal of 16 elements. -/
theorem list_eq16 {α : Type} {l : List α} (h : l.length = 16) :
    ∃ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15,
      l = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] := by
  rcases l with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, _ | ⟨x6, _ | ⟨x7, _ | ⟨x8,
      _ | ⟨x9, _ | ⟨x10, _ | ⟨x11, _ | ⟨x12, _ | ⟨x13, _ | ⟨x14, _ | ⟨x15, _ | ⟨x16,
      l⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals first
    | exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
    | (simp only [List.length_cons, List.length_nil] at h <;> omega)

/-- A list of length 20 is a literal of 20 elements. -/
theorem list_eq20 {α : Type} {l : List α} (h : l.length = 20) :
    ∃ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19,
      l = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18,
        x19] := by
  rcases l with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, _ | ⟨x6, _ | ⟨x7, _ | ⟨x8,
      _ | ⟨x9, _ | ⟨x10, _ | ⟨x11, _ | ⟨x12, _ | ⟨x13, _ | ⟨x14, _ | ⟨x15, _ | ⟨x16, _ | ⟨x17, _ |
      ⟨x18, _ | ⟨x19, _ | ⟨x20, l⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals first
    | exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
    | (simp only [List.length_cons, List.length_nil] at h <;> omega)

/-! ## Map calls

`UInt8::range_pair` and `UInt8::raw_bit_decomposition` are maps: a call returns the output row
aligned with the input row equal to its arguments, so its arguments are an input row. -/

theorem rangePair_none :
    IxAIStep.Fixed.source.program.sourceFunction? "UInt8::range_pair" = none :=
  Aiur.Generic.Program.sourceFunction?_of_key (p := IxAIStep.Fixed.program)
    (by
      show Aiur.Generic.nameKey "UInt8::range_pair" ∉
        IxAIStep.Fixed.functions.map (fun f => Aiur.Generic.nameKey f.name)
      rw [IxAIStep.Fixed.functionKeys_eq]
      decide +kernel)
    (Aiur.Generic.head_ne_of_bytes (by decide +kernel))

theorem rawBits_none :
    IxAIStep.Fixed.source.program.sourceFunction? "UInt8::raw_bit_decomposition" = none :=
  Aiur.Generic.Program.sourceFunction?_of_key (p := IxAIStep.Fixed.program)
    (by
      show Aiur.Generic.nameKey "UInt8::raw_bit_decomposition" ∉
        IxAIStep.Fixed.functions.map (fun f => Aiur.Generic.nameKey f.name)
      rw [IxAIStep.Fixed.functionKeys_eq]
      decide +kernel)
    (Aiur.Generic.head_ne_of_bytes (by decide +kernel))

theorem findMap_rangePair :
    (IxAIStep.Fixed.coreTables.findMap? "UInt8::range_pair").map (fun m => (m.input, m.output)) =
      some ("UInt8::pair_inputs", "UInt8::pair_units") := by
  decide +kernel

theorem findMap_rawBits :
    (IxAIStep.Fixed.coreTables.findMap? "UInt8::raw_bit_decomposition").map
        (fun m => (m.input, m.output)) =
      some ("UInt8::byte_inputs", "UInt8::byte_bits") := by
  decide +kernel

/-- **A map call returns a row** of the static tables and leaves the heap. -/
theorem map_obs {name : String} {args : List (SourceValue F)} {h0 h1 : Heap F}
    {r : SourceValue F} {cs : List (Call F)}
    (hfn : IxAIStep.Fixed.source.program.sourceFunction? name = none)
    (ev : ObsFn W name args h0 r h1 cs) :
    ∃ row, lookupMap IxAIStep.Fixed.coreTables name args = .ok row ∧ r = row.toValue ∧
      h1 = h0 := by
  have hm := EvalFn.map_row hfn ev.erase
  change mapCall IxAIStep.Fixed.coreTables name args h0 = some (r, h1) at hm
  cases looked : lookupMap IxAIStep.Fixed.coreTables name args with
  | error e => simp [mapCall, looked] at hm
  | ok row =>
    simp only [mapCall, looked, Option.some.injEq, Prod.mk.injEq] at hm
    exact ⟨row, by first | rfl | exact looked, hm.1.symm, hm.2.symm⟩

/-- **`UInt8::range_pair` accepts only bytes**: its arguments are a row of the pair table. -/
theorem rangePair_spec {a b r : SourceValue F} {h0 h1 : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt8::range_pair" [a, b] h0 r h1 cs) :
    ∃ x y : ℕ, x < 256 ∧ y < 256 ∧ a = .field (x : F) ∧ b = .field (y : F) := by
  obtain ⟨row, looked, -, -⟩ := map_obs rangePair_none ev
  obtain ⟨m, key, found, -, -, hkey, hrow, -⟩ := Aiur.lookupMap_spec looked
  have hio := findMap_rangePair
  rw [found] at hio
  obtain ⟨hin, hout⟩ : m.input = "UInt8::pair_inputs" ∧ m.output = "UInt8::pair_units" := by
    simpa using hio
  simp only [Aiur.Program.mapRows, hin, hout, IxAIStep.Fixed.find_pairInputsT,
    IxAIStep.Fixed.find_pairUnits] at hrow
  have hk := (List.of_mem_zip hrow).1
  simp only [IxAIStep.Fixed.pairInputsTTable, List.map_map, List.mem_map, Function.comp] at hk
  obtain ⟨⟨x, y⟩, hp, rfl⟩ := hk
  simp only [IxAIStep.Fixed.pairInputs, List.mem_flatMap, List.mem_map, List.mem_range,
    Prod.mk.injEq] at hp
  obtain ⟨x', hx, y', hy, rfl, rfl⟩ := hp
  have same := Aiur.Value.toConstant_spec hkey
  simp only [IxAIStep.Fixed.coreRow, IxAIStep.Fixed.coreLeaf, List.map_cons, List.map_nil,
    Aiur.Constant.toValue, Aiur.Value.mapAddress, Aiur.Value.tuple.injEq, List.cons.injEq,
    and_true] at same
  obtain ⟨rfl, rfl⟩ := same
  exact ⟨_, _, hx, hy, rfl, rfl⟩

/-- `UInt8::to_field` is the identity. -/
theorem toField_spec {x r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt8::to_field" [x] h r h' cs) : r = x ∧ h' = h := by
  obtain ⟨he2, he3, -⟩ := «UInt8::to_field».obs ev
  exact ⟨he2, he3⟩

/-- **`UInt8::from_fields` range-checks two bytes** and returns them. -/
theorem fromFields_spec {u w c d : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt8::from_fields" [u, w] h (.tuple [c, d]) h' cs) :
    ∃ a b : ℕ, a < 256 ∧ b < 256 ∧ u = .field (a : F) ∧ w = .field (b : F) ∧
      c = .field (a : F) ∧ d = .field (b : F) := by
  obtain ⟨v1, m2, cs12, ev14, he35, -, -⟩ := «UInt8::from_fields».obs ev
  obtain ⟨a, b, ha, hb, rfl, rfl⟩ := rangePair_spec ev14
  simp only [Aiur.Value.tuple.injEq, List.cons.injEq, and_true] at he35
  exact ⟨a, b, ha, hb, rfl, rfl, he35.1, he35.2⟩

/-- **`UInt8::bit_decomposition` of a byte** is its row of the bit table. -/
theorem bitDecomposition_spec {x : ℕ} (hx : x < 256) {h h' : Heap F} {r : SourceValue F}
    {cs : List (Call F)} (ev : ObsFn W "UInt8::bit_decomposition" [.field (x : F)] h r h' cs) :
    r = ((IxAIStep.Fixed.coreRow
      (.array ((List.range 8).map fun i => .literal ((x / 2 ^ i) % 2))) :
        Aiur.Constant F).toValue) := by
  obtain ⟨cs4, ev6, -⟩ := «UInt8::bit_decomposition».obs ev
  obtain ⟨row, looked, rfl, -⟩ := map_obs rawBits_none ev6
  obtain ⟨m, key, found, -, -, hkey, hrow, -⟩ := Aiur.lookupMap_spec looked
  have hio := findMap_rawBits
  rw [found] at hio
  obtain ⟨hin, hout⟩ : m.input = "UInt8::byte_inputs" ∧ m.output = "UInt8::byte_bits" := by
    simpa using hio
  simp only [Aiur.Program.mapRows, hin, hout, IxAIStep.Fixed.find_byteInputs,
    IxAIStep.Fixed.find_byteBits, IxAIStep.Fixed.byteInputsTable, IxAIStep.Fixed.byteBitsTable,
    List.map_map] at hrow
  obtain ⟨y, hy, rfl, rfl⟩ := mem_zip_map hrow
  have same := Aiur.Value.toConstant_spec hkey
  simp only [Function.comp_apply, IxAIStep.Fixed.coreRow, IxAIStep.Fixed.coreLeaf,
    List.map_cons, List.map_nil, Aiur.Constant.toValue, Aiur.Value.mapAddress,
    Aiur.Value.tuple.injEq, List.cons.injEq, Aiur.Value.field.injEq, and_true] at same
  rw [List.mem_range] at hy
  obtain rfl := IxAIStep.Fixed.natCast_inj (by omega) (by omega) same
  rfl

/-- Bit 7 of the bit-table row of `x`. -/
theorem bits_proj7 (x : ℕ) {v : SourceValue F}
    (h : projectValue ((IxAIStep.Fixed.coreRow
      (.array ((List.range 8).map fun i => .literal ((x / 2 ^ i) % 2))) : Aiur.Constant F).toValue :
        SourceValue F) 7 = .ok v) :
    v = .field ((((x / 128) % 2 : ℕ)) : F) := by
  have hL : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := by decide
  have e : projectValue ((IxAIStep.Fixed.coreRow
      (.array ((List.range 8).map fun i => .literal ((x / 2 ^ i) % 2))) : Aiur.Constant F).toValue :
        SourceValue F) 7 = .ok (.field ((((x / 128) % 2 : ℕ)) : F)) := by
    rw [hL]
    simp [IxAIStep.Fixed.coreRow, IxAIStep.Fixed.coreLeaf, Aiur.Constant.toValue,
      Aiur.Value.mapAddress, projectValue, pure, Except.pure]
  rw [e] at h
  exact (Except.ok.inj h).symm

/-! ## `shr8` -/

/-- **`Fixed::shr8` is the floor of `s / 256`** for `|s| < 2^55`: the hinted remainder is a
byte, the hinted quotient is six bytes offset by `2^47`, and `256 q + r = s` holds in the field,
hence over the integers. -/
theorem shr8_spec {x : F} {s : ℤ} (hx : x = (s : F)) (hs : |s| < 2 ^ 55)
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Fixed::shr8" [.field x] h r h' calls) :
    r = .field ((s / 256 : ℤ) : F) := by
  subst hx
  obtain ⟨k10, m15, cs25, v28, v29, x_r, x_b0, m64, cs74, v77, v78, x_b1, x_b2, m113, cs123,
      v126, v127, x_b3, x_b4, m162, cs172, v175, v176, x_b5, x_z, v221, m224, cs232, v250,
      m251, x258, y259, m260, x266, y267, m268, x274, y275, m276, x282, y283, m284, x290,
      y291, m292, cs301, y313, cs323, y335, cs345, y357, cs367, y379, cs389, y401, cs411,
      v422, v450, m453, x458, y459, cs478, ty12, pr38, pr48, ev27, pr87, pr97, ev76, pr136,
      pr146, ev125, pr185, pr195, ev174, ev234, heq249, ev303, ev325, op319, op297, ev347,
      op341, op289, ev369, op363, op281, ev391, op385, op273, ev413, op407, op265, op437,
      op473, ev480, op465, heq496, he498, he499, hc500⟩ :=
    «Fixed::shr8».obs ev
  obtain ⟨r0, b0, hr0, hb0, rfl, rfl, rfl, rfl⟩ := fromFields_spec ev27
  obtain ⟨b1, b2, hb1, hb2, rfl, rfl, rfl, rfl⟩ := fromFields_spec ev76
  obtain ⟨b3, b4, hb3, hb4, rfl, rfl, rfl, rfl⟩ := fromFields_spec ev125
  obtain ⟨b5, z, hb5, hz, rfl, rfl, rfl, rfl⟩ := fromFields_spec ev174
  obtain ⟨rfl, -⟩ := toField_spec ev303
  obtain ⟨rfl, -⟩ := toField_spec ev325
  obtain ⟨rfl, -⟩ := toField_spec ev347
  obtain ⟨rfl, -⟩ := toField_spec ev369
  obtain ⟨rfl, -⟩ := toField_spec ev391
  obtain ⟨rfl, -⟩ := toField_spec ev413
  obtain ⟨rfl, -⟩ := toField_spec ev480
  obtain rfl := mul_ff op319
  obtain rfl := add_ff op297
  obtain rfl := mul_ff op341
  obtain rfl := add_ff op289
  obtain rfl := mul_ff op363
  obtain rfl := add_ff op281
  obtain rfl := mul_ff op385
  obtain rfl := add_ff op273
  obtain rfl := mul_ff op407
  obtain rfl := add_ff op265
  obtain rfl := sub_ff op437
  obtain rfl := mul_ff op473
  obtain rfl := add_ff op465
  have hfield := Aiur.Value.field.inj heq496
  subst he498
  have hq : ((256 * ((b0 : ℤ) + 256 * b1 + 65536 * b2 + 16777216 * b3 + 4294967296 * b4 +
      1099511627776 * b5 - 140737488355328) + r0 : ℤ) : F) = (s : F) := by
    rw [← hfield]
    push_cast <;> ring
  obtain ⟨hs1, hs2⟩ := abs_lt.mp hs
  norm_num at hs1 hs2
  have hint := int_eq_of_cast_eq (abs_lt.mpr ⟨by omega, by omega⟩) hq
  have hqs : ((b0 : ℤ) + 256 * b1 + 65536 * b2 + 16777216 * b3 + 4294967296 * b4 +
      1099511627776 * b5 - 140737488355328) = s / 256 := by omega
  rw [← hqs]
  congr 1
  push_cast <;> ring

/-! ## `sign_split` -/

/-- **`Fixed::sign_split v` is `([v ≥ 0], [v ≠ 0])`** for `|v| < 2^55`: seven range-checked
bytes reconstruct `v + 2^55` over the integers, so their bit 55 is `v ≥ 0`; and
`v · (1 − v · w) = 0` forces `v · w = 1` when `v ≠ 0`, whatever `w` the hint supplies. -/
theorem sign_split_spec {x : F} {v : ℤ} (hx : x = (v : F)) (hv : |v| < 2 ^ 55)
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Fixed::sign_split" [.field x] h r h' calls) :
    r = .tuple [.field (if 0 ≤ v then 1 else 0), .field (if v ≠ 0 then 1 else 0)] := by
  subst hx
  obtain ⟨k10, m15, cs25, v28, v29, x_b0, x_b1, m64, cs74, v77, v78, x_b2, x_b3, m113, cs123,
      v126, v127, x_b4, x_b5, m162, cs172, v175, x_b6, x_z, v206, m207, x214, y215, m216,
      x222, y223, m224, x230, y231, m232, x238, y239, m240, x246, y247, m248, x254, y255,
      m256, cs265, y277, cs287, y299, cs309, y321, cs331, y343, cs353, y365, cs375, y387,
      cs397, v420, v444, m445, cs455, v466, y475, v498, y507, v533, ty12, pr38, pr48, ev27,
      pr87, pr97, ev76, pr136, pr146, ev125, pr185, ev174, ev267, ev289, op283, op261, ev311,
      op305, op253, ev333, op327, op245, ev355, op349, op237, ev377, op371, op229, ev399,
      op393, op221, op441, heq443, ev457, pr485, op481, op522, op513, heq530, he535, pr544,
      he553, hc554⟩ :=
    «Fixed::sign_split».obs ev
  obtain ⟨b0, b1, hb0, hb1, rfl, rfl, rfl, rfl⟩ := fromFields_spec ev27
  obtain ⟨b2, b3, hb2, hb3, rfl, rfl, rfl, rfl⟩ := fromFields_spec ev76
  obtain ⟨b4, b5, hb4, hb5, rfl, rfl, rfl, rfl⟩ := fromFields_spec ev125
  obtain ⟨b6, z, hb6, hz, rfl, -, rfl, -⟩ := fromFields_spec ev174
  obtain ⟨rfl, -⟩ := toField_spec ev267
  obtain ⟨rfl, -⟩ := toField_spec ev289
  obtain ⟨rfl, -⟩ := toField_spec ev311
  obtain ⟨rfl, -⟩ := toField_spec ev333
  obtain ⟨rfl, -⟩ := toField_spec ev355
  obtain ⟨rfl, -⟩ := toField_spec ev377
  obtain ⟨rfl, -⟩ := toField_spec ev399
  obtain rfl := mul_ff op283
  obtain rfl := add_ff op261
  obtain rfl := mul_ff op305
  obtain rfl := add_ff op253
  obtain rfl := mul_ff op327
  obtain rfl := add_ff op245
  obtain rfl := mul_ff op349
  obtain rfl := add_ff op237
  obtain rfl := mul_ff op371
  obtain rfl := add_ff op229
  obtain rfl := mul_ff op393
  obtain rfl := add_ff op221
  obtain rfl := add_ff op441
  have hoffF := Aiur.Value.field.inj heq443
  obtain rfl := bitDecomposition_spec hb6 ev457
  obtain rfl := bits_proj7 b6 pr544
  obtain ⟨w, rfl⟩ := mul_right_field op481
  obtain rfl := mul_ff op481
  obtain rfl := sub_ff op522
  obtain rfl := mul_ff op513
  have hzero := Aiur.Value.field.inj heq530
  subst he535
  obtain ⟨hv1, hv2⟩ := abs_lt.mp hv
  norm_num at hv1 hv2
  -- The offset bytes reconstruct `v + 2^55` exactly.
  have hcast : (((b0 : ℤ) + 256 * b1 + 65536 * b2 + 16777216 * b3 + 4294967296 * b4 +
      1099511627776 * b5 + 281474976710656 * b6 : ℤ) : F) =
      ((v + 36028797018963968 : ℤ) : F) := by
    push_cast
    linear_combination hoffF
  have hoff := int_eq_of_cast_eq (abs_lt.mpr ⟨by omega, by omega⟩) hcast
  have h1 : ((((b6 / 128) % 2 : ℕ)) : F) = if 0 ≤ v then 1 else 0 := by
    by_cases hv0 : 0 ≤ v
    · rw [if_pos hv0, show (b6 / 128) % 2 = 1 by omega, Nat.cast_one]
    · rw [if_neg hv0, show (b6 / 128) % 2 = 0 by omega, Nat.cast_zero]
  have h2 : (v : F) * w = if v ≠ 0 then 1 else 0 := by
    by_cases hv0 : v = 0
    · subst hv0
      simp
    · rw [if_pos hv0]
      have hvF : (v : F) ≠ 0 := by
        intro hc
        have hc' : ((v : ℤ) : F) = ((0 : ℤ) : F) := by rw [hc, Int.cast_zero]
        have hab : |v - 0| < 18446744069414584321 := by
          rw [sub_zero]
          exact lt_trans hv (by norm_num)
        exact hv0 (int_eq_of_cast_eq hab hc')
      have h1w := (mul_eq_zero.mp hzero).resolve_left hvF
      linear_combination -h1w
  rw [h1, h2]

/-! ## `bound` -/

/-- **`Fixed::bound` admits only small values**: two range-checked bytes `lo`, `hi` with
`lo + 32 hi = x + 4096` make `x` the image of the integer `lo + 32 hi - 4096`. -/
theorem bound_spec {x : F} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Fixed::bound" [.field x] h r h' calls) :
    r = .field x ∧ ∃ k : ℤ, -4096 ≤ k ∧ k < 4320 ∧ x = (k : F) := by
  obtain ⟨k10, m15, cs25, v28, v29, x_lo, x_hi, v74, v75, m77, x82, y83, m84, cs93, y105, cs115,
      ty12, pr38, pr48, ev27, ev95, ev117, op111, op89, op139, heq141, he143, -, -⟩ :=
    «Fixed::bound».obs ev
  obtain ⟨a, b, ha, hb, rfl, rfl, rfl, rfl⟩ := fromFields_spec ev27
  obtain ⟨rfl, -⟩ := toField_spec ev95
  obtain ⟨rfl, -⟩ := toField_spec ev117
  obtain rfl := mul_ff op111
  obtain rfl := add_ff op89
  obtain rfl := add_ff op139
  have hfield := Aiur.Value.field.inj heq141
  refine ⟨he143, (a : ℤ) + 32 * b - 4096, by omega, by omega, ?_⟩
  push_cast
  linear_combination -hfield

/-! ## `mul`, `relu`, `pos` -/

/-- **`Fixed::mul` is `Fx.mul`** when the exact product is below `2^55` in magnitude. -/
theorem mul_spec {a b : IxAICore.Fx} (hab : |a.raw * b.raw| < 2 ^ 55)
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Fixed::mul" [fxVal a, fxVal b] h r h' calls) :
    r = fxVal (IxAICore.Fx.mul a b) := by
  obtain ⟨cs4, v7, op21, ev6, -⟩ := «Fixed::mul».obs ev
  obtain rfl := mul_ff op21
  exact (shr8_spec (s := a.raw * b.raw)
    (by first | exact (Int.cast_mul a.raw b.raw).symm | (push_cast; ring) | simp) hab ev6).trans
    (by simp only [fxVal, IxAICore.Fx.mul, shr8_eq])

/-- **`Fixed::relu` is `Fx.relu`** for `|x.raw| < 2^55`. -/
theorem relu_spec {x : IxAICore.Fx} (hv : |x.raw| < 2 ^ 55)
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Fixed::relu" [fxVal x] h r h' calls) :
    r = fxVal (IxAICore.Fx.relu x) := by
  obtain ⟨m2, cs12, x_nonneg, x__nz, ev14, -, op43, -⟩ := «Fixed::relu».obs ev
  have hs := sign_split_spec (v := x.raw) rfl hv ev14
  simp only [Aiur.Value.tuple.injEq, List.cons.injEq, and_true] at hs
  obtain ⟨rfl, -⟩ := hs
  obtain rfl := mul_ff op43
  rcases lt_trichotomy x.raw 0 with hlt | heq | hgt
  · rw [if_neg (show ¬ (0 : ℤ) ≤ x.raw by omega)]
    simp only [fxVal, IxAICore.Fx.relu, if_neg (show ¬ (x.raw > 0) by omega)]
    simp [IxAICore.Fx.zero]
  · rw [if_pos (show (0 : ℤ) ≤ x.raw by omega)]
    simp only [fxVal, IxAICore.Fx.relu, if_neg (show ¬ (x.raw > 0) by omega)]
    simp [IxAICore.Fx.zero, heq]
  · rw [if_pos (show (0 : ℤ) ≤ x.raw by omega)]
    simp only [fxVal, IxAICore.Fx.relu, if_pos (show x.raw > 0 by omega)]
    simp

/-- **`Fixed::pos` is `Fx.pos`** for `|x.raw| < 2^55`, as the field's `0` or `1`. -/
theorem pos_spec {x : IxAICore.Fx} (hv : |x.raw| < 2 ^ 55)
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Fixed::pos" [fxVal x] h r h' calls) :
    r = .field (if IxAICore.Fx.pos x then 1 else 0) := by
  obtain ⟨m2, cs12, x_nonneg, x_nz, ev14, -, op43, -⟩ := «Fixed::pos».obs ev
  have hs := sign_split_spec (v := x.raw) rfl hv ev14
  simp only [Aiur.Value.tuple.injEq, List.cons.injEq, and_true] at hs
  obtain ⟨rfl, rfl⟩ := hs
  obtain rfl := mul_ff op43
  have hp : (IxAICore.Fx.pos x = true) ↔ 0 < x.raw := by simp [IxAICore.Fx.pos]
  rcases lt_trichotomy x.raw 0 with hlt | heq | hgt
  · rw [if_neg (show ¬ (0 : ℤ) ≤ x.raw by omega),
      if_neg (show ¬ (IxAICore.Fx.pos x = true) by rw [hp]; omega), zero_mul]
  · rw [if_neg (show ¬ (x.raw ≠ 0) by omega),
      if_neg (show ¬ (IxAICore.Fx.pos x = true) by rw [hp]; omega), mul_zero]
  · rw [if_pos (show (0 : ℤ) ≤ x.raw by omega), if_pos (show x.raw ≠ 0 by omega),
      if_pos (show IxAICore.Fx.pos x = true by rw [hp]; omega), mul_one]

/-! ## Dot products and sums -/

/-- **`Fixed::dot8`**: a dot product of length 8 is `Fx.dot`, the exact integer sum of the
products rounded once by `shr8`, provided that sum is below `2^55` in magnitude. -/
theorem dot8_spec {xs ys : List IxAICore.Fx} (hxs : xs.length = 8) (hys : ys.length = 8)
    (hb : |IxAICore.Fx.dotRaw xs ys| < 2 ^ 55) {h h' : Heap F} {r : SourceValue F}
    {calls : List (Call F)}
    (ev : ObsFn W "Fixed::dot8" [.tuple (xs.map fxVal), .tuple (ys.map fxVal)] h r h' calls) :
    r = fxVal (IxAICore.Fx.dot xs ys) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ :=
    list_eq8 hxs
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩ :=
    list_eq8 hys
  simp only [List.map_cons, List.map_nil] at ev
  obtain ⟨cs4, v7, x14, y15, x22, y23, x30, y31, x38, y39, x46, y47, x54, y55, x62, y63, x70,
      y71, x86, y87, x102, y103, x118, y119, x134, y135, x150, y151, x166, y167, x182, y183,
      pr80, pr84, op77, pr96, pr100, op93, op69, pr112, pr116, op109, op61, pr128, pr132,
      op125, op53, pr144, pr148, op141, op45, pr160, pr164, op157, op37, pr176, pr180, op173,
      op29, pr192, pr196, op189, op21, ev6, hc198⟩ :=
    «Fixed::dot8».obs ev
  obtain rfl : fxVal a0 = x70 := by
    first | exact Except.ok.inj pr80 | simpa using proj_ok pr80
  obtain rfl : fxVal b0 = y71 := by
    first | exact Except.ok.inj pr84 | simpa using proj_ok pr84
  obtain rfl := mul_ff op77
  obtain rfl : fxVal a1 = x86 := by
    first | exact Except.ok.inj pr96 | simpa using proj_ok pr96
  obtain rfl : fxVal b1 = y87 := by
    first | exact Except.ok.inj pr100 | simpa using proj_ok pr100
  obtain rfl := mul_ff op93
  obtain rfl := add_ff op69
  obtain rfl : fxVal a2 = x102 := by
    first | exact Except.ok.inj pr112 | simpa using proj_ok pr112
  obtain rfl : fxVal b2 = y103 := by
    first | exact Except.ok.inj pr116 | simpa using proj_ok pr116
  obtain rfl := mul_ff op109
  obtain rfl := add_ff op61
  obtain rfl : fxVal a3 = x118 := by
    first | exact Except.ok.inj pr128 | simpa using proj_ok pr128
  obtain rfl : fxVal b3 = y119 := by
    first | exact Except.ok.inj pr132 | simpa using proj_ok pr132
  obtain rfl := mul_ff op125
  obtain rfl := add_ff op53
  obtain rfl : fxVal a4 = x134 := by
    first | exact Except.ok.inj pr144 | simpa using proj_ok pr144
  obtain rfl : fxVal b4 = y135 := by
    first | exact Except.ok.inj pr148 | simpa using proj_ok pr148
  obtain rfl := mul_ff op141
  obtain rfl := add_ff op45
  obtain rfl : fxVal a5 = x150 := by
    first | exact Except.ok.inj pr160 | simpa using proj_ok pr160
  obtain rfl : fxVal b5 = y151 := by
    first | exact Except.ok.inj pr164 | simpa using proj_ok pr164
  obtain rfl := mul_ff op157
  obtain rfl := add_ff op37
  obtain rfl : fxVal a6 = x166 := by
    first | exact Except.ok.inj pr176 | simpa using proj_ok pr176
  obtain rfl : fxVal b6 = y167 := by
    first | exact Except.ok.inj pr180 | simpa using proj_ok pr180
  obtain rfl := mul_ff op173
  obtain rfl := add_ff op29
  obtain rfl : fxVal a7 = x182 := by
    first | exact Except.ok.inj pr192 | simpa using proj_ok pr192
  obtain rfl : fxVal b7 = y183 := by
    first | exact Except.ok.inj pr196 | simpa using proj_ok pr196
  obtain rfl := mul_ff op189
  obtain rfl := add_ff op21
  exact (shr8_spec
    (s := IxAICore.Fx.dotRaw
      [a0, a1, a2, a3, a4, a5, a6, a7]
      [b0, b1, b2, b3, b4, b5, b6, b7])
    (by simp only [dotRaw_cons, dotRaw_nil, Int.cast_add, Int.cast_mul, Int.cast_zero] <;> ring)
    hb ev6).trans (by simp only [fxVal, IxAICore.Fx.dot, shr8_eq])

/-- **`Fixed::dot16`**: a dot product of length 16 is `Fx.dot`, the exact integer sum of the
products rounded once by `shr8`, provided that sum is below `2^55` in magnitude. -/
theorem dot16_spec {xs ys : List IxAICore.Fx} (hxs : xs.length = 16) (hys : ys.length = 16)
    (hb : |IxAICore.Fx.dotRaw xs ys| < 2 ^ 55) {h h' : Heap F} {r : SourceValue F}
    {calls : List (Call F)}
    (ev : ObsFn W "Fixed::dot16" [.tuple (xs.map fxVal), .tuple (ys.map fxVal)] h r h' calls) :
    r = fxVal (IxAICore.Fx.dot xs ys) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, rfl⟩ :=
    list_eq16 hxs
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, rfl⟩ :=
    list_eq16 hys
  simp only [List.map_cons, List.map_nil] at ev
  obtain ⟨cs4, v7, x14, y15, x22, y23, x30, y31, x38, y39, x46, y47, x54, y55, x62, y63, x70,
      y71, x78, y79, x86, y87, x94, y95, x102, y103, x110, y111, x118, y119, x126, y127,
      x134, y135, x150, y151, x166, y167, x182, y183, x198, y199, x214, y215, x230, y231,
      x246, y247, x262, y263, x278, y279, x294, y295, x310, y311, x326, y327, x342, y343,
      x358, y359, x374, y375, pr144, pr148, op141, pr160, pr164, op157, op133, pr176, pr180,
      op173, op125, pr192, pr196, op189, op117, pr208, pr212, op205, op109, pr224, pr228,
      op221, op101, pr240, pr244, op237, op93, pr256, pr260, op253, op85, pr272, pr276,
      op269, op77, pr288, pr292, op285, op69, pr304, pr308, op301, op61, pr320, pr324, op317,
      op53, pr336, pr340, op333, op45, pr352, pr356, op349, op37, pr368, pr372, op365, op29,
      pr384, pr388, op381, op21, ev6, hc390⟩ :=
    «Fixed::dot16».obs ev
  obtain rfl : fxVal a0 = x134 := by
    first | exact Except.ok.inj pr144 | simpa using proj_ok pr144
  obtain rfl : fxVal b0 = y135 := by
    first | exact Except.ok.inj pr148 | simpa using proj_ok pr148
  obtain rfl := mul_ff op141
  obtain rfl : fxVal a1 = x150 := by
    first | exact Except.ok.inj pr160 | simpa using proj_ok pr160
  obtain rfl : fxVal b1 = y151 := by
    first | exact Except.ok.inj pr164 | simpa using proj_ok pr164
  obtain rfl := mul_ff op157
  obtain rfl := add_ff op133
  obtain rfl : fxVal a2 = x166 := by
    first | exact Except.ok.inj pr176 | simpa using proj_ok pr176
  obtain rfl : fxVal b2 = y167 := by
    first | exact Except.ok.inj pr180 | simpa using proj_ok pr180
  obtain rfl := mul_ff op173
  obtain rfl := add_ff op125
  obtain rfl : fxVal a3 = x182 := by
    first | exact Except.ok.inj pr192 | simpa using proj_ok pr192
  obtain rfl : fxVal b3 = y183 := by
    first | exact Except.ok.inj pr196 | simpa using proj_ok pr196
  obtain rfl := mul_ff op189
  obtain rfl := add_ff op117
  obtain rfl : fxVal a4 = x198 := by
    first | exact Except.ok.inj pr208 | simpa using proj_ok pr208
  obtain rfl : fxVal b4 = y199 := by
    first | exact Except.ok.inj pr212 | simpa using proj_ok pr212
  obtain rfl := mul_ff op205
  obtain rfl := add_ff op109
  obtain rfl : fxVal a5 = x214 := by
    first | exact Except.ok.inj pr224 | simpa using proj_ok pr224
  obtain rfl : fxVal b5 = y215 := by
    first | exact Except.ok.inj pr228 | simpa using proj_ok pr228
  obtain rfl := mul_ff op221
  obtain rfl := add_ff op101
  obtain rfl : fxVal a6 = x230 := by
    first | exact Except.ok.inj pr240 | simpa using proj_ok pr240
  obtain rfl : fxVal b6 = y231 := by
    first | exact Except.ok.inj pr244 | simpa using proj_ok pr244
  obtain rfl := mul_ff op237
  obtain rfl := add_ff op93
  obtain rfl : fxVal a7 = x246 := by
    first | exact Except.ok.inj pr256 | simpa using proj_ok pr256
  obtain rfl : fxVal b7 = y247 := by
    first | exact Except.ok.inj pr260 | simpa using proj_ok pr260
  obtain rfl := mul_ff op253
  obtain rfl := add_ff op85
  obtain rfl : fxVal a8 = x262 := by
    first | exact Except.ok.inj pr272 | simpa using proj_ok pr272
  obtain rfl : fxVal b8 = y263 := by
    first | exact Except.ok.inj pr276 | simpa using proj_ok pr276
  obtain rfl := mul_ff op269
  obtain rfl := add_ff op77
  obtain rfl : fxVal a9 = x278 := by
    first | exact Except.ok.inj pr288 | simpa using proj_ok pr288
  obtain rfl : fxVal b9 = y279 := by
    first | exact Except.ok.inj pr292 | simpa using proj_ok pr292
  obtain rfl := mul_ff op285
  obtain rfl := add_ff op69
  obtain rfl : fxVal a10 = x294 := by
    first | exact Except.ok.inj pr304 | simpa using proj_ok pr304
  obtain rfl : fxVal b10 = y295 := by
    first | exact Except.ok.inj pr308 | simpa using proj_ok pr308
  obtain rfl := mul_ff op301
  obtain rfl := add_ff op61
  obtain rfl : fxVal a11 = x310 := by
    first | exact Except.ok.inj pr320 | simpa using proj_ok pr320
  obtain rfl : fxVal b11 = y311 := by
    first | exact Except.ok.inj pr324 | simpa using proj_ok pr324
  obtain rfl := mul_ff op317
  obtain rfl := add_ff op53
  obtain rfl : fxVal a12 = x326 := by
    first | exact Except.ok.inj pr336 | simpa using proj_ok pr336
  obtain rfl : fxVal b12 = y327 := by
    first | exact Except.ok.inj pr340 | simpa using proj_ok pr340
  obtain rfl := mul_ff op333
  obtain rfl := add_ff op45
  obtain rfl : fxVal a13 = x342 := by
    first | exact Except.ok.inj pr352 | simpa using proj_ok pr352
  obtain rfl : fxVal b13 = y343 := by
    first | exact Except.ok.inj pr356 | simpa using proj_ok pr356
  obtain rfl := mul_ff op349
  obtain rfl := add_ff op37
  obtain rfl : fxVal a14 = x358 := by
    first | exact Except.ok.inj pr368 | simpa using proj_ok pr368
  obtain rfl : fxVal b14 = y359 := by
    first | exact Except.ok.inj pr372 | simpa using proj_ok pr372
  obtain rfl := mul_ff op365
  obtain rfl := add_ff op29
  obtain rfl : fxVal a15 = x374 := by
    first | exact Except.ok.inj pr384 | simpa using proj_ok pr384
  obtain rfl : fxVal b15 = y375 := by
    first | exact Except.ok.inj pr388 | simpa using proj_ok pr388
  obtain rfl := mul_ff op381
  obtain rfl := add_ff op21
  exact (shr8_spec
    (s := IxAICore.Fx.dotRaw
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15]
      [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15])
    (by simp only [dotRaw_cons, dotRaw_nil, Int.cast_add, Int.cast_mul, Int.cast_zero] <;> ring)
    hb ev6).trans (by simp only [fxVal, IxAICore.Fx.dot, shr8_eq])

/-- **`Fixed::dot11`**: a dot product of length 11 is `Fx.dot`, the exact integer sum of the
products rounded once by `shr8`, provided that sum is below `2^55` in magnitude. -/
theorem dot11_spec {xs ys : List IxAICore.Fx} (hxs : xs.length = 11) (hys : ys.length = 11)
    (hb : |IxAICore.Fx.dotRaw xs ys| < 2 ^ 55) {h h' : Heap F} {r : SourceValue F}
    {calls : List (Call F)}
    (ev : ObsFn W "Fixed::dot11" [.tuple (xs.map fxVal), .tuple (ys.map fxVal)] h r h' calls) :
    r = fxVal (IxAICore.Fx.dot xs ys) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, rfl⟩ :=
    list_eq11 hxs
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, rfl⟩ :=
    list_eq11 hys
  simp only [List.map_cons, List.map_nil] at ev
  obtain ⟨cs4, v7, x14, y15, x22, y23, x30, y31, x38, y39, x46, y47, x54, y55, x62, y63, x70,
      y71, x78, y79, x86, y87, x94, y95, x110, y111, x126, y127, x142, y143, x158, y159,
      x174, y175, x190, y191, x206, y207, x222, y223, x238, y239, x254, y255, pr104, pr108,
      op101, pr120, pr124, op117, op93, pr136, pr140, op133, op85, pr152, pr156, op149, op77,
      pr168, pr172, op165, op69, pr184, pr188, op181, op61, pr200, pr204, op197, op53, pr216,
      pr220, op213, op45, pr232, pr236, op229, op37, pr248, pr252, op245, op29, pr264, pr268,
      op261, op21, ev6, hc270⟩ :=
    «Fixed::dot11».obs ev
  obtain rfl : fxVal a0 = x94 := by
    first | exact Except.ok.inj pr104 | simpa using proj_ok pr104
  obtain rfl : fxVal b0 = y95 := by
    first | exact Except.ok.inj pr108 | simpa using proj_ok pr108
  obtain rfl := mul_ff op101
  obtain rfl : fxVal a1 = x110 := by
    first | exact Except.ok.inj pr120 | simpa using proj_ok pr120
  obtain rfl : fxVal b1 = y111 := by
    first | exact Except.ok.inj pr124 | simpa using proj_ok pr124
  obtain rfl := mul_ff op117
  obtain rfl := add_ff op93
  obtain rfl : fxVal a2 = x126 := by
    first | exact Except.ok.inj pr136 | simpa using proj_ok pr136
  obtain rfl : fxVal b2 = y127 := by
    first | exact Except.ok.inj pr140 | simpa using proj_ok pr140
  obtain rfl := mul_ff op133
  obtain rfl := add_ff op85
  obtain rfl : fxVal a3 = x142 := by
    first | exact Except.ok.inj pr152 | simpa using proj_ok pr152
  obtain rfl : fxVal b3 = y143 := by
    first | exact Except.ok.inj pr156 | simpa using proj_ok pr156
  obtain rfl := mul_ff op149
  obtain rfl := add_ff op77
  obtain rfl : fxVal a4 = x158 := by
    first | exact Except.ok.inj pr168 | simpa using proj_ok pr168
  obtain rfl : fxVal b4 = y159 := by
    first | exact Except.ok.inj pr172 | simpa using proj_ok pr172
  obtain rfl := mul_ff op165
  obtain rfl := add_ff op69
  obtain rfl : fxVal a5 = x174 := by
    first | exact Except.ok.inj pr184 | simpa using proj_ok pr184
  obtain rfl : fxVal b5 = y175 := by
    first | exact Except.ok.inj pr188 | simpa using proj_ok pr188
  obtain rfl := mul_ff op181
  obtain rfl := add_ff op61
  obtain rfl : fxVal a6 = x190 := by
    first | exact Except.ok.inj pr200 | simpa using proj_ok pr200
  obtain rfl : fxVal b6 = y191 := by
    first | exact Except.ok.inj pr204 | simpa using proj_ok pr204
  obtain rfl := mul_ff op197
  obtain rfl := add_ff op53
  obtain rfl : fxVal a7 = x206 := by
    first | exact Except.ok.inj pr216 | simpa using proj_ok pr216
  obtain rfl : fxVal b7 = y207 := by
    first | exact Except.ok.inj pr220 | simpa using proj_ok pr220
  obtain rfl := mul_ff op213
  obtain rfl := add_ff op45
  obtain rfl : fxVal a8 = x222 := by
    first | exact Except.ok.inj pr232 | simpa using proj_ok pr232
  obtain rfl : fxVal b8 = y223 := by
    first | exact Except.ok.inj pr236 | simpa using proj_ok pr236
  obtain rfl := mul_ff op229
  obtain rfl := add_ff op37
  obtain rfl : fxVal a9 = x238 := by
    first | exact Except.ok.inj pr248 | simpa using proj_ok pr248
  obtain rfl : fxVal b9 = y239 := by
    first | exact Except.ok.inj pr252 | simpa using proj_ok pr252
  obtain rfl := mul_ff op245
  obtain rfl := add_ff op29
  obtain rfl : fxVal a10 = x254 := by
    first | exact Except.ok.inj pr264 | simpa using proj_ok pr264
  obtain rfl : fxVal b10 = y255 := by
    first | exact Except.ok.inj pr268 | simpa using proj_ok pr268
  obtain rfl := mul_ff op261
  obtain rfl := add_ff op21
  exact (shr8_spec
    (s := IxAICore.Fx.dotRaw
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]
      [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10])
    (by simp only [dotRaw_cons, dotRaw_nil, Int.cast_add, Int.cast_mul, Int.cast_zero] <;> ring)
    hb ev6).trans (by simp only [fxVal, IxAICore.Fx.dot, shr8_eq])

/-- **`Fixed::dot20`**: a dot product of length 20 is `Fx.dot`, the exact integer sum of the
products rounded once by `shr8`, provided that sum is below `2^55` in magnitude. -/
theorem dot20_spec {xs ys : List IxAICore.Fx} (hxs : xs.length = 20) (hys : ys.length = 20)
    (hb : |IxAICore.Fx.dotRaw xs ys| < 2 ^ 55) {h h' : Heap F} {r : SourceValue F}
    {calls : List (Call F)}
    (ev : ObsFn W "Fixed::dot20" [.tuple (xs.map fxVal), .tuple (ys.map fxVal)] h r h' calls) :
    r = fxVal (IxAICore.Fx.dot xs ys) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
    a18, a19, rfl⟩ :=
    list_eq20 hxs
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
    b18, b19, rfl⟩ :=
    list_eq20 hys
  simp only [List.map_cons, List.map_nil] at ev
  obtain ⟨cs4, v7, x14, y15, x22, y23, x30, y31, x38, y39, x46, y47, x54, y55, x62, y63, x70,
      y71, x78, y79, x86, y87, x94, y95, x102, y103, x110, y111, x118, y119, x126, y127,
      x134, y135, x142, y143, x150, y151, x158, y159, x166, y167, x182, y183, x198, y199,
      x214, y215, x230, y231, x246, y247, x262, y263, x278, y279, x294, y295, x310, y311,
      x326, y327, x342, y343, x358, y359, x374, y375, x390, y391, x406, y407, x422, y423,
      x438, y439, x454, y455, x470, y471, pr176, pr180, op173, pr192, pr196, op189, op165,
      pr208, pr212, op205, op157, pr224, pr228, op221, op149, pr240, pr244, op237, op141,
      pr256, pr260, op253, op133, pr272, pr276, op269, op125, pr288, pr292, op285, op117,
      pr304, pr308, op301, op109, pr320, pr324, op317, op101, pr336, pr340, op333, op93,
      pr352, pr356, op349, op85, pr368, pr372, op365, op77, pr384, pr388, op381, op69, pr400,
      pr404, op397, op61, pr416, pr420, op413, op53, pr432, pr436, op429, op45, pr448, pr452,
      op445, op37, pr464, pr468, op461, op29, pr480, pr484, op477, op21, ev6, hc486⟩ :=
    «Fixed::dot20».obs ev
  obtain rfl : fxVal a0 = x166 := by
    first | exact Except.ok.inj pr176 | simpa using proj_ok pr176
  obtain rfl : fxVal b0 = y167 := by
    first | exact Except.ok.inj pr180 | simpa using proj_ok pr180
  obtain rfl := mul_ff op173
  obtain rfl : fxVal a1 = x182 := by
    first | exact Except.ok.inj pr192 | simpa using proj_ok pr192
  obtain rfl : fxVal b1 = y183 := by
    first | exact Except.ok.inj pr196 | simpa using proj_ok pr196
  obtain rfl := mul_ff op189
  obtain rfl := add_ff op165
  obtain rfl : fxVal a2 = x198 := by
    first | exact Except.ok.inj pr208 | simpa using proj_ok pr208
  obtain rfl : fxVal b2 = y199 := by
    first | exact Except.ok.inj pr212 | simpa using proj_ok pr212
  obtain rfl := mul_ff op205
  obtain rfl := add_ff op157
  obtain rfl : fxVal a3 = x214 := by
    first | exact Except.ok.inj pr224 | simpa using proj_ok pr224
  obtain rfl : fxVal b3 = y215 := by
    first | exact Except.ok.inj pr228 | simpa using proj_ok pr228
  obtain rfl := mul_ff op221
  obtain rfl := add_ff op149
  obtain rfl : fxVal a4 = x230 := by
    first | exact Except.ok.inj pr240 | simpa using proj_ok pr240
  obtain rfl : fxVal b4 = y231 := by
    first | exact Except.ok.inj pr244 | simpa using proj_ok pr244
  obtain rfl := mul_ff op237
  obtain rfl := add_ff op141
  obtain rfl : fxVal a5 = x246 := by
    first | exact Except.ok.inj pr256 | simpa using proj_ok pr256
  obtain rfl : fxVal b5 = y247 := by
    first | exact Except.ok.inj pr260 | simpa using proj_ok pr260
  obtain rfl := mul_ff op253
  obtain rfl := add_ff op133
  obtain rfl : fxVal a6 = x262 := by
    first | exact Except.ok.inj pr272 | simpa using proj_ok pr272
  obtain rfl : fxVal b6 = y263 := by
    first | exact Except.ok.inj pr276 | simpa using proj_ok pr276
  obtain rfl := mul_ff op269
  obtain rfl := add_ff op125
  obtain rfl : fxVal a7 = x278 := by
    first | exact Except.ok.inj pr288 | simpa using proj_ok pr288
  obtain rfl : fxVal b7 = y279 := by
    first | exact Except.ok.inj pr292 | simpa using proj_ok pr292
  obtain rfl := mul_ff op285
  obtain rfl := add_ff op117
  obtain rfl : fxVal a8 = x294 := by
    first | exact Except.ok.inj pr304 | simpa using proj_ok pr304
  obtain rfl : fxVal b8 = y295 := by
    first | exact Except.ok.inj pr308 | simpa using proj_ok pr308
  obtain rfl := mul_ff op301
  obtain rfl := add_ff op109
  obtain rfl : fxVal a9 = x310 := by
    first | exact Except.ok.inj pr320 | simpa using proj_ok pr320
  obtain rfl : fxVal b9 = y311 := by
    first | exact Except.ok.inj pr324 | simpa using proj_ok pr324
  obtain rfl := mul_ff op317
  obtain rfl := add_ff op101
  obtain rfl : fxVal a10 = x326 := by
    first | exact Except.ok.inj pr336 | simpa using proj_ok pr336
  obtain rfl : fxVal b10 = y327 := by
    first | exact Except.ok.inj pr340 | simpa using proj_ok pr340
  obtain rfl := mul_ff op333
  obtain rfl := add_ff op93
  obtain rfl : fxVal a11 = x342 := by
    first | exact Except.ok.inj pr352 | simpa using proj_ok pr352
  obtain rfl : fxVal b11 = y343 := by
    first | exact Except.ok.inj pr356 | simpa using proj_ok pr356
  obtain rfl := mul_ff op349
  obtain rfl := add_ff op85
  obtain rfl : fxVal a12 = x358 := by
    first | exact Except.ok.inj pr368 | simpa using proj_ok pr368
  obtain rfl : fxVal b12 = y359 := by
    first | exact Except.ok.inj pr372 | simpa using proj_ok pr372
  obtain rfl := mul_ff op365
  obtain rfl := add_ff op77
  obtain rfl : fxVal a13 = x374 := by
    first | exact Except.ok.inj pr384 | simpa using proj_ok pr384
  obtain rfl : fxVal b13 = y375 := by
    first | exact Except.ok.inj pr388 | simpa using proj_ok pr388
  obtain rfl := mul_ff op381
  obtain rfl := add_ff op69
  obtain rfl : fxVal a14 = x390 := by
    first | exact Except.ok.inj pr400 | simpa using proj_ok pr400
  obtain rfl : fxVal b14 = y391 := by
    first | exact Except.ok.inj pr404 | simpa using proj_ok pr404
  obtain rfl := mul_ff op397
  obtain rfl := add_ff op61
  obtain rfl : fxVal a15 = x406 := by
    first | exact Except.ok.inj pr416 | simpa using proj_ok pr416
  obtain rfl : fxVal b15 = y407 := by
    first | exact Except.ok.inj pr420 | simpa using proj_ok pr420
  obtain rfl := mul_ff op413
  obtain rfl := add_ff op53
  obtain rfl : fxVal a16 = x422 := by
    first | exact Except.ok.inj pr432 | simpa using proj_ok pr432
  obtain rfl : fxVal b16 = y423 := by
    first | exact Except.ok.inj pr436 | simpa using proj_ok pr436
  obtain rfl := mul_ff op429
  obtain rfl := add_ff op45
  obtain rfl : fxVal a17 = x438 := by
    first | exact Except.ok.inj pr448 | simpa using proj_ok pr448
  obtain rfl : fxVal b17 = y439 := by
    first | exact Except.ok.inj pr452 | simpa using proj_ok pr452
  obtain rfl := mul_ff op445
  obtain rfl := add_ff op37
  obtain rfl : fxVal a18 = x454 := by
    first | exact Except.ok.inj pr464 | simpa using proj_ok pr464
  obtain rfl : fxVal b18 = y455 := by
    first | exact Except.ok.inj pr468 | simpa using proj_ok pr468
  obtain rfl := mul_ff op461
  obtain rfl := add_ff op29
  obtain rfl : fxVal a19 = x470 := by
    first | exact Except.ok.inj pr480 | simpa using proj_ok pr480
  obtain rfl : fxVal b19 = y471 := by
    first | exact Except.ok.inj pr484 | simpa using proj_ok pr484
  obtain rfl := mul_ff op477
  obtain rfl := add_ff op21
  exact (shr8_spec
    (s := IxAICore.Fx.dotRaw
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19]
      [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19])
    (by simp only [dotRaw_cons, dotRaw_nil, Int.cast_add, Int.cast_mul, Int.cast_zero] <;> ring)
    hb ev6).trans (by simp only [fxVal, IxAICore.Fx.dot, shr8_eq])

/-- **`Fixed::sum20`**: the exact sum of 20 fixed-point numbers, `Fx.sum`. No rounding happens,
so no bound is needed. -/
theorem sum20_spec {xs : List IxAICore.Fx} (hxs : xs.length = 20) {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Fixed::sum20" [.tuple (xs.map fxVal)] h r h' calls) :
    r = fxVal (IxAICore.Fx.sum xs) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
    a18, a19, rfl⟩ :=
    list_eq20 hxs
  simp only [List.map_cons, List.map_nil] at ev
  obtain ⟨x1, y2, x9, y10, x17, y18, x25, y26, x33, y34, x41, y42, x49, y50, x57, y58, x65,
      y66, x73, y74, x81, y82, x89, y90, x97, y98, x105, y106, x113, y114, x121, y122, x129,
      y130, x137, y138, x145, y146, pr155, pr159, op152, pr163, op144, pr167, op136, pr171,
      op128, pr175, op120, pr179, op112, pr183, op104, pr187, op96, pr191, op88, pr195, op80,
      pr199, op72, pr203, op64, pr207, op56, pr211, op48, pr215, op40, pr219, op32, pr223,
      op24, pr227, op16, he233, pr231, op8, hc234⟩ :=
    «Fixed::sum20».obs ev
  obtain rfl : fxVal a0 = x145 := by
    first | exact Except.ok.inj pr155 | simpa using proj_ok pr155
  obtain rfl : fxVal a1 = y146 := by
    first | exact Except.ok.inj pr159 | simpa using proj_ok pr159
  obtain rfl := add_ff op152
  obtain rfl : fxVal a2 = y138 := by
    first | exact Except.ok.inj pr163 | simpa using proj_ok pr163
  obtain rfl := add_ff op144
  obtain rfl : fxVal a3 = y130 := by
    first | exact Except.ok.inj pr167 | simpa using proj_ok pr167
  obtain rfl := add_ff op136
  obtain rfl : fxVal a4 = y122 := by
    first | exact Except.ok.inj pr171 | simpa using proj_ok pr171
  obtain rfl := add_ff op128
  obtain rfl : fxVal a5 = y114 := by
    first | exact Except.ok.inj pr175 | simpa using proj_ok pr175
  obtain rfl := add_ff op120
  obtain rfl : fxVal a6 = y106 := by
    first | exact Except.ok.inj pr179 | simpa using proj_ok pr179
  obtain rfl := add_ff op112
  obtain rfl : fxVal a7 = y98 := by
    first | exact Except.ok.inj pr183 | simpa using proj_ok pr183
  obtain rfl := add_ff op104
  obtain rfl : fxVal a8 = y90 := by
    first | exact Except.ok.inj pr187 | simpa using proj_ok pr187
  obtain rfl := add_ff op96
  obtain rfl : fxVal a9 = y82 := by
    first | exact Except.ok.inj pr191 | simpa using proj_ok pr191
  obtain rfl := add_ff op88
  obtain rfl : fxVal a10 = y74 := by
    first | exact Except.ok.inj pr195 | simpa using proj_ok pr195
  obtain rfl := add_ff op80
  obtain rfl : fxVal a11 = y66 := by
    first | exact Except.ok.inj pr199 | simpa using proj_ok pr199
  obtain rfl := add_ff op72
  obtain rfl : fxVal a12 = y58 := by
    first | exact Except.ok.inj pr203 | simpa using proj_ok pr203
  obtain rfl := add_ff op64
  obtain rfl : fxVal a13 = y50 := by
    first | exact Except.ok.inj pr207 | simpa using proj_ok pr207
  obtain rfl := add_ff op56
  obtain rfl : fxVal a14 = y42 := by
    first | exact Except.ok.inj pr211 | simpa using proj_ok pr211
  obtain rfl := add_ff op48
  obtain rfl : fxVal a15 = y34 := by
    first | exact Except.ok.inj pr215 | simpa using proj_ok pr215
  obtain rfl := add_ff op40
  obtain rfl : fxVal a16 = y26 := by
    first | exact Except.ok.inj pr219 | simpa using proj_ok pr219
  obtain rfl := add_ff op32
  obtain rfl : fxVal a17 = y18 := by
    first | exact Except.ok.inj pr223 | simpa using proj_ok pr223
  obtain rfl := add_ff op24
  obtain rfl : fxVal a18 = y10 := by
    first | exact Except.ok.inj pr227 | simpa using proj_ok pr227
  obtain rfl := add_ff op16
  obtain rfl : fxVal a19 = y2 := by
    first | exact Except.ok.inj pr231 | simpa using proj_ok pr231
  obtain rfl := add_ff op8
  simp only [fxVal, IxAICore.Fx.sum, sumRaw_cons, sumRaw_nil, Int.cast_add, Int.cast_zero]
  congr 1
  ring

end IxAIStep.Fixed.Specs
