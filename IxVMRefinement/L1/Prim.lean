import IxVMRefinement.Obs.UInt8
import IxVMRefinement.Obs.UInt32
import IxVMRefinement.Obs.UInt64
import IxVMRefinement.Obs.Fields
import IxVMRefinement.Obs.Lists
import Aiur.Library.Blake3.BlockLoop

/-! # Bytes and words at source level

The checked byte and word operations of IxVM's library (`UInt8`, `UInt32`, `UInt64`, `Fields`)
as the observed source semantics evaluates them, against Lean's `UInt8`, `UInt32` and
`UInt64`. Each lemma takes an observed derivation (`ObsFn`, inverted by the generated path
lemmas) and concludes what it returns and that it leaves the heap as it found it.

No lemma assumes a hint honest. A hinted word (`u32.add`, `u32.add3`) is pinned by the
byte-range lookup of its bytes (`UInt8::range_pair`) and the carry relation the source
constrains on it; a byte comes from a static table whose rows the lookup returns.

* Representation: a byte is `bv b` (its value as a field element, as `RepU8`); a word is
  `wv w`, its four little-endian bytes (`w4`, as `RepU32`).
* Maps: the rows of `UInt8::raw_xor`, `raw_xor_split4`, `raw_xor_split7`, `from_field`, and
  the inversion of `range_pair` and `from_field`.
* Words: `UInt32::{compact, from_fields, add, add3, xor, rotr8, rotr16, xor_rotr7,
  xor_rotr12}` compute `+`, `^^^` and `Blake3.Pure.rotateRight` (through the byte-level
  identities of `Aiur.Library.Blake3`'s model: `xor_spec`, `rotr8_spec`, …).
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics

namespace IxVM.Refinement.L1

open IxVM (F)
open IxVM.Refinement.Obs

/-! ## Bytes and words -/

/-- **A checked byte** (`UInt8::U8`) as IxVM holds it: its value as a field element. -/
abbrev bv (b : UInt8) : SourceValue F := .field (b.toNat : F)

/-- **A word from its four little-endian bytes** (`UInt32::U32 = [U8; 4]`). -/
def w4 (b0 b1 b2 b3 : UInt8) : SourceValue F := .tuple [bv b0, bv b1, bv b2, bv b3]

/-- **A word** as IxVM holds it: its four little-endian bytes. -/
def wv (w : UInt32) : SourceValue F :=
  w4 (Blake3.Pure.wordBytes w)[0] (Blake3.Pure.wordBytes w)[1] (Blake3.Pure.wordBytes w)[2]
    (Blake3.Pure.wordBytes w)[3]

theorem wv_wordOfBytes (b0 b1 b2 b3 : UInt8) :
    wv (Aiur.Library.Blake3.wordOfBytes b0 b1 b2 b3) = w4 b0 b1 b2 b3 := by
  rw [wv, Aiur.Library.Blake3.wordBytes_wordOfBytes]
  rfl

/-- Every word is the word of its bytes. -/
theorem wv_bytes (w : UInt32) :
    Aiur.Library.Blake3.wordOfBytes (Blake3.Pure.wordBytes w)[0] (Blake3.Pure.wordBytes w)[1]
      (Blake3.Pure.wordBytes w)[2] (Blake3.Pure.wordBytes w)[3] = w :=
  Aiur.Library.Blake3.wordOfBytes_wordBytes w

theorem toNat_ofNat_lt {x : Nat} (hx : x < 256) : (UInt8.ofNat x).toNat = x := by
  first
  | (rw [UInt8.toNat_ofNat']; exact Nat.mod_eq_of_lt hx)
  | (simp [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hx])
  | (simp [UInt8.toNat_ofNat]; omega)
  | simp; omega

theorem bv_ofNat {x : Nat} (hx : x < 256) : bv (UInt8.ofNat x) = .field (x : F) := by
  simp only [bv, toNat_ofNat_lt hx]

theorem byte_lt (b : UInt8) : b.toNat < 256 := by
  have := b.toNat_lt
  omega

theorem natCast_byte_inj {a b : Nat} (ha : a < 256) (hb : b < 256) (h : (a : F) = (b : F)) :
    a = b :=
  IxVM.natCast_inj (by omega) (by omega) h

theorem bv_inj {a b : UInt8} (h : bv a = bv b) : a = b :=
  UInt8.ext (natCast_byte_inj (byte_lt a) (byte_lt b) (Value.field.inj h))

/-! ## Evaluation steps -/

theorem ok_inj {x y : SourceValue F}
    (h : (Except.ok x : Except EvalError (SourceValue F)) = .ok y) : x = y :=
  Except.ok.inj h

theorem binop_add {x y : F} {r : SourceValue F}
    (h : evalBinOp .add (.field x : SourceValue F) (.field y) = .ok r) : r = .field (x + y) :=
  (Except.ok.inj h).symm

theorem binop_sub {x y : F} {r : SourceValue F}
    (h : evalBinOp .sub (.field x : SourceValue F) (.field y) = .ok r) : r = .field (x - y) :=
  (Except.ok.inj h).symm

theorem binop_mul {x y : F} {r : SourceValue F}
    (h : evalBinOp .mul (.field x : SourceValue F) (.field y) = .ok r) : r = .field (x * y) :=
  (Except.ok.inj h).symm

theorem binop_div {x y : F} {r : SourceValue F} (hy : y ≠ 0)
    (h : evalBinOp .div (.field x : SourceValue F) (.field y) = .ok r) : r = .field (x / y) := by
  have e : evalBinOp .div (.field x : SourceValue F) (.field y) = .ok (.field (x / y)) := by
    first
    | simp [evalBinOp, hy]
    | (unfold evalBinOp; simp [hy])
    | (show (if y = 0 then _ else _) = _; rw [if_neg hy])
  rw [e] at h
  exact (Except.ok.inj h).symm

theorem base_ne_zero : (4294967296 : F) ≠ 0 := by decide

theorem proj_w4_0 (b0 b1 b2 b3 : UInt8) : projectValue (w4 b0 b1 b2 b3) 0 = .ok (bv b0) := rfl
theorem proj_w4_1 (b0 b1 b2 b3 : UInt8) : projectValue (w4 b0 b1 b2 b3) 1 = .ok (bv b1) := rfl
theorem proj_w4_2 (b0 b1 b2 b3 : UInt8) : projectValue (w4 b0 b1 b2 b3) 2 = .ok (bv b2) := rfl
theorem proj_w4_3 (b0 b1 b2 b3 : UInt8) : projectValue (w4 b0 b1 b2 b3) 3 = .ok (bv b3) := rfl

/-- A projection of a tuple, read off. -/
theorem proj_getElem (items : List (SourceValue F)) (i : Nat) (hi : i < items.length) :
    projectValue (.tuple items) i = .ok items[i] := by
  simp [projectValue, List.getElem?_eq_getElem hi]

theorem proj_inv {items : List (SourceValue F)} {i : Nat} {v : SourceValue F} (hi : i < items.length)
    (h : projectValue (.tuple items) i = .ok v) : v = items[i] :=
  (ok_inj ((proj_getElem items i hi).symm.trans h)).symm

/-! ## The byte tables -/

theorem mem_zip_map {α β γ : Type} {l : List α} {f : α → β} {g : α → γ} {x : α} (hx : x ∈ l) :
    (f x, g x) ∈ (l.map f).zip (l.map g) := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hx ⊢
    rcases hx with rfl | hx
    · exact .inl rfl
    · exact .inr (ih hx)

theorem mem_zip_map_iff {α β γ : Type} {l : List α} {f : α → β} {g : α → γ} {p : β × γ} :
    p ∈ (l.map f).zip (l.map g) ↔ ∃ x ∈ l, p = (f x, g x) := by
  induction l generalizing p with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨x, hx, rfl⟩)
      · exact ⟨a, .inl rfl, rfl⟩
      · exact ⟨x, .inr hx, rfl⟩
    · rintro ⟨x, rfl | hx, rfl⟩
      · exact .inl rfl
      · exact .inr ⟨x, hx, rfl⟩

theorem pair_mem {a b : Nat} (ha : a < 256) (hb : b < 256) : (a, b) ∈ IxVM.pairInputs :=
  List.mem_flatMap.mpr ⟨a, List.mem_range.mpr ha, List.mem_map.mpr ⟨b, List.mem_range.mpr hb, rfl⟩⟩

/-- The static map `UInt8::from_field`. -/
def fromFieldMap : Aiur.MapDecl := IxVM.coreTables.maps[0]'(by decide)
/-- The static map `UInt8::range_pair`. -/
def rangePairMap : Aiur.MapDecl := IxVM.coreTables.maps[2]'(by decide)
/-- The static map `UInt8::raw_xor`. -/
def rawXorMap : Aiur.MapDecl := IxVM.coreTables.maps[3]'(by decide)
/-- The static map `UInt8::raw_xor_split4`. -/
def rawXorSplit4Map : Aiur.MapDecl := IxVM.coreTables.maps[7]'(by decide)
/-- The static map `UInt8::raw_xor_split7`. -/
def rawXorSplit7Map : Aiur.MapDecl := IxVM.coreTables.maps[8]'(by decide)

theorem fromField_none : IxVM.source.program.sourceFunction? "UInt8::from_field" = none :=
  Program.sourceFunction?_of_key
    (IxVM.mapKeys_fresh _ (List.getElem_mem (l := IxVM.maps) (n := 0) (by decide)))
    (head_ne_of_bytes (by decide +kernel))

theorem rangePair_none : IxVM.source.program.sourceFunction? "UInt8::range_pair" = none :=
  Program.sourceFunction?_of_key
    (IxVM.mapKeys_fresh _ (List.getElem_mem (l := IxVM.maps) (n := 2) (by decide)))
    (head_ne_of_bytes (by decide +kernel))

theorem rawXor_none : IxVM.source.program.sourceFunction? "UInt8::raw_xor" = none :=
  Program.sourceFunction?_of_key
    (IxVM.mapKeys_fresh _ (List.getElem_mem (l := IxVM.maps) (n := 3) (by decide)))
    (head_ne_of_bytes (by decide +kernel))

theorem rawXorSplit4_none : IxVM.source.program.sourceFunction? "UInt8::raw_xor_split4" = none :=
  Program.sourceFunction?_of_key
    (IxVM.mapKeys_fresh _ (List.getElem_mem (l := IxVM.maps) (n := 7) (by decide)))
    (head_ne_of_bytes (by decide +kernel))

theorem rawXorSplit7_none : IxVM.source.program.sourceFunction? "UInt8::raw_xor_split7" = none :=
  Program.sourceFunction?_of_key
    (IxVM.mapKeys_fresh _ (List.getElem_mem (l := IxVM.maps) (n := 8) (by decide)))
    (head_ne_of_bytes (by decide +kernel))

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
    convert mem_zip_map (pair_mem ha hb) using 1
    simp [IxVM.coreRow, IxVM.coreLeaf]
  have looked := Aiur.lookupMap_of_entry (A := Nat) IxVM.tablesChecked member row
  simpa [Constant.toValue, Value.mapAddress, show rawXorMap.name = "UInt8::raw_xor" from rfl,
    IxVM.source] using looked

theorem rawXorSplit4_row {a b : Nat} (ha : a < 256) (hb : b < 256) :
    lookupMap IxVM.source.tables "UInt8::raw_xor_split4"
        ([.field (a : F), .field (b : F)] : List (SourceValue F)) =
      .ok (.tuple [.field ((Nat.xor a b / 16 : Nat) : F),
        .field (((Nat.xor a b % 16) * 16 : Nat) : F)]) := by
  have member : rawXorSplit4Map ∈ IxVM.coreTables.maps := List.getElem_mem _
  have rows : IxVM.coreTables.mapRows rawXorSplit4Map =
      IxVM.pairInputsTTable.rows.zip IxVM.pairXorParts4Table.rows := by
    simp only [Aiur.Program.mapRows, show rawXorSplit4Map.input = "UInt8::pair_inputs" from rfl,
      show rawXorSplit4Map.output = "UInt8::pair_xor_parts4" from rfl, IxVM.find_pairInputsT,
      IxVM.find_pairXorParts4]
  have row : (⟨[.field (a : F), .field (b : F)], .tuple [.field ((Nat.xor a b / 16 : Nat) : F),
      .field (((Nat.xor a b % 16) * 16 : Nat) : F)]⟩ : MapEntry F) ∈
      IxVM.coreTables.mapEntries rawXorSplit4Map := by
    apply Aiur.mapEntry_mem_iff.mpr
    rw [rows]
    simp only [IxVM.pairInputsTTable, IxVM.pairXorParts4Table, List.map_map]
    convert mem_zip_map (pair_mem ha hb) using 1
    simp [IxVM.coreRow, IxVM.coreLeaf]
  have looked := Aiur.lookupMap_of_entry (A := Nat) IxVM.tablesChecked member row
  simpa [Constant.toValue, Value.mapAddress,
    show rawXorSplit4Map.name = "UInt8::raw_xor_split4" from rfl, IxVM.source] using looked

theorem rawXorSplit7_row {a b : Nat} (ha : a < 256) (hb : b < 256) :
    lookupMap IxVM.source.tables "UInt8::raw_xor_split7"
        ([.field (a : F), .field (b : F)] : List (SourceValue F)) =
      .ok (.tuple [.field ((Nat.xor a b / 128 : Nat) : F),
        .field (((Nat.xor a b % 128) * 2 : Nat) : F)]) := by
  have member : rawXorSplit7Map ∈ IxVM.coreTables.maps := List.getElem_mem _
  have rows : IxVM.coreTables.mapRows rawXorSplit7Map =
      IxVM.pairInputsTTable.rows.zip IxVM.pairXorParts7Table.rows := by
    simp only [Aiur.Program.mapRows, show rawXorSplit7Map.input = "UInt8::pair_inputs" from rfl,
      show rawXorSplit7Map.output = "UInt8::pair_xor_parts7" from rfl, IxVM.find_pairInputsT,
      IxVM.find_pairXorParts7]
  have row : (⟨[.field (a : F), .field (b : F)], .tuple [.field ((Nat.xor a b / 128 : Nat) : F),
      .field (((Nat.xor a b % 128) * 2 : Nat) : F)]⟩ : MapEntry F) ∈
      IxVM.coreTables.mapEntries rawXorSplit7Map := by
    apply Aiur.mapEntry_mem_iff.mpr
    rw [rows]
    simp only [IxVM.pairInputsTTable, IxVM.pairXorParts7Table, List.map_map]
    convert mem_zip_map (pair_mem ha hb) using 1
    simp [IxVM.coreRow, IxVM.coreLeaf]
  have looked := Aiur.lookupMap_of_entry (A := Nat) IxVM.tablesChecked member row
  simpa [Constant.toValue, Value.mapAddress,
    show rawXorSplit7Map.name = "UInt8::raw_xor_split7" from rfl, IxVM.source] using looked

theorem find_fromFieldMap :
    IxVM.coreTables.findMap? "UInt8::from_field" = some fromFieldMap := by
  decide +kernel

theorem find_rangePairMap :
    IxVM.coreTables.findMap? "UInt8::range_pair" = some rangePairMap := by
  decide +kernel

/-- **Any successful `UInt8::from_field` lookup** returns its input, and the input is a byte. -/
theorem fromField_mapCall_inv {v w : SourceValue F} {h h' : Heap F}
    (hm : mapCall IxVM.source.tables "UInt8::from_field" [v] h = some (w, h')) :
    w = v ∧ h' = h ∧ ∃ x : Nat, x < 256 ∧ v = .field (x : F) := by
  unfold mapCall at hm
  cases looked : lookupMap IxVM.source.tables "UInt8::from_field" [v] with
  | error _ => simp [looked] at hm
  | ok row =>
    simp only [looked, Option.some.injEq, Prod.mk.injEq] at hm
    rcases hm with ⟨hrow, rfl⟩
    subst hrow
    obtain ⟨map, key, found, -, -, extracted, mem, -⟩ := Aiur.lookupMap_spec looked
    change IxVM.coreTables.findMap? "UInt8::from_field" = some map at found
    rw [find_fromFieldMap, Option.some.injEq] at found
    subst found
    have rows : IxVM.coreTables.mapRows fromFieldMap =
        IxVM.byteInputsTable.rows.zip IxVM.byteValuesTable.rows := by
      simp only [Aiur.Program.mapRows, show fromFieldMap.input = "UInt8::byte_inputs" from rfl,
        show fromFieldMap.output = "UInt8::byte_values" from rfl, IxVM.find_byteInputs,
        IxVM.find_byteValues]
    change (key, row) ∈ IxVM.coreTables.mapRows fromFieldMap at mem
    rw [rows] at mem
    simp only [IxVM.byteInputsTable, IxVM.byteValuesTable, List.map_map] at mem
    obtain ⟨x, hx, hkr⟩ := mem_zip_map_iff.mp mem
    simp only [List.mem_range] at hx
    simp only [Function.comp, IxVM.coreRow, IxVM.coreLeaf, List.map,
      Prod.mk.injEq] at hkr
    rcases hkr with ⟨rfl, rfl⟩
    have hv := Aiur.Value.toConstant_spec extracted
    simp [Constant.toValue, Value.mapAddress] at hv
    subst hv
    exact ⟨by simp [Constant.toValue, Value.mapAddress], rfl, x, hx, rfl⟩

/-- **Any successful `UInt8::range_pair` lookup** returns `()` and witnesses that both inputs are
bytes. -/
theorem rangePair_mapCall_inv {v1 v2 w : SourceValue F} {h h' : Heap F}
    (hm : mapCall IxVM.source.tables "UInt8::range_pair" [v1, v2] h = some (w, h')) :
    w = .tuple [] ∧ h' = h ∧
      ∃ a b : Nat, a < 256 ∧ b < 256 ∧ v1 = .field (a : F) ∧ v2 = .field (b : F) := by
  unfold mapCall at hm
  cases looked : lookupMap IxVM.source.tables "UInt8::range_pair" [v1, v2] with
  | error _ => simp [looked] at hm
  | ok row =>
    simp only [looked, Option.some.injEq, Prod.mk.injEq] at hm
    rcases hm with ⟨hrow, rfl⟩
    subst hrow
    obtain ⟨map, key, found, -, -, extracted, mem, -⟩ := Aiur.lookupMap_spec looked
    change IxVM.coreTables.findMap? "UInt8::range_pair" = some map at found
    rw [find_rangePairMap, Option.some.injEq] at found
    subst found
    have rows : IxVM.coreTables.mapRows rangePairMap =
        IxVM.pairInputsTTable.rows.zip IxVM.pairUnitsTable.rows := by
      simp only [Aiur.Program.mapRows, show rangePairMap.input = "UInt8::pair_inputs" from rfl,
        show rangePairMap.output = "UInt8::pair_units" from rfl, IxVM.find_pairInputsT,
        IxVM.find_pairUnits]
    change (key, row) ∈ IxVM.coreTables.mapRows rangePairMap at mem
    rw [rows] at mem
    simp only [IxVM.pairInputsTTable, IxVM.pairUnitsTable, List.map_map] at mem
    obtain ⟨p, hp, hkr⟩ := mem_zip_map_iff.mp mem
    rcases p with ⟨a, b⟩
    simp only [IxVM.pairInputs, List.mem_flatMap, List.mem_map, List.mem_range,
      Prod.mk.injEq] at hp
    obtain ⟨a, ha, b, hb, rfl, rfl⟩ := hp
    simp only [Function.comp, IxVM.coreRow, IxVM.coreLeaf, List.map,
      Prod.mk.injEq] at hkr
    rcases hkr with ⟨rfl, rfl⟩
    have hv := Aiur.Value.toConstant_spec extracted
    simp only [Constant.toValue, Value.mapAddress, List.map, Value.tuple.injEq,
      List.cons.injEq, and_true] at hv
    rcases hv with ⟨rfl, rfl⟩
    exact ⟨by simp [Constant.toValue, Value.mapAddress], rfl, a, b, ha, hb, rfl, rfl⟩

theorem fromField_row {x : Nat} (hx : x < 256) :
    lookupMap IxVM.source.tables "UInt8::from_field" ([.field (x : F)] : List (SourceValue F)) =
      .ok (.field (x : F)) := by
  have member : fromFieldMap ∈ IxVM.coreTables.maps := List.getElem_mem _
  have rows : IxVM.coreTables.mapRows fromFieldMap =
      IxVM.byteInputsTable.rows.zip IxVM.byteValuesTable.rows := by
    simp only [Aiur.Program.mapRows, show fromFieldMap.input = "UInt8::byte_inputs" from rfl,
      show fromFieldMap.output = "UInt8::byte_values" from rfl, IxVM.find_byteInputs,
      IxVM.find_byteValues]
  have row : (⟨[.field (x : F)], .field (x : F)⟩ : MapEntry F) ∈
      IxVM.coreTables.mapEntries fromFieldMap := by
    apply Aiur.mapEntry_mem_iff.mpr
    rw [rows]
    simp only [IxVM.byteInputsTable, IxVM.byteValuesTable, List.map_map]
    convert mem_zip_map (List.mem_range.mpr hx) using 1
    simp [IxVM.coreRow, IxVM.coreLeaf]
  have looked := Aiur.lookupMap_of_entry (A := Nat) IxVM.tablesChecked member row
  simpa [Constant.toValue, Value.mapAddress, show fromFieldMap.name = "UInt8::from_field" from rfl,
    IxVM.source] using looked

/-! ## Map calls in an observed derivation -/

/-- An observed call of a map is the map's row for its arguments. -/
theorem obs_map {name : String} (hfn : IxVM.source.program.sourceFunction? name = none)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {cs : List (Call F)}
    (ev : ObsFn W name args h r h' cs) : mapCall IxVM.source.tables name args h = some (r, h') :=
  EvalFn.map_row hfn ev.erase

theorem obs_map_row {name : String} (hfn : IxVM.source.program.sourceFunction? name = none)
    {args : List (SourceValue F)} {row : Constant F}
    (hrow : lookupMap IxVM.source.tables name args = .ok row)
    {h h' : Heap F} {r : SourceValue F} {cs : List (Call F)}
    (ev : ObsFn W name args h r h' cs) : r = row.toValue ∧ h' = h := by
  have hm := obs_map hfn ev
  simp only [mapCall, hrow, Option.some.injEq, Prod.mk.injEq] at hm
  exact ⟨hm.1.symm, hm.2.symm⟩

/-! ## `UInt8` -/

theorem u8_toField {x r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt8::to_field" [x] h r h' cs) : r = x ∧ h' = h := by
  obtain ⟨he, hh, -⟩ := «UInt8::to_field».obs ev
  exact ⟨he, hh⟩

/-- **`UInt8::from_field` checks a byte**: it returns its input, which is a byte. -/
theorem u8_fromField {x r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt8::from_field" [x] h r h' cs) :
    ∃ b : UInt8, x = bv b ∧ r = bv b ∧ h' = h := by
  obtain ⟨rfl, rfl, n, hn, rfl⟩ := fromField_mapCall_inv (obs_map fromField_none ev)
  exact ⟨UInt8.ofNat n, (bv_ofNat hn).symm, (bv_ofNat hn).symm, rfl⟩

/-- **`UInt8::from_fields` checks two bytes**: its result is its inputs, which are bytes. -/
theorem u8_fromFields {x y r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt8::from_fields" [x, y] h r h' cs) :
    ∃ a b : UInt8, x = bv a ∧ y = bv b ∧ r = .tuple [bv a, bv b] ∧ h' = h := by
  obtain ⟨v1, m2, cs12, ev14, rfl, rfl, -⟩ := «UInt8::from_fields».obs ev
  obtain ⟨-, rfl, a, b, ha, hb, rfl, rfl⟩ := rangePair_mapCall_inv (obs_map rangePair_none ev14)
  exact ⟨UInt8.ofNat a, UInt8.ofNat b, (bv_ofNat ha).symm, (bv_ofNat hb).symm,
    by rw [bv_ofNat ha, bv_ofNat hb], rfl⟩

theorem u8_xor {a b : UInt8} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt8::xor" [bv a, bv b] h r h' cs) : r = bv (a ^^^ b) ∧ h' = h := by
  obtain ⟨cs4, ev6, -⟩ := «UInt8::xor».obs ev
  obtain ⟨rfl, rfl⟩ := obs_map_row rawXor_none (rawXor_row (byte_lt a) (byte_lt b)) ev6
  refine ⟨?_, rfl⟩
  have hx : (a ^^^ b).toNat = Nat.xor a.toNat b.toNat := UInt8.toNat_xor a b
  simp [Constant.toValue, Value.mapAddress, bv, hx]

/-- The two parts of `UInt8::xor_split4`: the xor's high nibble, and its low nibble times 16. -/
theorem u8_xorSplit4 {a b : UInt8} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt8::xor_split4" [bv a, bv b] h r h' cs) :
    r = .tuple [.field (((a ^^^ b).toNat / 16 : Nat) : F),
      .field ((((a ^^^ b).toNat % 16) * 16 : Nat) : F)] ∧ h' = h := by
  obtain ⟨cs4, ev6, -⟩ := «UInt8::xor_split4».obs ev
  obtain ⟨rfl, rfl⟩ := obs_map_row rawXorSplit4_none (rawXorSplit4_row (byte_lt a) (byte_lt b)) ev6
  refine ⟨?_, rfl⟩
  have hx : (a ^^^ b).toNat = Nat.xor a.toNat b.toNat := UInt8.toNat_xor a b
  simp [Constant.toValue, Value.mapAddress, hx]

/-- The two parts of `UInt8::xor_split7`: the xor's top bit, and its low seven bits times 2. -/
theorem u8_xorSplit7 {a b : UInt8} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt8::xor_split7" [bv a, bv b] h r h' cs) :
    r = .tuple [.field (((a ^^^ b).toNat / 128 : Nat) : F),
      .field ((((a ^^^ b).toNat % 128) * 2 : Nat) : F)] ∧ h' = h := by
  obtain ⟨cs4, ev6, -⟩ := «UInt8::xor_split7».obs ev
  obtain ⟨rfl, rfl⟩ := obs_map_row rawXorSplit7_none (rawXorSplit7_row (byte_lt a) (byte_lt b)) ev6
  refine ⟨?_, rfl⟩
  have hx : (a ^^^ b).toNat = Nat.xor a.toNat b.toNat := UInt8.toNat_xor a b
  simp [Constant.toValue, Value.mapAddress, hx]

/-- `UInt8::join4` / `join7`: the first part of `high` plus the second of `low`. -/
theorem u8_join4 {r : SourceValue F} {x0 x1 y0 y1 : F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt8::join4" [.tuple [.field x0, .field x1], .tuple [.field y0, .field y1]]
      h r h' cs) : r = .field (x0 + y1) ∧ h' = h := by
  obtain ⟨u1, u2, pr11, rfl, pr15, op8, -⟩ := «UInt8::join4».obs ev
  obtain rfl := proj_inv (by simp) pr11
  obtain rfl := proj_inv (by simp) pr15
  exact ⟨binop_add op8, rfl⟩

theorem u8_join7 {r : SourceValue F} {x0 x1 y0 y1 : F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt8::join7" [.tuple [.field x0, .field x1], .tuple [.field y0, .field y1]]
      h r h' cs) : r = .field (x0 + y1) ∧ h' = h := by
  obtain ⟨u1, u2, pr11, rfl, pr15, op8, -⟩ := «UInt8::join7».obs ev
  obtain rfl := proj_inv (by simp) pr11
  obtain rfl := proj_inv (by simp) pr15
  exact ⟨binop_add op8, rfl⟩

/-! ## `UInt32` -/

open Aiur.Library.Blake3 (wordOfBytes wordOfBytes_toNat)

theorem u32_fromBytes {x r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt32::from_bytes" [x] h r h' cs) : r = x ∧ h' = h := by
  obtain ⟨he, hh, -⟩ := «UInt32::from_bytes».obs ev
  exact ⟨he, hh⟩

theorem u32_toBytes {x r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt32::to_bytes" [x] h r h' cs) : r = x ∧ h' = h := by
  obtain ⟨he, hh, -⟩ := «UInt32::to_bytes».obs ev
  exact ⟨he, hh⟩

/-- **`UInt32::from_fields` checks four bytes** (whatever its input): it returns a word. -/
theorem u32_fromFields {x r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt32::from_fields" [x] h r h' cs) :
    ∃ c0 c1 c2 c3 : UInt8, r = w4 c0 c1 c2 c3 ∧ h' = h := by
  obtain ⟨m2, cs12, v15, v16, x_b0, x_b1, m51, cs61, v64, v65, x_b2, x_b3, pr25, pr35, ev14, pr74,
    pr84, ev63, rfl, rfl, -⟩ := «UInt32::from_fields».obs ev
  obtain ⟨c0, c1, -, -, e1, rfl⟩ := u8_fromFields ev14
  obtain ⟨c2, c3, -, -, e2, rfl⟩ := u8_fromFields ev63
  obtain ⟨rfl, rfl⟩ : x_b0 = bv c0 ∧ x_b1 = bv c1 := by simpa using e1
  obtain ⟨rfl, rfl⟩ : x_b2 = bv c2 ∧ x_b3 = bv c3 := by simpa using e2
  exact ⟨c0, c1, c2, c3, rfl, rfl⟩

/-- **`UInt32::compact`**: the word's value as a field element. -/
theorem u32_compact {b0 b1 b2 b3 : UInt8} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt32::compact" [w4 b0 b1 b2 b3] h r h' cs) :
    r = .field ((wordOfBytes b0 b1 b2 b3).toNat : F) ∧ h' = h := by
  obtain ⟨x1, y2, m3, x9, y10, m11, x17, y18, m19, cs28, v31, y43, cs53, v56, y68, cs78, v81, y93,
    cs103, v106, pr40, ev30, pr65, ev55, op49, op24, pr90, ev80, op74, op16, pr115, ev105, op99,
    op8, -⟩ := «UInt32::compact».obs ev
  obtain rfl := ok_inj ((proj_w4_0 b0 b1 b2 b3).symm.trans pr40)
  obtain rfl := ok_inj ((proj_w4_1 b0 b1 b2 b3).symm.trans pr65)
  obtain rfl := ok_inj ((proj_w4_2 b0 b1 b2 b3).symm.trans pr90)
  obtain rfl := ok_inj ((proj_w4_3 b0 b1 b2 b3).symm.trans pr115)
  obtain ⟨rfl, rfl⟩ := u8_toField ev30
  obtain ⟨rfl, rfl⟩ := u8_toField ev55
  obtain ⟨rfl, rfl⟩ := u8_toField ev80
  obtain ⟨rfl, rfl⟩ := u8_toField ev105
  obtain rfl := binop_mul op49
  obtain rfl := binop_add op24
  obtain rfl := binop_mul op74
  obtain rfl := binop_add op16
  obtain rfl := binop_mul op99
  obtain rfl := binop_add op8
  refine ⟨?_, rfl⟩
  rw [wordOfBytes_toNat]
  congr 1
  simp only [Aiur.Library.U32.pack]
  push_cast
  ring

theorem u32_compact_wv {a : UInt32} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt32::compact" [wv a] h r h' cs) : r = .field (a.toNat : F) ∧ h' = h := by
  have := u32_compact (b0 := (Blake3.Pure.wordBytes a)[0]) (b1 := (Blake3.Pure.wordBytes a)[1])
    (b2 := (Blake3.Pure.wordBytes a)[2]) (b3 := (Blake3.Pure.wordBytes a)[3]) ev
  rwa [wv_bytes] at this

theorem word_lt (w : UInt32) : w.toNat < Aiur.Library.U32.base := by
  have := w.toNat_lt
  simp only [Aiur.Library.U32.base]
  omega

/-- A word's bytes give back a word of the value they pack to. -/
theorem w4_eq_wv {c0 c1 c2 c3 : UInt8} {w : UInt32}
    (hw : (wordOfBytes c0 c1 c2 c3).toNat = w.toNat) : w4 c0 c1 c2 c3 = (wv w : SourceValue F) := by
  have e : wordOfBytes c0 c1 c2 c3 = w := UInt32.ext hw
  rw [← e, wv_wordOfBytes]

/-- **`UInt32::add`** computes wrapping addition, whatever word the hint supplies. -/
theorem u32_add {a b : UInt32} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt32::add" [wv a, wv b] h r h' cs) : r = wv (a + b) ∧ h' = h := by
  obtain ⟨k10, v25, v26, v27, v28, m30, cs38, v41, m53, cs61, v64, m76, cs84, v87, m99, cs107,
    v110, v129, v130, v131, v132, m134, cs142, v145, m157, cs165, v168, m180, cs188, v191, m203,
    cs211, v214, v225, m226, cs236, v247, x255, m257, x263, y264, m265, x271, y272, m273, cs282,
    cs296, cs310, v332, y341, pr50, ev40, pr73, ev63, pr96, ev86, pr119, ev109, pr154, ev144,
    pr177, ev167, pr200, ev190, pr223, ev213, ty12, ev238, ev284, ev298, op278, ev312, op270,
    op262, op356, op347, heq364, rfl, rfl, -⟩ := «UInt32::add».obs ev
  obtain ⟨-, rfl⟩ := u8_toField ev40
  obtain ⟨-, rfl⟩ := u8_toField ev63
  obtain ⟨-, rfl⟩ := u8_toField ev86
  obtain ⟨-, rfl⟩ := u8_toField ev109
  obtain ⟨-, rfl⟩ := u8_toField ev144
  obtain ⟨-, rfl⟩ := u8_toField ev167
  obtain ⟨-, rfl⟩ := u8_toField ev190
  obtain ⟨-, rfl⟩ := u8_toField ev213
  obtain ⟨c0, c1, c2, c3, rfl, rfl⟩ := u32_fromFields ev238
  obtain ⟨rfl, rfl⟩ := u32_compact_wv ev284
  obtain ⟨rfl, rfl⟩ := u32_compact_wv ev298
  obtain ⟨rfl, rfl⟩ := u32_compact ev312
  obtain rfl := binop_add op278
  obtain rfl := binop_sub op270
  obtain rfl := binop_div base_ne_zero op262
  obtain rfl := binop_sub op356
  obtain rfl := binop_mul op347
  refine ⟨?_, rfl⟩
  have hc := Value.field.inj heq364
  have key := (Aiur.Library.U32.add_words_check_iff Aiur.Library.U32.Goldilocks.compatible
    (word_lt a) (word_lt b) (word_lt (wordOfBytes c0 c1 c2 c3))).1
    (by first | exact hc | simpa [Aiur.Library.U32.base] using hc)
  apply w4_eq_wv
  rw [key, UInt32.toNat_add]
  first | rfl | simp [Aiur.Library.U32.base] | (simp [Aiur.Library.U32.base, UInt32.size])

/-- **`UInt32::add3`** computes wrapping addition of three words. -/
theorem u32_add3 {a b c : UInt32} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt32::add3" [wv a, wv b, wv c] h r h' cs) :
    r = wv (a + b + c) ∧ h' = h := by
  obtain ⟨k10, v26, v27, v28, v29, m31, cs39, v42, m54, cs62, v65, m77, cs85, v88, m100, cs108,
    v111, v130, v131, v132, v133, m135, cs143, v146, m158, cs166, v169, m181, cs189, v192, m204,
    cs212, v215, v234, v235, v236, v237, m239, cs247, v250, m262, cs270, v273, m285, cs293, v296,
    m308, cs316, v319, v330, m331, cs341, v352, x360, m362, x368, y369, m370, x376, y377, m378,
    x384, y385, m386, cs395, cs409, cs423, cs437, v459, x467, y468, y476, pr51, ev41, pr74, ev64,
    pr97, ev87, pr120, ev110, pr155, ev145, pr178, ev168, pr201, ev191, pr224, ev214, pr259, ev249,
    pr282, ev272, pr305, ev295, pr328, ev318, ty12, ev343, ev397, ev411, op391, ev425, op383,
    ev439, op375, op367, op491, op482, op500, op474, heq508, rfl, rfl, -⟩ := «UInt32::add3».obs ev
  obtain ⟨-, rfl⟩ := u8_toField ev41
  obtain ⟨-, rfl⟩ := u8_toField ev64
  obtain ⟨-, rfl⟩ := u8_toField ev87
  obtain ⟨-, rfl⟩ := u8_toField ev110
  obtain ⟨-, rfl⟩ := u8_toField ev145
  obtain ⟨-, rfl⟩ := u8_toField ev168
  obtain ⟨-, rfl⟩ := u8_toField ev191
  obtain ⟨-, rfl⟩ := u8_toField ev214
  obtain ⟨-, rfl⟩ := u8_toField ev249
  obtain ⟨-, rfl⟩ := u8_toField ev272
  obtain ⟨-, rfl⟩ := u8_toField ev295
  obtain ⟨-, rfl⟩ := u8_toField ev318
  obtain ⟨c0, c1, c2, c3, rfl, rfl⟩ := u32_fromFields ev343
  obtain ⟨rfl, rfl⟩ := u32_compact_wv ev397
  obtain ⟨rfl, rfl⟩ := u32_compact_wv ev411
  obtain rfl := binop_add op391
  obtain ⟨rfl, rfl⟩ := u32_compact_wv ev425
  obtain rfl := binop_add op383
  obtain ⟨rfl, rfl⟩ := u32_compact ev439
  obtain rfl := binop_sub op375
  obtain rfl := binop_div base_ne_zero op367
  obtain rfl := binop_sub op491
  obtain rfl := binop_mul op482
  obtain rfl := binop_sub op500
  obtain rfl := binop_mul op474
  refine ⟨?_, rfl⟩
  have hc := Value.field.inj heq508
  have key := (Aiur.Library.U32.add3_words_check_iff Aiur.Library.U32.Goldilocks.compatible
    (word_lt a) (word_lt b) (word_lt c) (word_lt (wordOfBytes c0 c1 c2 c3))).1
    (by first | exact hc | simpa [Aiur.Library.U32.base] using hc)
  apply w4_eq_wv
  rw [key, UInt32.toNat_add, UInt32.toNat_add]
  first
  | (simp only [Aiur.Library.U32.base]; omega)
  | (norm_num [Aiur.Library.U32.base]; omega)
  | (simp [Aiur.Library.U32.base, Nat.add_mod])
  | (rw [Nat.add_mod (_ % _), Nat.mod_mod, ← Nat.add_mod]; rfl)

theorem u32_xor_w4 {a0 a1 a2 a3 b0 b1 b2 b3 : UInt8} {r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "UInt32::xor" [w4 a0 a1 a2 a3, w4 b0 b1 b2 b3] h r h' cs) :
    r = w4 (a0 ^^^ b0) (a1 ^^^ b1) (a2 ^^^ b2) (a3 ^^^ b3) ∧ h' = h := by
  obtain ⟨v3, v4, v5, v6, m9, cs17, v20, v21, m43, cs51, v54, v55, m77, cs85, v88, v89, m111,
    cs119, v122, v123, rfl, pr30, pr40, ev19, pr64, pr74, ev53, pr98, pr108, ev87, pr132, pr142,
    ev121, rfl, -⟩ := «UInt32::xor».obs ev
  obtain rfl := ok_inj ((proj_w4_0 a0 a1 a2 a3).symm.trans pr30)
  obtain rfl := ok_inj ((proj_w4_0 b0 b1 b2 b3).symm.trans pr40)
  obtain rfl := ok_inj ((proj_w4_1 a0 a1 a2 a3).symm.trans pr64)
  obtain rfl := ok_inj ((proj_w4_1 b0 b1 b2 b3).symm.trans pr74)
  obtain rfl := ok_inj ((proj_w4_2 a0 a1 a2 a3).symm.trans pr98)
  obtain rfl := ok_inj ((proj_w4_2 b0 b1 b2 b3).symm.trans pr108)
  obtain rfl := ok_inj ((proj_w4_3 a0 a1 a2 a3).symm.trans pr132)
  obtain rfl := ok_inj ((proj_w4_3 b0 b1 b2 b3).symm.trans pr142)
  obtain ⟨rfl, rfl⟩ := u8_xor ev19
  obtain ⟨rfl, rfl⟩ := u8_xor ev53
  obtain ⟨rfl, rfl⟩ := u8_xor ev87
  obtain ⟨rfl, rfl⟩ := u8_xor ev121
  exact ⟨rfl, rfl⟩

theorem u32_xor {a b : UInt32} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt32::xor" [wv a, wv b] h r h' cs) : r = wv (a ^^^ b) ∧ h' = h := by
  obtain ⟨rfl, rfl⟩ := u32_xor_w4 ev
  refine ⟨?_, rfl⟩
  rw [← wv_wordOfBytes, ← Aiur.Library.Blake3.xor_spec, wv_bytes, wv_bytes]

theorem u32_rotr8 {a : UInt32} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt32::rotr8" [wv a] h r h' cs) :
    r = wv (Blake3.Pure.rotateRight a 8) ∧ h' = h := by
  obtain ⟨v3, v4, v5, v6, rfl, pr16, pr26, pr36, pr46, rfl, -⟩ := «UInt32::rotr8».obs ev
  rw [wv] at pr16 pr26 pr36 pr46
  obtain rfl := ok_inj ((proj_w4_1 _ _ _ _).symm.trans pr16)
  obtain rfl := ok_inj ((proj_w4_2 _ _ _ _).symm.trans pr26)
  obtain rfl := ok_inj ((proj_w4_3 _ _ _ _).symm.trans pr36)
  obtain rfl := ok_inj ((proj_w4_0 _ _ _ _).symm.trans pr46)
  refine ⟨?_, rfl⟩
  conv_rhs => rw [← wv_bytes a]
  rw [Aiur.Library.Blake3.rotr8_spec, wv_wordOfBytes]
  try rfl

theorem u32_rotr16 {a : UInt32} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt32::rotr16" [wv a] h r h' cs) :
    r = wv (Blake3.Pure.rotateRight a 16) ∧ h' = h := by
  obtain ⟨v3, v4, v5, v6, rfl, pr16, pr26, pr36, pr46, rfl, -⟩ := «UInt32::rotr16».obs ev
  rw [wv] at pr16 pr26 pr36 pr46
  obtain rfl := ok_inj ((proj_w4_2 _ _ _ _).symm.trans pr16)
  obtain rfl := ok_inj ((proj_w4_3 _ _ _ _).symm.trans pr26)
  obtain rfl := ok_inj ((proj_w4_0 _ _ _ _).symm.trans pr36)
  obtain rfl := ok_inj ((proj_w4_1 _ _ _ _).symm.trans pr46)
  refine ⟨?_, rfl⟩
  conv_rhs => rw [← wv_bytes a]
  rw [Aiur.Library.Blake3.rotr16_spec, wv_wordOfBytes]
  try rfl

theorem u32_xor_rotr12 {a b : UInt32} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt32::xor_rotr12" [wv a, wv b] h r h' cs) :
    r = wv (Blake3.Pure.rotateRight (a ^^^ b) 12) ∧ h' = h := by
  obtain ⟨v1, m2, cs12, v15, v16, v37, m38, cs48, v51, v52, v73, m74, cs84, v87, v88, v109, m110,
    cs120, v123, v124, v147, v148, v149, v150, m153, cs161, m181, cs189, m209, cs217, m237, cs245,
    pr25, pr35, ev14, pr61, pr71, ev50, pr97, pr107, ev86, pr133, pr143, ev122, rfl, ev163, ev191,
    ev219, ev247, rfl, -⟩ := «UInt32::xor_rotr12».obs ev
  rw [wv] at pr25 pr35 pr61 pr71 pr97 pr107 pr133 pr143
  obtain rfl := ok_inj ((proj_w4_0 _ _ _ _).symm.trans pr25)
  obtain rfl := ok_inj ((proj_w4_0 _ _ _ _).symm.trans pr35)
  obtain rfl := ok_inj ((proj_w4_1 _ _ _ _).symm.trans pr61)
  obtain rfl := ok_inj ((proj_w4_1 _ _ _ _).symm.trans pr71)
  obtain rfl := ok_inj ((proj_w4_2 _ _ _ _).symm.trans pr97)
  obtain rfl := ok_inj ((proj_w4_2 _ _ _ _).symm.trans pr107)
  obtain rfl := ok_inj ((proj_w4_3 _ _ _ _).symm.trans pr133)
  obtain rfl := ok_inj ((proj_w4_3 _ _ _ _).symm.trans pr143)
  obtain ⟨rfl, rfl⟩ := u8_xorSplit4 ev14
  obtain ⟨rfl, rfl⟩ := u8_xorSplit4 ev50
  obtain ⟨rfl, rfl⟩ := u8_xorSplit4 ev86
  obtain ⟨rfl, rfl⟩ := u8_xorSplit4 ev122
  obtain ⟨rfl, rfl⟩ := u8_join4 ev163
  obtain ⟨rfl, rfl⟩ := u8_join4 ev191
  obtain ⟨rfl, rfl⟩ := u8_join4 ev219
  obtain ⟨rfl, rfl⟩ := u8_join4 ev247
  refine ⟨?_, rfl⟩
  have hspec := Aiur.Library.Blake3.xor_rotr12_spec (Blake3.Pure.wordBytes a)[0]
    (Blake3.Pure.wordBytes a)[1] (Blake3.Pure.wordBytes a)[2] (Blake3.Pure.wordBytes a)[3]
    (Blake3.Pure.wordBytes b)[0] (Blake3.Pure.wordBytes b)[1] (Blake3.Pure.wordBytes b)[2]
    (Blake3.Pure.wordBytes b)[3]
  simp only [wv_bytes] at hspec
  rw [hspec, wv_wordOfBytes]
  simp only [w4, bv]
  congr 1
  simp only [List.cons.injEq, Value.field.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [toNat_ofNat_lt (Aiur.Library.U32.joined_nibbles_lt (byte_lt _) (byte_lt _))]
    first | (push_cast; ring) | push_cast | simp

theorem u32_xor_rotr7 {a b : UInt32} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt32::xor_rotr7" [wv a, wv b] h r h' cs) :
    r = wv (Blake3.Pure.rotateRight (a ^^^ b) 7) ∧ h' = h := by
  obtain ⟨v1, m2, cs12, v15, v16, v37, m38, cs48, v51, v52, v73, m74, cs84, v87, v88, v109, m110,
    cs120, v123, v124, v147, v148, v149, v150, m153, cs161, m181, cs189, m209, cs217, m237, cs245,
    pr25, pr35, ev14, pr61, pr71, ev50, pr97, pr107, ev86, pr133, pr143, ev122, rfl, ev163, ev191,
    ev219, ev247, rfl, -⟩ := «UInt32::xor_rotr7».obs ev
  rw [wv] at pr25 pr35 pr61 pr71 pr97 pr107 pr133 pr143
  obtain rfl := ok_inj ((proj_w4_0 _ _ _ _).symm.trans pr25)
  obtain rfl := ok_inj ((proj_w4_0 _ _ _ _).symm.trans pr35)
  obtain rfl := ok_inj ((proj_w4_1 _ _ _ _).symm.trans pr61)
  obtain rfl := ok_inj ((proj_w4_1 _ _ _ _).symm.trans pr71)
  obtain rfl := ok_inj ((proj_w4_2 _ _ _ _).symm.trans pr97)
  obtain rfl := ok_inj ((proj_w4_2 _ _ _ _).symm.trans pr107)
  obtain rfl := ok_inj ((proj_w4_3 _ _ _ _).symm.trans pr133)
  obtain rfl := ok_inj ((proj_w4_3 _ _ _ _).symm.trans pr143)
  obtain ⟨rfl, rfl⟩ := u8_xorSplit7 ev14
  obtain ⟨rfl, rfl⟩ := u8_xorSplit7 ev50
  obtain ⟨rfl, rfl⟩ := u8_xorSplit7 ev86
  obtain ⟨rfl, rfl⟩ := u8_xorSplit7 ev122
  obtain ⟨rfl, rfl⟩ := u8_join7 ev163
  obtain ⟨rfl, rfl⟩ := u8_join7 ev191
  obtain ⟨rfl, rfl⟩ := u8_join7 ev219
  obtain ⟨rfl, rfl⟩ := u8_join7 ev247
  refine ⟨?_, rfl⟩
  have hspec := Aiur.Library.Blake3.xor_rotr7_spec (Blake3.Pure.wordBytes a)[0]
    (Blake3.Pure.wordBytes a)[1] (Blake3.Pure.wordBytes a)[2] (Blake3.Pure.wordBytes a)[3]
    (Blake3.Pure.wordBytes b)[0] (Blake3.Pure.wordBytes b)[1] (Blake3.Pure.wordBytes b)[2]
    (Blake3.Pure.wordBytes b)[3]
  simp only [wv_bytes] at hspec
  rw [hspec, wv_wordOfBytes]
  simp only [w4, bv]
  congr 1
  simp only [List.cons.injEq, Value.field.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [toNat_ofNat_lt (Aiur.Library.U32.joined_seven_bits_lt (byte_lt _) (byte_lt _))]
    first | (push_cast; ring) | push_cast | simp

/-! ## `Fields`, `UInt64`, `Lists` -/

theorem natCast_small_inj {a b : Nat} (ha : a < 1024) (hb : b < 1024) :
    ((a : F) = (b : F)) ↔ a = b :=
  ⟨IxVM.natCast_inj ha hb, fun e => by rw [e]⟩

/-- `Fields::is_zero` of a small natural. -/
theorem fields_isZero {n : Nat} (hn : n < 1024) {r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} (ev : ObsFn W "Fields::is_zero" [.field (n : F)] h r h' cs) :
    r = .field (if n = 0 then 1 else 0) ∧ h' = h := by
  rcases «Fields::is_zero».obs ev with ⟨hv, rfl, rfl, -⟩ | ⟨hne, rfl, rfl, -⟩
  · have : n = 0 := (natCast_small_inj hn (by omega)).1 (by simpa using Value.field.inj hv)
    subst this
    exact ⟨by simp, rfl⟩
  · have : n ≠ 0 := by
      rintro rfl
      exact hne (by simp)
    exact ⟨by simp [this], rfl⟩

end IxVM.Refinement.L1
