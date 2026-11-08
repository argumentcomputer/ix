import Ix.IxVM.Refinement.Mirror
import IxVM.Checked.Lookup
import Ix.IxVM.Refinement.Statement

/-! # The TagN slice: IxVM's TagN decoder against IxC's `Ixon.getTagN`

Track B, Phase 3's first vertical slice (`plans/ixvm-certification-gap.md`).
Mirror lemmas for the functions `IxonDeserialize::get_tagn0` calls, in the
checked source's world, read off their bodies with the helper library
(`Ix.IxVM.Refinement.Mirror`), and the refinement of `Ixon.getTagN 0`.

* Byte maps: `rawSub_row`, `rawAdd_row`, `fromField_row` (the static
  tables' rows, from the table generator and `tablesChecked`), with the
  facts that they are maps, not functions (`rawSub_none`, …).
* Mirrors: `rawLt`, `lessThan`, `toField`. -/

namespace IxVM.Refinement.TagN

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM.Checked (F)

/-- The checked source's world. -/
abbrev W : World F := IxVM.Checked.source.world

/-! ## Rows of the byte maps -/

theorem mem_zip_map {α β γ : Type} {l : List α} {f : α → β} {g : α → γ} {x : α} (hx : x ∈ l) :
    (f x, g x) ∈ (l.map f).zip (l.map g) := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hx ⊢
    rcases hx with rfl | hx
    · exact .inl rfl
    · exact .inr (ih hx)

theorem pair_mem {a b : Nat} (ha : a < 256) (hb : b < 256) : (a, b) ∈ IxVM.Checked.pairInputs :=
  List.mem_flatMap.mpr ⟨a, List.mem_range.mpr ha, List.mem_map.mpr ⟨b, List.mem_range.mpr hb, rfl⟩⟩

/-- The static map `UInt8::from_field`. -/
def fromFieldMap : Aiur.MapDecl := IxVM.Checked.coreTables.maps[0]'(by decide)
/-- The static map `UInt8::raw_add`. -/
def rawAddMap : Aiur.MapDecl := IxVM.Checked.coreTables.maps[4]'(by decide)
/-- The static map `UInt8::raw_sub`. -/
def rawSubMap : Aiur.MapDecl := IxVM.Checked.coreTables.maps[5]'(by decide)

theorem rawSub_row {a b : Nat} (ha : a < 256) (hb : b < 256) :
    lookupMap IxVM.Checked.source.tables "UInt8::raw_sub" ([.field (a : F), .field (b : F)] : List (SourceValue F)) =
      .ok (.tuple [.field (((a + 256 - b) % 256 : Nat) : F),
        .field ((if a < b then 1 else 0 : Nat) : F)]) := by
  have member : rawSubMap ∈ IxVM.Checked.coreTables.maps := List.getElem_mem _
  have rows : IxVM.Checked.coreTables.mapRows rawSubMap =
      IxVM.Checked.pairInputsTTable.rows.zip IxVM.Checked.pairSubsTable.rows := by
    simp only [Aiur.Program.mapRows, show rawSubMap.input = "UInt8::pair_inputs" from rfl,
      show rawSubMap.output = "UInt8::pair_subs" from rfl, IxVM.Checked.find_pairInputsT,
      IxVM.Checked.find_pairSubs]
  have row : (⟨[.field (a : F), .field (b : F)], .tuple [.field (((a + 256 - b) % 256 : Nat) : F),
      .field ((if a < b then 1 else 0 : Nat) : F)]⟩ : MapEntry F) ∈
      IxVM.Checked.coreTables.mapEntries rawSubMap := by
    apply Aiur.mapEntry_mem_iff.mpr
    rw [rows]
    simp only [IxVM.Checked.pairInputsTTable, IxVM.Checked.pairSubsTable, List.map_map]
    convert mem_zip_map (pair_mem ha hb) using 1
    simp [IxVM.Checked.coreRow, IxVM.Checked.coreLeaf]
  have looked := Aiur.lookupMap_of_entry (A := Nat) IxVM.Checked.tablesChecked member row
  simpa [Constant.toValue, Value.mapAddress, show rawSubMap.name = "UInt8::raw_sub" from rfl, IxVM.Checked.source]
    using looked

theorem rawAdd_row {a b : Nat} (ha : a < 256) (hb : b < 256) :
    lookupMap IxVM.Checked.source.tables "UInt8::raw_add" ([.field (a : F), .field (b : F)] : List (SourceValue F)) =
      .ok (.tuple [.field (((a + b) % 256 : Nat) : F), .field (((a + b) / 256 : Nat) : F)]) := by
  have member : rawAddMap ∈ IxVM.Checked.coreTables.maps := List.getElem_mem _
  have rows : IxVM.Checked.coreTables.mapRows rawAddMap =
      IxVM.Checked.pairInputsTTable.rows.zip IxVM.Checked.pairAddsTable.rows := by
    simp only [Aiur.Program.mapRows, show rawAddMap.input = "UInt8::pair_inputs" from rfl,
      show rawAddMap.output = "UInt8::pair_adds" from rfl, IxVM.Checked.find_pairInputsT,
      IxVM.Checked.find_pairAdds]
  have row : (⟨[.field (a : F), .field (b : F)], .tuple [.field (((a + b) % 256 : Nat) : F),
      .field (((a + b) / 256 : Nat) : F)]⟩ : MapEntry F) ∈
      IxVM.Checked.coreTables.mapEntries rawAddMap := by
    apply Aiur.mapEntry_mem_iff.mpr
    rw [rows]
    simp only [IxVM.Checked.pairInputsTTable, IxVM.Checked.pairAddsTable, List.map_map]
    convert mem_zip_map (pair_mem ha hb) using 1
    simp [IxVM.Checked.coreRow, IxVM.Checked.coreLeaf]
  have looked := Aiur.lookupMap_of_entry (A := Nat) IxVM.Checked.tablesChecked member row
  simpa [Constant.toValue, Value.mapAddress, show rawAddMap.name = "UInt8::raw_add" from rfl, IxVM.Checked.source]
    using looked

theorem fromField_row {x : Nat} (hx : x < 256) :
    lookupMap IxVM.Checked.source.tables "UInt8::from_field" ([.field (x : F)] : List (SourceValue F)) =
      .ok (.field (x : F)) := by
  have member : fromFieldMap ∈ IxVM.Checked.coreTables.maps := List.getElem_mem _
  have rows : IxVM.Checked.coreTables.mapRows fromFieldMap =
      IxVM.Checked.byteInputsTable.rows.zip IxVM.Checked.byteValuesTable.rows := by
    simp only [Aiur.Program.mapRows, show fromFieldMap.input = "UInt8::byte_inputs" from rfl,
      show fromFieldMap.output = "UInt8::byte_values" from rfl, IxVM.Checked.find_byteInputs,
      IxVM.Checked.find_byteValues]
  have row : (⟨[.field (x : F)], .field (x : F)⟩ : MapEntry F) ∈
      IxVM.Checked.coreTables.mapEntries fromFieldMap := by
    apply Aiur.mapEntry_mem_iff.mpr
    rw [rows]
    simp only [IxVM.Checked.byteInputsTable, IxVM.Checked.byteValuesTable, List.map_map]
    convert mem_zip_map (List.mem_range.mpr hx) using 1
    simp [IxVM.Checked.coreRow, IxVM.Checked.coreLeaf]
  have looked := Aiur.lookupMap_of_entry (A := Nat) IxVM.Checked.tablesChecked member row
  simpa [Constant.toValue, Value.mapAddress, show fromFieldMap.name = "UInt8::from_field" from rfl, IxVM.Checked.source]
    using looked

/-! ## Maps are not functions -/

theorem rawSub_none : IxVM.Checked.source.program.sourceFunction? "UInt8::raw_sub" = none :=
  Program.sourceFunction?_of_key
    (IxVM.Checked.mapKeys_fresh _ (List.getElem_mem (l := IxVM.Checked.maps) (n := 5) (by decide)))
    (head_ne_of_bytes (by decide +kernel))

theorem rawAdd_none : IxVM.Checked.source.program.sourceFunction? "UInt8::raw_add" = none :=
  Program.sourceFunction?_of_key
    (IxVM.Checked.mapKeys_fresh _ (List.getElem_mem (l := IxVM.Checked.maps) (n := 4) (by decide)))
    (head_ne_of_bytes (by decide +kernel))

theorem fromField_none : IxVM.Checked.source.program.sourceFunction? "UInt8::from_field" = none :=
  Program.sourceFunction?_of_key
    (IxVM.Checked.mapKeys_fresh _ (List.getElem_mem (l := IxVM.Checked.maps) (n := 0) (by decide)))
    (head_ne_of_bytes (by decide +kernel))

/-! ## Mirrors of the byte helpers -/

theorem instanceName_plain (name : String) : instanceName [] name (some []) = name := by
  simp [instanceName, Instance.symbol]

/-- `UInt8::raw_lt(a, b)`: the borrow of `a - b`. -/
theorem rawLt {a b : Nat} (ha : a < 256) (hb : b < 256) {h h' : Heap F} {r : SourceValue F}
    (ev : EvalFn W "UInt8::raw_lt" [.field (a : F), .field (b : F)] h r h') :
    r = .field ((if a < b then 1 else 0 : Nat) : F) ∧ h' = h := by
  have body := ev.function_inv IxVM.Checked.Lookup.«UInt8::raw_lt»
    (by simp [IxVM.Checked.Fn.«UInt8::raw_lt», ControlLower.hasControl])
  simp only [IxVM.Checked.Fn.«UInt8::raw_lt»] at body
  obtain ⟨input, middle, bindings, value, matched, rest⟩ := body.letValue_inv
  obtain ⟨values, m1, args, callee⟩ := value.call_inv
  obtain ⟨v1, vs, m2, rfl, e1, args⟩ := args.cons_inv
  obtain ⟨v2, vs, m3, rfl, e2, args⟩ := args.cons_inv
  obtain ⟨rfl, rfl⟩ := args.nil_inv
  obtain ⟨l1, rfl⟩ := e1.var_inv
  obtain ⟨l2, rfl⟩ := e2.var_inv
  simp at l1 l2
  subst l1 l2
  rw [instanceName_plain] at callee
  obtain ⟨rfl, rfl⟩ := callee.map_inv rawSub_none (rawSub_row ha hb)
  simp [Constant.toValue, Value.mapAddress, matchPattern_tuple, matchListWith,
    matchPattern_wildcard, matchPattern_bind, pure, Except.pure, bind, Except.bind] at matched
  subst matched
  obtain ⟨l, rfl⟩ := rest.var_inv
  simp at l
  subst l
  simp

/-- `UInt8::less_than(a, b)`: `1` if `a < b`, else `0`. -/
theorem lessThan {a b : Nat} (ha : a < 256) (hb : b < 256) {h h' : Heap F} {r : SourceValue F}
    (ev : EvalFn W "UInt8::less_than" [.field (a : F), .field (b : F)] h r h') :
    r = .field ((if a < b then 1 else 0 : Nat) : F) ∧ h' = h := by
  have body := ev.function_inv IxVM.Checked.Lookup.«UInt8::less_than»
    (by simp [IxVM.Checked.Fn.«UInt8::less_than», ControlLower.hasControl])
  simp only [IxVM.Checked.Fn.«UInt8::less_than»] at body
  obtain ⟨values, m1, args, callee⟩ := body.call_inv
  obtain ⟨v1, vs, m2, rfl, e1, args⟩ := args.cons_inv
  obtain ⟨v2, vs, m3, rfl, e2, args⟩ := args.cons_inv
  obtain ⟨rfl, rfl⟩ := args.nil_inv
  obtain ⟨l1, rfl⟩ := e1.var_inv
  obtain ⟨l2, rfl⟩ := e2.var_inv
  simp at l1 l2
  subst l1 l2
  rw [instanceName_plain] at callee
  exact rawLt ha hb callee

/-- `UInt8::to_field(x)`: `x`. -/
theorem toField {x : F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalFn W "UInt8::to_field" [.field x] h r h') : r = .field x ∧ h' = h := by
  have body := ev.function_inv IxVM.Checked.Lookup.«UInt8::to_field»
    (by simp [IxVM.Checked.Fn.«UInt8::to_field», ControlLower.hasControl])
  simp only [IxVM.Checked.Fn.«UInt8::to_field»] at body
  obtain ⟨l, rfl⟩ := body.var_inv
  simp at l
  subst l
  exact ⟨rfl, rfl⟩

/-! ## Constants -/

theorem global_literal {types : Types} {locals : Environment F Nat} {name : String} {x : F}
    (hc : W.constant name .field = .ok (.literal x)) {before after : Heap F} {r : SourceValue F}
    (h : EvalExpr W types locals (.global name (some .field)) before r after) :
    r = .field x ∧ after = before := by
  obtain ⟨pattern, body, lookup, interpreted, value⟩ := h.global_inv
  simp only [Ty.subst, hc, Except.ok.injEq] at lookup
  subst lookup
  simp only [Consts.toExpr, pure, Except.pure, Except.ok.injEq] at interpreted
  subst interpreted
  exact value.literal_inv

theorem byte0 : W.constant "UInt8::BYTE_0" .field = .ok (.literal 0) :=
  eq_of_isLiteral (by decide +kernel)

theorem byte128 : W.constant "UInt8::BYTE_128" .field = .ok (.literal 128) :=
  eq_of_isLiteral (by decide +kernel)

/-! ## The byte stream -/

/-- `Lists::Node<UInt8::U8>`'s constructor name is the byte-stream enum. -/
theorem node_ctor : constructorName [] (.named "Lists::Node" [.field]) = byteStreamEnum := by
  decide +kernel

/-- **Reading a byte off the stream**: the `let Cons(byte, s) = load(stream)`
every TagN reader starts with binds the head byte and the tail pointer. -/
theorem readCons {locals : Environment F Nat} {stream : SourceValue F} {byte s : String}
    {rest : Aiur.Generic.Expr F} {heap h' : Heap F} {r : SourceValue F} {bytes : List UInt8}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum heap bytes stream)
    (look : locals.find? (·.1 == "stream") = some ("stream", stream))
    (ev : EvalExpr W [] locals (.letValue
      (.construct (.named "Lists::Node" [.field]) "Cons" [.bind byte, .bind s])
      (.load (.var "stream")) rest) heap r h') :
    ∃ b tail tailPtr, bytes = b :: tail ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum heap tail tailPtr ∧
      EvalExpr W [] ([(byte, .field (b.toNat : F)), (s, tailPtr)] ++ locals) rest heap r h' := by
  obtain ⟨input, middle, bindings, value, matched, body⟩ := ev.letValue_inv
  obtain ⟨p, pointer, loaded⟩ := value.load_inv
  obtain ⟨l, rfl⟩ := pointer.var_inv
  rw [look] at l
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at l
  subst l
  cases rep with
  | nil cell =>
    simp [loadValue, cell, Value.type, bind, Except.bind, pure, Except.pure] at loaded
    subst loaded
    simp [matchPattern_construct, node_ctor] at matched
  | cons cell headRep tailRep =>
    simp [loadValue, cell, Value.type, bind, Except.bind, pure, Except.pure] at loaded
    subst loaded
    simp only [Aiur.Library.RepU8] at headRep
    subst headRep
    simp [matchPattern_construct, node_ctor, matchListWith, matchPattern_bind, bind, Except.bind,
      pure, Except.pure] at matched
    subst matched
    exact ⟨_, _, _, rfl, tailRep, body⟩

/-! ## Little-endian words -/

/-- **A `UInt64` as IxVM holds it**: eight byte fields, least significant
first. -/
def u64Value (n : Nat) : SourceValue F :=
  .tuple [.field ((n % 256 : Nat) : F), .field ((n / 256 % 256 : Nat) : F),
    .field ((n / 65536 % 256 : Nat) : F), .field ((n / 16777216 % 256 : Nat) : F),
    .field ((n / 4294967296 % 256 : Nat) : F), .field ((n / 1099511627776 % 256 : Nat) : F),
    .field ((n / 281474976710656 % 256 : Nat) : F), .field ((n / 72057594037927936 % 256 : Nat) : F)]

theorem u64Value_two {x y : Nat} (hx : x < 256) (hy : y < 256) :
    u64Value (x + 256 * y) = .tuple [.field (x : F), .field (y : F), .field 0, .field 0, .field 0,
      .field 0, .field 0, .field 0] := by
  simp only [u64Value]
  rw [show (x + 256 * y) % 256 = x by omega, show (x + 256 * y) / 256 % 256 = y by omega,
    show (x + 256 * y) / 65536 % 256 = 0 by omega, show (x + 256 * y) / 16777216 % 256 = 0 by omega,
    show (x + 256 * y) / 4294967296 % 256 = 0 by omega,
    show (x + 256 * y) / 1099511627776 % 256 = 0 by omega,
    show (x + 256 * y) / 281474976710656 % 256 = 0 by omega,
    show (x + 256 * y) / 72057594037927936 % 256 = 0 by omega]
  simp

/-- Arguments that are all `UInt8::BYTE_0` evaluate to zeros. -/
theorem args_zeros {locals : Environment F Nat} :
    ∀ {es : List (Aiur.Generic.Expr F)}, (∀ e ∈ es, e = .global "UInt8::BYTE_0" (some .field)) →
      ∀ {vs : List (SourceValue F)} {before after : Heap F},
        EvalArgs W [] locals es before vs after → vs = es.map (fun _ => .field 0) ∧ after = before
  | [], _, _, _, _, h => by obtain ⟨rfl, rfl⟩ := h.nil_inv; exact ⟨rfl, rfl⟩
  | e :: es, all, _, _, _, h => by
    obtain ⟨v, vs, middle, rfl, head, tail⟩ := h.cons_inv
    rw [all e (by simp)] at head
    obtain ⟨rfl, rfl⟩ := global_literal byte0 head
    obtain ⟨rfl, rfl⟩ := args_zeros (fun x hx => all x (by simp [hx])) tail
    exact ⟨rfl, rfl⟩

/-! ## The TagN readers -/

/-- **`IxonDeserialize::get_tagn_tail(q, h, stream)` with `q < h`**: the
two-byte rung, `2h + 256q + lo` for the next byte `lo`. -/
theorem tagnTail_short {q hh : Nat} (hq : q < hh) (hh' : hh < 128) {stream r : SourceValue F}
    {heap h' : Heap F} {bytes : List UInt8}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum heap bytes stream)
    (ev : EvalFn W "IxonDeserialize::get_tagn_tail" [.field (q : F), .field (hh : F), stream]
      heap r h') :
    h' = heap ∧ ∃ lo tail tailPtr, bytes = lo :: tail ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum heap tail tailPtr ∧
      r = .tuple [u64Value (2 * hh + q * 256 + lo.toNat), tailPtr] := by
  have body := ev.function_inv IxVM.Checked.Lookup.«IxonDeserialize::get_tagn_tail»
    (by simp [IxVM.Checked.Fn.«IxonDeserialize::get_tagn_tail», ControlLower.hasControl])
  simp only [IxVM.Checked.Fn.«IxonDeserialize::get_tagn_tail»] at body
  obtain ⟨input, middle, bindings, arm, value, selected, branch⟩ := body.matchValue_inv
  -- the borrow of `q - h`
  obtain ⟨values, m1, args, callee⟩ := value.call_inv
  obtain ⟨v1, vs, m2, rfl, e1, args⟩ := args.cons_inv
  obtain ⟨v2, vs, m3, rfl, e2, args⟩ := args.cons_inv
  obtain ⟨rfl, rfl⟩ := args.nil_inv
  obtain ⟨l1, rfl⟩ := e1.var_inv
  obtain ⟨l2, rfl⟩ := e2.var_inv
  simp at l1 l2
  subst l1 l2
  rw [instanceName_plain] at callee
  obtain ⟨rfl, rfl⟩ := rawLt (by omega) (by omega) callee
  clear e1 e2 callee
  simp [hq, SourceSemantics.selectArm, matchPattern_literal, bind, Except.bind, pure, Except.pure] at selected
  obtain ⟨rfl, rfl⟩ := selected
  -- read the low byte
  obtain ⟨lo, tail, tailPtr, rfl, tailRep, body⟩ := readCons rep (by simp) branch
  refine ⟨?_, lo, tail, tailPtr, rfl, tailRep, ?_⟩ <;> clear rep
  all_goals
    obtain ⟨sum, m4, bnds, pairs, matched, rest⟩ := body.letValue_inv
    obtain ⟨values, m5, args, callee⟩ := pairs.call_inv
    obtain ⟨v1, vs, m6, rfl, e1, args⟩ := args.cons_inv
    obtain ⟨v2, vs, m7, rfl, e2, args⟩ := args.cons_inv
    obtain ⟨rfl, rfl⟩ := args.nil_inv
    -- `to_field(lo)`
    obtain ⟨ws, m8, wargs, wcallee⟩ := e1.call_inv
    obtain ⟨w1, ws', m9, rfl, we1, wargs⟩ := wargs.cons_inv
    obtain ⟨rfl, rfl⟩ := wargs.nil_inv
    obtain ⟨l3, rfl⟩ := we1.var_inv
    simp at l3
    subst l3
    rw [instanceName_plain] at wcallee
    obtain ⟨rfl, rfl⟩ := toField wcallee
    -- `2 * h`
    obtain ⟨x, y, m10, ex, ey, op⟩ := e2.binary_inv
    obtain ⟨rfl, rfl⟩ := ex.literal_inv
    obtain ⟨l4, rfl⟩ := ey.var_inv
    simp at l4
    subst l4
    simp only [evalBinOp, Except.ok.injEq] at op
    subst op
    rw [instanceName_plain, show (2 : F) * (hh : F) = ((2 * hh : Nat) : F) by push_cast; ring]
      at callee
    obtain ⟨rfl, rfl⟩ := callee.map_inv rawAdd_none (rawAdd_row lo.toNat_lt (by omega))
    simp [Constant.toValue, Value.mapAddress, matchPattern_tuple, matchListWith,
      matchPattern_bind, pure, Except.pure, bind, Except.bind] at matched
    subst matched
    -- the result
    obtain ⟨items, rargs, rfl⟩ := rest.tuple_inv
    obtain ⟨word, ptr, m11, rfl, eword, rargs⟩ := rargs.cons_inv
    obtain ⟨ptr', none', m12, rfl, eptr, rargs⟩ := rargs.cons_inv
    obtain ⟨rfl, rfl⟩ := rargs.nil_inv
    obtain ⟨l5, rfl⟩ := eptr.var_inv
    simp at l5
    subst l5
    obtain ⟨bytes8, wargs, rfl⟩ := eword.array_inv
    obtain ⟨b0, bs, m13, rfl, eb0, wargs⟩ := wargs.cons_inv
    obtain ⟨b1, bs, m14, rfl, eb1, wargs⟩ := wargs.cons_inv
    obtain ⟨rfl, rfl⟩ := args_zeros (by simp) wargs
    obtain ⟨l6, rfl⟩ := eb0.var_inv
    simp at l6
    subst l6
    -- `from_field(q + to_field(carry))`
    obtain ⟨fs, m15, fargs, fcallee⟩ := eb1.call_inv
    obtain ⟨f1, fs', m16, rfl, fe1, fargs⟩ := fargs.cons_inv
    obtain ⟨rfl, rfl⟩ := fargs.nil_inv
    obtain ⟨x', y', m17, ex', ey', op'⟩ := fe1.binary_inv
    obtain ⟨l7, rfl⟩ := ex'.var_inv
    simp at l7
    subst l7
    obtain ⟨cs, m18, cargs, ccallee⟩ := ey'.call_inv
    obtain ⟨c1, cs', m19, rfl, ce1, cargs⟩ := cargs.cons_inv
    obtain ⟨rfl, rfl⟩ := cargs.nil_inv
    obtain ⟨l8, rfl⟩ := ce1.var_inv
    simp at l8
    subst l8
    rw [instanceName_plain] at ccallee
    obtain ⟨rfl, rfl⟩ := toField ccallee
    simp only [evalBinOp, Except.ok.injEq] at op'
    subst op'
    rw [instanceName_plain, show ((q : Nat) : F) + (((lo.toNat + 2 * hh) / 256 : Nat) : F) =
      ((q + (lo.toNat + 2 * hh) / 256 : Nat) : F) by push_cast; ring] at fcallee
    have hlo := lo.toNat_lt
    obtain ⟨rfl, rfl⟩ := fcallee.map_inv fromField_none (fromField_row (by omega))
  · rfl
  · rw [show 2 * hh + q * 256 + lo.toNat =
        (lo.toNat + 2 * hh) % 256 + 256 * (q + (lo.toNat + 2 * hh) / 256) by omega,
      u64Value_two (Nat.mod_lt _ (by omega)) (by omega)]
    simp [Constant.toValue, Value.mapAddress]

/-- **`IxonDeserialize::get_tagn0(stream)` on its one- and two-byte rungs**:
a first byte `b` below `128` is the value; a first byte in `[128, 192)` and the
next byte `lo` give `128 + 256 (b - 128) + lo`. The heap is unchanged. -/
theorem tagn0 {stream r : SourceValue F} {heap h' : Heap F} {bytes : List UInt8}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum heap bytes stream)
    (narrow : ∀ b ∈ bytes.head?, b.toNat < 192)
    (ev : EvalFn W "IxonDeserialize::get_tagn0" [stream] heap r h') :
    h' = heap ∧ ∃ b rest, bytes = b :: rest ∧
      ((b.toNat < 128 ∧ ∃ restPtr, Aiur.Library.Bytes.RepByteStream byteStreamEnum heap rest restPtr ∧
          r = .tuple [u64Value b.toNat, restPtr]) ∨
        (128 ≤ b.toNat ∧ ∃ lo rest' restPtr, rest = lo :: rest' ∧
          Aiur.Library.Bytes.RepByteStream byteStreamEnum heap rest' restPtr ∧
          r = .tuple [u64Value (128 + (b.toNat - 128) * 256 + lo.toNat), restPtr])) := by
  have body := ev.function_inv IxVM.Checked.Lookup.«IxonDeserialize::get_tagn0»
    (by simp [IxVM.Checked.Fn.«IxonDeserialize::get_tagn0», ControlLower.hasControl])
  simp only [IxVM.Checked.Fn.«IxonDeserialize::get_tagn0»] at body
  obtain ⟨b, tail, tailPtr, rfl, tailRep, body⟩ := readCons rep (by simp) body
  have hb := b.toNat_lt
  have hnarrow : b.toNat < 192 := narrow b (by simp)
  obtain ⟨input, middle, bindings, arm, value, selected, branch⟩ := body.matchValue_inv
  -- `less_than(byte, BYTE_128)`
  obtain ⟨values, m1, args, callee⟩ := value.call_inv
  obtain ⟨v1, vs, m2, rfl, e1, args⟩ := args.cons_inv
  obtain ⟨v2, vs, m3, rfl, e2, args⟩ := args.cons_inv
  obtain ⟨rfl, rfl⟩ := args.nil_inv
  obtain ⟨l1, rfl⟩ := e1.var_inv
  simp at l1
  subst l1
  obtain ⟨rfl, rfl⟩ := global_literal byte128 e2
  rw [instanceName_plain, show (128 : F) = ((128 : Nat) : F) by simp] at callee
  obtain ⟨rfl, rfl⟩ := lessThan hb (by omega) callee
  by_cases small : b.toNat < 128
  · -- one byte
    simp [small, SourceSemantics.selectArm, matchPattern_literal, bind, Except.bind, pure, Except.pure] at selected
    obtain ⟨rfl, rfl⟩ := selected
    obtain ⟨items, rargs, rfl⟩ := branch.tuple_inv
    obtain ⟨word, ptr, m4, rfl, eword, rargs⟩ := rargs.cons_inv
    obtain ⟨ptr', none', m5, rfl, eptr, rargs⟩ := rargs.cons_inv
    obtain ⟨rfl, rfl⟩ := rargs.nil_inv
    obtain ⟨l2, rfl⟩ := eptr.var_inv
    simp at l2
    subst l2
    obtain ⟨bytes8, wargs, rfl⟩ := eword.array_inv
    obtain ⟨b0, bs, m6, rfl, eb0, wargs⟩ := wargs.cons_inv
    obtain ⟨rfl, rfl⟩ := args_zeros (by simp) wargs
    obtain ⟨l3, rfl⟩ := eb0.var_inv
    simp at l3
    subst l3
    refine ⟨rfl, b, tail, rfl, .inl ⟨small, tailPtr, tailRep, ?_⟩⟩
    rw [show b.toNat = b.toNat + 256 * 0 by omega, u64Value_two hb (by omega)]
    simp
  · -- two bytes
    have one_ne : (1 : F) ≠ 0 := one_ne_zero
    simp [small, SourceSemantics.selectArm, matchPattern_literal, one_ne, bind, Except.bind, pure,
      Except.pure] at selected
    obtain ⟨rfl, rfl⟩ := selected
    clear e1 e2 callee
    obtain ⟨values, m4, targs, callee⟩ := branch.call_inv
    obtain ⟨v1, vs, m5, rfl, t1, targs⟩ := targs.cons_inv
    obtain ⟨v2, vs, m6, rfl, t2, targs⟩ := targs.cons_inv
    obtain ⟨v3, vs, m7, rfl, t3, targs⟩ := targs.cons_inv
    obtain ⟨rfl, rfl⟩ := targs.nil_inv
    -- `to_field(byte) - 128`
    obtain ⟨x, y, m8, ex, ey, op⟩ := t1.binary_inv
    obtain ⟨ws, m9, wargs, wcallee⟩ := ex.call_inv
    obtain ⟨w1, ws', m10, rfl, we1, wargs⟩ := wargs.cons_inv
    obtain ⟨rfl, rfl⟩ := wargs.nil_inv
    obtain ⟨l4, rfl⟩ := we1.var_inv
    simp at l4
    subst l4
    rw [instanceName_plain] at wcallee
    obtain ⟨rfl, rfl⟩ := toField wcallee
    obtain ⟨rfl, rfl⟩ := ey.literal_inv
    simp only [evalBinOp, Except.ok.injEq] at op
    subst op
    obtain ⟨rfl, rfl⟩ := t2.literal_inv
    obtain ⟨l5, rfl⟩ := t3.var_inv
    simp at l5
    subst l5
    rw [instanceName_plain,
      show ((b.toNat : Nat) : F) - 128 = ((b.toNat - 128 : Nat) : F) by
        rw [Nat.cast_sub (by omega)]; simp,
      show (64 : F) = ((64 : Nat) : F) by simp] at callee
    obtain ⟨rfl, lo, rest', restPtr, rfl, restRep, rfl⟩ :=
      tagnTail_short (q := b.toNat - 128) (hh := 64) (by omega) (by omega) tailRep callee
    refine ⟨rfl, b, lo :: rest', rfl, .inr ⟨by omega, lo, rest', restPtr, rfl, restRep, ?_⟩⟩
    rw [show 2 * 64 + (b.toNat - 128) * 256 + lo.toNat = 128 + (b.toNat - 128) * 256 + lo.toNat by
      omega]

/-! ## IxC's reader on the same bytes -/

/-- The state `Ixon.getTagN` starts from on the stream's bytes. -/
def start (bytes : List UInt8) : Ixon.GetState := { idx := 0, bytes := ⟨bytes.toArray⟩ }

theorem getU8_at {bytes : List UInt8} {i : Nat} (hi : i < bytes.length) :
    Ixon.getU8 { idx := i, bytes := ⟨bytes.toArray⟩ } =
      .ok bytes[i] { idx := i + 1, bytes := ⟨bytes.toArray⟩ } := by
  have hs : i < (ByteArray.mk bytes.toArray).size := by simpa [ByteArray.size] using hi
  simp only [Ixon.getU8, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, set,
    MonadStateOf.set, EStateM.set, pure, EStateM.pure, hs, ite_true]
  rw [getElem!_pos (ByteArray.mk bytes.toArray) i hs]
  rfl

/-- **IxC's `getTagN 0`, one byte**: a first byte below `128` is the value. -/
theorem getTagN0_one {b : UInt8} {rest : List UInt8} (small : b.toNat < 128) :
    Ixon.getTagN 0 (start (b :: rest)) =
      .ok ⟨0, b.toNat.toUInt64⟩ { idx := 1, bytes := ⟨(b :: rest).toArray⟩ } := by
  have read := getU8_at (bytes := b :: rest) (i := 0) (by simp)
  simp only [start, Ixon.getTagN, bind, EStateM.bind, read]
  simp [small, pure, EStateM.pure, Nat.mod_eq_of_lt (show b.toNat < 256 from b.toNat_lt),
    Nat.div_eq_of_lt (show b.toNat < 256 from b.toNat_lt)]

/-- **IxC's `getTagN 0`, two bytes**: a first byte `b` in `[128, 192)` and the
next byte `lo` give `128 + 256 (b - 128) + lo`. -/
theorem getTagN0_two {b lo : UInt8} {rest : List UInt8} (lower : 128 ≤ b.toNat)
    (upper : b.toNat < 192) :
    Ixon.getTagN 0 (start (b :: lo :: rest)) =
      .ok ⟨0, (128 + (b.toNat - 128) * 256 + lo.toNat).toUInt64⟩
        { idx := 2, bytes := ⟨(b :: lo :: rest).toArray⟩ } := by
  have read0 := getU8_at (bytes := b :: lo :: rest) (i := 0) (by simp)
  have read1 := getU8_at (bytes := b :: lo :: rest) (i := 1) (by simp)
  have hb := b.toNat_lt
  simp only [start, Ixon.getTagN, bind, EStateM.bind, read0, Nat.zero_add]
  simp only [Nat.reduceSub, Nat.reducePow, Nat.mod_eq_of_lt hb, show ¬ b.toNat < 128 by omega,
    ite_false, show b.toNat - 128 < 64 by omega, ite_true, List.getElem_cons_zero]
  simp [EStateM.bind, read1, pure, EStateM.pure, Ixon.tagNEnd1, Nat.div_eq_of_lt hb]

/-! ## The refinement -/

/-- **IxVM's `get_tagn0` refines IxC's `Ixon.getTagN 0` on the one- and
two-byte rungs**: every derivation of `IxonDeserialize::get_tagn0` on a stream
of `bytes` whose first byte is below `192` (the codes the wide rungs do not
use) is matched by IxC's reader on the same bytes: it succeeds with flag `0`
and the value the derivation returns as eight little-endian bytes, and the
derivation's rest pointer holds the bytes IxC's reader did not consume. The
heap is unchanged. The wide rungs (a first byte from `192`, through
`IxonDeserialize::get_tagn_wide`) are not covered here. -/
theorem getTagN0_refines {stream r : SourceValue F} {heap h' : Heap F} {bytes : List UInt8}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum heap bytes stream)
    (narrow : ∀ b ∈ bytes.head?, b.toNat < 192)
    (ev : EvalFn W "IxonDeserialize::get_tagn0" [stream] heap r h') :
    h' = heap ∧ ∃ (t : Ixon.TagN) (n : Nat) (restPtr : SourceValue F),
      Ixon.getTagN 0 (start bytes) = .ok t { idx := n, bytes := ⟨bytes.toArray⟩ } ∧ t.flag = 0 ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum heap (bytes.drop n) restPtr ∧
      r = .tuple [u64Value t.value.toNat, restPtr] := by
  obtain ⟨rfl, b, rest, rfl, cases⟩ := tagn0 rep narrow ev
  refine ⟨rfl, ?_⟩
  rcases cases with ⟨small, restPtr, restRep, rfl⟩ | ⟨lower, lo, rest', restPtr, rfl, restRep, rfl⟩
  · refine ⟨_, 1, restPtr, getTagN0_one small, rfl, by simpa using restRep, ?_⟩
    simp only [UInt64.toNat_ofNat', Nat.toUInt64_eq]
    rw [Nat.mod_eq_of_lt (by have := b.toNat_lt; omega)]
  · have upper : b.toNat < 192 := narrow b (by simp)
    refine ⟨_, 2, restPtr, getTagN0_two lower upper, rfl, by simpa using restRep, ?_⟩
    simp only [UInt64.toNat_ofNat', Nat.toUInt64_eq]
    rw [Nat.mod_eq_of_lt (by have := lo.toNat_lt; omega)]

end IxVM.Refinement.TagN
