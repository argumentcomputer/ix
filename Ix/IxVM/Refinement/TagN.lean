import Ix.IxVM.Refinement.Mirrors.TagN
import Ix.IxVM.Refinement.Statement

/-! # The TagN slice: IxVM's TagN decoder against IxC's `Ixon.getTagN`

Track B, Phase 3's first vertical slice (`plans/ixvm-certification-gap.md`).
The mechanical layer is generated (`Ix.IxVM.Refinement.Mirrors.TagN`: a
mirror per function and its lemma `of_eval`, every derivation is a run of the
mirror). This module is the creative layer on top of it:

* the byte maps' rows (`rawSub_row`, `rawAdd_row`, `fromField_row`), from the
  table generator and `tablesChecked`;
* `getU64le_complete`: the lemma of the one recursive function,
  `get_u64_le`, by induction on its byte count;
* what the mirrors compute (`*_run`);
* the refinements of IxC's `Ixon.getTagN 0`, `2` and `4` on the one- and two-byte
  rungs (`getTagN{0,2,4}_refines_short`), and the 64-bit machinery of the wide rungs
  (`getU64le_run`, `u64Add_value`). The wide rungs and the refinements on every header
  are in `Ix.IxVM.Refinement.TagNWide`. -/

namespace IxVM.Refinement.TagN

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM.Checked (F)

set_option linter.unusedSimpArgs false

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

/-! ## The byte stream -/

/-- `Lists::Node<UInt8::U8>`'s constructor name is the byte-stream enum. -/
theorem node_ctor : constructorName [] (.named "Lists::Node" [.field]) = byteStreamEnum := by
  decide +kernel

theorem loadValue_cell {heap : Heap F} {addr : Nat} {c : String} {xs : List (SourceValue F)}
    (cell : heap[addr]? = some (.construct byteStreamEnum c xs)) :
    loadValue heap (.ptr (.enum byteStreamEnum) addr) = .ok (.construct byteStreamEnum c xs) := by
  simp [loadValue, cell, Value.type, bind, Except.bind, pure, Except.pure]

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


/-! ## `get_u64_le`, the recursive function -/

/-- The byte count `get_u64_le` recurses on, as a number. -/
def u64Measure : SourceValue F → Nat
  | .field n => n.val
  | _ => 0

theorem u64Measure_dec {x y : SourceValue F} (hc : x ≠ .field 0)
    (op : evalBinOp .sub x (.field 1) = .ok y) : u64Measure y < u64Measure x := by
  cases x with
  | field n =>
    simp only [evalBinOp, Except.ok.injEq] at op
    subst op
    have hn : n ≠ 0 := fun e => hc (by rw [e])
    have hv : n.val ≠ 0 := by rwa [ne_eq, ZMod.val_eq_zero]
    have hsum : (n - 1) + 1 = n := by ring
    have key := congrArg ZMod.val hsum
    rw [ZMod.val_add, ZMod.val_one] at key
    have hlt := ZMod.val_lt (n - 1)
    simp only [u64Measure]
    by_cases h : (n - 1).val + 1 < Aiur.Library.U32.Goldilocks.modulus
    · rw [Nat.mod_eq_of_lt h] at key
      omega
    · have heq : (n - 1).val + 1 = Aiur.Library.U32.Goldilocks.modulus := by omega
      rw [heq, Nat.mod_self] at key
      omega
  | _ => simp [evalBinOp] at op

/-- **Every derivation of `get_u64_le` is a run of its mirror**, by strong
induction on the byte count. The script is the generator's, with the
recursive call taken from the induction hypothesis. -/
theorem getU64le_complete : Mirrors.«IxonDeserialize::get_u64_le».Complete := by
  suffices H : ∀ m, ∀ {x_stream x_num_bytes : SourceValue F} {h h' : Heap F} {r : SourceValue F},
      u64Measure x_num_bytes = m →
      EvalFn W "IxonDeserialize::get_u64_le" [x_stream, x_num_bytes] h r h' →
      ∃ k0, ∀ k ≥ k0, Mirrors.«IxonDeserialize::get_u64_le» k h x_stream x_num_bytes = some (r, h') by
    intro x_stream x_num_bytes h h' r ev
    exact H _ rfl ev
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro x_stream x_num_bytes h h' r hm ev
  have body := ev.function_inv IxVM.Checked.Lookup.«IxonDeserialize::get_u64_le»
    (by simp [IxVM.Checked.Fn.«IxonDeserialize::get_u64_le», ControlLower.hasControl])
  simp only [IxVM.Checked.Fn.«IxonDeserialize::get_u64_le»] at body
  obtain ⟨v1, m2, bs3, body4, d5, sel6, d7⟩ := body.matchValue_inv
  obtain ⟨l8, rfl⟩ := d5.var_inv
  simp at l8
  subst l8
  rcases selectArm_literal_inv sel6 with ⟨hc9, rfl, rfl⟩ | ⟨hc9, sel10⟩
  · obtain ⟨vs11, args12, rfl⟩ := d7.tuple_inv
    obtain ⟨v13, vs14, m15, rfl, d16, args17⟩ := args12.cons_inv
    obtain ⟨v18, d19, rfl⟩ := d16.repeat_inv
    obtain ⟨rfl, rfl⟩ := d19.global_literal_inv (x := (0 : F)) (eq_of_isLiteral (by decide +kernel))
    obtain ⟨v20, vs21, m22, rfl, d23, args24⟩ := args17.cons_inv
    obtain ⟨l25, rfl⟩ := d23.var_inv
    simp at l25
    subst l25
    obtain ⟨rfl, rfl⟩ := args24.nil_inv
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp (config := { decide := true }) [Mirrors.«IxonDeserialize::get_u64_le», hc9]
  · obtain ⟨rfl, rfl⟩ := selectArm_wildcard_inv sel10
    obtain ⟨v26, m27, bs28, d29, mt30, d31⟩ := d7.letValue_inv
    obtain ⟨p32, d33, ld34⟩ := d29.load_inv
    obtain ⟨l35, rfl⟩ := d33.var_inv
    simp at l35
    subst l35
    obtain ⟨ys36, hp37, hl38, ml39⟩ := matchPattern_construct_inv mt30
    rcases ys36 with _ | ⟨y40, _ | ⟨y41, _ | ⟨_, _⟩⟩⟩ <;> simp at hl38
    simp [matchListWith, matchPattern_bind, matchPattern_wildcard, bind, Except.bind, pure,
      Except.pure] at ml39
    subst ml39
    obtain ⟨v42, m43, bs44, d45, mt46, d47⟩ := d31.letValue_inv
    obtain ⟨vs48, m49, args50, callee51⟩ := d45.call_inv
    obtain ⟨v52, vs53, m54, rfl, d55, args56⟩ := args50.cons_inv
    obtain ⟨l57, rfl⟩ := d55.var_inv
    simp at l57
    subst l57
    obtain ⟨v58, vs59, m60, rfl, d61, args62⟩ := args56.cons_inv
    obtain ⟨x63, y64, m65, d66, d67, op68⟩ := d61.binary_inv
    obtain ⟨l69, rfl⟩ := d66.var_inv
    simp at l69
    subst l69
    obtain ⟨rfl, rfl⟩ := d67.literal_inv
    obtain ⟨rfl, rfl⟩ := args62.nil_inv
    rw [instanceName_plain_some] at callee51
    have dec : u64Measure v58 < m := by rw [← hm]; exact u64Measure_dec hc9 op68
    obtain ⟨k70, hk71⟩ := ih _ dec rfl callee51
    obtain ⟨ys72, hp73, hl74, ml75⟩ := matchPattern_tuple_inv mt46
    rcases ys72 with _ | ⟨y76, _ | ⟨y77, _ | ⟨_, _⟩⟩⟩ <;> simp at hl74
    simp [matchListWith, matchPattern_bind, matchPattern_wildcard, bind, Except.bind, pure,
      Except.pure] at ml75
    subst ml75
    obtain ⟨v78, m79, bs80, d81, mt82, d83⟩ := d47.letValue_inv
    obtain ⟨l84, rfl⟩ := d81.var_inv
    simp at l84
    subst l84
    obtain ⟨ys85, hp86, hl87, ml88⟩ := matchPattern_array_inv mt82
    rcases ys85 with _ | ⟨z0, _ | ⟨z1, _ | ⟨z2, _ | ⟨z3, _ | ⟨z4, _ | ⟨z5, _ | ⟨z6, _ | ⟨z7, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      simp at hl87
    simp [matchListWith, matchPattern_bind, matchPattern_wildcard, bind, Except.bind, pure,
      Except.pure] at ml88
    subst ml88
    obtain ⟨vs89, args90, rfl⟩ := d83.tuple_inv
    obtain ⟨w91, ws92, m93, rfl, f94, args95⟩ := args90.cons_inv
    obtain ⟨vs96, args97, rfl⟩ := f94.array_inv
    obtain ⟨u0, us0, mu0, rfl, g0, args107⟩ := args97.cons_inv
    obtain ⟨lu0, rfl⟩ := g0.var_inv
    simp at lu0
    subst lu0
    obtain ⟨u1, us1, mu1, rfl, g1, args117⟩ := args107.cons_inv
    obtain ⟨lu1, rfl⟩ := g1.var_inv
    simp at lu1
    subst lu1
    obtain ⟨u2, us2, mu2, rfl, g2, args127⟩ := args117.cons_inv
    obtain ⟨lu2, rfl⟩ := g2.var_inv
    simp at lu2
    subst lu2
    obtain ⟨u3, us3, mu3, rfl, g3, args137⟩ := args127.cons_inv
    obtain ⟨lu3, rfl⟩ := g3.var_inv
    simp at lu3
    subst lu3
    obtain ⟨u4, us4, mu4, rfl, g4, args147⟩ := args137.cons_inv
    obtain ⟨lu4, rfl⟩ := g4.var_inv
    simp at lu4
    subst lu4
    obtain ⟨u5, us5, mu5, rfl, g5, args157⟩ := args147.cons_inv
    obtain ⟨lu5, rfl⟩ := g5.var_inv
    simp at lu5
    subst lu5
    obtain ⟨u6, us6, mu6, rfl, g6, args167⟩ := args157.cons_inv
    obtain ⟨lu6, rfl⟩ := g6.var_inv
    simp at lu6
    subst lu6
    obtain ⟨u7, us7, mu7, rfl, g7, args177⟩ := args167.cons_inv
    obtain ⟨lu7, rfl⟩ := g7.var_inv
    simp at lu7
    subst lu7
    obtain ⟨rfl, rfl⟩ := args177.nil_inv
    obtain ⟨w98, ws99, m100, rfl, f101, args102⟩ := args95.cons_inv
    obtain ⟨l103, rfl⟩ := f101.var_inv
    simp at l103
    subst l103
    obtain ⟨rfl, rfl⟩ := args102.nil_inv
    refine ⟨k70 + 1, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp (config := { decide := true, maxSteps := 10000000 }) [Mirrors.«IxonDeserialize::get_u64_le»,
      hc9, ld34, hp37, op68, hk71 k' (by omega), hp73, hp86]

/-! ## What the mirrors compute -/

theorem rawLt_run {a b : Nat} (ha : a < 256) (hb : b < 256) (k : Nat) (h : Heap F) :
    Mirrors.«UInt8::raw_lt» (k + 1) h (.field (a : F)) (.field (b : F)) =
      some (.field ((if a < b then 1 else 0 : Nat) : F), h) := by
  simp [Mirrors.«UInt8::raw_lt», mapCall, rawSub_row ha hb, Constant.toValue, Value.mapAddress]

theorem lessThan_run {a b : Nat} (ha : a < 256) (hb : b < 256) (k : Nat) (h : Heap F) :
    Mirrors.«UInt8::less_than» (k + 2) h (.field (a : F)) (.field (b : F)) =
      some (.field ((if a < b then 1 else 0 : Nat) : F), h) := by
  simp only [Mirrors.«UInt8::less_than»]
  exact rawLt_run ha hb k h

theorem toField_run (k : Nat) (h : Heap F) (x : SourceValue F) :
    Mirrors.«UInt8::to_field» (k + 1) h x = some (x, h) := by
  simp [Mirrors.«UInt8::to_field»]

/-- **`get_tagn_tail(q, h, stream)` with `q < h`**: the two-byte rung,
`2h + 256q + lo` for the stream's next byte `lo`. -/
theorem tailShort_run {q hh : Nat} (hq : q < hh) (hh' : hh < 128) {heap : Heap F} {addr : Nat}
    {lo : UInt8} {tailPtr : SourceValue F}
    (cell : heap[addr]? = some (.construct byteStreamEnum "Cons" [.field (lo.toNat : F), tailPtr]))
    (k : Nat) :
    Mirrors.«IxonDeserialize::get_tagn_tail» (k + 2) heap (.field (q : F)) (.field (hh : F))
        (.ptr (.enum byteStreamEnum) addr) =
      some (.tuple [u64Value (2 * hh + q * 256 + lo.toNat), tailPtr], heap) := by
  have hlo := lo.toNat_lt
  have hlt := rawLt_run (a := q) (b := hh) (by omega) (by omega) k heap
  have hadd : lookupMap IxVM.Checked.source.tables "UInt8::raw_add"
      ([.field (lo.toNat : F), .field (2 * (hh : F))] : List (SourceValue F)) =
      .ok (.tuple [.field (((lo.toNat + 2 * hh) % 256 : Nat) : F),
        .field (((lo.toNat + 2 * hh) / 256 : Nat) : F)]) := by
    have := rawAdd_row (a := lo.toNat) (b := 2 * hh) hlo (by omega)
    push_cast at this
    exact this
  have hff : lookupMap IxVM.Checked.source.tables "UInt8::from_field"
      ([.field ((q : F) + (((lo.toNat + 2 * hh) / 256 : Nat) : F))] : List (SourceValue F)) =
      .ok (.field ((q + (lo.toNat + 2 * hh) / 256 : Nat) : F)) := by
    have := fromField_row (x := q + (lo.toNat + 2 * hh) / 256) (by omega)
    push_cast at this ⊢
    exact this
  rw [show 2 * hh + q * 256 + lo.toNat =
      (lo.toNat + 2 * hh) % 256 + 256 * (q + (lo.toNat + 2 * hh) / 256) by omega,
    u64Value_two (Nat.mod_lt _ (by omega)) (by omega)]
  simp [Mirrors.«IxonDeserialize::get_tagn_tail», hlt, hq, loadValue_cell cell, node_ctor, pure, Except.pure,
    toField_run, evalBinOp, mapCall, hadd, hff, Constant.toValue, Value.mapAddress]

/-- **`get_tagn0(stream)`, one byte**: a first byte below `128` is the value. -/
theorem tagn0One_run {heap : Heap F} {addr : Nat} {b : UInt8} {tailPtr : SourceValue F}
    (cell : heap[addr]? = some (.construct byteStreamEnum "Cons" [.field (b.toNat : F), tailPtr]))
    (small : b.toNat < 128) (k : Nat) :
    Mirrors.«IxonDeserialize::get_tagn0» (k + 3) heap (.ptr (.enum byteStreamEnum) addr) =
      some (.tuple [u64Value b.toNat, tailPtr], heap) := by
  have hlt : Mirrors.«UInt8::less_than» (k + 2) heap (.field (b.toNat : F)) (.field 128) =
      some (.field 1, heap) := by
    have := lessThan_run (a := b.toNat) (b := 128) b.toNat_lt (by norm_num) k heap
    simpa [small] using this
  rw [show b.toNat = b.toNat + 256 * 0 by omega, u64Value_two b.toNat_lt (by norm_num)]
  simp [Mirrors.«IxonDeserialize::get_tagn0», loadValue_cell cell, node_ctor, hlt]

/-- **`get_tagn0(stream)`, two bytes**: a first byte `b` in `[128, 192)` and
the next byte `lo` give `128 + 256 (b - 128) + lo`. -/
theorem tagn0Two_run {heap : Heap F} {addr addr2 : Nat} {b lo : UInt8} {tailPtr : SourceValue F}
    (cell : heap[addr]? = some (.construct byteStreamEnum "Cons"
      [.field (b.toNat : F), .ptr (.enum byteStreamEnum) addr2]))
    (cell2 : heap[addr2]? = some (.construct byteStreamEnum "Cons" [.field (lo.toNat : F), tailPtr]))
    (lower : 128 ≤ b.toNat) (upper : b.toNat < 192) (k : Nat) :
    Mirrors.«IxonDeserialize::get_tagn0» (k + 3) heap (.ptr (.enum byteStreamEnum) addr) =
      some (.tuple [u64Value (128 + (b.toNat - 128) * 256 + lo.toNat), tailPtr], heap) := by
  have hlt : Mirrors.«UInt8::less_than» (k + 2) heap (.field (b.toNat : F)) (.field 128) =
      some (.field 0, heap) := by
    have := lessThan_run (a := b.toNat) (b := 128) b.toNat_lt (by norm_num) k heap
    simpa [show ¬ b.toNat < 128 by omega] using this
  have htail := tailShort_run (q := b.toNat - 128) (hh := 64) (by omega) (by norm_num) cell2 k
  rw [Nat.cast_sub lower, show 2 * 64 + (b.toNat - 128) * 256 + lo.toNat =
    128 + (b.toNat - 128) * 256 + lo.toNat by omega] at htail
  simp only [Nat.cast_ofNat] at htail
  simp (config := { decide := true }) [Mirrors.«IxonDeserialize::get_tagn0», loadValue_cell cell,
    node_ctor, hlt, toField_run, evalBinOp, htail, loadValue_cell cell2]

/-! ## The refinement -/

/-- **IxVM's `get_tagn0` refines IxC's `Ixon.getTagN 0` on the one- and
two-byte rungs**: every derivation of `IxonDeserialize::get_tagn0` on a stream
of `bytes` whose first byte is below `192` (the codes the wide rungs do not
use) is matched by IxC's reader on the same bytes: it succeeds with flag `0`
and the value the derivation returns as eight little-endian bytes, and the
derivation's rest pointer holds the bytes IxC's reader did not consume. The
heap is unchanged. Proved from the generated mirror lemma
(`Mirrors.«IxonDeserialize::get_tagn0».of_eval`) and what the mirror computes. -/
theorem getTagN0_refines_short {stream r : SourceValue F} {heap h' : Heap F} {bytes : List UInt8}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum heap bytes stream)
    (narrow : ∀ b ∈ bytes.head?, b.toNat < 192)
    (ev : EvalFn W "IxonDeserialize::get_tagn0" [stream] heap r h') :
    h' = heap ∧ ∃ (t : Ixon.TagN) (n : Nat) (restPtr : SourceValue F),
      Ixon.getTagN 0 (start bytes) = .ok t { idx := n, bytes := ⟨bytes.toArray⟩ } ∧ t.flag = 0 ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum heap (bytes.drop n) restPtr ∧
      r = .tuple [u64Value t.value.toNat, restPtr] := by
  obtain ⟨k0, hk0⟩ := Mirrors.«IxonDeserialize::get_tagn0».of_eval getU64le_complete ev
  have run := hk0 (k0 + 3) (by omega)
  cases rep with
  | nil cell =>
    simp [Mirrors.«IxonDeserialize::get_tagn0», loadValue_cell cell] at run
  | @cons b rest addr headVal tailPtr cell headRep tailRep =>
    simp only [Aiur.Library.RepU8] at headRep
    subst headRep
    have upper : b.toNat < 192 := narrow b (by simp)
    by_cases small : b.toNat < 128
    · rw [tagn0One_run cell small k0] at run
      simp only [Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨rfl, _, 1, tailPtr, getTagN0_one small, rfl, by simpa using tailRep, ?_⟩
      simp only [UInt64.toNat_ofNat', Nat.toUInt64_eq]
      rw [Nat.mod_eq_of_lt (by have := b.toNat_lt; omega)]
    · cases tailRep with
      | nil cell2 =>
        have hlt : Mirrors.«UInt8::less_than» (k0 + 2) heap (.field (b.toNat : F)) (.field 128) =
            some (.field 0, heap) := by
          have := lessThan_run (a := b.toNat) (b := 128) b.toNat_lt (by norm_num) k0 heap
          simpa [small] using this
        have hrl : Mirrors.«UInt8::raw_lt» (k0 + 1) heap (.field ((b.toNat : F) - 128)) (.field 64) =
            some (.field 1, heap) := by
          have := rawLt_run (a := b.toNat - 128) (b := 64) (by omega) (by norm_num) k0 heap
          rw [Nat.cast_sub (by omega)] at this
          simpa [show b.toNat - 128 < 64 by omega] using this
        simp (config := { decide := true }) [Mirrors.«IxonDeserialize::get_tagn0»,
          loadValue_cell cell, node_ctor, hlt, toField_run, evalBinOp,
          Mirrors.«IxonDeserialize::get_tagn_tail», hrl, loadValue_cell cell2] at run
      | @cons lo rest' addr2 headVal2 tailPtr2 cell2 headRep2 tailRep2 =>
        simp only [Aiur.Library.RepU8] at headRep2
        subst headRep2
        rw [tagn0Two_run cell cell2 (by omega) upper k0] at run
        simp only [Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        refine ⟨rfl, _, 2, tailPtr2, getTagN0_two (by omega) upper, rfl, by simpa using tailRep2, ?_⟩
        simp only [UInt64.toNat_ofNat', Nat.toUInt64_eq]
        rw [Nat.mod_eq_of_lt (by have := lo.toNat_lt; omega)]

/-! ## `get_tagn4`: the four-bit flag -/

/-- The static map `UInt8::raw_bit_decomposition`. -/
def bitsMap : Aiur.MapDecl := IxVM.Checked.coreTables.maps[1]'(by decide)

theorem bitDecomp_row {x : Nat} (hx : x < 256) :
    lookupMap IxVM.Checked.source.tables "UInt8::raw_bit_decomposition"
        ([.field (x : F)] : List (SourceValue F)) =
      .ok (.tuple [.field ((x % 2 : Nat) : F), .field ((x / 2 % 2 : Nat) : F),
        .field ((x / 4 % 2 : Nat) : F), .field ((x / 8 % 2 : Nat) : F),
        .field ((x / 16 % 2 : Nat) : F), .field ((x / 32 % 2 : Nat) : F),
        .field ((x / 64 % 2 : Nat) : F), .field ((x / 128 % 2 : Nat) : F)]) := by
  have member : bitsMap ∈ IxVM.Checked.coreTables.maps := List.getElem_mem _
  have rows : IxVM.Checked.coreTables.mapRows bitsMap =
      IxVM.Checked.byteInputsTable.rows.zip IxVM.Checked.byteBitsTable.rows := by
    simp only [Aiur.Program.mapRows, show bitsMap.input = "UInt8::byte_inputs" from rfl,
      show bitsMap.output = "UInt8::byte_bits" from rfl, IxVM.Checked.find_byteInputs,
      IxVM.Checked.find_byteBits]
  have row : (⟨[.field (x : F)], .tuple [.field ((x % 2 : Nat) : F), .field ((x / 2 % 2 : Nat) : F),
      .field ((x / 4 % 2 : Nat) : F), .field ((x / 8 % 2 : Nat) : F),
      .field ((x / 16 % 2 : Nat) : F), .field ((x / 32 % 2 : Nat) : F),
      .field ((x / 64 % 2 : Nat) : F), .field ((x / 128 % 2 : Nat) : F)]⟩ : MapEntry F) ∈
      IxVM.Checked.coreTables.mapEntries bitsMap := by
    apply Aiur.mapEntry_mem_iff.mpr
    rw [rows]
    simp only [IxVM.Checked.byteInputsTable, IxVM.Checked.byteBitsTable, List.map_map]
    convert mem_zip_map (List.mem_range.mpr hx) using 1
    simp [IxVM.Checked.coreRow, IxVM.Checked.coreLeaf, List.range_succ]
  have looked := Aiur.lookupMap_of_entry (A := Nat) IxVM.Checked.tablesChecked member row
  simpa [Constant.toValue, Value.mapAddress,
    show bitsMap.name = "UInt8::raw_bit_decomposition" from rfl, IxVM.Checked.source] using looked

/-- The value of the bit fields `x₀ + 2x₁ + 4x₂ (+ 8x₃)` a reader adds up. -/
theorem bits_low {x : Nat} :
    ((x % 2 : Nat) : F) + 2 * ((x / 2 % 2 : Nat) : F) + 4 * ((x / 4 % 2 : Nat) : F) =
      ((x % 8 : Nat) : F) := by
  rw [show x % 8 = x % 2 + 2 * (x / 2 % 2) + 4 * (x / 4 % 2) by omega]
  push_cast
  ring

theorem bits_high {x : Nat} (hx : x < 256) :
    ((x / 16 % 2 : Nat) : F) + 2 * ((x / 32 % 2 : Nat) : F) + 4 * ((x / 64 % 2 : Nat) : F) +
      8 * ((x / 128 % 2 : Nat) : F) = ((x / 16 : Nat) : F) := by
  have e : x / 16 = x / 16 % 2 + 2 * (x / 32 % 2) + 4 * (x / 64 % 2) + 8 * (x / 128 % 2) := by omega
  rw [congrArg (Nat.cast : Nat → F) e]
  push_cast
  ring

theorem bitDecomp_run {x : Nat} (hx : x < 256) (k : Nat) (h : Heap F) :
    Mirrors.«UInt8::bit_decomposition» (k + 1) h (.field (x : F)) =
      some (.tuple [.field ((x % 2 : Nat) : F), .field ((x / 2 % 2 : Nat) : F),
        .field ((x / 4 % 2 : Nat) : F), .field ((x / 8 % 2 : Nat) : F),
        .field ((x / 16 % 2 : Nat) : F), .field ((x / 32 % 2 : Nat) : F),
        .field ((x / 64 % 2 : Nat) : F), .field ((x / 128 % 2 : Nat) : F)], h) := by
  simp only [Mirrors.«UInt8::bit_decomposition», mapCall, bitDecomp_row hx]
  simp [Constant.toValue, Value.mapAddress]

/-- **`get_tagn4(stream)`, one byte**: a header byte whose low four bits are
below `8` is the flag (its high four bits) and that value. -/
theorem tagn4One_run {heap : Heap F} {addr : Nat} {b : UInt8} {tailPtr : SourceValue F}
    (cell : heap[addr]? = some (.construct byteStreamEnum "Cons" [.field (b.toNat : F), tailPtr]))
    (small : b.toNat % 16 < 8) (k : Nat) :
    Mirrors.«IxonDeserialize::get_tagn4» (k + 3) heap (.ptr (.enum byteStreamEnum) addr) =
      some (.tuple [.tuple [.field ((b.toNat / 16 : Nat) : F), u64Value (b.toNat % 16)], tailPtr],
        heap) := by
  have hb := b.toNat_lt
  have hbits := bitDecomp_run hb (k + 1) heap
  have hb3 : b.toNat / 8 % 2 = 0 := by omega
  have hff : lookupMap IxVM.Checked.source.tables "UInt8::from_field"
      ([.field (((b.toNat % 2 : Nat) : F) + 2 * ((b.toNat / 2 % 2 : Nat) : F) +
        4 * ((b.toNat / 4 % 2 : Nat) : F))] : List (SourceValue F)) =
      .ok (.field ((b.toNat % 8 : Nat) : F)) := by
    rw [bits_low]
    exact fromField_row (by omega)
  rw [show b.toNat % 16 = b.toNat % 8 + 256 * 0 by omega, u64Value_two (by omega) (by norm_num)]
  simp [Mirrors.«IxonDeserialize::get_tagn4», loadValue_cell cell, node_ctor, hbits, evalBinOp,
    bits_high hb, hb3, mapCall, hff, Constant.toValue, Value.mapAddress]

/-- **`get_tagn4(stream)`, two bytes**: low four bits `p` in `[8, 12)` and the
next byte `lo` give `8 + 256 (p - 8) + lo`. -/
theorem tagn4Two_run {heap : Heap F} {addr addr2 : Nat} {b lo : UInt8} {tailPtr : SourceValue F}
    (cell : heap[addr]? = some (.construct byteStreamEnum "Cons"
      [.field (b.toNat : F), .ptr (.enum byteStreamEnum) addr2]))
    (cell2 : heap[addr2]? = some (.construct byteStreamEnum "Cons" [.field (lo.toNat : F), tailPtr]))
    (lower : 8 ≤ b.toNat % 16) (upper : b.toNat % 16 < 12) (k : Nat) :
    Mirrors.«IxonDeserialize::get_tagn4» (k + 3) heap (.ptr (.enum byteStreamEnum) addr) =
      some (.tuple [.tuple [.field ((b.toNat / 16 : Nat) : F),
        u64Value (8 + (b.toNat % 16 - 8) * 256 + lo.toNat)], tailPtr], heap) := by
  have hb := b.toNat_lt
  have hbits := bitDecomp_run hb (k + 1) heap
  have hb3 : b.toNat / 8 % 2 = 1 := by omega
  have htail := tailShort_run (q := b.toNat % 8) (hh := 4) (by omega) (by norm_num) cell2 k
  rw [show 2 * 4 + b.toNat % 8 * 256 + lo.toNat = 8 + (b.toNat % 16 - 8) * 256 + lo.toNat by omega,
    ← bits_low] at htail
  simp only [Nat.cast_ofNat] at htail
  simp (config := { decide := true }) [Mirrors.«IxonDeserialize::get_tagn4», loadValue_cell cell,
    node_ctor, hbits, evalBinOp, bits_high hb, hb3, htail]

/-- **IxC's `getTagN 4`, one byte**: low four bits below `8` are the value,
the high four bits the flag. -/
theorem getTagN4_one {b : UInt8} {rest : List UInt8} (small : b.toNat % 16 < 8) :
    Ixon.getTagN 4 (start (b :: rest)) =
      .ok ⟨(b.toNat / 16).toUInt8, (b.toNat % 16).toUInt64⟩
        { idx := 1, bytes := ⟨(b :: rest).toArray⟩ } := by
  have read := getU8_at (bytes := b :: rest) (i := 0) (by simp)
  simp only [start, Ixon.getTagN, bind, EStateM.bind, read]
  simp [small, pure, EStateM.pure]

/-- **IxC's `getTagN 4`, two bytes**: low four bits `p` in `[8, 12)` and the
next byte `lo` give `8 + 256 (p - 8) + lo`. -/
theorem getTagN4_two {b lo : UInt8} {rest : List UInt8} (lower : 8 ≤ b.toNat % 16)
    (upper : b.toNat % 16 < 12) :
    Ixon.getTagN 4 (start (b :: lo :: rest)) =
      .ok ⟨(b.toNat / 16).toUInt8, (8 + (b.toNat % 16 - 8) * 256 + lo.toNat).toUInt64⟩
        { idx := 2, bytes := ⟨(b :: lo :: rest).toArray⟩ } := by
  have read0 := getU8_at (bytes := b :: lo :: rest) (i := 0) (by simp)
  have read1 := getU8_at (bytes := b :: lo :: rest) (i := 1) (by simp)
  simp only [start, Ixon.getTagN, bind, EStateM.bind, read0, Nat.zero_add]
  simp only [Nat.reduceSub, Nat.reducePow, show ¬ b.toNat % 16 < 8 by omega,
    ite_false, show b.toNat % 16 - 8 < 4 by omega, ite_true, List.getElem_cons_zero]
  simp [EStateM.bind, read1, pure, EStateM.pure, Ixon.tagNEnd1]

set_option maxHeartbeats 2000000 in
/-- **IxVM's `get_tagn4` refines IxC's `Ixon.getTagN 4` on the one- and
two-byte rungs**: on a stream whose first byte has low four bits below `12`
(the codes the wide rungs do not use), every derivation agrees with IxC's
reader on the same bytes: the flag, the value as eight little-endian bytes,
the rest pointer at IxC's position, the heap unchanged. -/
theorem getTagN4_refines_short {stream r : SourceValue F} {heap h' : Heap F} {bytes : List UInt8}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum heap bytes stream)
    (narrow : ∀ b ∈ bytes.head?, b.toNat % 16 < 12)
    (ev : EvalFn W "IxonDeserialize::get_tagn4" [stream] heap r h') :
    h' = heap ∧ ∃ (t : Ixon.TagN) (n : Nat) (restPtr : SourceValue F),
      Ixon.getTagN 4 (start bytes) = .ok t { idx := n, bytes := ⟨bytes.toArray⟩ } ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum heap (bytes.drop n) restPtr ∧
      r = .tuple [.tuple [.field (t.flag.toNat : F), u64Value t.value.toNat], restPtr] := by
  obtain ⟨k0, hk0⟩ := Mirrors.«IxonDeserialize::get_tagn4».of_eval getU64le_complete ev
  have run := hk0 (k0 + 3) (by omega)
  cases rep with
  | nil cell =>
    simp [Mirrors.«IxonDeserialize::get_tagn4», loadValue_cell cell] at run
  | @cons b rest addr headVal tailPtr cell headRep tailRep =>
    simp only [Aiur.Library.RepU8] at headRep
    subst headRep
    have hb := b.toNat_lt
    have upper : b.toNat % 16 < 12 := narrow b (by simp)
    have hflag : (b.toNat / 16).toUInt8.toNat = b.toNat / 16 := by
      simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat']
      exact Nat.mod_eq_of_lt (by omega)
    by_cases small : b.toNat % 16 < 8
    · rw [tagn4One_run cell small k0] at run
      simp only [Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨rfl, _, 1, tailPtr, getTagN4_one small, by simpa using tailRep, ?_⟩
      simp only [hflag, UInt64.toNat_ofNat', Nat.toUInt64_eq]
      rw [Nat.mod_eq_of_lt (show b.toNat % 16 < 2 ^ 64 by omega)]
    · cases tailRep with
      | nil cell2 =>
        have hbits := bitDecomp_run hb (k0 + 1) heap
        have hb3 : b.toNat / 8 % 2 = 1 := by omega
        have hrl : Mirrors.«UInt8::raw_lt» (k0 + 1) heap
            (.field (((b.toNat % 2 : Nat) : F) + 2 * ((b.toNat / 2 % 2 : Nat) : F) +
              4 * ((b.toNat / 4 % 2 : Nat) : F))) (.field 4) = some (.field 1, heap) := by
          have := rawLt_run (a := b.toNat % 8) (b := 4) (by omega) (by norm_num) k0 heap
          rw [← bits_low] at this
          simpa [show b.toNat % 8 < 4 by omega] using this
        simp (config := { decide := true, maxSteps := 10000000 }) [Mirrors.«IxonDeserialize::get_tagn4»,
          loadValue_cell cell, node_ctor, hbits, evalBinOp, bits_high hb, hb3, Mirrors.«IxonDeserialize::get_tagn_tail», hrl,
          loadValue_cell cell2] at run
      | @cons lo rest' addr2 headVal2 tailPtr2 cell2 headRep2 tailRep2 =>
        simp only [Aiur.Library.RepU8] at headRep2
        subst headRep2
        rw [tagn4Two_run cell cell2 (by omega) upper k0] at run
        simp only [Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        refine ⟨rfl, _, 2, tailPtr2, getTagN4_two (by omega) upper, by simpa using tailRep2, ?_⟩
        simp only [hflag, UInt64.toNat_ofNat', Nat.toUInt64_eq]
        rw [Nat.mod_eq_of_lt (show 8 + (b.toNat % 16 - 8) * 256 + lo.toNat < 2 ^ 64 by
          have := lo.toNat_lt; omega)]

/-! ## `get_tagn2`: the two-bit flag -/

theorem bits_low5 {x : Nat} :
    ((x % 2 : Nat) : F) + 2 * ((x / 2 % 2 : Nat) : F) + 4 * ((x / 4 % 2 : Nat) : F) +
      8 * ((x / 8 % 2 : Nat) : F) + 16 * ((x / 16 % 2 : Nat) : F) = ((x % 32 : Nat) : F) := by
  have e : x % 32 = x % 2 + 2 * (x / 2 % 2) + 4 * (x / 4 % 2) + 8 * (x / 8 % 2) + 16 * (x / 16 % 2) := by
    omega
  rw [congrArg (Nat.cast : Nat → F) e]
  push_cast
  ring

theorem bits_high2 {x : Nat} (hx : x < 256) :
    ((x / 64 % 2 : Nat) : F) + 2 * ((x / 128 % 2 : Nat) : F) = ((x / 64 : Nat) : F) := by
  have e : x / 64 = x / 64 % 2 + 2 * (x / 128 % 2) := by omega
  rw [congrArg (Nat.cast : Nat → F) e]
  push_cast
  ring

/-- **`get_tagn2(stream)`, one byte**: low six bits below `32` are the value,
the high two bits the flag. -/
theorem tagn2One_run {heap : Heap F} {addr : Nat} {b : UInt8} {tailPtr : SourceValue F}
    (cell : heap[addr]? = some (.construct byteStreamEnum "Cons" [.field (b.toNat : F), tailPtr]))
    (small : b.toNat % 64 < 32) (k : Nat) :
    Mirrors.«IxonDeserialize::get_tagn2» (k + 3) heap (.ptr (.enum byteStreamEnum) addr) =
      some (.tuple [.tuple [.field ((b.toNat / 64 : Nat) : F), u64Value (b.toNat % 64)], tailPtr],
        heap) := by
  have hb := b.toNat_lt
  have hbits := bitDecomp_run hb (k + 1) heap
  have hb5 : b.toNat / 32 % 2 = 0 := by omega
  have hff : lookupMap IxVM.Checked.source.tables "UInt8::from_field"
      ([.field (((b.toNat % 2 : Nat) : F) + 2 * ((b.toNat / 2 % 2 : Nat) : F) +
        4 * ((b.toNat / 4 % 2 : Nat) : F) + 8 * ((b.toNat / 8 % 2 : Nat) : F) +
        16 * ((b.toNat / 16 % 2 : Nat) : F))] : List (SourceValue F)) =
      .ok (.field ((b.toNat % 32 : Nat) : F)) := by
    rw [bits_low5]
    exact fromField_row (by omega)
  rw [show b.toNat % 64 = b.toNat % 32 + 256 * 0 by omega, u64Value_two (by omega) (by norm_num)]
  simp [Mirrors.«IxonDeserialize::get_tagn2», loadValue_cell cell, node_ctor, hbits, evalBinOp,
    bits_high2 hb, hb5, mapCall, hff, Constant.toValue, Value.mapAddress]

/-- **`get_tagn2(stream)`, two bytes**: low six bits `p` in `[32, 48)` and the
next byte `lo` give `32 + 256 (p - 32) + lo`. -/
theorem tagn2Two_run {heap : Heap F} {addr addr2 : Nat} {b lo : UInt8} {tailPtr : SourceValue F}
    (cell : heap[addr]? = some (.construct byteStreamEnum "Cons"
      [.field (b.toNat : F), .ptr (.enum byteStreamEnum) addr2]))
    (cell2 : heap[addr2]? = some (.construct byteStreamEnum "Cons" [.field (lo.toNat : F), tailPtr]))
    (lower : 32 ≤ b.toNat % 64) (upper : b.toNat % 64 < 48) (k : Nat) :
    Mirrors.«IxonDeserialize::get_tagn2» (k + 3) heap (.ptr (.enum byteStreamEnum) addr) =
      some (.tuple [.tuple [.field ((b.toNat / 64 : Nat) : F),
        u64Value (32 + (b.toNat % 64 - 32) * 256 + lo.toNat)], tailPtr], heap) := by
  have hb := b.toNat_lt
  have hbits := bitDecomp_run hb (k + 1) heap
  have hb5 : b.toNat / 32 % 2 = 1 := by omega
  have htail := tailShort_run (q := b.toNat % 32) (hh := 16) (by omega) (by norm_num) cell2 k
  rw [show 2 * 16 + b.toNat % 32 * 256 + lo.toNat = 32 + (b.toNat % 64 - 32) * 256 + lo.toNat by
    omega, ← bits_low5] at htail
  simp only [Nat.cast_ofNat] at htail
  simp (config := { decide := true }) [Mirrors.«IxonDeserialize::get_tagn2», loadValue_cell cell,
    node_ctor, hbits, evalBinOp, bits_high2 hb, hb5, htail]

/-- **IxC's `getTagN 2`, one byte**: low six bits below `32` are the value,
the high two bits the flag. -/
theorem getTagN2_one {b : UInt8} {rest : List UInt8} (small : b.toNat % 64 < 32) :
    Ixon.getTagN 2 (start (b :: rest)) =
      .ok ⟨(b.toNat / 64).toUInt8, (b.toNat % 64).toUInt64⟩
        { idx := 1, bytes := ⟨(b :: rest).toArray⟩ } := by
  have read := getU8_at (bytes := b :: rest) (i := 0) (by simp)
  simp only [start, Ixon.getTagN, bind, EStateM.bind, read]
  simp [small, pure, EStateM.pure]

/-- **IxC's `getTagN 2`, two bytes**: low six bits `p` in `[32, 48)` and the
next byte `lo` give `32 + 256 (p - 32) + lo`. -/
theorem getTagN2_two {b lo : UInt8} {rest : List UInt8} (lower : 32 ≤ b.toNat % 64)
    (upper : b.toNat % 64 < 48) :
    Ixon.getTagN 2 (start (b :: lo :: rest)) =
      .ok ⟨(b.toNat / 64).toUInt8, (32 + (b.toNat % 64 - 32) * 256 + lo.toNat).toUInt64⟩
        { idx := 2, bytes := ⟨(b :: lo :: rest).toArray⟩ } := by
  have read0 := getU8_at (bytes := b :: lo :: rest) (i := 0) (by simp)
  have read1 := getU8_at (bytes := b :: lo :: rest) (i := 1) (by simp)
  simp only [start, Ixon.getTagN, bind, EStateM.bind, read0, Nat.zero_add]
  simp only [Nat.reduceSub, Nat.reducePow, show ¬ b.toNat % 64 < 32 by omega,
    ite_false, show b.toNat % 64 - 32 < 16 by omega, ite_true, List.getElem_cons_zero]
  simp [EStateM.bind, read1, pure, EStateM.pure, Ixon.tagNEnd1]

set_option maxHeartbeats 2000000 in
/-- **IxVM's `get_tagn2` refines IxC's `Ixon.getTagN 2` on the one- and
two-byte rungs**: on a stream whose first byte has low six bits below `48`
(the codes the wide rungs do not use), every derivation agrees with IxC's
reader on the same bytes: the flag, the value as eight little-endian bytes,
the rest pointer at IxC's position, the heap unchanged. -/
theorem getTagN2_refines_short {stream r : SourceValue F} {heap h' : Heap F} {bytes : List UInt8}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum heap bytes stream)
    (narrow : ∀ b ∈ bytes.head?, b.toNat % 64 < 48)
    (ev : EvalFn W "IxonDeserialize::get_tagn2" [stream] heap r h') :
    h' = heap ∧ ∃ (t : Ixon.TagN) (n : Nat) (restPtr : SourceValue F),
      Ixon.getTagN 2 (start bytes) = .ok t { idx := n, bytes := ⟨bytes.toArray⟩ } ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum heap (bytes.drop n) restPtr ∧
      r = .tuple [.tuple [.field (t.flag.toNat : F), u64Value t.value.toNat], restPtr] := by
  obtain ⟨k0, hk0⟩ := Mirrors.«IxonDeserialize::get_tagn2».of_eval getU64le_complete ev
  have run := hk0 (k0 + 3) (by omega)
  cases rep with
  | nil cell =>
    simp [Mirrors.«IxonDeserialize::get_tagn2», loadValue_cell cell] at run
  | @cons b rest addr headVal tailPtr cell headRep tailRep =>
    simp only [Aiur.Library.RepU8] at headRep
    subst headRep
    have hb := b.toNat_lt
    have upper : b.toNat % 64 < 48 := narrow b (by simp)
    have hflag : (b.toNat / 64).toUInt8.toNat = b.toNat / 64 := by
      simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat']
      exact Nat.mod_eq_of_lt (by omega)
    by_cases small : b.toNat % 64 < 32
    · rw [tagn2One_run cell small k0] at run
      simp only [Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨rfl, _, 1, tailPtr, getTagN2_one small, by simpa using tailRep, ?_⟩
      simp only [hflag, UInt64.toNat_ofNat', Nat.toUInt64_eq]
      rw [Nat.mod_eq_of_lt (show b.toNat % 64 < 2 ^ 64 by omega)]
    · cases tailRep with
      | nil cell2 =>
        have hbits := bitDecomp_run hb (k0 + 1) heap
        have hb5 : b.toNat / 32 % 2 = 1 := by omega
        have hrl : Mirrors.«UInt8::raw_lt» (k0 + 1) heap
            (.field (((b.toNat % 2 : Nat) : F) + 2 * ((b.toNat / 2 % 2 : Nat) : F) +
              4 * ((b.toNat / 4 % 2 : Nat) : F) + 8 * ((b.toNat / 8 % 2 : Nat) : F) +
              16 * ((b.toNat / 16 % 2 : Nat) : F))) (.field 16) = some (.field 1, heap) := by
          have := rawLt_run (a := b.toNat % 32) (b := 16) (by omega) (by norm_num) k0 heap
          rw [← bits_low5] at this
          simpa [show b.toNat % 32 < 16 by omega] using this
        simp (config := { decide := true, maxSteps := 10000000 }) [Mirrors.«IxonDeserialize::get_tagn2»,
          loadValue_cell cell, node_ctor, hbits, evalBinOp, bits_high2 hb, hb5,
          Mirrors.«IxonDeserialize::get_tagn_tail», hrl, loadValue_cell cell2] at run
      | @cons lo rest' addr2 headVal2 tailPtr2 cell2 headRep2 tailRep2 =>
        simp only [Aiur.Library.RepU8] at headRep2
        subst headRep2
        rw [tagn2Two_run cell cell2 (by omega) upper k0] at run
        simp only [Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        refine ⟨rfl, _, 2, tailPtr2, getTagN2_two (by omega) upper, by simpa using tailRep2, ?_⟩
        simp only [hflag, UInt64.toNat_ofNat', Nat.toUInt64_eq]
        rw [Nat.mod_eq_of_lt (show 32 + (b.toNat % 64 - 32) * 256 + lo.toNat < 2 ^ 64 by
          have := lo.toNat_lt; omega)]

/-! ## Wide rungs: `get_u64_le` -/

/-- A byte string as a little-endian number. -/
def leValue : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leValue bs

theorem leValue_lt : ∀ (bs : List UInt8), leValue bs < 256 ^ bs.length
  | [] => by simp [leValue]
  | b :: bs => by
    have ih := leValue_lt bs
    have hb := b.toNat_lt
    simp only [leValue, List.length_cons, Nat.pow_succ]
    generalize 256 ^ bs.length = P at *
    generalize leValue bs = L at *
    omega

theorem u64Value_cons {b x : Nat} (hb : b < 256) :
    u64Value (b + 256 * x) = .tuple [.field (b : F), .field ((x % 256 : Nat) : F),
      .field ((x / 256 % 256 : Nat) : F), .field ((x / 65536 % 256 : Nat) : F),
      .field ((x / 16777216 % 256 : Nat) : F), .field ((x / 4294967296 % 256 : Nat) : F),
      .field ((x / 1099511627776 % 256 : Nat) : F),
      .field ((x / 281474976710656 % 256 : Nat) : F)] := by
  simp only [u64Value]
  rw [show (b + 256 * x) % 256 = b by omega, show (b + 256 * x) / 256 % 256 = x % 256 by omega,
    show (b + 256 * x) / 65536 % 256 = x / 256 % 256 by omega,
    show (b + 256 * x) / 16777216 % 256 = x / 65536 % 256 by omega,
    show (b + 256 * x) / 4294967296 % 256 = x / 16777216 % 256 by omega,
    show (b + 256 * x) / 1099511627776 % 256 = x / 4294967296 % 256 by omega,
    show (b + 256 * x) / 281474976710656 % 256 = x / 1099511627776 % 256 by omega,
    show (b + 256 * x) / 72057594037927936 % 256 = x / 281474976710656 % 256 by omega]

theorem natCast_succ_ne_zero {n : Nat} (hn : n < 1000) : (n : F) + 1 ≠ 0 := by
  intro h
  have h' : ((n + 1 : Nat) : F) = ((0 : Nat) : F) := by push_cast; exact h
  have := IxVM.Checked.natCast_inj (by omega) (by omega) h'
  omega

/-- **`get_u64_le(stream, n)` reads `n` bytes**, little-endian, for `n ≤ 8`. -/
theorem getU64le_run {heap : Heap F} : ∀ (n : Nat), n ≤ 8 → ∀ {bs : List UInt8} {stream : SourceValue F},
    n ≤ bs.length → Aiur.Library.Bytes.RepByteStream byteStreamEnum heap bs stream →
    ∃ restPtr, Aiur.Library.Bytes.RepByteStream byteStreamEnum heap (bs.drop n) restPtr ∧
      ∀ k, n + 1 ≤ k → Mirrors.«IxonDeserialize::get_u64_le» k heap stream (.field (n : F)) =
        some (.tuple [u64Value (leValue (bs.take n)), restPtr], heap)
  | 0, _, bs, stream, _, rep => by
    refine ⟨stream, by simpa using rep, fun k hk => ?_⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp [Mirrors.«IxonDeserialize::get_u64_le», leValue, u64Value]
  | n + 1, hn, bs, stream, hlen, rep => by
    cases rep with
    | nil cell => simp at hlen
    | @cons b tl addr headVal tailPtr cell headRep tailRep =>
      simp only [Aiur.Library.RepU8] at headRep
      subst headRep
      obtain ⟨restPtr, restRep, run⟩ :=
        getU64le_run n (by omega) (bs := tl) (by simp at hlen; omega) tailRep
      refine ⟨restPtr, by simpa using restRep, fun k hk => ?_⟩
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hne := natCast_succ_ne_zero (n := n) (by omega)
      have hrun := run k' (by omega)
      have hb := b.toNat_lt
      rw [show leValue (List.take (n + 1) (b :: tl)) = b.toNat + 256 * leValue (tl.take n) from rfl,
        u64Value_cons hb]
      simp [Mirrors.«IxonDeserialize::get_u64_le», hne, loadValue_cell cell, node_ctor, evalBinOp,
        hrun, u64Value]

/-! ## Wide rungs: 64-bit addition -/

/-- The static map `UInt8::raw_sum_byte`. -/
def sumByteMap : Aiur.MapDecl := IxVM.Checked.coreTables.maps[9]'(by decide)

theorem sumByte_row {s : Nat} (hs : s < 768) :
    lookupMap IxVM.Checked.source.tables "UInt8::raw_sum_byte" ([.field (s : F)] : List (SourceValue F)) =
      .ok (.field ((s % 256 : Nat) : F)) := by
  have member : sumByteMap ∈ IxVM.Checked.coreTables.maps := List.getElem_mem _
  have rows : IxVM.Checked.coreTables.mapRows sumByteMap =
      IxVM.Checked.sumInputsTable.rows.zip IxVM.Checked.sumBytesTable.rows := by
    simp only [Aiur.Program.mapRows, show sumByteMap.input = "UInt8::sum_inputs" from rfl,
      show sumByteMap.output = "UInt8::sum_bytes" from rfl, IxVM.Checked.find_sumInputs,
      IxVM.Checked.find_sumBytes]
  have row : (⟨[.field (s : F)], .field ((s % 256 : Nat) : F)⟩ : MapEntry F) ∈
      IxVM.Checked.coreTables.mapEntries sumByteMap := by
    apply Aiur.mapEntry_mem_iff.mpr
    rw [rows]
    simp only [IxVM.Checked.sumInputsTable, IxVM.Checked.sumBytesTable, List.map_map]
    have mem : (s, s % 256) ∈ IxVM.Checked.sumPairs := by
      simp only [IxVM.Checked.sumPairs, Aiur.Library.Carry.rows]
      exact List.mem_map.mpr ⟨s, List.mem_range.mpr hs, rfl⟩
    convert mem_zip_map mem using 1
    simp [IxVM.Checked.coreRow, IxVM.Checked.coreLeaf]
  have looked := Aiur.lookupMap_of_entry (A := Nat) IxVM.Checked.tablesChecked member row
  simpa [Constant.toValue, Value.mapAddress, show sumByteMap.name = "UInt8::raw_sum_byte" from rfl,
    IxVM.Checked.source] using looked

theorem two56_ne_zero : (256 : F) ≠ 0 := by decide

theorem splitSum_run {s : Nat} (hs : s < 768) (k : Nat) (h : Heap F) :
    Mirrors.«UInt8::split_sum» (k + 1) h (.field (s : F)) =
      some (.tuple [.field ((s % 256 : Nat) : F), .field ((s / 256 : Nat) : F)], h) := by
  have e : (s : F) = ((s % 256 : Nat) : F) + 256 * ((s / 256 : Nat) : F) := by
    have := congrArg (Nat.cast : Nat → F) (show s = s % 256 + 256 * (s / 256) by omega)
    push_cast at this
    exact this
  have hdiv : ((s : F) - ((s % 256 : Nat) : F)) / 256 = ((s / 256 : Nat) : F) := by
    rw [div_eq_iff two56_ne_zero, e]
    ring
  simp [Mirrors.«UInt8::split_sum», mapCall, sumByte_row hs, Constant.toValue, Value.mapAddress,
    evalBinOp, two56_ne_zero, hdiv]

theorem splitSum_run2 {a b : Nat} (hs : a + b < 768) (k : Nat) (h : Heap F) :
    Mirrors.«UInt8::split_sum» (k + 1) h (.field ((a : F) + (b : F))) =
      some (.tuple [.field (((a + b) % 256 : Nat) : F), .field (((a + b) / 256 : Nat) : F)], h) := by
  have := splitSum_run hs k h
  push_cast at this
  exact this

theorem splitSum_run3 {a b c : Nat} (hs : a + b + c < 768) (k : Nat) (h : Heap F) :
    Mirrors.«UInt8::split_sum» (k + 1) h (.field ((a : F) + (b : F) + (c : F))) =
      some (.tuple [.field (((a + b + c) % 256 : Nat) : F),
        .field (((a + b + c) / 256 : Nat) : F)], h) := by
  have := splitSum_run hs k h
  push_cast at this
  exact this


/-- **`UInt64::add` on bytes**: given the ripple-carry digits `s` and carries `c` of
`a + b`, the mirror returns them. -/
theorem u64Add_run {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    {s0 s1 s2 s3 s4 s5 s6 s7 c1 c2 c3 c4 c5 c6 c7 c8 : Nat}
    (ha0 : a0 < 256) (ha1 : a1 < 256) (ha2 : a2 < 256) (ha3 : a3 < 256)
    (ha4 : a4 < 256) (ha5 : a5 < 256) (ha6 : a6 < 256) (ha7 : a7 < 256)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (hb4 : b4 < 256) (hb5 : b5 < 256) (hb6 : b6 < 256) (hb7 : b7 < 256)
    (hs0 : s0 < 256) (hs1 : s1 < 256) (hs2 : s2 < 256) (hs3 : s3 < 256)
    (hs4 : s4 < 256) (hs5 : s5 < 256) (hs6 : s6 < 256) (hs7 : s7 < 256)
    (h0 : a0 + b0 = s0 + 256 * c1) (h1 : a1 + b1 + c1 = s1 + 256 * c2)
    (h2 : a2 + b2 + c2 = s2 + 256 * c3) (h3 : a3 + b3 + c3 = s3 + 256 * c4)
    (h4 : a4 + b4 + c4 = s4 + 256 * c5) (h5 : a5 + b5 + c5 = s5 + 256 * c6)
    (h6 : a6 + b6 + c6 = s6 + 256 * c7) (h7 : a7 + b7 + c7 = s7 + 256 * c8) (k : Nat) (h : Heap F) :
    Mirrors.«UInt64::add» (k + 2) h
        (.tuple [.field (a0 : F), .field (a1 : F), .field (a2 : F), .field (a3 : F), .field (a4 : F),
          .field (a5 : F), .field (a6 : F), .field (a7 : F)])
        (.tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F), .field (b4 : F),
          .field (b5 : F), .field (b6 : F), .field (b7 : F)]) =
      some (.tuple [.tuple [.field (s0 : F), .field (s1 : F), .field (s2 : F), .field (s3 : F),
        .field (s4 : F), .field (s5 : F), .field (s6 : F), .field (s7 : F)], .field (c8 : F)], h) := by
  have e0 : Mirrors.«UInt8::split_sum» (k + 1) h (.field ((a0 : F) + (b0 : F))) =
      some (.tuple [.field (s0 : F), .field (c1 : F)], h) := by
    rw [show s0 = (a0 + b0) % 256 by omega, show c1 = (a0 + b0) / 256 by omega]
    exact splitSum_run2 (by omega) k h
  have e1 : Mirrors.«UInt8::split_sum» (k + 1) h (.field ((a1 : F) + (b1 : F) + (c1 : F))) =
      some (.tuple [.field (s1 : F), .field (c2 : F)], h) := by
    rw [show s1 = (a1 + b1 + c1) % 256 by omega, show c2 = (a1 + b1 + c1) / 256 by omega]
    exact splitSum_run3 (by omega) k h
  have e2 : Mirrors.«UInt8::split_sum» (k + 1) h (.field ((a2 : F) + (b2 : F) + (c2 : F))) =
      some (.tuple [.field (s2 : F), .field (c3 : F)], h) := by
    rw [show s2 = (a2 + b2 + c2) % 256 by omega, show c3 = (a2 + b2 + c2) / 256 by omega]
    exact splitSum_run3 (by omega) k h
  have e3 : Mirrors.«UInt8::split_sum» (k + 1) h (.field ((a3 : F) + (b3 : F) + (c3 : F))) =
      some (.tuple [.field (s3 : F), .field (c4 : F)], h) := by
    rw [show s3 = (a3 + b3 + c3) % 256 by omega, show c4 = (a3 + b3 + c3) / 256 by omega]
    exact splitSum_run3 (by omega) k h
  have e4 : Mirrors.«UInt8::split_sum» (k + 1) h (.field ((a4 : F) + (b4 : F) + (c4 : F))) =
      some (.tuple [.field (s4 : F), .field (c5 : F)], h) := by
    rw [show s4 = (a4 + b4 + c4) % 256 by omega, show c5 = (a4 + b4 + c4) / 256 by omega]
    exact splitSum_run3 (by omega) k h
  have e5 : Mirrors.«UInt8::split_sum» (k + 1) h (.field ((a5 : F) + (b5 : F) + (c5 : F))) =
      some (.tuple [.field (s5 : F), .field (c6 : F)], h) := by
    rw [show s5 = (a5 + b5 + c5) % 256 by omega, show c6 = (a5 + b5 + c5) / 256 by omega]
    exact splitSum_run3 (by omega) k h
  have e6 : Mirrors.«UInt8::split_sum» (k + 1) h (.field ((a6 : F) + (b6 : F) + (c6 : F))) =
      some (.tuple [.field (s6 : F), .field (c7 : F)], h) := by
    rw [show s6 = (a6 + b6 + c6) % 256 by omega, show c7 = (a6 + b6 + c6) / 256 by omega]
    exact splitSum_run3 (by omega) k h
  have e7 : Mirrors.«UInt8::split_sum» (k + 1) h (.field ((a7 : F) + (b7 : F) + (c7 : F))) =
      some (.tuple [.field (s7 : F), .field (c8 : F)], h) := by
    rw [show s7 = (a7 + b7 + c7) % 256 by omega, show c8 = (a7 + b7 + c7) / 256 by omega]
    exact splitSum_run3 (by omega) k h
  simp only [Mirrors.«UInt64::add», projectValue, toField_run, evalBinOp, e0, e1, e2, e3, e4, e5,
    e6, e7, bind, Except.bind, pure, Except.pure, Option.bind, List.getElem?_cons_succ,
    List.getElem?_cons_zero]

set_option maxHeartbeats 4000000 in
/-- **`UInt64::add` is 64-bit addition with a carry.** -/
theorem u64Add_value {x y : Nat} (hx : x < 18446744073709551616) (hy : y < 18446744073709551616) (k : Nat) (h : Heap F) :
    Mirrors.«UInt64::add» (k + 2) h (u64Value x) (u64Value y) =
      some (.tuple [u64Value ((x + y) % 18446744073709551616), .field (((x + y) / 18446744073709551616 : Nat) : F)], h) := by
  have run := u64Add_run
    (a0 := x % 256) (b0 := y % 256) (s0 := (x + y) % 18446744073709551616 % 256)
    (a1 := x / 256 % 256) (b1 := y / 256 % 256) (s1 := (x + y) % 18446744073709551616 / 256 % 256)
    (a2 := x / 65536 % 256) (b2 := y / 65536 % 256) (s2 := (x + y) % 18446744073709551616 / 65536 % 256)
    (a3 := x / 16777216 % 256) (b3 := y / 16777216 % 256) (s3 := (x + y) % 18446744073709551616 / 16777216 % 256)
    (a4 := x / 4294967296 % 256) (b4 := y / 4294967296 % 256) (s4 := (x + y) % 18446744073709551616 / 4294967296 % 256)
    (a5 := x / 1099511627776 % 256) (b5 := y / 1099511627776 % 256) (s5 := (x + y) % 18446744073709551616 / 1099511627776 % 256)
    (a6 := x / 281474976710656 % 256) (b6 := y / 281474976710656 % 256) (s6 := (x + y) % 18446744073709551616 / 281474976710656 % 256)
    (a7 := x / 72057594037927936 % 256) (b7 := y / 72057594037927936 % 256) (s7 := (x + y) % 18446744073709551616 / 72057594037927936 % 256)
    (c1 := (x % 256 + y % 256) / 256)
    (c2 := (x % 65536 + y % 65536) / 65536)
    (c3 := (x % 16777216 + y % 16777216) / 16777216)
    (c4 := (x % 4294967296 + y % 4294967296) / 4294967296)
    (c5 := (x % 1099511627776 + y % 1099511627776) / 1099511627776)
    (c6 := (x % 281474976710656 + y % 281474976710656) / 281474976710656)
    (c7 := (x % 72057594037927936 + y % 72057594037927936) / 72057594037927936)
    (c8 := (x % 18446744073709551616 + y % 18446744073709551616) / 18446744073709551616)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) k h
  rw [show (x % 18446744073709551616 + y % 18446744073709551616) / 18446744073709551616 =
    (x + y) / 18446744073709551616 by omega] at run
  simp only [u64Value]
  rw [run]


end IxVM.Refinement.TagN
