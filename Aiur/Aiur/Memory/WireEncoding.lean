import Aiur.Memory.Typing
import Aiur.DeclarationTotal
import Aiur.WireMemory

namespace Aiur

@[simp] theorem Value.pointerNames_mapAddress (decls : Declarations) (encode : A → B) (value : Value F A) :
    (value.mapAddress encode).PointerNames decls ↔ value.PointerNames decls := by
  cases value with
  | field | ptr => simp only [Value.mapAddress, Value.PointerNames]
  | tuple values | construct name ctor values =>
      simp only [Value.mapAddress, Value.PointerNames, List.forall_mem_map]
      exact forall_congr' (fun v => imp_congr_right (fun _ => Value.pointerNames_mapAddress decls encode v))
termination_by sizeOf value

@[simp] theorem Value.good_mapAddress (decls : Declarations) (encode : A → B) (value : Value F A) :
    (value.mapAddress encode).Good decls ↔ value.Good decls := by simp [Value.Good]

/-- Well-formed source values have an encoding; field size is needed only to decode tags uniquely. -/
theorem Value.encode_total [NatCast F] [Zero F] {decls : Declarations}
    (checked : checkDeclarations decls = .ok ()) {value : Value F} (good : value.Good decls) :
    ∃ wire, value.encode decls = some wire := by
  obtain ⟨layout, expanded⟩ := Declarations.layout_total checked (Value.type_names good.1 good.2)
  obtain ⟨words, encoded⟩ := (Declarations.layout_describes expanded).encode_total rfl good.1
  exact ⟨⟨value.type, words⟩, by simp [Value.encode, good.1, expanded, Except.toOption, encoded]⟩

/-- Encode the values in a semantic table, keeping its addresses. -/
def ROM.encode [NatCast F] [Zero F] (decls : Declarations) (rom : ROM F) : WireROM F :=
  ⟨rom.entries.filterMap (fun cell => (cell.2.encode decls).map (fun wire => (cell.1, wire)))⟩

theorem ROM.encode_addresses [NatCast F] [Zero F] {decls : Declarations}
    (checked : checkDeclarations decls = .ok ()) {rom : ROM F}
    (good : ∀ cell ∈ rom.entries, cell.2.Good decls) :
    ((rom.encode decls).entries.map Prod.fst) = rom.entries.map Prod.fst := by
  rcases rom with ⟨entries⟩
  change ((entries.filterMap _).map Prod.fst) = entries.map Prod.fst
  induction entries with
  | nil => rfl
  | cons cell entries ih =>
      obtain ⟨wire, encoded⟩ := Value.encode_total checked (good cell (by simp))
      simp only [List.filterMap_cons, encoded, Option.map_some, List.map_cons]
      exact congrArg (cell.1 :: ·) (ih (fun c h => good c (by simp [h])))

theorem ROM.encode_valid [NatCast F] [Zero F] {decls : Declarations}
    (checked : checkDeclarations decls = .ok ()) {rom : ROM F}
    (good : ∀ cell ∈ rom.entries, cell.2.Good decls) (valid : rom.Valid) :
    (rom.encode decls).Valid := by
  intro a ha b hb address types
  obtain ⟨⟨la, lv⟩, lm, le⟩ := List.mem_filterMap.mp ha
  obtain ⟨⟨ra, rv⟩, rm, re⟩ := List.mem_filterMap.mp hb
  obtain ⟨lw, ld, rfl⟩ := Option.map_eq_some_iff.mp le
  obtain ⟨rw, rd, rfl⟩ := Option.map_eq_some_iff.mp re
  have typed : lv.type = rv.type :=
    (Value.encode_spec ld).2.1.symm.trans (types.trans (Value.encode_spec rd).2.1)
  have same : lv = rv := valid _ lm _ rm address typed
  rw [same, rd] at ld
  exact (Option.some.inj ld).symm

/-- The canonical table encoding decodes to exactly the same heterogeneous ROM. -/
theorem ROM.decode_encode [NatCast F] [Zero F] [DecidableEq F] {decls : Declarations}
    (checked : checkDeclarations decls = .ok ()) (tags : decls.tagsValid F = true) {rom : ROM F}
    (good : ∀ cell ∈ rom.entries, cell.2.Good decls) : (rom.encode decls).decode decls = rom := by
  rcases rom with ⟨entries⟩
  apply congrArg ROM.mk
  change (entries.filterMap _).filterMap _ = entries
  induction entries with
  | nil => rfl
  | cons cell entries ih =>
      obtain ⟨wire, encoded⟩ := Value.encode_total checked (good cell (by simp))
      have decoded := Value.decode_encode encoded (fun _ => Declarations.layout_tagSafe tags)
      simp only [List.filterMap_cons, encoded, Option.map_some, decoded]
      exact congrArg (cell :: ·) (ih (fun c h => good c (by simp [h])))

theorem ROM.ofHeap_good {decls : Declarations} {heap : Heap F}
    (good : heap.Good decls) (encode : Nat → F) :
    ∀ cell ∈ (ROM.ofHeap heap encode).entries, cell.2.Good decls := by
  intro cell member
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  simpa using good heap[index] (List.getElem_mem _)

end Aiur
