import Aiur.Circuit.SemanticCorrectness
import Aiur.MemoryCorrectness

namespace Aiur.Circuit

variable {F : Type} [Field F] [DecidableEq F]
  {program : Program F} {system : System F}

private theorem public_arguments {decls : Declarations}
    {wires : List (WireValue F)} {values : List (Value F)}
    (arguments : DecodesValues decls wires values)
    (free : ∀ value ∈ values, value.type.pointerFree decls = true) :
    ∀ wire ∈ wires, wire.type.pointerFree decls = true := by
  induction arguments with
  | nil => simp
  | @cons wire value wires values head tail ih =>
      have headFree := free value (by simp)
      rw [(WireValue.decode_spec head).1] at headFree
      simpa using And.intro headFree (ih (fun v h => free v (by simp [h])))

/-- Heap completeness only uses local compiler correctness. Addresses may be
chosen freely, provided distinct allocated cells have distinct field addresses. -/
theorem System.SemanticModel.heap_complete (model : system.SemanticModel program)
    (checked : typecheck program = .ok ()) (tags : program.enums.tagsValid F = true)
    (enums : system.enums = program.enums)
    {name : String} {args : List (SourceValue F)} {value : SourceValue F} {heap : Heap F}
    (entry : checkEntry program name = .ok ()) (evaluated : EvalFn program name args [] value heap)
    (encode : Nat → F)
    (distinct : ∀ i j, i < heap.length → j < heap.length → encode i = encode j → i = j) :
    EncodedEntryDerives system name (entryValues args) (value.mapAddress encode) := by
  have free := evaluated.public_pointerFree entry
  have heapGood := (evaluated.heap_good checked (by simp [Heap.Good])
    (fun arg member => Value.pointerNames_of_free (free arg member))).2
  let table := ROM.ofHeap heap encode
  have good := ROM.ofHeap_good heapGood encode
  have decodeTable := ROM.decode_encode model.declarations tags good
  have body := evaluated.toROM (ROM.ofHeap_cells heap encode)
  have encodedBody : ROMEvalCall ((table.encode program.enums).decode program.enums) program name
      (args.map (Value.mapAddress encode)) (value.mapAddress encode) := by
    rw [decodeTable]; exact body
  obtain ⟨wires, output, arguments, decoded, derives⟩ := model.evaluation_complete encodedBody
  rw [entryValues_eq free encode] at arguments
  have argsFree : ∀ arg ∈ entryValues args, arg.type.pointerFree program.enums = true := by
    intro arg member
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
    simpa using (evaluated.publicArguments entry source sourceMember).1
  have tableValid := ROM.encode_valid model.declarations good (ROM.ofHeap_valid heap encode distinct)
  refine ⟨wires, output, ?_, ?_, ?_⟩
  · simpa only [enums] using arguments
  · simpa only [enums] using decoded
  · refine ⟨?_, ?_, table.encode program.enums, tableValid, derives⟩
    · exact ⟨by simpa only [enums] using arguments.each,
        by simpa only [enums] using
          (show ∃ value, output.decode program.enums = some value from ⟨_, decoded⟩)⟩
    · simpa only [enums, Message.PublicArguments] using public_arguments arguments argsFree

/-- Acyclic evaluation is realized with ordinary fresh allocations, without
equating source addresses with prover-chosen ROM addresses. -/
theorem System.SemanticModel.heap_sound (model : system.SemanticModel program)
    {rom : WireROM F} (valid : rom.Valid)
    {name : String} {args : List (SourceValue F)} {result : Value F}
    (entry : checkEntry program name = .ok ()) {wires : List (WireValue F)} {output : WireValue F}
    (derived : CircuitEvaluates system rom name wires output)
    (arguments : DecodesValues program.enums wires (entryValues args))
    (decoded : output.decode program.enums = some result) :
    ∃ source heap, EvalFn program name args [] source heap ∧
      Represents (rom.decode program.enums) heap source result := by
  have evaluated := model.sound_encoded derived arguments decoded
  have free : ∀ value ∈ args, value.pointerFree = true := by
    intro value member
    have valid := evaluated.publicArguments entry (value.mapAddress (fun _ => 0))
      (List.mem_map.mpr ⟨value, member, rfl⟩)
    exact Value.pointerFree_of_type (by simpa using valid.1) (by simpa using valid.2)
  have relatedArgs : RepresentsArgs (rom.decode program.enums) [] args (entryValues args) := by
    apply List.forall₂_map_right_iff.mpr
    exact List.forall₂_same.mpr (fun value member => Represents.of_pointerFree value (free value member) _)
  obtain ⟨source, heap, evaluated, _, related⟩ := evaluated.realize (WireROM.decode_valid valid) relatedArgs
  exact ⟨source, heap, evaluated, related⟩

end Aiur.Circuit
