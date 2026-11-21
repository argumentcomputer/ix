import Aiur.Memory.Soundness
import Aiur.Memory.Completeness
import Aiur.Memory.WireEncoding
import Aiur.Completeness
import Aiur.MemoSoundness
import Aiur.Circuit.Entry
import Aiur.EvalCorrectness
import Aiur.InputTypes

namespace Aiur

/-- Canonical entry values: the address map is immaterial because arguments contain no pointers. -/
def entryValues [Zero F] (args : List (SourceValue F)) : List (Value F) :=
  args.map (Value.mapAddress (fun _ => 0))

theorem entryValues_eq [Zero F] {args : List (SourceValue F)}
    (free : ∀ value ∈ args, value.pointerFree = true) (encode : Nat → F) :
    args.map (Value.mapAddress encode) = entryValues args :=
  List.map_congr_left (fun value member => value.mapAddress_free (free value member) _ _)

/-- Public acceptance of the canonical flat encodings of semantic entry values. -/
def Circuit.EncodedEntryDerives [Field F] [DecidableEq F] (system : Circuit.System F)
    (name : String) (args : List (Value F)) (result : Value F) : Prop :=
  ∃ wires output, DecodesValues system.enums wires args ∧ output.decode system.enums = some result ∧
    Circuit.EntryDerives system ⟨name, wires, output⟩

/-- The same public claim with a finite memoized graph. Cycles remain permitted. -/
def Circuit.EncodedMemoEntryDerives [Field F] [DecidableEq F] (system : Circuit.System F)
    (name : String) (args : List (Value F)) (result : Value F) : Prop :=
  ∃ wires output, DecodesValues system.enums wires args ∧ output.decode system.enums = some result ∧
    Circuit.MemoEntryDerives system ⟨name, wires, output⟩

theorem Circuit.EncodedEntryDerives.memo [Field F] [DecidableEq F]
    {system : Circuit.System F} {name : String} {args : List (Value F)} {result : Value F}
    (accepted : Circuit.EncodedEntryDerives system name args result) :
    Circuit.EncodedMemoEntryDerives system name args result := by
  obtain ⟨wires, output, arguments, decoded, tree⟩ := accepted
  exact ⟨wires, output, arguments, decoded, tree.memo⟩

private theorem public_arguments [Field F] [DecidableEq F] {decls : Declarations}
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

private theorem decoded_public_arguments [Field F] [DecidableEq F] {decls : Declarations}
    {wires : List (WireValue F)} {values : List (Value F)}
    (arguments : DecodesValues decls wires values)
    (free : ∀ wire ∈ wires, wire.type.pointerFree decls = true) :
    ∀ value ∈ values, value.type.pointerFree decls = true := by
  induction arguments with
  | nil => simp
  | @cons wire value wires values head tail ih =>
      have spec := WireValue.decode_spec head
      have valid : value.type.pointerFree decls = true := by
        rw [spec.1]; exact free wire (by simp)
      simpa only [List.mem_cons, forall_eq_or_imp] using
        And.intro valid (ih (fun w h => free w (by simp [h])))

/-- Completeness uses an injection only on allocated locations; enums need no extra execution premise. -/
theorem compiler_heap_complete [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system)
    {name : String} {args : List (SourceValue F)} {value : SourceValue F} {heap : Heap F}
    (entry : checkEntry program name = .ok ()) (evaluated : EvalFn program name args [] value heap)
    (encode : Nat → F)
    (distinct : ∀ i j, i < heap.length → j < heap.length → encode i = encode j → i = j) :
    Circuit.EncodedEntryDerives system name (entryValues args) (value.mapAddress encode) := by
  have stages := Circuit.compile_stages compiled
  have declarations := typecheck_declarations stages.1
  have free := evaluated.public_pointerFree entry
  have heapGood := (evaluated.heap_good stages.1 (by simp [Heap.Good])
    (fun arg member => Value.pointerNames_of_free (free arg member))).2
  let table := ROM.ofHeap heap encode
  have good := ROM.ofHeap_good heapGood encode
  have decodeTable := ROM.decode_encode declarations stages.2.1 good
  have body := evaluated.toROM (ROM.ofHeap_cells heap encode)
  have encodedBody : ROMEvalCall ((table.encode program.enums).decode program.enums) program name
      (args.map (Value.mapAddress encode)) (value.mapAddress encode) := by
    rw [decodeTable]; exact body
  obtain ⟨wires, output, arguments, decoded, derives⟩ := evaluation_complete compiled encodedBody
  rw [entryValues_eq free encode] at arguments
  have argsFree : ∀ arg ∈ entryValues args, arg.type.pointerFree program.enums = true := by
    intro arg member
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
    simpa using (evaluated.publicArguments entry source sourceMember).1
  have tableValid := ROM.encode_valid declarations good (ROM.ofHeap_valid heap encode distinct)
  refine ⟨wires, output, ?_, ?_, ?_⟩
  · simpa only [stages.2.2.2.1] using arguments
  · simpa only [stages.2.2.2.1] using decoded
  · refine ⟨?_, ?_, table.encode program.enums, tableValid, derives⟩
    · exact ⟨by simpa only [stages.2.2.2.1] using arguments.each,
        by simpa only [stages.2.2.2.1] using
          (show ∃ value, output.decode program.enums = some value from ⟨_, decoded⟩)⟩
    · simpa only [stages.2.2.2.1, Circuit.Message.PublicArguments] using public_arguments arguments argsFree

/-- Allocation capacity and tag injectivity are separate: compilation already checks the latter. -/
theorem compiler_heap_complete_finite [Field F] [DecidableEq F] [Fintype F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system)
    {name : String} {args : List (SourceValue F)} {value : SourceValue F} {heap : Heap F}
    (entry : checkEntry program name = .ok ()) (evaluated : EvalFn program name args [] value heap)
    (capacity : heap.length ≤ Fintype.card F) :
    ∃ encode : Nat → F, Circuit.EncodedEntryDerives system name (entryValues args) (value.mapAddress encode) := by
  obtain ⟨encode, distinct⟩ := heap_address_embedding heap capacity
  exact ⟨encode, compiler_heap_complete compiled entry evaluated encode distinct⟩

/-- A successful executable run supplies a witness when its allocations fit the field. -/
theorem compiler_run_complete [Field F] [DecidableEq F] [Fintype F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system)
    {name : String} {args : List (SourceValue F)} {fuel : Nat}
    {value : SourceValue F} {heap : Heap F} {hints : HintProvider F program.enums}
    (executed : run program name args fuel hints = .ok (value, heap)) (capacity : heap.length ≤ Fintype.card F) :
    ∃ encode : Nat → F, Circuit.EncodedEntryDerives system name (entryValues args) (value.mapAddress encode) := by
  obtain ⟨_, entry, locals, expr, prepared, body⟩ := run_eq_ok_iff.mp executed
  exact compiler_heap_complete_finite compiled entry (.intro prepared (evalExpr_spec body)) capacity

/-- Memoized completeness reuses the same tree witness and allocation bound. -/
theorem memo_run_complete [Field F] [DecidableEq F] [Fintype F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system)
    {name : String} {args : List (SourceValue F)} {fuel : Nat}
    {value : SourceValue F} {heap : Heap F} {hints : HintProvider F program.enums}
    (executed : run program name args fuel hints = .ok (value, heap)) (capacity : heap.length ≤ Fintype.card F) :
    ∃ encode : Nat → F, Circuit.EncodedMemoEntryDerives system name (entryValues args) (value.mapAddress encode) := by
  obtain ⟨encode, tree⟩ := compiler_run_complete compiled executed capacity
  exact ⟨encode, tree.memo⟩

/-- Soundness realizes decoded circuit values by fresh source allocations, allowing address sharing. -/
theorem compiler_heap_sound [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system) {rom : WireROM F} (valid : rom.Valid)
    {name : String} {args : List (SourceValue F)} {result : Value F}
    (entry : checkEntry program name = .ok ())
    {wires : List (WireValue F)} {output : WireValue F}
    (derived : Circuit.CircuitEvaluates system rom name wires output)
    (arguments : DecodesValues program.enums wires (entryValues args))
    (decoded : output.decode program.enums = some result) :
    ∃ source heap, EvalFn program name args [] source heap ∧
      Represents (rom.decode program.enums) heap source result := by
  have evaluated := compiler_sound compiled derived arguments decoded
  have free : ∀ value ∈ args, value.pointerFree = true := by
    intro value member
    have valid := evaluated.publicArguments entry (value.mapAddress (fun _ => 0))
      (List.mem_map.mpr ⟨value, member, rfl⟩)
    exact Value.pointerFree_of_type (by simpa using valid.1) (by simpa using valid.2)
  have relatedArgs : RepresentsArgs (rom.decode program.enums) [] args (entryValues args) := by
    apply List.forall₂_map_right_iff.mpr
    exact List.forall₂_same.mpr (fun value member =>
      Represents.of_pointerFree value (free value member) _)
  obtain ⟨source, heap, evaluated, _, related⟩ := evaluated.realize (WireROM.decode_valid valid) relatedArgs
  exact ⟨source, heap, evaluated, related⟩

/-- Pointer-free decoded results agree exactly with source evaluation. -/
theorem compiler_entry_sound [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system)
    {name : String} {args : List (SourceValue F)} {result : Value F}
    (accepted : Circuit.EncodedEntryDerives system name (entryValues args) result)
    (free : result.pointerFree = true) :
    EvalCall program name args (result.mapAddress (fun _ => 0)) := by
  obtain ⟨wires, output, arguments, decoded, _, argumentsFree, rom, valid, derived⟩ := accepted
  have enums := (Circuit.compile_stages compiled).2.2.2.1
  rw [enums] at arguments decoded argumentsFree
  have sourceFree := decoded_public_arguments arguments argumentsFree
  have entry : checkEntry program name = .ok () :=
    (compiler_sound compiled derived arguments decoded).entry_of_publicArguments sourceFree
  obtain ⟨source, heap, evaluated, related⟩ := compiler_heap_sound compiled valid entry derived arguments decoded
  rw [related.pointerFree_eq free] at evaluated
  exact ⟨entry, heap, evaluated⟩

/-- Acyclic memoized call graphs have heap soundness without a totality hypothesis. -/
theorem memo_acyclic_heap_sound [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system) {rom : WireROM F} (valid : rom.Valid)
    {name : String} {args : List (SourceValue F)} {result : Value F}
    (entry : checkEntry program name = .ok ())
    {wires : List (WireValue F)} {output : WireValue F}
    (graph : Circuit.MemoDerivation system rom ⟨name, wires, output⟩) (acyclic : graph.Acyclic)
    (arguments : DecodesValues program.enums wires (entryValues args))
    (decoded : output.decode program.enums = some result) :
    ∃ source heap, EvalFn program name args [] source heap ∧
      Represents (rom.decode program.enums) heap source result :=
  compiler_heap_sound compiled valid entry (graph.derives_of_acyclic acyclic) arguments decoded

end Aiur
