import Aiur.Optimized.Equivalence

namespace Aiur.Optimized

variable {F : Type} [Field F] [DecidableEq F]
  {source : Generic.Source F} {entries : List String}

theorem GenericArtifact.native_entry_iff {prepared : Generic.Specialized source entries}
    (compiled : GenericArtifact prepared) {name : String} (selected : name ∈ entries) :
    Generic.SourceSemantics.EvalFn source.world name args [] value heap ↔
      Aiur.EvalFn compiled.inlined.program name args [] value heap :=
  (prepared.native_entry_iff selected).trans (compiled.inlined.entry_iff selected)

/-- Completeness begins at the independent predicate on the original source.
Specialization, mandatory inlining, scoped compilation, physical layout, and
deduplication are all included. -/
theorem GenericArtifact.heap_complete {prepared : Generic.Specialized source entries}
    (compiled : GenericArtifact prepared) {name : String} (selected : name ∈ entries)
    {args : List (SourceValue F)} {value : SourceValue F} {heap : Heap F}
    (evaluated : Generic.SourceSemantics.EvalFn source.world name args [] value heap)
    (encode : Nat → F) (distinct : ∀ i j, i < heap.length → j < heap.length → encode i = encode j → i = j) :
    Circuit.EncodedEntryDerives compiled.system name (entryValues args) (value.mapAddress encode) := by
  have stages := compile_stages compiled.compiled
  have model := compile_semanticModel compiled.compiled
  have originalEnums : compiled.artifact.unmerged.enums = compiled.inlined.program.enums := by
    rw [stages.2.2.2.2.2]
  obtain ⟨wires, output, arguments, decoded, formed, free, rom, valid, derived⟩ :=
    model.heap_complete stages.1 stages.2.1 originalEnums (compiled.inlined.valid.2.2 name selected).2
      ((compiled.native_entry_iff selected).mp evaluated) encode distinct
  have sameEnums : compiled.system.enums = compiled.artifact.unmerged.enums :=
    compiled.artifact.deduplication.2.2.2.2.2.1
  refine ⟨wires, output, ?_, ?_, ?_, ?_, rom, valid, ?_⟩
  · simpa only [sameEnums] using arguments
  · simpa only [sameEnums] using decoded
  · simpa only [sameEnums] using formed
  · simpa only [sameEnums] using free
  · exact (compiled.artifact.dedup_derives_iff (by simpa only [stages.2.2.1] using selected)).mp derived

theorem GenericArtifact.heap_sound {prepared : Generic.Specialized source entries}
    (compiled : GenericArtifact prepared) {name : String} (selected : name ∈ entries)
    {rom : WireROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (derived : Circuit.CircuitEvaluates compiled.system rom name wires output)
    (arguments : DecodesValues prepared.program.enums wires (entryValues args))
    (decoded : output.decode prepared.program.enums = some result) :
    ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
      Represents (rom.decode prepared.program.enums) heap value result := by
  have stages := compile_stages compiled.compiled
  have original := (compiled.artifact.dedup_derives_iff (by simpa only [stages.2.2.1] using selected)).mpr derived
  obtain ⟨value, heap, evaluated, related⟩ :=
    (compile_semanticModel compiled.compiled).heap_sound valid (compiled.inlined.valid.2.2 name selected).2
      original arguments decoded
  exact ⟨value, heap, (compiled.native_entry_iff selected).mpr evaluated, related⟩

theorem GenericArtifact.checker_heap_complete [Fintype F] {prepared : Generic.Specialized source entries}
    (compiled : GenericArtifact prepared) {name : String} (selected : name ∈ entries)
    {args : List (SourceValue F)} {value : SourceValue F} {heap : Heap F}
    (evaluated : Generic.SourceSemantics.EvalFn source.world name args [] value heap)
    (capacity : heap.length ≤ Fintype.card F) :
    ∃ (encode : Nat → F), ∃ wires output rom rows,
      DecodesValues compiled.system.enums wires (entryValues args) ∧
      output.decode compiled.system.enums = some (value.mapAddress encode) ∧
      compiled.system.check rom ⟨name, wires, output⟩ rows = .ok () := by
  obtain ⟨encode, distinct⟩ := heap_address_embedding heap capacity
  obtain ⟨wires, output, arguments, decoded, derived⟩ := compiled.heap_complete selected evaluated encode distinct
  obtain ⟨rom, rows, checked⟩ := (compiled.system.check_entry_iff compiled.artifact.wellFormed).mpr derived
  exact ⟨encode, wires, output, rom, rows, arguments, decoded, checked⟩

theorem GenericArtifact.checkerMemo_heap_complete [Fintype F] {prepared : Generic.Specialized source entries}
    (compiled : GenericArtifact prepared) {name : String} (selected : name ∈ entries)
    {args : List (SourceValue F)} {value : SourceValue F} {heap : Heap F}
    (evaluated : Generic.SourceSemantics.EvalFn source.world name args [] value heap)
    (capacity : heap.length ≤ Fintype.card F) :
    ∃ (encode : Nat → F), ∃ wires output rom rows,
      DecodesValues compiled.system.enums wires (entryValues args) ∧
      output.decode compiled.system.enums = some (value.mapAddress encode) ∧
      compiled.system.checkMemo rom ⟨name, wires, output⟩ rows = .ok () := by
  obtain ⟨encode, distinct⟩ := heap_address_embedding heap capacity
  obtain ⟨wires, output, arguments, decoded, derived⟩ :=
    (compiled.heap_complete selected evaluated encode distinct).memo
  obtain ⟨rom, rows, checked⟩ := (compiled.system.checkMemo_entry_iff compiled.artifact.wellFormed).mpr derived
  exact ⟨encode, wires, output, rom, rows, arguments, decoded, checked⟩

theorem GenericArtifact.checker_heap_sound {prepared : Generic.Specialized source entries}
    (compiled : GenericArtifact prepared) {name : String} (selected : name ∈ entries)
    {rom : WireROM F} {args : List (SourceValue F)} {result : Value F}
    {wires : List (WireValue F)} {output : WireValue F} {rows : List (Circuit.Row F)}
    (checked : compiled.system.check rom ⟨name, wires, output⟩ rows = .ok ())
    (arguments : DecodesValues prepared.program.enums wires (entryValues args))
    (decoded : output.decode prepared.program.enums = some result) :
    ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
      Represents (rom.decode prepared.program.enums) heap value result :=
  compiled.heap_sound selected
    (Circuit.System.checkContext_iff.mp (Circuit.System.check_iff.mp checked).1).2.2.1
    (compiled.system.check_sound checked) arguments decoded

theorem GenericArtifact.checkerMemo_acyclic_heap_sound {prepared : Generic.Specialized source entries}
    (compiled : GenericArtifact prepared) {name : String} (selected : name ∈ entries)
    {rom : WireROM F} {args : List (SourceValue F)} {result : Value F}
    {wires : List (WireValue F)} {output : WireValue F} {rows : List (Circuit.WeightedRow F)}
    (checked : compiled.system.checkMemo rom ⟨name, wires, output⟩ rows = .ok ())
    (acyclic : (Classical.choice (compiled.system.checkMemo_sound checked)).Acyclic)
    (arguments : DecodesValues prepared.program.enums wires (entryValues args))
    (decoded : output.decode prepared.program.enums = some result) :
    ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
      Represents (rom.decode prepared.program.enums) heap value result :=
  compiled.heap_sound selected
    (Circuit.System.checkContext_iff.mp (Circuit.System.checkMemo_iff.mp checked).1).2.2.1
    ((Classical.choice (compiled.system.checkMemo_sound checked)).derives_of_acyclic acyclic) arguments decoded

theorem GenericArtifact.check_sound {prepared : Generic.Specialized source entries}
    (compiled : GenericArtifact prepared) {name : String}
    {rom : WireROM F} {args : List (SourceValue F)} {result : Value F}
    {wires : List (WireValue F)} {output : WireValue F} {rows : List (Circuit.Row F)}
    (checked : compiled.artifact.check rom ⟨name, wires, output⟩ rows = .ok ())
    (arguments : DecodesValues prepared.program.enums wires (entryValues args))
    (decoded : output.decode prepared.program.enums = some result) :
    ∃ value heap, source.EvalCall name args value ∧
      Represents (rom.decode prepared.program.enums) heap value result := by
  obtain ⟨selected, checked⟩ := Artifact.check_iff.mp checked
  have selected : name ∈ entries := by simpa only [(compile_stages compiled.compiled).2.2.1] using selected
  obtain ⟨value, heap, evaluated, related⟩ := compiled.checker_heap_sound selected checked arguments decoded
  exact ⟨value, heap, ⟨(prepared.valid.2.2.2.2.2.2.2 name selected).2.1, heap, evaluated⟩, related⟩

/-- The public module API connects the original source predicate to the final
integer checker. No reference-compiler run is required. -/
theorem ModulesArtifact.check_complete [Fintype F] {program : Modules.Program F}
    {prepared : Modules.Prepared program} (compiled : ModulesArtifact prepared)
    (evaluated : prepared.EvalFn name args value heap) (capacity : heap.length ≤ Fintype.card F) :
    ∃ (encode : Nat → F), ∃ wires output rom rows,
      DecodesValues compiled.circuit.system.enums wires (entryValues args) ∧
      output.decode compiled.circuit.system.enums = some (value.mapAddress encode) ∧
      compiled.check rom name wires output rows = .ok () := by
  obtain ⟨entry, selected, evaluated⟩ := evaluated
  obtain ⟨encode, wires, output, rom, rows, arguments, decoded, checked⟩ :=
    compiled.circuit.checker_heap_complete (Modules.Prepared.entry_mem selected) evaluated capacity
  refine ⟨encode, wires, output, rom, rows, arguments, decoded, ?_⟩
  simp only [ModulesArtifact.check, selected]
  exact Artifact.check_iff.mpr ⟨by
    simpa only [(compile_stages compiled.circuit.compiled).2.2.1] using Modules.Prepared.entry_mem selected, checked⟩

theorem ModulesArtifact.checkMemo_complete [Fintype F] {program : Modules.Program F}
    {prepared : Modules.Prepared program} (compiled : ModulesArtifact prepared)
    (evaluated : prepared.EvalFn name args value heap) (capacity : heap.length ≤ Fintype.card F) :
    ∃ (encode : Nat → F), ∃ wires output rom rows,
      DecodesValues compiled.circuit.system.enums wires (entryValues args) ∧
      output.decode compiled.circuit.system.enums = some (value.mapAddress encode) ∧
      compiled.checkMemo rom name wires output rows = .ok () := by
  obtain ⟨entry, selected, evaluated⟩ := evaluated
  obtain ⟨encode, wires, output, rom, rows, arguments, decoded, checked⟩ :=
    compiled.circuit.checkerMemo_heap_complete (Modules.Prepared.entry_mem selected) evaluated capacity
  refine ⟨encode, wires, output, rom, rows, arguments, decoded, ?_⟩
  simp only [ModulesArtifact.checkMemo, selected]
  exact Artifact.checkMemo_iff.mpr ⟨by
    simpa only [(compile_stages compiled.circuit.compiled).2.2.1] using Modules.Prepared.entry_mem selected, checked⟩

theorem ModulesArtifact.run_complete [Fintype F] {program : Modules.Program F}
    {prepared : Modules.Prepared program} (compiled : ModulesArtifact prepared)
    {hints : prepared.environment.source.HintProvider}
    (executed : prepared.run name args fuel hints = .ok (value, heap)) (capacity : heap.length ≤ Fintype.card F) :
    ∃ (encode : Nat → F), ∃ wires output rom rows,
      DecodesValues compiled.circuit.system.enums wires (entryValues args) ∧
      output.decode compiled.circuit.system.enums = some (value.mapAddress encode) ∧
      compiled.check rom name wires output rows = .ok () :=
  compiled.check_complete (Modules.Prepared.run_heap_spec executed) capacity

theorem ModulesArtifact.runMemo_complete [Fintype F] {program : Modules.Program F}
    {prepared : Modules.Prepared program} (compiled : ModulesArtifact prepared)
    {hints : prepared.environment.source.HintProvider}
    (executed : prepared.run name args fuel hints = .ok (value, heap)) (capacity : heap.length ≤ Fintype.card F) :
    ∃ (encode : Nat → F), ∃ wires output rom rows,
      DecodesValues compiled.circuit.system.enums wires (entryValues args) ∧
      output.decode compiled.circuit.system.enums = some (value.mapAddress encode) ∧
      compiled.checkMemo rom name wires output rows = .ok () :=
  compiled.checkMemo_complete (Modules.Prepared.run_heap_spec executed) capacity

theorem ModulesArtifact.check_sound {program : Modules.Program F} {prepared : Modules.Prepared program}
    (compiled : ModulesArtifact prepared)
    {rom : WireROM F} {args : List (SourceValue F)} {result : Value F}
    {wires : List (WireValue F)} {output : WireValue F} {rows : List (Circuit.Row F)}
    (checked : compiled.check rom name wires output rows = .ok ())
    (arguments : DecodesValues compiled.specialized.program.enums wires (entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result) :
    ∃ value heap, prepared.EvalCall name args value ∧
      Represents (rom.decode compiled.specialized.program.enums) heap value result := by
  cases selected : prepared.find? name with
  | none => simp [ModulesArtifact.check, selected] at checked
  | some entry =>
      simp only [ModulesArtifact.check, selected] at checked
      obtain ⟨value, heap, evaluated, related⟩ := compiled.circuit.check_sound checked arguments decoded
      exact ⟨value, heap, ⟨entry, selected, evaluated⟩, related⟩

theorem ModulesArtifact.checkMemo_rows {program : Modules.Program F} {prepared : Modules.Prepared program}
    (compiled : ModulesArtifact prepared) {entry : Modules.Selection program prepared.environment.assembly.instances}
    (selected : prepared.find? name = some entry)
    (checked : compiled.checkMemo rom name wires output rows = .ok ()) :
    compiled.circuit.system.checkMemo rom ⟨entry.resolved.name, wires, output⟩ rows = .ok () := by
  simp only [ModulesArtifact.checkMemo, selected] at checked
  exact (Artifact.checkMemo_iff.mp checked).2

/-- Memoized soundness uses acyclicity of the support graph chosen through
`checkMemo_sound`. It does not assume that the source functions are total. -/
theorem ModulesArtifact.checkMemo_acyclic_sound {program : Modules.Program F}
    {prepared : Modules.Prepared program} (compiled : ModulesArtifact prepared)
    {entry : Modules.Selection program prepared.environment.assembly.instances}
    (selected : prepared.find? name = some entry)
    {rom : WireROM F} {args : List (SourceValue F)} {result : Value F}
    {wires : List (WireValue F)} {output : WireValue F} {rows : List (Circuit.WeightedRow F)}
    (checked : compiled.checkMemo rom name wires output rows = .ok ())
    (acyclic : (Classical.choice (compiled.circuit.system.checkMemo_sound
      (compiled.checkMemo_rows selected checked))).Acyclic)
    (arguments : DecodesValues compiled.specialized.program.enums wires (entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result) :
    ∃ value heap, prepared.EvalCall name args value ∧
      Represents (rom.decode compiled.specialized.program.enums) heap value result := by
  obtain ⟨value, heap, evaluated, related⟩ :=
    compiled.circuit.checkerMemo_acyclic_heap_sound (Modules.Prepared.entry_mem selected)
      (compiled.checkMemo_rows selected checked) acyclic arguments decoded
  have checkedEntry :=
    (compiled.specialized.valid.2.2.2.2.2.2.2 _ (Modules.Prepared.entry_mem selected)).2.1
  exact ⟨value, heap, ⟨entry, selected, checkedEntry, heap, evaluated⟩, related⟩

end Aiur.Optimized
