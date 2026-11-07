import Aiur.Generic.NativeSoundness
import Aiur.Generic.Circuit

namespace Aiur.Generic

variable {F : Type} [Field F] [DecidableEq F]
variable {s : Source F} {entries : List String}

/-- Completeness starts at the independent predicate on the original generic
source, before const expansion, array lowering, or function specialization. -/
theorem Specialized.heap_complete (q : Specialized s entries)
    (selected : name ∈ entries) {system : Aiur.Circuit.System F}
    (compiled : Aiur.Circuit.compile q.program = .ok system)
    (evaluated : SourceSemantics.EvalFn s.world name args [] value heap) (encode : Nat → F)
    (distinct : ∀ i j, i < heap.length → j < heap.length → encode i = encode j → i = j) :
    Aiur.Circuit.EncodedEntryDerives system name (entryValues args) (value.mapAddress encode) := by
  have root := q.valid.2.2.2.2.2.2.2 name selected
  exact q.core_heap_complete selected compiled (q.native_complete root.1 evaluated) encode distinct

theorem Specialized.run_complete [Fintype F] (q : Specialized s entries)
    (selected : name ∈ entries) {system : Aiur.Circuit.System F}
    (compiled : Aiur.Circuit.compile q.program = .ok system) {hints : s.HintProvider}
    (executed : s.run name args fuel hints = .ok (value, heap)) (capacity : heap.length ≤ Fintype.card F) :
    ∃ encode : Nat → F, Aiur.Circuit.EncodedEntryDerives system name (entryValues args) (value.mapAddress encode) := by
  obtain ⟨encode, distinct⟩ := heap_address_embedding heap capacity
  exact ⟨encode, q.heap_complete selected compiled (Source.run_spec executed).2 encode distinct⟩

/-- Native evaluation produces a finite sequence accepted by the integer
one-for-one row checker, under the finite-field address-capacity condition. -/
theorem Specialized.checker_heap_complete [Fintype F] (q : Specialized s entries)
    (selected : name ∈ entries) {system : Aiur.Circuit.System F}
    (compiled : Aiur.Circuit.compile q.program = .ok system) (wellFormed : system.WellFormed)
    (evaluated : SourceSemantics.EvalFn s.world name args [] value heap)
    (capacity : heap.length ≤ Fintype.card F) :
    ∃ (encode : Nat → F), ∃ wires output rom rows,
      DecodesValues system.enums wires (entryValues args) ∧
      output.decode system.enums = some (value.mapAddress encode) ∧
      system.check rom ⟨name, wires, output⟩ rows = .ok () := by
  obtain ⟨encode, distinct⟩ := heap_address_embedding heap capacity
  obtain ⟨wires, output, arguments, decoded, derived⟩ := q.heap_complete selected compiled evaluated encode distinct
  obtain ⟨rom, rows, checked⟩ := (system.check_entry_iff wellFormed).mpr derived
  exact ⟨encode, wires, output, rom, rows, arguments, decoded, checked⟩

/-- The same native evaluation also produces accepted memoized rows. Cycles
are permitted by that checker; completeness needs no acyclicity assumption. -/
theorem Specialized.checkerMemo_heap_complete [Fintype F] (q : Specialized s entries)
    (selected : name ∈ entries) {system : Aiur.Circuit.System F}
    (compiled : Aiur.Circuit.compile q.program = .ok system) (wellFormed : system.WellFormed)
    (evaluated : SourceSemantics.EvalFn s.world name args [] value heap)
    (capacity : heap.length ≤ Fintype.card F) :
    ∃ (encode : Nat → F), ∃ wires output rom rows,
      DecodesValues system.enums wires (entryValues args) ∧
      output.decode system.enums = some (value.mapAddress encode) ∧
      system.checkMemo rom ⟨name, wires, output⟩ rows = .ok () := by
  obtain ⟨encode, distinct⟩ := heap_address_embedding heap capacity
  obtain ⟨wires, output, arguments, decoded, derived⟩ :=
    (q.heap_complete selected compiled evaluated encode distinct).memo
  obtain ⟨rom, rows, checked⟩ := (system.checkMemo_entry_iff wellFormed).mpr derived
  exact ⟨encode, wires, output, rom, rows, arguments, decoded, checked⟩

theorem Specialized.checker_run_complete [Fintype F] (q : Specialized s entries)
    (selected : name ∈ entries) {system : Aiur.Circuit.System F}
    (compiled : Aiur.Circuit.compile q.program = .ok system) (wellFormed : system.WellFormed)
    {hints : s.HintProvider}
    (executed : s.run name args fuel hints = .ok (value, heap)) (capacity : heap.length ≤ Fintype.card F) :
    ∃ (encode : Nat → F), ∃ wires output rom rows,
      DecodesValues system.enums wires (entryValues args) ∧
      output.decode system.enums = some (value.mapAddress encode) ∧
      system.check rom ⟨name, wires, output⟩ rows = .ok () :=
  q.checker_heap_complete selected compiled wellFormed (Source.run_spec executed).2 capacity

theorem Specialized.checkerMemo_run_complete [Fintype F] (q : Specialized s entries)
    (selected : name ∈ entries) {system : Aiur.Circuit.System F}
    (compiled : Aiur.Circuit.compile q.program = .ok system) (wellFormed : system.WellFormed)
    {hints : s.HintProvider}
    (executed : s.run name args fuel hints = .ok (value, heap)) (capacity : heap.length ≤ Fintype.card F) :
    ∃ (encode : Nat → F), ∃ wires output rom rows,
      DecodesValues system.enums wires (entryValues args) ∧
      output.decode system.enums = some (value.mapAddress encode) ∧
      system.checkMemo rom ⟨name, wires, output⟩ rows = .ok () :=
  q.checkerMemo_heap_complete selected compiled wellFormed (Source.run_spec executed).2 capacity

/-- A circuit derivation realizes an evaluation of the original generic source.
Pointer addresses are related through the ROM, not equated with source addresses. -/
theorem Specialized.heap_sound (q : Specialized s entries) (selected : name ∈ entries)
    {system : Aiur.Circuit.System F} (compiled : Aiur.Circuit.compile q.program = .ok system)
    {rom : WireROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (derived : Aiur.Circuit.CircuitEvaluates system rom name wires output)
    (arguments : DecodesValues q.program.enums wires (entryValues args))
    (decoded : output.decode q.program.enums = some result) :
    ∃ value heap, SourceSemantics.EvalFn s.world name args [] value heap ∧
      Represents (rom.decode q.program.enums) heap value result := by
  have entry := (q.valid.2.2.2.2.2.2.2 name selected).2.2
  obtain ⟨value, heap, evaluated, related⟩ :=
    compiler_heap_sound compiled valid entry derived arguments decoded
  exact ⟨value, heap, q.native_entry_sound selected evaluated, related⟩

/-- Sharing is allowed; acyclicity of this finite graph replaces any source
totality requirement. -/
theorem Specialized.memo_acyclic_heap_sound (q : Specialized s entries) (selected : name ∈ entries)
    {system : Aiur.Circuit.System F} (compiled : Aiur.Circuit.compile q.program = .ok system)
    {rom : WireROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (graph : Aiur.Circuit.MemoDerivation system rom ⟨name, wires, output⟩) (acyclic : graph.Acyclic)
    (arguments : DecodesValues q.program.enums wires (entryValues args))
    (decoded : output.decode q.program.enums = some result) :
    ∃ value heap, SourceSemantics.EvalFn s.world name args [] value heap ∧
      Represents (rom.decode q.program.enums) heap value result :=
  q.heap_sound selected compiled valid (graph.derives_of_acyclic acyclic) arguments decoded

/-- Integer unit balance, including redundant rows, implies evaluation on the
original source AST. No source-to-core equivalence is assumed. -/
theorem Specialized.checker_heap_sound (q : Specialized s entries) (selected : name ∈ entries)
    {system : Aiur.Circuit.System F} (compiled : Aiur.Circuit.compile q.program = .ok system)
    {rom : WireROM F} {args : List (SourceValue F)} {result : Value F}
    {wires : List (WireValue F)} {output : WireValue F} {rows : List (Aiur.Circuit.Row F)}
    (checked : system.check rom ⟨name, wires, output⟩ rows = .ok ())
    (arguments : DecodesValues q.program.enums wires (entryValues args))
    (decoded : output.decode q.program.enums = some result) :
    ∃ value heap, SourceSemantics.EvalFn s.world name args [] value heap ∧
      Represents (rom.decode q.program.enums) heap value result := by
  have entry := (q.valid.2.2.2.2.2.2.2 name selected).2.2
  obtain ⟨value, heap, evaluated, related⟩ := Aiur.checker_heap_sound compiled checked entry arguments decoded
  exact ⟨value, heap, q.native_entry_sound selected evaluated, related⟩

/-- Conditional soundness for weighted rows. Acceptance supplies a closed
support graph; the additional condition concerns that graph's edges, not
termination or totality of the source program. -/
theorem Specialized.checkerMemo_acyclic_heap_sound (q : Specialized s entries) (selected : name ∈ entries)
    {system : Aiur.Circuit.System F} (compiled : Aiur.Circuit.compile q.program = .ok system)
    {rom : WireROM F} {args : List (SourceValue F)} {result : Value F}
    {wires : List (WireValue F)} {output : WireValue F} {rows : List (Aiur.Circuit.WeightedRow F)}
    (checked : system.checkMemo rom ⟨name, wires, output⟩ rows = .ok ())
    (acyclic : (Classical.choice (system.checkMemo_sound checked)).Acyclic)
    (arguments : DecodesValues q.program.enums wires (entryValues args))
    (decoded : output.decode q.program.enums = some result) :
    ∃ value heap, SourceSemantics.EvalFn s.world name args [] value heap ∧
      Represents (rom.decode q.program.enums) heap value result :=
  q.memo_acyclic_heap_sound selected compiled
    (Aiur.Circuit.System.checkContext_iff.mp (Aiur.Circuit.System.checkMemo_iff.mp checked).1).2.2.1
    (Classical.choice (system.checkMemo_sound checked)) acyclic arguments decoded

/-- Inlining is downstream of the native source predicate. -/
theorem Compiled.native_entry_iff {q : Specialized s entries} (c : Compiled q)
    (selected : name ∈ entries) :
    SourceSemantics.EvalFn s.world name args [] result heap ↔
      Aiur.EvalFn c.program name args [] result heap :=
  (q.native_entry_iff selected).trans (c.inlined.entry_iff selected)

theorem Compiled.heap_complete {q : Specialized s entries} (c : Compiled q)
    (selected : name ∈ entries)
    (evaluated : SourceSemantics.EvalFn s.world name args [] value heap) (encode : Nat → F)
    (distinct : ∀ i j, i < heap.length → j < heap.length → encode i = encode j → i = j) :
    Aiur.Circuit.EncodedEntryDerives c.system name (entryValues args) (value.mapAddress encode) :=
  compiler_heap_complete c.compiled (c.inlined.valid.2.2 name selected).2
    ((c.native_entry_iff selected).mp evaluated) encode distinct

theorem Compiled.heap_sound {q : Specialized s entries} (c : Compiled q) (selected : name ∈ entries)
    {rom : WireROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (derived : Aiur.Circuit.CircuitEvaluates c.system rom name wires output)
    (arguments : DecodesValues q.program.enums wires (entryValues args))
    (decoded : output.decode q.program.enums = some result) :
    ∃ value heap, SourceSemantics.EvalFn s.world name args [] value heap ∧
      Represents (rom.decode q.program.enums) heap value result := by
  obtain ⟨value,heap,evaluated,related⟩ := compiler_heap_sound c.compiled valid
    (c.inlined.valid.2.2 name selected).2 derived arguments decoded
  exact ⟨value,heap,(c.native_entry_iff selected).mpr evaluated,related⟩

theorem Compiled.checker_heap_complete [Fintype F] {q : Specialized s entries} (c : Compiled q)
    (selected : name ∈ entries) (wellFormed : c.system.WellFormed)
    (evaluated : SourceSemantics.EvalFn s.world name args [] value heap) (capacity : heap.length ≤ Fintype.card F) :
    ∃ (encode : Nat → F), ∃ wires output rom rows,
      DecodesValues c.system.enums wires (entryValues args) ∧
      output.decode c.system.enums = some (value.mapAddress encode) ∧
      c.system.check rom ⟨name,wires,output⟩ rows = .ok () := by
  obtain ⟨encode,distinct⟩ := heap_address_embedding heap capacity
  obtain ⟨wires,output,arguments,decoded,derived⟩ := c.heap_complete selected evaluated encode distinct
  obtain ⟨rom,rows,checked⟩ := (c.system.check_entry_iff wellFormed).mpr derived
  exact ⟨encode,wires,output,rom,rows,arguments,decoded,checked⟩

theorem Compiled.checkerMemo_heap_complete [Fintype F] {q : Specialized s entries} (c : Compiled q)
    (selected : name ∈ entries) (wellFormed : c.system.WellFormed)
    (evaluated : SourceSemantics.EvalFn s.world name args [] value heap) (capacity : heap.length ≤ Fintype.card F) :
    ∃ (encode : Nat → F), ∃ wires output rom rows,
      DecodesValues c.system.enums wires (entryValues args) ∧
      output.decode c.system.enums = some (value.mapAddress encode) ∧
      c.system.checkMemo rom ⟨name,wires,output⟩ rows = .ok () := by
  obtain ⟨encode,distinct⟩ := heap_address_embedding heap capacity
  obtain ⟨wires,output,arguments,decoded,derived⟩ := (c.heap_complete selected evaluated encode distinct).memo
  obtain ⟨rom,rows,checked⟩ := (c.system.checkMemo_entry_iff wellFormed).mpr derived
  exact ⟨encode,wires,output,rom,rows,arguments,decoded,checked⟩

theorem Compiled.checker_heap_sound {q : Specialized s entries} (c : Compiled q) (selected : name ∈ entries)
    {rom : WireROM F} {args : List (SourceValue F)} {result : Value F}
    {wires : List (WireValue F)} {output : WireValue F} {rows : List (Aiur.Circuit.Row F)}
    (checked : c.system.check rom ⟨name,wires,output⟩ rows = .ok ())
    (arguments : DecodesValues q.program.enums wires (entryValues args))
    (decoded : output.decode q.program.enums = some result) :
    ∃ value heap, SourceSemantics.EvalFn s.world name args [] value heap ∧
      Represents (rom.decode q.program.enums) heap value result := by
  obtain ⟨value,heap,evaluated,related⟩ := Aiur.checker_heap_sound c.compiled checked
    (c.inlined.valid.2.2 name selected).2 arguments decoded
  exact ⟨value,heap,(c.native_entry_iff selected).mpr evaluated,related⟩

theorem Compiled.checkerMemo_acyclic_heap_sound {q : Specialized s entries} (c : Compiled q)
    (selected : name ∈ entries)
    {rom : WireROM F} {args : List (SourceValue F)} {result : Value F}
    {wires : List (WireValue F)} {output : WireValue F} {rows : List (Aiur.Circuit.WeightedRow F)}
    (checked : c.system.checkMemo rom ⟨name,wires,output⟩ rows = .ok ())
    (acyclic : (Classical.choice (c.system.checkMemo_sound checked)).Acyclic)
    (arguments : DecodesValues q.program.enums wires (entryValues args))
    (decoded : output.decode q.program.enums = some result) :
    ∃ value heap, SourceSemantics.EvalFn s.world name args [] value heap ∧
      Represents (rom.decode q.program.enums) heap value result :=
  c.heap_sound selected
    (Aiur.Circuit.System.checkContext_iff.mp (Aiur.Circuit.System.checkMemo_iff.mp checked).1).2.2.1
    ((Classical.choice (c.system.checkMemo_sound checked)).derives_of_acyclic acyclic) arguments decoded

/-- The public checker supplies the selected-entry condition, so its soundness
statement concludes the public predicate on the original source. -/
theorem Compiled.check_sound {q : Specialized s entries} (c : Compiled q)
    {rom : WireROM F} {args : List (SourceValue F)} {result : Value F}
    {wires : List (WireValue F)} {output : WireValue F} {rows : List (Aiur.Circuit.Row F)}
    (checked : c.check rom ⟨name, wires, output⟩ rows = .ok ())
    (arguments : DecodesValues q.program.enums wires (entryValues args))
    (decoded : output.decode q.program.enums = some result) :
    ∃ value heap, s.EvalCall name args value ∧
      Represents (rom.decode q.program.enums) heap value result := by
  obtain ⟨selected, checked⟩ := c.check_iff.mp checked
  obtain ⟨value, heap, evaluated, related⟩ := c.checker_heap_sound selected checked arguments decoded
  exact ⟨value, heap, ⟨(q.valid.2.2.2.2.2.2.2 name selected).2.1, heap, evaluated⟩, related⟩

theorem Compiled.checkMemo_acyclic_sound {q : Specialized s entries} (c : Compiled q)
    {rom : WireROM F} {args : List (SourceValue F)} {result : Value F}
    {wires : List (WireValue F)} {output : WireValue F} {rows : List (Aiur.Circuit.WeightedRow F)}
    (checked : c.checkMemo rom ⟨name, wires, output⟩ rows = .ok ())
    (acyclic : (Classical.choice (c.system.checkMemo_sound (c.checkMemo_iff.mp checked).2)).Acyclic)
    (arguments : DecodesValues q.program.enums wires (entryValues args))
    (decoded : output.decode q.program.enums = some result) :
    ∃ value heap, s.EvalCall name args value ∧
      Represents (rom.decode q.program.enums) heap value result := by
  obtain ⟨selected, accepted⟩ := c.checkMemo_iff.mp checked
  obtain ⟨value, heap, evaluated, related⟩ :=
    c.checkerMemo_acyclic_heap_sound selected accepted acyclic arguments decoded
  exact ⟨value, heap, ⟨(q.valid.2.2.2.2.2.2.2 name selected).2.1, heap, evaluated⟩, related⟩

end Aiur.Generic
