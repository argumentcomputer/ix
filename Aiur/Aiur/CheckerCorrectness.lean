import Aiur.Circuit.CheckerContext
import Aiur.MemoryCorrectness

namespace Aiur

variable {F : Type} [Field F] [DecidableEq F]

/-- Unit balance feeds the existing compiler soundness proof through a finite tree. -/
theorem checker_sound {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system)
    {rom : WireROM F} {message : Circuit.Message F} {rows : List (Circuit.Row F)}
    (checked : system.check rom message rows = .ok ()) : message.Evaluates program rom := by
  obtain ⟨tree⟩ := system.check_sound checked
  exact derivation_sound compiled tree

/-- The public checker also supplies ROM validity for the existing heap realization proof. -/
theorem checker_heap_sound {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system)
    {rom : WireROM F} {name : String} {args : List (SourceValue F)} {result : Value F}
    {wires : List (WireValue F)} {output : WireValue F} {rows : List (Circuit.Row F)}
    (checked : system.check rom ⟨name, wires, output⟩ rows = .ok ())
    (entry : checkEntry program name = .ok ())
    (arguments : DecodesValues program.enums wires (entryValues args))
    (decoded : output.decode program.enums = some result) :
    ∃ source heap, EvalFn program name args [] source heap ∧
      Represents (rom.decode program.enums) heap source result :=
  compiler_heap_sound compiled
    (Circuit.System.checkContext_iff.mp (Circuit.System.check_iff.mp checked).1).2.2.1
    entry (system.check_sound checked) arguments decoded

/-- A successful run has a unit-balanced trace when the system passes its global
namespace/layout checks and its allocations fit the field. -/
theorem checker_run_complete [Fintype F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system) (wellFormed : system.WellFormed)
    {name : String} {args : List (SourceValue F)} {fuel : Nat}
    {value : SourceValue F} {heap : Heap F} {hints : HintProvider F program.enums}
    (executed : run program name args fuel hints = .ok (value, heap))
    (capacity : heap.length ≤ Fintype.card F) :
    ∃ (encode : Nat → F), ∃ wires output rom rows,
      DecodesValues system.enums wires (entryValues args) ∧
      output.decode system.enums = some (value.mapAddress encode) ∧
      system.check rom ⟨name, wires, output⟩ rows = .ok () := by
  obtain ⟨encode, wires, output, arguments, decoded, accepted⟩ :=
    compiler_run_complete compiled executed capacity
  obtain ⟨rom, rows, checked⟩ := (system.check_entry_iff wellFormed).mpr accepted
  exact ⟨encode, wires, output, rom, rows, arguments, decoded, checked⟩

/-- The memoized version reuses execution completeness and the graph-to-trace bridge. -/
theorem checkerMemo_run_complete [Fintype F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system) (wellFormed : system.WellFormed)
    {name : String} {args : List (SourceValue F)} {fuel : Nat}
    {value : SourceValue F} {heap : Heap F} {hints : HintProvider F program.enums}
    (executed : run program name args fuel hints = .ok (value, heap))
    (capacity : heap.length ≤ Fintype.card F) :
    ∃ (encode : Nat → F), ∃ wires output rom rows,
      DecodesValues system.enums wires (entryValues args) ∧
      output.decode system.enums = some (value.mapAddress encode) ∧
      system.checkMemo rom ⟨name, wires, output⟩ rows = .ok () := by
  obtain ⟨encode, wires, output, arguments, decoded, accepted⟩ :=
    memo_run_complete compiled executed capacity
  obtain ⟨rom, rows, checked⟩ := (system.checkMemo_entry_iff wellFormed).mpr accepted
  exact ⟨encode, wires, output, rom, rows, arguments, decoded, checked⟩

end Aiur
