import Aiur.Generic.Correctness
import Aiur.CheckerCorrectness
import Aiur.Circuit.Stats
import Aiur.Inlining.Program

namespace Aiur.Generic

variable {F : Type} [Field F] [DecidableEq F]
variable {s : Source F} {entries : List String}

/-- The original declaration controls every concrete instance of a helper. -/
def Specialized.inlineNames (q : Specialized s entries) : List String :=
  q.program.functions.filterMap fun f =>
    match Instance.ofSymbol f.name with
    | .error _ => none
    | .ok key => if (s.program.findFunction? key.name).any (·.isInline) then some f.name else none

structure Compiled (q : Specialized s entries) where
  inlined : Inlining.Prepared q.program q.inlineNames entries
  system : Aiur.Circuit.System F
  compiled : Aiur.Circuit.compile inlined.program = .ok system

/-- The program actually passed to chip compilation, after mandatory inlining. -/
def Compiled.program {q : Specialized s entries} (c : Compiled q) : Aiur.Program F := c.inlined.program

def Specialized.compile (q : Specialized s entries) : Except String (Compiled q) := do
  let inlined ← Inlining.prepare q.program q.inlineNames entries
  match h : Aiur.Circuit.compile inlined.program with
  | .error e => .error (reprStr e)
  | .ok system => .ok ⟨inlined,system,h⟩

/-- Public checking retains the externally selected protocol interface. -/
def Compiled.check {q : Specialized s entries} (c : Compiled q) (rom : WireROM F)
    (root : Aiur.Circuit.Message F) (rows : List (Aiur.Circuit.Row F)) : Except String Unit := do
  q.checkEntry root.channel
  (c.system.check rom root rows).mapError reprStr

def Compiled.checkMemo {q : Specialized s entries} (c : Compiled q) (rom : WireROM F)
    (root : Aiur.Circuit.Message F) (rows : List (Aiur.Circuit.WeightedRow F)) : Except String Unit := do
  q.checkEntry root.channel
  (c.system.checkMemo rom root rows).mapError reprStr

theorem Compiled.check_iff {q : Specialized s entries} (c : Compiled q)
    {rom : WireROM F} {root : Aiur.Circuit.Message F} {rows : List (Aiur.Circuit.Row F)} :
    c.check rom root rows = .ok () ↔
      root.channel ∈ entries ∧ c.system.check rom root rows = .ok () := by
  cases entry : q.checkEntry root.channel with
  | error e =>
      have absent : root.channel ∉ entries := by
        intro h
        have := q.checkEntry_iff.mpr h
        simp [entry] at this
      simp [Compiled.check, entry, absent, bind, Except.bind]
  | ok u =>
      cases u
      have selected := q.checkEntry_iff.mp entry
      cases h : c.system.check rom root rows <;>
        simp [Compiled.check, entry, selected, h, Except.mapError, bind, Except.bind]

theorem Compiled.checkMemo_iff {q : Specialized s entries} (c : Compiled q)
    {rom : WireROM F} {root : Aiur.Circuit.Message F} {rows : List (Aiur.Circuit.WeightedRow F)} :
    c.checkMemo rom root rows = .ok () ↔
      root.channel ∈ entries ∧ c.system.checkMemo rom root rows = .ok () := by
  cases entry : q.checkEntry root.channel with
  | error e =>
      have absent : root.channel ∉ entries := by
        intro h
        have := q.checkEntry_iff.mpr h
        simp [entry] at this
      simp [Compiled.checkMemo, entry, absent, bind, Except.bind]
  | ok u =>
      cases u
      have selected := q.checkEntry_iff.mp entry
      cases h : c.system.checkMemo rom root rows <;>
        simp [Compiled.checkMemo, entry, selected, h, Except.mapError, bind, Except.bind]

theorem Specialized.core_heap_complete (q : Specialized s entries)
    (selected : name ∈ entries) {system : Aiur.Circuit.System F}
    (compiled : Aiur.Circuit.compile q.program = .ok system)
    (evaluated : Engine.EvalFn s.coreWorld name args [] value heap) (encode : Nat → F)
    (distinct : ∀ i j, i < heap.length → j < heap.length → encode i = encode j → i = j) :
    Aiur.Circuit.EncodedEntryDerives system name (entryValues args) (value.mapAddress encode) := by
  have root := q.valid.2.2.2.2.2.2.2 name selected
  exact compiler_heap_complete compiled root.2.2 ((q.coreEvalFn_iff root.1).mp evaluated) encode distinct

theorem Specialized.core_run_complete [Fintype F] (q : Specialized s entries)
    (selected : name ∈ entries) {system : Aiur.Circuit.System F}
    (compiled : Aiur.Circuit.compile q.program = .ok system)
    {hints : s.CoreHintProvider}
    (executed : s.coreRun name args fuel hints = .ok (value, heap)) (capacity : heap.length ≤ Fintype.card F) :
    ∃ encode : Nat → F, Aiur.Circuit.EncodedEntryDerives system name (entryValues args) (value.mapAddress encode) := by
  obtain ⟨encode, distinct⟩ := heap_address_embedding heap capacity
  exact ⟨encode, q.core_heap_complete selected compiled (Source.coreRun_spec executed).2 encode distinct⟩

theorem Specialized.core_memo_run_complete [Fintype F] (q : Specialized s entries)
    (selected : name ∈ entries) {system : Aiur.Circuit.System F}
    (compiled : Aiur.Circuit.compile q.program = .ok system)
    {hints : s.CoreHintProvider}
    (executed : s.coreRun name args fuel hints = .ok (value, heap)) (capacity : heap.length ≤ Fintype.card F) :
    ∃ encode : Nat → F, Aiur.Circuit.EncodedMemoEntryDerives system name (entryValues args) (value.mapAddress encode) := by
  obtain ⟨encode, tree⟩ := q.core_run_complete selected compiled executed capacity
  exact ⟨encode, tree.memo⟩

theorem Specialized.core_heap_sound (q : Specialized s entries) (selected : name ∈ entries)
    {system : Aiur.Circuit.System F} (compiled : Aiur.Circuit.compile q.program = .ok system)
    {rom : WireROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (derived : Aiur.Circuit.CircuitEvaluates system rom name wires output)
    (arguments : DecodesValues q.program.enums wires (entryValues args))
    (decoded : output.decode q.program.enums = some result) :
    ∃ value heap, Engine.EvalFn s.coreWorld name args [] value heap ∧
      Represents (rom.decode q.program.enums) heap value result := by
  have root := q.valid.2.2.2.2.2.2.2 name selected
  obtain ⟨value, heap, evaluated, related⟩ := compiler_heap_sound compiled valid root.2.2 derived arguments decoded
  exact ⟨value, heap, (q.coreEvalFn_iff root.1).mpr evaluated, related⟩

theorem Specialized.core_memo_acyclic_heap_sound (q : Specialized s entries) (selected : name ∈ entries)
    {system : Aiur.Circuit.System F} (compiled : Aiur.Circuit.compile q.program = .ok system)
    {rom : WireROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (graph : Aiur.Circuit.MemoDerivation system rom ⟨name, wires, output⟩) (acyclic : graph.Acyclic)
    (arguments : DecodesValues q.program.enums wires (entryValues args))
    (decoded : output.decode q.program.enums = some result) :
    ∃ value heap, Engine.EvalFn s.coreWorld name args [] value heap ∧
      Represents (rom.decode q.program.enums) heap value result :=
  q.core_heap_sound selected compiled valid (graph.derives_of_acyclic acyclic) arguments decoded

theorem Specialized.core_checker_run_complete [Fintype F] (q : Specialized s entries)
    (selected : name ∈ entries) {system : Aiur.Circuit.System F}
    (compiled : Aiur.Circuit.compile q.program = .ok system) (wellFormed : system.WellFormed)
    {hints : s.CoreHintProvider}
    (executed : s.coreRun name args fuel hints = .ok (value, heap)) (capacity : heap.length ≤ Fintype.card F) :
    ∃ (encode : Nat → F), ∃ wires output rom rows,
      DecodesValues system.enums wires (entryValues args) ∧
      output.decode system.enums = some (value.mapAddress encode) ∧
      system.check rom ⟨name, wires, output⟩ rows = .ok () := by
  obtain ⟨encode, wires, output, arguments, decoded, accepted⟩ := q.core_run_complete selected compiled executed capacity
  obtain ⟨rom, rows, checked⟩ := (system.check_entry_iff wellFormed).mpr accepted
  exact ⟨encode, wires, output, rom, rows, arguments, decoded, checked⟩

theorem Specialized.core_checkerMemo_run_complete [Fintype F] (q : Specialized s entries)
    (selected : name ∈ entries) {system : Aiur.Circuit.System F}
    (compiled : Aiur.Circuit.compile q.program = .ok system) (wellFormed : system.WellFormed)
    {hints : s.CoreHintProvider}
    (executed : s.coreRun name args fuel hints = .ok (value, heap)) (capacity : heap.length ≤ Fintype.card F) :
    ∃ (encode : Nat → F), ∃ wires output rom rows,
      DecodesValues system.enums wires (entryValues args) ∧
      output.decode system.enums = some (value.mapAddress encode) ∧
      system.checkMemo rom ⟨name, wires, output⟩ rows = .ok () := by
  obtain ⟨encode, wires, output, arguments, decoded, accepted⟩ := q.core_memo_run_complete selected compiled executed capacity
  obtain ⟨rom, rows, checked⟩ := (system.checkMemo_entry_iff wellFormed).mpr accepted
  exact ⟨encode, wires, output, rom, rows, arguments, decoded, checked⟩

theorem Specialized.core_checker_heap_sound (q : Specialized s entries) (selected : name ∈ entries)
    {system : Aiur.Circuit.System F} (compiled : Aiur.Circuit.compile q.program = .ok system)
    {rom : WireROM F} {args : List (SourceValue F)} {result : Value F}
    {wires : List (WireValue F)} {output : WireValue F} {rows : List (Aiur.Circuit.Row F)}
    (checked : system.check rom ⟨name, wires, output⟩ rows = .ok ())
    (arguments : DecodesValues q.program.enums wires (entryValues args))
    (decoded : output.decode q.program.enums = some result) :
    ∃ value heap, Engine.EvalFn s.coreWorld name args [] value heap ∧
      Represents (rom.decode q.program.enums) heap value result := by
  have root := q.valid.2.2.2.2.2.2.2 name selected
  obtain ⟨value, heap, evaluated, related⟩ := Aiur.checker_heap_sound compiled checked root.2.2 arguments decoded
  exact ⟨value, heap, (q.coreEvalFn_iff root.1).mpr evaluated, related⟩

end Aiur.Generic
