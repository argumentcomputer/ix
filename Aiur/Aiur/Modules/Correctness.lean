import Aiur.Modules.Link
import Aiur.Generic.NativeCircuit

namespace Aiur.Modules
variable {F : Type} [Field F] [DecidableEq F] {program : Program F}

def Prepared.EvalFn (p : Prepared program) (name : String) (args : List (SourceValue F))
    (value : SourceValue F) (heap : Heap F) : Prop :=
  ∃ entry, p.find? name = some entry ∧
    Generic.SourceSemantics.EvalFn p.environment.source.world entry.resolved.name args [] value heap

theorem Prepared.run_heap_spec {p : Prepared program} {hints : p.environment.source.HintProvider}
    (executed : p.run name args fuel hints = .ok (value,heap)) : p.EvalFn name args value heap := by
  cases selected : p.find? name with
  | none => simp [Prepared.run,selected] at executed
  | some entry =>
      simp only [Prepared.run,selected] at executed
      exact ⟨entry,selected,(Generic.Source.run_spec executed).2⟩

omit [Field F] in
theorem Prepared.entry_mem {p : Prepared program}
    {entry : Selection program p.environment.assembly.instances}
    (selected : p.find? name = some entry) : entry.resolved.name ∈ p.entries := by
  have present := List.mem_of_find?_eq_some selected
  exact List.mem_map.mpr ⟨entry,present,rfl⟩

structure Compiled (p : Prepared program) where
  specialized : Generic.Specialized p.environment.source p.entries
  circuit : Generic.Compiled specialized

def Prepared.compile (p : Prepared program) : Except String (Compiled p) := do
  let specialized ← Generic.specialize p.environment.source p.entries
  return ⟨specialized, ← specialized.compile⟩

def Compiled.check {p : Prepared program} (c : Compiled p) (rom : WireROM F)
    (name : String) (args : List (WireValue F)) (result : WireValue F)
    (rows : List (Circuit.Row F)) : Except String Unit := do
  let some entry := p.find? name | throw s!"unselected entrypoint '{name}'"
  c.circuit.check rom ⟨entry.resolved.name,args,result⟩ rows

def Compiled.checkMemo {p : Prepared program} (c : Compiled p) (rom : WireROM F)
    (name : String) (args : List (WireValue F)) (result : WireValue F)
    (rows : List (Circuit.WeightedRow F)) : Except String Unit := do
  let some entry := p.find? name | throw s!"unselected entrypoint '{name}'"
  c.circuit.checkMemo rom ⟨entry.resolved.name,args,result⟩ rows

/-- Completeness from the module-denoted native environment to integer rows.
Module aliases only rename the external entrypoint; they introduce no wrapper. -/
theorem Compiled.check_complete [Fintype F] {p : Prepared program} (c : Compiled p)
    (wellFormed : c.circuit.system.WellFormed)
    (evaluated : p.EvalFn name args value heap) (capacity : heap.length ≤ Fintype.card F) :
    ∃ (encode : Nat → F), ∃ wires output rom rows,
      DecodesValues c.circuit.system.enums wires (entryValues args) ∧
      output.decode c.circuit.system.enums = some (value.mapAddress encode) ∧
      c.check rom name wires output rows = .ok () := by
  obtain ⟨entry,selected,evaluated⟩ := evaluated
  obtain ⟨encode,wires,output,rom,rows,arguments,decoded,checked⟩ :=
    c.circuit.checker_heap_complete (Prepared.entry_mem selected) wellFormed evaluated capacity
  refine ⟨encode,wires,output,rom,rows,arguments,decoded,?_⟩
  simp only [Compiled.check,selected]
  exact c.circuit.check_iff.mpr ⟨Prepared.entry_mem selected,checked⟩

theorem Compiled.checkMemo_complete [Fintype F] {p : Prepared program} (c : Compiled p)
    (wellFormed : c.circuit.system.WellFormed)
    (evaluated : p.EvalFn name args value heap) (capacity : heap.length ≤ Fintype.card F) :
    ∃ (encode : Nat → F), ∃ wires output rom rows,
      DecodesValues c.circuit.system.enums wires (entryValues args) ∧
      output.decode c.circuit.system.enums = some (value.mapAddress encode) ∧
      c.checkMemo rom name wires output rows = .ok () := by
  obtain ⟨entry,selected,evaluated⟩ := evaluated
  obtain ⟨encode,wires,output,rom,rows,arguments,decoded,checked⟩ :=
    c.circuit.checkerMemo_heap_complete (Prepared.entry_mem selected) wellFormed evaluated capacity
  refine ⟨encode,wires,output,rom,rows,arguments,decoded,?_⟩
  simp only [Compiled.checkMemo,selected]
  exact c.circuit.checkMemo_iff.mpr ⟨Prepared.entry_mem selected,checked⟩

theorem Compiled.run_complete [Fintype F] {p : Prepared program} (c : Compiled p)
    (wellFormed : c.circuit.system.WellFormed) {hints : p.environment.source.HintProvider}
    (executed : p.run name args fuel hints = .ok (value,heap)) (capacity : heap.length ≤ Fintype.card F) :
    ∃ (encode : Nat → F), ∃ wires output rom rows,
      DecodesValues c.circuit.system.enums wires (entryValues args) ∧
      output.decode c.circuit.system.enums = some (value.mapAddress encode) ∧
      c.check rom name wires output rows = .ok () :=
  c.check_complete wellFormed (Prepared.run_heap_spec executed) capacity

theorem Compiled.runMemo_complete [Fintype F] {p : Prepared program} (c : Compiled p)
    (wellFormed : c.circuit.system.WellFormed) {hints : p.environment.source.HintProvider}
    (executed : p.run name args fuel hints = .ok (value,heap)) (capacity : heap.length ≤ Fintype.card F) :
    ∃ (encode : Nat → F), ∃ wires output rom rows,
      DecodesValues c.circuit.system.enums wires (entryValues args) ∧
      output.decode c.circuit.system.enums = some (value.mapAddress encode) ∧
      c.checkMemo rom name wires output rows = .ok () :=
  c.checkMemo_complete wellFormed (Prepared.run_heap_spec executed) capacity

theorem Compiled.check_sound {p : Prepared program} (c : Compiled p)
    {rom : WireROM F} {args : List (SourceValue F)} {result : Value F}
    {wires : List (WireValue F)} {output : WireValue F} {rows : List (Circuit.Row F)}
    (checked : c.check rom name wires output rows = .ok ())
    (arguments : DecodesValues c.specialized.program.enums wires (entryValues args))
    (decoded : output.decode c.specialized.program.enums = some result) :
    ∃ value heap, p.EvalCall name args value ∧
      Represents (rom.decode c.specialized.program.enums) heap value result := by
  cases selected : p.find? name with
  | none => simp [Compiled.check,selected] at checked
  | some entry =>
      simp only [Compiled.check,selected] at checked
      obtain ⟨value,heap,evaluated,related⟩ := c.circuit.check_sound checked arguments decoded
      exact ⟨value,heap,⟨entry,selected,evaluated⟩,related⟩

/-- The weighted checker permits cyclic justification. Its soundness remains
conditional on acyclicity of the extracted support graph, never on totality. -/
theorem Compiled.checkerMemo_acyclic_sound {p : Prepared program} (c : Compiled p)
    {entry : Selection program p.environment.assembly.instances}
    (selected : p.find? name = some entry)
    {rom : WireROM F} {args : List (SourceValue F)} {result : Value F}
    {wires : List (WireValue F)} {output : WireValue F} {rows : List (Circuit.WeightedRow F)}
    (checked : c.circuit.system.checkMemo rom ⟨entry.resolved.name,wires,output⟩ rows = .ok ())
    (acyclic : (Classical.choice (c.circuit.system.checkMemo_sound checked)).Acyclic)
    (arguments : DecodesValues c.specialized.program.enums wires (entryValues args))
    (decoded : output.decode c.specialized.program.enums = some result) :
    ∃ value heap, p.EvalCall name args value ∧
      Represents (rom.decode c.specialized.program.enums) heap value result := by
  obtain ⟨value,heap,evaluated,related⟩ :=
    c.circuit.checkerMemo_acyclic_heap_sound (Prepared.entry_mem selected)
      checked acyclic arguments decoded
  have checkedEntry := (c.specialized.valid.2.2.2.2.2.2.2 _ (Prepared.entry_mem selected)).2.1
  exact ⟨value,heap,⟨entry,selected,checkedEntry,heap,evaluated⟩,related⟩

theorem Compiled.checkMemo_rows {p : Prepared program} (c : Compiled p)
    {entry : Selection program p.environment.assembly.instances}
    (selected : p.find? name = some entry)
    (checked : c.checkMemo rom name wires output rows = .ok ()) :
    c.circuit.system.checkMemo rom ⟨entry.resolved.name,wires,output⟩ rows = .ok () := by
  simp only [Compiled.checkMemo,selected] at checked
  exact (c.circuit.checkMemo_iff.mp checked).2

theorem Compiled.checkMemo_acyclic_sound {p : Prepared program} (c : Compiled p)
    {entry : Selection program p.environment.assembly.instances}
    (selected : p.find? name = some entry)
    {rom : WireROM F} {args : List (SourceValue F)} {result : Value F}
    {wires : List (WireValue F)} {output : WireValue F} {rows : List (Circuit.WeightedRow F)}
    (checked : c.checkMemo rom name wires output rows = .ok ())
    (acyclic : (Classical.choice (c.circuit.system.checkMemo_sound (c.checkMemo_rows selected checked))).Acyclic)
    (arguments : DecodesValues c.specialized.program.enums wires (entryValues args))
    (decoded : output.decode c.specialized.program.enums = some result) :
    ∃ value heap, p.EvalCall name args value ∧
      Represents (rom.decode c.specialized.program.enums) heap value result :=
  c.checkerMemo_acyclic_sound selected (c.checkMemo_rows selected checked) acyclic arguments decoded

omit [Field F] in
/-- Every source name exposed by a compiled root has a declarative module
resolution, with its target included in the assembled environment. -/
theorem Prepared.selected_denotes {p : Prepared program}
    {entry : Selection program p.environment.assembly.instances}
    (_selected : p.find? name = some entry) :
    NameDenotes program (.mk "" []) [] entry.external entry.resolved.target entry.resolved.name ∧
      p.environment.assembly.instances.contains entry.resolved.target = true :=
  ⟨entry.resolved.denotes,entry.resolved.closed⟩

end Aiur.Modules
