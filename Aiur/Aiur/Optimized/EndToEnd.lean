import Aiur.Optimized.Grouping.Plan
import Aiur.Optimized.Activation

/-!
Unified end-to-end compiler soundness from activated and grouped physical circuits
all the way back to the independent modular source evaluation predicate
`Modules.Prepared.EvalFn`.
-/

namespace Aiur

variable {F : Type} [Field F] [DecidableEq F]

/-- Conditional soundness for weighted memoized rows at the core `Program F` level. -/
theorem checkerMemo_acyclic_heap_sound {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system)
    {rom : WireROM F} {name : String} {args : List (SourceValue F)} {result : Value F}
    {wires : List (WireValue F)} {output : WireValue F} {rows : List (Circuit.WeightedRow F)}
    (checked : system.checkMemo rom ⟨name, wires, output⟩ rows = .ok ())
    (acyclic : (Classical.choice (system.checkMemo_sound checked)).Acyclic)
    (entry : checkEntry program name = .ok ())
    (arguments : DecodesValues program.enums wires (entryValues args))
    (decoded : output.decode program.enums = some result) :
    ∃ source heap, EvalFn program name args [] source heap ∧
      Represents (rom.decode program.enums) heap source result :=
  memo_acyclic_heap_sound compiled
    (Circuit.System.checkContext_iff.mp (Circuit.System.checkMemo_iff.mp checked).1).2.2.1
    entry (Classical.choice (system.checkMemo_sound checked)) acyclic arguments decoded

end Aiur

namespace Aiur.Optimized.Activation

open Circuit
variable {F : Type} [Field F] [DecidableEq F]

/-- An active row of the activation-padded chip `compile chip` satisfies the
padded chip's constraints and memory lookups with selector `1`. -/
def ActiveRule (chip : Chip F) (rom : WireROM F)
    (root : Message F) (premises : List (Message F)) : Prop :=
  ∃ row : Row F, row.chip = chip.name ∧ (compile chip).ValidRow rom row ∧
    row.assignment chip.numVars = 1 ∧ (compile chip).receive row = root ∧
    (compile chip).premises row = premises

/-- Active rows of `Activation.compile chip` have the exact same local rule as
`chip` itself. -/
theorem activeRule_iff (chip : Chip F) (formed : chip.wellFormed = true)
    (paddedFormed : (compile chip).wellFormed = true) (rom : WireROM F)
    (root : Message F) (premises : List (Message F)) :
    ActiveRule chip rom root premises ↔ chip.LocalRule rom root premises :=
  active_rule_iff chip formed paddedFormed rom root premises

end Aiur.Optimized.Activation

namespace Aiur.Optimized.Grouping

open Circuit
variable {F : Type} [Field F] [DecidableEq F]
variable {source : Circuit.System F} {id : String → Except String Nat}

/-- Every ungrouped single chip in the plan is well-formed both before and after
row-activation compilation. -/
def Plan.WellFormedActivation (plan : Plan source id) : Prop :=
  ∀ c ∈ plan.singles, c.wellFormed = true ∧ (Activation.compile c).wellFormed = true

instance (plan : Plan source id) : Decidable plan.WellFormedActivation := by
  unfold Plan.WellFormedActivation
  infer_instance

/-- Local rule of a grouped physical plan after applying `Activation.compile` to
every ungrouped single chip (grouped chips already include activation in
`Layout.RowRule`). -/
def Plan.ActivatedLocalRule (plan : Plan source id) (rom : WireROM F)
    (root : Message F) (premises : List (Message F)) : Prop :=
  (∃ c ∈ plan.singles, Activation.ActiveRule c rom root premises) ∨
    ∃ p ∈ plan.groups, p.checked.layout.RowRule rom root premises

theorem Plan.activatedLocalRule_iff (plan : Plan source id)
    (activated : plan.WellFormedActivation) (rom : WireROM F)
    (root : Message F) (premises : List (Message F)) :
    plan.ActivatedLocalRule rom root premises ↔ plan.LocalRule rom root premises := by
  constructor
  · rintro (⟨c, hc, rule⟩ | ⟨p, hp, rule⟩)
    · have wf := activated c hc
      exact Or.inl ⟨c, hc, (Activation.activeRule_iff c wf.1 wf.2 rom root premises).mp rule⟩
    · exact Or.inr ⟨p, hp, rule⟩
  · rintro (⟨c, hc, rule⟩ | ⟨p, hp, rule⟩)
    · have wf := activated c hc
      exact Or.inl ⟨c, hc, (Activation.activeRule_iff c wf.1 wf.2 rom root premises).mpr rule⟩
    · exact Or.inr ⟨p, hp, rule⟩

/-- Finite derivation tree over the activated grouped physical system. -/
inductive Plan.ActivatedDerives (plan : Plan source id) (rom : WireROM F) : Message F → Prop
  | node {root premises} (rule : plan.ActivatedLocalRule rom root premises)
      (children : ∀ message ∈ premises, plan.ActivatedDerives rom message) :
      plan.ActivatedDerives rom root
  | table {message} (member : source.MapClaim message) : plan.ActivatedDerives rom message

theorem Plan.activatedDerives_sound_plan (plan : Plan source id)
    (activated : plan.WellFormedActivation) {rom : WireROM F} {root : Message F}
    (derived : plan.ActivatedDerives rom root) : plan.Derives rom root := by
  induction derived with
  | node rule _ ih =>
      exact .node ((plan.activatedLocalRule_iff activated _ _ _).mp rule) ih
  | table member => exact .table member

theorem Plan.activatedDerives_complete_plan (plan : Plan source id)
    (activated : plan.WellFormedActivation) {rom : WireROM F} {root : Message F}
    (derived : plan.Derives rom root) : plan.ActivatedDerives rom root := by
  induction derived with
  | node rule _ ih =>
      exact .node ((plan.activatedLocalRule_iff activated _ _ _).mpr rule) ih
  | table member => exact .table member

theorem Plan.activatedDerives_iff (plan : Plan source id)
    (activated : plan.WellFormedActivation) {rom : WireROM F} {root : Message F} :
    plan.ActivatedDerives rom root ↔ plan.Derives rom root :=
  ⟨plan.activatedDerives_sound_plan activated, plan.activatedDerives_complete_plan activated⟩

theorem Plan.activatedDerives_sound (plan : Plan source id)
    (activated : plan.WellFormedActivation) {rom : WireROM F} {root : Message F}
    (derived : plan.ActivatedDerives rom root) : Circuit.Derives source rom root :=
  plan.derives_sound (plan.activatedDerives_sound_plan activated derived)

end Aiur.Optimized.Grouping

namespace Aiur.Optimized.Physical

open Circuit
variable {F : Type} [Field F] [DecidableEq F]
variable {id : String → Except String Nat}

theorem Prepared.grouped_activated_native_heap_sound {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Prepared compiled.artifact) (plan : Grouping.Plan prepared.system id)
    (activated : plan.WellFormedActivation)
    {name : String} (entry : name ∈ entries) {rom : WidthROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    (derived : plan.ActivatedDerives (Erasure.rawROM rom) (Erasure.message compiled.system ⟨name, wires, output⟩))
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result) :
    ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
      Represents ((Erasure.typedROM compiled.system rom).decode specialized.program.enums) heap value result :=
  prepared.grouped_native_heap_sound compiled plan entry valid signed
    (plan.activatedDerives_sound_plan activated derived) arguments decoded

end Aiur.Optimized.Physical

namespace Aiur.Optimized

open Circuit
variable {F : Type} [Field F] [DecidableEq F]
variable {id : String → Except String Nat}

theorem ModulesArtifact.physical_heap_sound {program : Modules.Program F}
    {prepared : Modules.Prepared program} (compiled : ModulesArtifact prepared)
    (physical : Physical.Prepared compiled.circuit.artifact)
    {external : String} {entry : Modules.Selection program prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {rom : WidthROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (derived : Derives physical.system (Erasure.rawROM rom)
      (Erasure.message compiled.circuit.system ⟨entry.resolved.name, wires, output⟩))
    (arguments : DecodesValues compiled.specialized.program.enums wires (entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result) :
    ∃ value heap, prepared.EvalFn external args value heap ∧
      Represents ((Erasure.typedROM compiled.circuit.system rom).decode compiled.specialized.program.enums)
        heap value result := by
  obtain ⟨value, heap, evaluated, related⟩ :=
    physical.native_heap_sound compiled.circuit (Modules.Prepared.entry_mem selected)
      valid signed derived arguments decoded
  exact ⟨value, heap, ⟨entry, selected, evaluated⟩, related⟩

theorem ModulesArtifact.grouped_heap_sound {program : Modules.Program F}
    {prepared : Modules.Prepared program} (compiled : ModulesArtifact prepared)
    (physical : Physical.Prepared compiled.circuit.artifact)
    (plan : Grouping.Plan physical.system id)
    {external : String} {entry : Modules.Selection program prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {rom : WidthROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (derived : plan.Derives (Erasure.rawROM rom)
      (Erasure.message compiled.circuit.system ⟨entry.resolved.name, wires, output⟩))
    (arguments : DecodesValues compiled.specialized.program.enums wires (entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result) :
    ∃ value heap, prepared.EvalFn external args value heap ∧
      Represents ((Erasure.typedROM compiled.circuit.system rom).decode compiled.specialized.program.enums)
        heap value result :=
  compiled.physical_heap_sound physical selected valid signed (plan.derives_sound derived) arguments decoded

theorem ModulesArtifact.grouped_activated_heap_sound {program : Modules.Program F}
    {prepared : Modules.Prepared program} (compiled : ModulesArtifact prepared)
    (physical : Physical.Prepared compiled.circuit.artifact)
    (plan : Grouping.Plan physical.system id)
    (activated : plan.WellFormedActivation)
    {external : String} {entry : Modules.Selection program prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {rom : WidthROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (derived : plan.ActivatedDerives (Erasure.rawROM rom)
      (Erasure.message compiled.circuit.system ⟨entry.resolved.name, wires, output⟩))
    (arguments : DecodesValues compiled.specialized.program.enums wires (entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result) :
    ∃ value heap, prepared.EvalFn external args value heap ∧
      Represents ((Erasure.typedROM compiled.circuit.system rom).decode compiled.specialized.program.enums)
        heap value result :=
  compiled.grouped_heap_sound physical plan selected valid signed
    (plan.activatedDerives_sound_plan activated derived) arguments decoded

end Aiur.Optimized

namespace Aiur.Modules

open Circuit Optimized
variable {F : Type} [Field F] [DecidableEq F]
variable {id : String → Except String Nat}

/-- End-to-end soundness from a physical type-erased circuit derivation to
`Modules.Prepared.EvalFn`. -/
theorem Prepared.physical_heap_sound {program : Modules.Program F}
    (prepared : Modules.Prepared program) (compiled : ModulesArtifact prepared)
    (physical : Physical.Prepared compiled.circuit.artifact)
    {external : String} {entry : Modules.Selection program prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {rom : WidthROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (derived : Derives physical.system (Erasure.rawROM rom)
      (Erasure.message compiled.circuit.system ⟨entry.resolved.name, wires, output⟩))
    (arguments : DecodesValues compiled.specialized.program.enums wires (entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result) :
    ∃ value heap, prepared.EvalFn external args value heap ∧
      Represents ((Erasure.typedROM compiled.circuit.system rom).decode compiled.specialized.program.enums)
        heap value result :=
  compiled.physical_heap_sound physical selected valid signed derived arguments decoded

/-- End-to-end soundness from a grouped physical circuit derivation to
`Modules.Prepared.EvalFn`. -/
theorem Prepared.grouped_heap_sound {program : Modules.Program F}
    (prepared : Modules.Prepared program) (compiled : ModulesArtifact prepared)
    (physical : Physical.Prepared compiled.circuit.artifact)
    (plan : Grouping.Plan physical.system id)
    {external : String} {entry : Modules.Selection program prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {rom : WidthROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (derived : plan.Derives (Erasure.rawROM rom)
      (Erasure.message compiled.circuit.system ⟨entry.resolved.name, wires, output⟩))
    (arguments : DecodesValues compiled.specialized.program.enums wires (entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result) :
    ∃ value heap, prepared.EvalFn external args value heap ∧
      Represents ((Erasure.typedROM compiled.circuit.system rom).decode compiled.specialized.program.enums)
        heap value result :=
  compiled.grouped_heap_sound physical plan selected valid signed derived arguments decoded

/-- End-to-end soundness from an activated grouped physical circuit derivation to
`Modules.Prepared.EvalFn`. -/
theorem Prepared.grouped_activated_heap_sound {program : Modules.Program F}
    (prepared : Modules.Prepared program) (compiled : ModulesArtifact prepared)
    (physical : Physical.Prepared compiled.circuit.artifact)
    (plan : Grouping.Plan physical.system id)
    (activated : plan.WellFormedActivation)
    {external : String} {entry : Modules.Selection program prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {rom : WidthROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (derived : plan.ActivatedDerives (Erasure.rawROM rom)
      (Erasure.message compiled.circuit.system ⟨entry.resolved.name, wires, output⟩))
    (arguments : DecodesValues compiled.specialized.program.enums wires (entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result) :
    ∃ value heap, prepared.EvalFn external args value heap ∧
      Represents ((Erasure.typedROM compiled.circuit.system rom).decode compiled.specialized.program.enums)
        heap value result :=
  compiled.grouped_activated_heap_sound physical plan activated selected valid signed derived arguments decoded

end Aiur.Modules
