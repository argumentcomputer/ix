import Aiur.Optimized.Grouping.Compile
import Aiur.Optimized.Physical

namespace Aiur.Optimized.Grouping
open Circuit
variable {F : Type} [Field F] [DecidableEq F]
variable {id : String → Except String Nat}

structure Packed (F : Type) [Field F] [DecidableEq F] (id : String → Except String Nat) where
  sources : List (Chip F)
  checked : Checked sources id

/-- The exporter certifies the entire partition, including chips that retain
their original physical layout. No source member may be dropped or replaced. -/
def PlanCertificate (source : Circuit.System F) (singles : List (Chip F))
    (groups : List (Packed F id)) : Prop :=
  (∀ c ∈ singles, source.findChip? c.name = some c) ∧
  (∀ p ∈ groups, ∀ c ∈ p.sources, source.findChip? c.name = some c) ∧
  (∀ c ∈ source.chips, c ∈ singles ∨ ∃ p ∈ groups, c ∈ p.sources)

instance (source : Circuit.System F) (singles : List (Chip F))
    (groups : List (Packed F id)) : Decidable (PlanCertificate source singles groups) := by
  letI (c : Chip F) (cs : List (Chip F)) : Decidable (c ∈ cs) :=
    decidable_of_iff (∃ d ∈ cs, d = c) (by simp)
  unfold PlanCertificate
  infer_instance

structure Plan (source : Circuit.System F) (id : String → Except String Nat) where
  singles : List (Chip F)
  groups : List (Packed F id)
  certificate : PlanCertificate source singles groups

def preparePlan (source : Circuit.System F) (id : String → Except String Nat)
    (groups : List (Packed F id)) : Except String (Plan source id) := do
  let names := groups.flatMap fun p => p.sources.map Chip.name
  let singles := source.chips.filter fun c => !names.contains c.name
  if h : PlanCertificate source singles groups then return ⟨singles, groups, h⟩
  else throw "grouping partition does not preserve the physical source circuits"

variable {source : Circuit.System F}

def Plan.LocalRule (plan : Plan source id) (rom : WireROM F)
    (root : Message F) (premises : List (Message F)) : Prop :=
  (∃ c ∈ plan.singles, c.LocalRule rom root premises) ∨
    ∃ p ∈ plan.groups, p.checked.layout.RowRule rom root premises

theorem Plan.localRule_iff (plan : Plan source id) (rom : WireROM F)
    (root : Message F) (premises : List (Message F)) :
    plan.LocalRule rom root premises ↔
      ∃ c, source.findChip? c.name = some c ∧ c.LocalRule rom root premises := by
  constructor
  · rintro (⟨c, hc, rule⟩ | ⟨p, hp, rule⟩)
    · exact ⟨c, plan.certificate.1 c hc, rule⟩
    · obtain ⟨c, hc, rule⟩ := (p.checked.localRule_iff rom root premises).mp rule
      exact ⟨c, plan.certificate.2.1 p hp c hc, rule⟩
  · rintro ⟨c, hc, rule⟩
    rcases plan.certificate.2.2 c (List.mem_of_find?_eq_some hc) with single | ⟨p, hp, grouped⟩
    · exact Or.inl ⟨c, single, rule⟩
    · exact Or.inr ⟨p, hp, (p.checked.localRule_iff rom root premises).mpr ⟨c, grouped, rule⟩⟩

/-- The same finite-derivation contract used by the compiler. Each group rule
reads its actual emitted equations and shared call/memory message words. -/
inductive Plan.Derives (plan : Plan source id) (rom : WireROM F) : Message F → Prop
  | node {root premises} (rule : plan.LocalRule rom root premises)
      (children : ∀ message ∈ premises, plan.Derives rom message) : plan.Derives rom root
  | table {message} (member : source.MapClaim message) : plan.Derives rom message

theorem Plan.derives_sound (plan : Plan source id) {rom : WireROM F} {root : Message F}
    (derived : plan.Derives rom root) : Circuit.Derives source rom root := by
  induction derived with
  | node rule _ ih =>
      obtain ⟨c, hc, row, chipEq, valid, rootEq, premisesEq⟩ :=
        (plan.localRule_iff _ _ _).mp rule
      have found : source.findChip? row.chip = some c := by simpa [chipEq] using hc
      obtain ⟨children⟩ := (derivations_nonempty_iff (messages := c.premises row)).mpr
        (by simpa only [premisesEq] using ih)
      rw [← rootEq]
      exact ⟨.node c row found valid children⟩
  | table member => exact ⟨.table member⟩

theorem Plan.derives_complete (plan : Plan source id) {rom : WireROM F} {root : Message F}
    (derived : Circuit.Derives source rom root) : plan.Derives rom root := by
  obtain ⟨tree⟩ := derived
  induction tree using Derivation.rec
    (motive_2 := fun messages _ => ∀ message ∈ messages, plan.Derives rom message) with
  | node c row found valid children ih =>
      apply Plan.Derives.node _ ih
      apply (plan.localRule_iff _ _ _).mpr
      have name := System.findChip_name found
      exact ⟨c, by simpa [name] using found, row, name.symm, valid, rfl, rfl⟩
  | table member => exact .table member
  | nil => simp_all
  | cons _ _ head tail =>
      rename_i message member
      rcases List.mem_cons.mp member with rfl | member
      · exact head
      · exact tail message member

theorem Plan.derives_iff (plan : Plan source id) {rom : WireROM F} {root : Message F} :
    plan.Derives rom root ↔ Circuit.Derives source rom root :=
  ⟨plan.derives_sound, plan.derives_complete⟩

end Aiur.Optimized.Grouping

namespace Aiur.Optimized.Physical
open Circuit
variable {F : Type} [Field F] [DecidableEq F]
variable {id : String → Except String Nat}

/-- Grouping composes all the way to independent source evaluation. There are
no selected-member or source-memory side conditions: those are recovered from
the certified grouped row rule. The existing ROM and public-schema hypotheses
are exactly the hypotheses of `Prepared.native_heap_sound`. -/
theorem Prepared.grouped_native_heap_sound {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : GenericArtifact specialized)
    (prepared : Prepared compiled.artifact) (plan : Grouping.Plan prepared.system id)
    {name : String} (entry : name ∈ entries) {rom : WidthROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
    (signed : Erasure.Signed compiled.system ⟨name, wires, output⟩)
    (derived : plan.Derives (Erasure.rawROM rom) (Erasure.message compiled.system ⟨name, wires, output⟩))
    (arguments : DecodesValues specialized.program.enums wires (entryValues args))
    (decoded : output.decode specialized.program.enums = some result) :
    ∃ value heap, Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
      Represents ((Erasure.typedROM compiled.system rom).decode specialized.program.enums) heap value result :=
  prepared.native_heap_sound compiled entry valid signed (plan.derives_sound derived) arguments decoded

end Aiur.Optimized.Physical
