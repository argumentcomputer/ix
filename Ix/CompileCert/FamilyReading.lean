import Ix.CompileCert.FamilyAssembly

/-! Whole-record family dispatch and composition of collection, source
consistency checks and complete reader assembly. Original-domain dischargers
and generator correctness/progress remain separate obligations. -/

namespace Ix.CompileCert.FamilyReading

open Ix Kernel.Reader
open FamilyReader (CtorRow RecRow)

def FamilyOnly (members : Array Ixon.MutConst) : Prop :=
  ∀ member ∈ members, match member with | .defn _ => False | _ => True

theorem selected_inductive (shape : BlockShape) (members : Array Ixon.MutConst)
    (entry : Nat × Ixon.Inductive) (present : entry ∈ FamilyCollection.selected shape members) :
    ∃ (index : Nat) (value : Ixon.Inductive), members[index]? = some (.indc value) := by
  obtain ⟨index, _, found⟩ := Array.mem_filterMap.mp present
  cases value : members[index]? with
  | none => simp [value] at found
  | some member =>
    cases member with
    | defn definition => simp [value] at found
    | recr recursor => simp [value] at found
    | indc ind => exact ⟨index, ind, value⟩

theorem has_inductive (shape : BlockShape) (members : Array Ixon.MutConst)
    (entry : Nat × Ixon.Inductive) (present : entry ∈ FamilyCollection.selected shape members) :
    members.any (fun | .indc _ => true | _ => false) = true := by
  obtain ⟨index, value, found⟩ := selected_inductive shape members entry present
  obtain ⟨inside, same⟩ := Array.getElem?_eq_some_iff.mp found
  apply Array.any_eq_true.mpr
  exact ⟨index, inside, by rw [same]⟩

theorem no_definitions (members : Array Ixon.MutConst) (family : FamilyOnly members) :
    members.any (fun | .defn _ => true | _ => false) = false := by
  apply Array.any_eq_false.mpr
  intro index inside
  have valid := family members[index] (Array.getElem_mem inside)
  cases found : members[index] <;> simp_all

/-- The real top-level reader selects the family branch from the indexed
member evidence and absence of definition members; no separate branch-success
premise is needed. -/
theorem record_eq (reader : Ctx) (state : State) (owner : Address) (constant : Ixon.Constant)
    (members : Array Ixon.MutConst) (shape : BlockShape) (entry : Nat × Ixon.Inductive)
    (kind : constant.info = .muts members) (family : FamilyOnly members)
    (present : entry ∈ FamilyCollection.selected shape members) :
    readRecord reader state owner constant = readInductive reader state owner constant members := by
  have hasInd := has_inductive shape members entry present
  have noDef := no_definitions members family
  simp only [readRecord, kind]
  split
  · split
    · rename_i hasDef
      change (members.any (fun | .defn _ => true | _ => false)) = true at hasDef
      rw [noDef] at hasDef
      cases hasDef
    · rfl
  · rename_i absent
    change ¬(members.any (fun | .indc _ => true | _ => false)) = true at absent
    exact False.elim (absent hasInd)

structure Collected (reader : Ctx) (owner : Address) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (sources : Array (Nat × Ind)) (inputs : Array FamilyRecursors.Input) where
  types : Array CVal
  groups : List (List CtorRow)
  recursors : Array RecRow
  typeMeanings : List.Forall₂ (FamilyTypes.TypeMeaning reader owner names params) sources.toList types.toList
  ctorMeanings : List.Forall₂ (FamilyConstructors.GroupMeaning reader owner names params) sources.toList groups
  recMeanings : List.Forall₂ (FamilyRecursors.RowMeaning reader params names) inputs.toList recursors.toList

def Collected.assembly {reader owner names params sources inputs}
    (collected : Collected reader owner names params sources inputs)
    (nPd : Nat) (targets : Array (Nat × Ixon.Inductive)) : FamilyAssembly.Assembly :=
  FamilyAssembly.prepare nPd collected.types targets collected.groups.flatten.toArray
    (collected.groups.map fun rows => rows.map (·.1.name)).toArray collected.recursors

/-- Concrete source signature/K conditions for the collected rows. This
condition does not assert reader success or successful model generation. -/
def Collected.Consistent {reader owner names params sources inputs}
    (collected : Collected reader owner names params sources inputs) (nPd : Nat) : Prop :=
  FamilySourceChecks.sourceNested sources inputs = 0 → ∀ input ∈ inputs,
    FamilySourceChecks.SourceRowOK reader owner nPd sources
      (FamilyConsistency.expectedK collected.types collected.groups.flatten.toArray
        (collected.groups.map fun rows => rows.map (·.1.name)).toArray) input

theorem Collected.finish_run {reader owner names params sources inputs}
    (collected : Collected reader owner names params sources inputs) (state : State)
    (nPd : Nat) (targets : Array (Nat × Ixon.Inductive)) (valid : collected.Consistent nPd) :
    FamilyReader.finish state nPd collected.types targets collected.groups.flatten.toArray
      (collected.groups.map fun rows => rows.map (·.1.name)).toArray collected.recursors =
      (collected.assembly nPd targets).run state := by
  rw [FamilySourceChecks.finish_from_source reader owner names params state nPd sources collected.types targets
    collected.groups inputs collected.recursors collected.typeMeanings collected.ctorMeanings collected.recMeanings valid,
    FamilyAssembly.assemble_run]
  rfl

theorem Collected.finish_plain {reader owner names params sources inputs}
    (collected : Collected reader owner names params sources inputs) (state : State)
    (nPd : Nat) (targets : Array (Nat × Ixon.Inductive)) (valid : collected.Consistent nPd)
    (small : sources.size ≤ 1) (plain : FamilySourceChecks.sourceNested sources inputs = 0) :
    FamilyReader.finish state nPd collected.types targets collected.groups.flatten.toArray
      (collected.groups.map fun rows => rows.map (·.1.name)).toArray collected.recursors =
      .ok ((collected.assembly nPd targets).result []) :=
  FamilyAssembly.finish_plain_from_source reader owner names params state nPd sources collected.types targets
    collected.groups inputs collected.recursors collected.typeMeanings collected.ctorMeanings collected.recMeanings
    small plain (valid plain)

theorem Collected.model_required {reader owner names params sources inputs}
    (collected : Collected reader owner names params sources inputs) (member : MemberReader)
    (nPd : Nat) (targets : Array (Nat × Ixon.Inductive))
    (payloads : List.Forall₂ (FamilyTypes.Paired member names params) sources.toList targets.toList)
    (needed : 1 < sources.size ∨ (0 < sources.size ∧ 0 < FamilySourceChecks.sourceNested sources inputs)) :
    Kernel.Frontend.InModel.wants (collected.assembly nPd targets).model = true :=
  FamilyAssembly.prepare_required_from_source reader owner names params member nPd sources collected.types targets
    collected.groups inputs collected.recursors collected.typeMeanings payloads collected.ctorMeanings collected.recMeanings needed

theorem Collected.finish_model {reader owner names params sources inputs}
    (collected : Collected reader owner names params sources inputs) (member : MemberReader) (state : State)
    (nPd : Nat) (targets : Array (Nat × Ixon.Inductive))
    (payloads : List.Forall₂ (FamilyTypes.Paired member names params) sources.toList targets.toList)
    (valid : collected.Consistent nPd)
    (needed : 1 < sources.size ∨ (0 < sources.size ∧ 0 < FamilySourceChecks.sourceNested sources inputs)) :
    FamilyReader.finish state nPd collected.types targets collected.groups.flatten.toArray
      (collected.groups.map fun rows => rows.map (·.1.name)).toArray collected.recursors =
      match Kernel.Frontend.InModel.generate ((collected.assembly nPd targets).context state) (collected.assembly nPd targets).model with
      | .error reason => declined s!"in-process model of {(collected.assembly nPd targets).diagnosticName}: {reason}"
      | .ok generated => .ok ((collected.assembly nPd targets).result generated) := by
  rw [collected.finish_run state nPd targets valid]
  simp only [FamilyAssembly.Assembly.run, collected.model_required member nPd targets payloads needed, ↓reduceIte]
  rfl

/-- Produce a source-related collection from the actual `readRecord` path.
The returned equation retains finalization until its concrete source
conditions have been discharged. -/
theorem collect_record (reader : Ctx) (state : State) (owner : Address) (constant : Ixon.Constant)
    (members : Array Ixon.MutConst) (shape : BlockShape)
    (sources : Array (Nat × Ind)) (targets : Array (Nat × Ixon.Inductive))
    (firstIndex : Nat) (first : Ixon.Inductive) (names : Name → Kernel.Name → Prop)
    (recursors : Array FamilyRecursors.Input)
    (kind : constant.info = .muts members) (family : FamilyOnly members)
    (indexed : reader.index.blocks[owner]? = some shape)
    (selection : FamilyCollection.selected shape members = targets)
    (coverage : targets.size = shape.order.size) (firstFound : targets[0]? = some (firstIndex, first))
    (related : List.Forall₂
      (FamilyTypes.Paired (FamilyCollection.memberReader reader owner constant members targets first) names
        (FamilyCollection.blockParams reader owner targets first)) sources.toList targets.toList)
    (safe : ∀ source ∈ sources, source.2.isUnsafe = false)
    (common : ∀ source ∈ sources, source.2.numParams = first.params.toNat)
    (constructors : ∀ source ∈ sources, FamilyConstructors.SourceReady first.params.toNat source.2)
    (recursorOrder : shape.recs = recursors.map FamilyRecursors.Input.ref)
    (recursorValid : ∀ input ∈ recursors,
      FamilyRecursors.Valid reader (FamilyCollection.blockParams reader owner targets first) names input) :
    ∃ collected : Collected reader owner names (FamilyCollection.blockParams reader owner targets first) sources recursors,
      readRecord reader state owner constant =
        FamilyReader.finish state first.params.toNat collected.types targets collected.groups.flatten.toArray
          (collected.groups.map fun rows => rows.map (·.1.name)).toArray collected.recursors := by
  have present : (firstIndex, first) ∈ FamilyCollection.selected shape members := by
    rw [selection]
    exact Array.mem_iff_getElem?.mpr ⟨0, firstFound⟩
  rw [record_eq reader state owner constant members shape (firstIndex, first) kind family present]
  obtain ⟨types, groups, rows, ran, typeMeanings, ctorMeanings, recMeanings⟩ :=
    FamilyCollection.collect reader state owner constant members shape sources targets firstIndex first names recursors
      indexed selection coverage firstFound related safe common constructors recursorOrder recursorValid
  exact ⟨⟨types, groups, rows, typeMeanings, ctorMeanings, recMeanings⟩, ran⟩

/-- Whole-record composition retains one concrete source-related collection.
Once its explicit source signature/K conditions are discharged, the actual
reader has the complete ordinary result or the unchanged modelling run. -/
theorem read_record (reader : Ctx) (state : State) (owner : Address) (constant : Ixon.Constant)
    (members : Array Ixon.MutConst) (shape : BlockShape)
    (sources : Array (Nat × Ind)) (targets : Array (Nat × Ixon.Inductive))
    (firstIndex : Nat) (first : Ixon.Inductive) (names : Name → Kernel.Name → Prop)
    (recursors : Array FamilyRecursors.Input)
    (kind : constant.info = .muts members) (family : FamilyOnly members)
    (indexed : reader.index.blocks[owner]? = some shape)
    (selection : FamilyCollection.selected shape members = targets)
    (coverage : targets.size = shape.order.size) (firstFound : targets[0]? = some (firstIndex, first))
    (related : List.Forall₂
      (FamilyTypes.Paired (FamilyCollection.memberReader reader owner constant members targets first) names
        (FamilyCollection.blockParams reader owner targets first)) sources.toList targets.toList)
    (safe : ∀ source ∈ sources, source.2.isUnsafe = false)
    (common : ∀ source ∈ sources, source.2.numParams = first.params.toNat)
    (constructors : ∀ source ∈ sources, FamilyConstructors.SourceReady first.params.toNat source.2)
    (recursorOrder : shape.recs = recursors.map FamilyRecursors.Input.ref)
    (recursorValid : ∀ input ∈ recursors,
      FamilyRecursors.Valid reader (FamilyCollection.blockParams reader owner targets first) names input) :
    ∃ collected : Collected reader owner names (FamilyCollection.blockParams reader owner targets first) sources recursors,
      (collected.Consistent first.params.toNat →
        readRecord reader state owner constant = (collected.assembly first.params.toNat targets).run state) ∧
      (collected.Consistent first.params.toNat → sources.size ≤ 1 →
        FamilySourceChecks.sourceNested sources recursors = 0 →
        readRecord reader state owner constant = .ok ((collected.assembly first.params.toNat targets).result [])) ∧
      (1 < sources.size ∨ (0 < sources.size ∧ 0 < FamilySourceChecks.sourceNested sources recursors) →
        Kernel.Frontend.InModel.wants (collected.assembly first.params.toNat targets).model = true) := by
  obtain ⟨collected, collectedRun⟩ := collect_record reader state owner constant members shape sources targets firstIndex first names recursors
    kind family indexed selection coverage firstFound related safe common constructors recursorOrder recursorValid
  refine ⟨collected, ?_, ?_, ?_⟩
  · intro valid
    exact collectedRun.trans (collected.finish_run state first.params.toNat targets valid)
  · intro valid small plain
    exact collectedRun.trans (collected.finish_plain state first.params.toNat targets valid small plain)
  · intro needed
    exact collected.model_required (FamilyCollection.memberReader reader owner constant members targets first)
      first.params.toNat targets related needed

/-- Classification of a successful whole-record family read retains every
reader-result field and the real generated prefix. It is not a progress or
kernel-admission theorem. -/
theorem record_success {reader owner names params sources inputs}
    (collected : Collected reader owner names params sources inputs)
    (state : State) (constant : Ixon.Constant) (nPd : Nat) (targets : Array (Nat × Ixon.Inductive))
    (collectedRun : readRecord reader state owner constant =
      FamilyReader.finish state nPd collected.types targets collected.groups.flatten.toArray
        (collected.groups.map fun rows => rows.map (·.1.name)).toArray collected.recursors)
    (valid : collected.Consistent nPd) (output : Read)
    (ran : readRecord reader state owner constant = .ok output) :
    ∃ generated, output = (collected.assembly nPd targets).result generated ∧
      ((Kernel.Frontend.InModel.wants (collected.assembly nPd targets).model = false ∧ generated = []) ∨
        (Kernel.Frontend.InModel.wants (collected.assembly nPd targets).model = true ∧
          Kernel.Frontend.InModel.generate ((collected.assembly nPd targets).context state)
            (collected.assembly nPd targets).model = .ok generated)) := by
  rw [collectedRun, collected.finish_run state nPd targets valid] at ran
  exact FamilyAssembly.run_success _ state output ran

end Ix.CompileCert.FamilyReading
