import Ix.CompileCert.FamilyConsistency

/-! Transport source family counts and telescope shapes to the actual
finalizer guards. K correspondence and source validity remain explicit;
generation success is not used to establish the conditions. -/

namespace Ix.CompileCert.FamilySourceChecks

open Ix Kernel.Reader
open FamilyReader (CtorRow RecRow)

def sortTelescope : Expr → Option Nat
  | .forallE _ _ body _ _ => (sortTelescope body).map (· + 1)
  | .sort .. => some 0
  | .mdata _ body _ => sortTelescope body
  | _ => none

theorem related_sortTelescope (names : Name → Kernel.Name → Prop) (sourceParams : List Name)
    (params : List Kernel.Name) (source : Expr) (target : Kernel.Expr)
    (related : ExpressionState.Related names sourceParams params source target) :
    target.piSortTeleLen? = sortTelescope source := by
  induction related <;> simp_all [sortTelescope, Kernel.Expr.piSortTeleLen?]

private theorem paired_length {α β : Type} {related : α → β → Prop}
    {sources : List α} {targets : List β} (pairs : List.Forall₂ related sources targets) :
    sources.length = targets.length := by
  induction pairs with
  | nil => rfl
  | cons head rest ih => exact congrArg Nat.succ ih

private theorem paired_right {α β : Type} {related : α → β → Prop}
    {sources : List α} {targets : List β} (pairs : List.Forall₂ related sources targets)
    (target : β) (present : target ∈ targets) : ∃ source ∈ sources, related source target := by
  induction pairs with
  | nil => simp at present
  | @cons source head sources targets paired rest ih =>
    rcases List.mem_cons.mp present with same | later
    · subst target; exact ⟨source, by simp, paired⟩
    · obtain ⟨source, present, paired⟩ := ih later
      exact ⟨source, by simp [present], paired⟩

def ctorCount (sources : List (Nat × Ind)) : Nat := (sources.map (·.2.ctors.size)).sum

theorem type_count (reader : Ctx) (owner : Address) (names : Name → Kernel.Name → Prop) (params : List Kernel.Name)
    (sources : Array (Nat × Ind)) (types : Array CVal)
    (meaning : List.Forall₂ (FamilyTypes.TypeMeaning reader owner names params) sources.toList types.toList) :
    types.size = sources.size := by simpa using (paired_length meaning).symm

theorem expectedK_from_count (reader : Ctx) (owner : Address) (names : Name → Kernel.Name → Prop) (params : List Kernel.Name)
    (sources : Array (Nat × Ind)) (types : Array CVal) (ctors : Array CtorRow) (ctorNames : Array (List Kernel.Name))
    (meaning : List.Forall₂ (FamilyTypes.TypeMeaning reader owner names params) sources.toList types.toList)
    (notOne : sources.size ≠ 1) : FamilyConsistency.expectedK types ctors ctorNames = some false := by
  apply FamilyConsistency.expectedK_nonsingleton
  rwa [type_count reader owner names params sources types meaning]

theorem constructor_count (reader : Ctx) (owner : Address) (names : Name → Kernel.Name → Prop) (params : List Kernel.Name)
    (sources : List (Nat × Ind)) (groups : List (List CtorRow))
    (meaning : List.Forall₂ (FamilyConstructors.GroupMeaning reader owner names params) sources groups) :
    groups.flatten.length = ctorCount sources := by
  induction meaning with
  | nil => rfl
  | @cons source group sources groups head rest ih =>
    have count : group.length = source.2.ctors.size := by simpa using (paired_length head.1).symm
    simp only [List.flatten_cons, List.length_append, ctorCount, List.map_cons, List.sum_cons]
    rw [count]
    exact congrArg (source.2.ctors.size + ·) ih

def sourceNested (sources : Array (Nat × Ind)) (recursors : Array FamilyRecursors.Input) : Nat :=
  match recursors[0]? with
  | some input => input.source.numMotives - sources.size
  | none => 0

theorem nested_eq (reader : Ctx) (owner : Address) (names : Name → Kernel.Name → Prop) (params : List Kernel.Name)
    (sources : Array (Nat × Ind)) (types : Array CVal)
    (typeMeanings : List.Forall₂ (FamilyTypes.TypeMeaning reader owner names params) sources.toList types.toList)
    (inputs : Array FamilyRecursors.Input) (rows : Array RecRow)
    (recMeanings : List.Forall₂ (FamilyRecursors.RowMeaning reader params names) inputs.toList rows.toList) :
    FamilyConsistency.numNested types rows = sourceNested sources inputs := by
  have count := type_count reader owner names params sources types typeMeanings
  rcases inputs with ⟨inputs⟩
  rcases rows with ⟨rows⟩
  cases recMeanings with
  | nil => rfl
  | @cons input row inputs rows head rest =>
    change row.2.1.motives.toNat - types.size = input.source.numMotives - sources.size
    rw [head.payload, head.header.motives, count]

structure SourceRowOK (reader : Ctx) (owner : Address) (nPd : Nat)
    (sources : Array (Nat × Ind)) (k : Option Bool) (input : FamilyRecursors.Input) : Prop where
  parameters : input.source.numParams = nPd
  motives : input.source.numMotives = sources.size
  minors : input.source.numMinors = ctorCount sources.toList
  kValue : ∀ value, k = some value → input.source.k = value
  indices : ∀ source ∈ sources,
    input.entry.name = .str (reader.nameOf (.member owner source.1)) "rec" →
      ∀ n, sortTelescope source.2.type = some n → nPd + input.source.numIndices = n

theorem row_ok (reader : Ctx) (owner : Address) (names : Name → Kernel.Name → Prop) (params : List Kernel.Name)
    (nPd : Nat) (sources : Array (Nat × Ind)) (types : Array CVal) (groups : List (List CtorRow)) (k : Option Bool)
    (typeMeanings : List.Forall₂ (FamilyTypes.TypeMeaning reader owner names params) sources.toList types.toList)
    (ctorMeanings : List.Forall₂ (FamilyConstructors.GroupMeaning reader owner names params) sources.toList groups)
    (input : FamilyRecursors.Input) (row : RecRow) (recMeaning : FamilyRecursors.RowMeaning reader params names input row)
    (valid : SourceRowOK reader owner nPd sources k input) :
    FamilyConsistency.RowOK nPd types groups.flatten.toArray.size k row := by
  constructor
  · rw [recMeaning.payload, recMeaning.header.parameters]; exact valid.parameters
  · rw [recMeaning.payload, recMeaning.header.motives, type_count reader owner names params sources types typeMeanings]
    exact valid.motives
  · rw [recMeaning.payload, recMeaning.header.minors]
    change input.source.numMinors = groups.flatten.length
    rw [constructor_count reader owner names params sources.toList groups ctorMeanings]
    exact valid.minors
  · intro value found
    rw [recMeaning.payload, recMeaning.header.k]
    exact valid.kValue value found
  · intro parent named ty present same n count
    obtain ⟨source, sourcePresent, typeMeaning⟩ := paired_right typeMeanings ty (by simpa using present)
    have sourceName : input.entry.name = .str (reader.nameOf (.member owner source.1)) "rec" := by
      rw [← recMeaning.name, ← typeMeaning.name, same]
      exact named
    have telescope : sortTelescope source.2.type = some n :=
      (related_sortTelescope names source.2.levelParams.toList params source.2.type ty.type typeMeaning.type).symm.trans count
    rw [recMeaning.payload, recMeaning.header.indices]
    exact valid.indices source (by simpa using sourcePresent) sourceName n telescope

/-- Source conditions justify the ordinary guards exactly when the source
family is non-nested. The nested branch retains its existing modelling path. -/
theorem checks_from_source (reader : Ctx) (owner : Address) (names : Name → Kernel.Name → Prop) (params : List Kernel.Name)
    (nPd : Nat) (sources : Array (Nat × Ind)) (types : Array CVal) (groups : List (List CtorRow))
    (inputs : Array FamilyRecursors.Input) (rows : Array RecRow)
    (typeMeanings : List.Forall₂ (FamilyTypes.TypeMeaning reader owner names params) sources.toList types.toList)
    (ctorMeanings : List.Forall₂ (FamilyConstructors.GroupMeaning reader owner names params) sources.toList groups)
    (recMeanings : List.Forall₂ (FamilyRecursors.RowMeaning reader params names) inputs.toList rows.toList)
    (valid : sourceNested sources inputs = 0 → ∀ input ∈ inputs,
      SourceRowOK reader owner nPd sources
        (FamilyConsistency.expectedK types groups.flatten.toArray (groups.map fun rows => rows.map (·.1.name)).toArray) input) :
    FamilyConsistency.checks nPd types groups.flatten.toArray
      (groups.map fun rows => rows.map (·.1.name)).toArray rows = .ok () := by
  apply FamilyConsistency.checks_succeed
  intro notNested row present
  have sourceNotNested : sourceNested sources inputs = 0 := by
    rwa [nested_eq reader owner names params sources types typeMeanings inputs rows recMeanings] at notNested
  obtain ⟨input, inputPresent, meaning⟩ := paired_right recMeanings row (by simpa using present)
  exact row_ok reader owner names params nPd sources types groups _ typeMeanings ctorMeanings input row meaning
    (valid sourceNotNested input (by simpa using inputPresent))

theorem finish_from_source (reader : Ctx) (owner : Address) (names : Name → Kernel.Name → Prop) (params : List Kernel.Name)
    (state : State) (nPd : Nat) (sources : Array (Nat × Ind)) (types : Array CVal)
    (tyRecs : Array (Nat × Ixon.Inductive)) (groups : List (List CtorRow))
    (inputs : Array FamilyRecursors.Input) (rows : Array RecRow)
    (typeMeanings : List.Forall₂ (FamilyTypes.TypeMeaning reader owner names params) sources.toList types.toList)
    (ctorMeanings : List.Forall₂ (FamilyConstructors.GroupMeaning reader owner names params) sources.toList groups)
    (recMeanings : List.Forall₂ (FamilyRecursors.RowMeaning reader params names) inputs.toList rows.toList)
    (valid : sourceNested sources inputs = 0 → ∀ input ∈ inputs,
      SourceRowOK reader owner nPd sources
        (FamilyConsistency.expectedK types groups.flatten.toArray (groups.map fun rows => rows.map (·.1.name)).toArray) input) :
    FamilyReader.finish state nPd types tyRecs groups.flatten.toArray
      (groups.map fun rows => rows.map (·.1.name)).toArray rows =
      FamilyConsistency.assemble state nPd types tyRecs groups.flatten.toArray
        (groups.map fun rows => rows.map (·.1.name)).toArray rows := by
  rw [FamilyConsistency.finish_run, checks_from_source reader owner names params nPd sources types groups inputs rows
    typeMeanings ctorMeanings recMeanings valid]
  rfl

end Ix.CompileCert.FamilySourceChecks
