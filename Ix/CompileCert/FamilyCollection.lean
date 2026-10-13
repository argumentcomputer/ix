import Ix.CompileCert.FamilyConstructors
import Ix.CompileCert.FamilyRecursors

/-! Collect source-related family rows through the actual kernel reader and
reduce its remaining work to the real consistency/modeller stage. This does
not assume that final stage succeeds or establish declaration admission. -/

namespace Ix.CompileCert.FamilyCollection

open Ix Kernel.Reader

def selected (shape : BlockShape) (members : Array Ixon.MutConst) : Array (Nat × Ixon.Inductive) :=
  shape.order.filterMap fun i => match (members[i]? : Option Ixon.MutConst) with
    | some (.indc ind) => some (i, ind)
    | _ => none

def blockParams (reader : Ctx) (owner : Address) (targets : Array (Nat × Ixon.Inductive))
    (first : Ixon.Inductive) : List Kernel.Name :=
  reader.lpsOf (.member owner (targets[0]!.1)) first.lvls.toNat

def memberReader (reader : Ctx) (owner : Address) (constant : Ixon.Constant)
    (members : Array Ixon.MutConst) (targets : Array (Nat × Ixon.Inductive)) (first : Ixon.Inductive) : MemberReader :=
  MemberReader.mk' reader constant (paramOf (blockParams reader owner targets first))
    (fun index => if index < members.size then some (reader.nameOf (.member owner index)) else none)

def levelsAt (reader : Ctx) (owner : Address) (targets : Array (Nat × Ixon.Inductive))
    (first : Ixon.Inductive) (count : UInt64) : List Kernel.Name :=
  if count == first.lvls then blockParams reader owner targets first else levelNames count.toNat

theorem levels_length (reader : Ctx) (owner : Address) (targets : Array (Nat × Ixon.Inductive))
    (first : Ixon.Inductive) (count : UInt64) : (levelsAt reader owner targets first count).length = count.toNat :=
  FamilyFields.lpsAt_length first.lvls count (blockParams reader owner targets first)
    (DefinitionReading.lpsOf_length reader _ first.lvls.toNat)

theorem paired_headers (member : MemberReader) (names : Name → Kernel.Name → Prop) (params : List Kernel.Name)
    (sources : List (Nat × Ind)) (targets : List (Nat × Ixon.Inductive))
    (related : List.Forall₂ (FamilyTypes.Paired member names params) sources targets)
    (nPd : Nat) (safe : ∀ source ∈ sources, source.2.isUnsafe = false)
    (common : ∀ source ∈ sources, source.2.numParams = nPd) :
    ∀ target ∈ targets, target.2.isUnsafe = false ∧ target.2.params.toNat = nPd := by
  induction related with
  | nil => simp
  | @cons source target sources targets head rest ih =>
    intro value present
    rcases List.mem_cons.mp present with same | later
    · subst value
      exact ⟨head.2.1.trans (safe source (by simp)), head.2.2.2.1.trans (common source (by simp))⟩
    · exact ih (fun source present => safe source (by simp [present]))
        (fun source present => common source (by simp [present])) value later

/-- The actual family reader reaches finalization with source-related type,
constructor and recursor rows in its actual order and logical contexts.
Index coverage, source shape and published recursor data remain explicit;
the final consistency/modeller computation is retained verbatim. -/
theorem collect (reader : Ctx) (state : State) (owner : Address) (constant : Ixon.Constant)
    (members : Array Ixon.MutConst) (shape : BlockShape)
    (sources : Array (Nat × Ind)) (targets : Array (Nat × Ixon.Inductive))
    (firstIndex : Nat) (first : Ixon.Inductive)
    (names : Name → Kernel.Name → Prop) (recursors : Array FamilyRecursors.Input)
    (indexed : reader.index.blocks[owner]? = some shape)
    (selection : selected shape members = targets)
    (coverage : targets.size = shape.order.size)
    (firstFound : targets[0]? = some (firstIndex, first))
    (related : List.Forall₂
      (FamilyTypes.Paired (memberReader reader owner constant members targets first) names (blockParams reader owner targets first))
      sources.toList targets.toList)
    (safe : ∀ source ∈ sources, source.2.isUnsafe = false)
    (common : ∀ source ∈ sources, source.2.numParams = first.params.toNat)
    (constructors : ∀ source ∈ sources, FamilyConstructors.SourceReady first.params.toNat source.2)
    (recursorOrder : shape.recs = recursors.map FamilyRecursors.Input.ref)
    (recursorValid : ∀ input ∈ recursors, FamilyRecursors.Valid reader (blockParams reader owner targets first) names input) :
    ∃ types groups rows,
      readInductive reader state owner constant members =
        FamilyReader.finish state first.params.toNat types targets groups.flatten.toArray
          (groups.map fun ctors => ctors.map (·.1.name)).toArray rows ∧
      List.Forall₂ (FamilyTypes.TypeMeaning reader owner names (blockParams reader owner targets first)) sources.toList types.toList ∧
      List.Forall₂ (FamilyConstructors.GroupMeaning reader owner names (blockParams reader owner targets first)) sources.toList groups ∧
      List.Forall₂ (FamilyRecursors.RowMeaning reader (blockParams reader owner targets first) names) recursors.toList rows.toList := by
  have headers := paired_headers (memberReader reader owner constant members targets first) names
    (blockParams reader owner targets first) sources.toList targets.toList related first.params.toNat
    (fun source present => safe source (by simpa using present))
    (fun source present => common source (by simpa using present))
  have noUnsafe : targets.any (·.2.isUnsafe) = false := by
    apply Array.any_eq_false.mpr
    intro index inside
    exact Bool.eq_false_iff.mp (headers targets[index] (by simp)).1
  have commonParams : targets.all (·.2.params.toNat == first.params.toNat) = true := by
    apply Array.all_eq_true.mpr
    intro index inside
    simp [(headers targets[index] (by simp)).2]
  obtain ⟨types, typesRun, typeMeanings⟩ := FamilyTypes.types_read reader owner
    (memberReader reader owner constant members targets first) (levelsAt reader owner targets first)
    (levels_length reader owner targets first) names (blockParams reader owner targets first) sources targets related
  obtain ⟨groups, ctorsRun, ctorMeanings⟩ := FamilyConstructors.constructors_read reader owner
    (memberReader reader owner constant members targets first) (levelsAt reader owner targets first)
    (levels_length reader owner targets first) first.params.toNat names (blockParams reader owner targets first)
    sources targets related constructors
  obtain ⟨rows, recsRun, recMeanings⟩ := FamilyRecursors.recursors_read reader (blockParams reader owner targets first)
    names recursors shape.recs recursorOrder recursorValid
  have covered : (targets.size == shape.order.size) = true := by simp [coverage]
  refine ⟨types, groups, rows, ?_, typeMeanings, ctorMeanings, recMeanings⟩
  rw [← FamilyReader.run_eq]
  unfold FamilyReader.run
  change (do
    let some found := reader.index.blocks[owner]?
      | declined "inductive block without a recursor in the input"
    let indcs := selected found members
    unless indcs.size == found.order.size do malformed "recursor motive is not a member of its block"
    let some (_, first) := (indcs[0]? : Option (Nat × Ixon.Inductive)) | malformed "empty inductive block"
    if indcs.any (·.2.isUnsafe) then declined "unsafe inductive declaration"
    unless indcs.all (·.2.params.toNat == first.params.toNat) do
      declined "inductive block whose type records disagree on numParams"
    let (types, tyRecs) ← FamilyReader.readTypes reader owner
      (memberReader reader owner constant members indcs first) (levelsAt reader owner indcs first) indcs
    let (ctors, ctorNames) ← FamilyReader.readConstructors reader owner
      (memberReader reader owner constant members indcs first) (levelsAt reader owner indcs first) first.params.toNat indcs
    let recs ← FamilyReader.readRecursors reader (blockParams reader owner indcs first) found.recs
    FamilyReader.finish state first.params.toNat types tyRecs ctors ctorNames recs) = _
  simp only [indexed, selection, covered, ↓reduceIte, firstFound,
    noUnsafe, Bool.false_eq_true, commonParams, typesRun, ctorsRun, recsRun, bind, Except.bind]

end Ix.CompileCert.FamilyCollection
