import Ix.CompileCert.FamilyFields

/-! Source-related type rows collected by the actual family reader. Member
positions follow the supplied motive order; index construction and the shared
family universe context remain separate caller obligations. -/

namespace Ix.CompileCert.FamilyTypes

open Ix Kernel.Reader

def Paired (member : MemberReader) (names : Name → Kernel.Name → Prop) (params : List Kernel.Name)
    (source : Nat × Ind) (target : Nat × Ixon.Inductive) : Prop :=
  target.1 = source.1 ∧
    InductiveEmission.Related member names source.2.levelParams.toList params source.2 target.2

def typeStep (reader : Ctx) (owner : Address) (member : MemberReader) (lpsAt : UInt64 → List Kernel.Name)
    (entry : Nat × Ixon.Inductive) (initial : Array CVal × Array (Nat × Ixon.Inductive)) :
    ReadM (ForInStep (Array CVal × Array (Nat × Ixon.Inductive))) := do
  let type ← member.read entry.2.typ
  pure (.yield (initial.1.push ⟨reader.nameOf (.member owner entry.1), lpsAt entry.2.lvls, type⟩,
    initial.2.push entry))

theorem types_run (reader : Ctx) (owner : Address) (member : MemberReader)
    (lpsAt : UInt64 → List Kernel.Name) (indcs : Array (Nat × Ixon.Inductive)) :
    FamilyReader.readTypes reader owner member lpsAt indcs =
      (do
        let result ← forIn indcs (#[], #[]) (typeStep reader owner member lpsAt)
        pure (result.1, result.2)) := rfl

private theorem push_join (initial : Array α) (head : α) (tail : List α) :
    initial.push head ++ tail.toArray = initial ++ (head :: tail).toArray := by
  rw [Array.push_eq_append, Array.append_assoc]
  exact congrArg (initial ++ ·) (List.toArray_cons head tail).symm

structure TypeMeaning (reader : Ctx) (owner : Address) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (source : Nat × Ind) (target : CVal) : Prop where
  name : target.name = reader.nameOf (.member owner source.1)
  levels : target.levelParams.length = source.2.levelParams.size
  type : ExpressionState.Related names source.2.levelParams.toList params source.2.type target.type

theorem types_loop (reader : Ctx) (owner : Address) (member : MemberReader)
    (lpsAt : UInt64 → List Kernel.Name) (lengths : ∀ count, (lpsAt count).length = count.toNat)
    (names : Name → Kernel.Name → Prop) (params : List Kernel.Name)
    (sources : List (Nat × Ind)) (targets : List (Nat × Ixon.Inductive))
    (related : List.Forall₂ (Paired member names params) sources targets)
    (initial : Array CVal × Array (Nat × Ixon.Inductive)) :
    ∃ types,
      forIn targets initial (typeStep reader owner member lpsAt) =
        .ok (initial.1 ++ types.toArray, initial.2 ++ targets.toArray) ∧
      List.Forall₂ (TypeMeaning reader owner names params) sources types := by
  induction related generalizing initial with
  | nil => exact ⟨[], by simp; rfl, .nil⟩
  | @cons source target sources targets head rest ih =>
    obtain ⟨position, _, levels, _, _, ⟨type, meaning, read⟩, _⟩ := head
    let cv : CVal := ⟨reader.nameOf (.member owner target.1), lpsAt target.2.lvls, type⟩
    obtain ⟨types, tailRun, meanings⟩ := ih (initial.1.push cv, initial.2.push target)
    refine ⟨cv :: types, ?_, .cons ?_ meanings⟩
    · rw [List.forIn_cons]
      simp only [typeStep, read, bind, Except.bind, pure, Except.pure]
      simpa only [cv, push_join] using tailRun
    · exact ⟨congrArg (fun i => reader.nameOf (.member owner i)) position,
        (lengths target.2.lvls).trans levels, meaning⟩

/-- The type reader keeps the exact motive-ordered payload array for later
family checks and supplies a source-related value for every collected type. -/
theorem types_read (reader : Ctx) (owner : Address) (member : MemberReader)
    (lpsAt : UInt64 → List Kernel.Name) (lengths : ∀ count, (lpsAt count).length = count.toNat)
    (names : Name → Kernel.Name → Prop) (params : List Kernel.Name)
    (sources : Array (Nat × Ind)) (targets : Array (Nat × Ixon.Inductive))
    (related : List.Forall₂ (Paired member names params) sources.toList targets.toList) :
    ∃ types, FamilyReader.readTypes reader owner member lpsAt targets = .ok (types, targets) ∧
      List.Forall₂ (TypeMeaning reader owner names params) sources.toList types.toList := by
  obtain ⟨types, ran, meanings⟩ := types_loop reader owner member lpsAt lengths names params
    sources.toList targets.toList related (#[], #[])
  refine ⟨types.toArray, ?_, meanings⟩
  rw [types_run, ← Array.forIn_toList]
  have actual : forIn targets.toList (#[], #[]) (typeStep reader owner member lpsAt) =
      .ok (types.toArray, targets) := by simpa using ran
  rw [actual]
  rfl

end Ix.CompileCert.FamilyTypes
