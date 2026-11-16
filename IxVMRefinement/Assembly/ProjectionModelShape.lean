import Ix.IxVM.Consistency.Statement

/-! # Structural requirements of modeled projections

Fields beyond the two bare-pair projections require a stored projection table. The public
model's table law requires a literal former telescope, even when its declared type is
definitionally equal to that telescope. These lemmas isolate the shape requirement.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel

universe u

variable {V : Type u} [SetTheory V]

/-- A denoted projection beyond the bare-pair fields has an actual table entry. -/
theorem projection_table_of_denotes {md : Mode}
    {cval : Key md → (LevelParam → Nat) → V} {env : Env md}
    {φ : LevelParam → Nat} {ρ : BVarIdx → V}
    {T : Key md} {i : Nat} {value : Expr md} {result : V}
    (beyondPair : 2 ≤ i) (denoted : Denotes cval env φ ρ (.proj T i value) result) :
    ∃ entry, env.findProj? T i = some entry := by
  cases denoted with
  | proj_table found _ => exact ⟨_, found⟩
  | proj_fst _ _ => omega
  | proj_snd _ _ => omega

/-- The public model forces the stored former telescope at every denoted later field. -/
theorem model_projection_former_telescope {md : Mode} {env : Env md} (model : Model V env)
    {T : Key md} {cv : ConstantVal md} {caps : IndCaps md}
    (former : env.find? T = some (.indInfo cv caps))
    {φ : LevelParam → Nat} {ρ : BVarIdx → V} {i : Nat} {value : Expr md} {result : V}
    (beyondPair : 2 ≤ i) (denoted : Denotes model.cval env φ ρ (.proj T i value) result) :
    ∃ entry binders, env.findProj? T i = some entry ∧
      cv.type.stripPis entry.numParams = some (binders, .sort entry.structSort) := by
  obtain ⟨entry, found⟩ := projection_table_of_denotes beyondPair denoted
  obtain ⟨binders, telescope⟩ := (model.proj_law T i entry cv caps found former).2.1
  exact ⟨entry, binders, found, telescope⟩

/-- A former stored at a constant alias cannot coexist with a denoted later-field projection
in the current public model, regardless of the alias's reduction behavior. -/
theorem model_alias_former_no_projection {md : Mode} {env : Env md} (model : Model V env)
    {T aliasKey : Key md} {levels : List Level} {cv : ConstantVal md} {caps : IndCaps md}
    (former : env.find? T = some (.indInfo cv caps)) (typeAlias : cv.type = .const aliasKey levels)
    {φ : LevelParam → Nat} {ρ : BVarIdx → V} {i : Nat} {value : Expr md} {result : V}
    (beyondPair : 2 ≤ i) : ¬ Denotes model.cval env φ ρ (.proj T i value) result := by
  intro denoted
  obtain ⟨entry, binders, _, telescope⟩ :=
    model_projection_former_telescope model former beyondPair denoted
  rw [typeAlias] at telescope
  cases entry.numParams <;> simp [Expr.stripPis] at telescope

/-- A model reads a lambda body at some input whenever a stored constant inhabits its domain. -/
theorem model_lam_body_denotes {md : Mode} {env : Env md} (model : Model V env)
    {φ : LevelParam → Nat} {ρ : BVarIdx → V} {domain body : Expr md}
    {binderMeta : BinderMeta} {result : V} {inhabitant : ConstantInfo md}
    (present : inhabitant ∈ env.consts) (typeEq : inhabitant.toConstantVal.type = domain)
    (denoted : Denotes model.cval env φ ρ (.lam domain body binderMeta) result) :
    ∃ input output, Denotes model.cval env φ (push input ρ) body output := by
  cases denoted with
  | lam domainRead bodyRead _ =>
    obtain ⟨actualDomain, actualRead, member⟩ := model.mem inhabitant present φ ρ
    rw [typeEq] at actualRead
    have same := Denotes_functional actualRead domainRead
    rw [same] at member
    exact ⟨model.cval inhabitant.name φ, _, bodyRead _ member⟩

/-- Storage correspondence preserves a constant alias literally; annotation cannot replace
it by its normalized telescope. -/
theorem stored_alias_former_no_projection {env : Env .anon} (model : Model V env)
    {T aliasKey : Key .anon} {levels : List Level} {cv raw : ConstantVal .anon} {caps : IndCaps .anon}
    (former : env.find? T = some (.indInfo cv caps))
    (stored : IxVM.Consistency.ValStored cv raw) (typeAlias : raw.type = .const aliasKey levels)
    {φ : LevelParam → Nat} {ρ : BVarIdx → V} {i : Nat} {value : Expr .anon} {result : V}
    (beyondPair : 2 ≤ i) : ¬ Denotes model.cval env φ ρ (.proj T i value) result := by
  have annotated := stored.2.2
  rw [typeAlias] at annotated
  exact model_alias_former_no_projection model former annotated.const_inv beyondPair

/-- A reader-shaped definition exposing such a projection cannot have the current public
model when the former is stored as its declared alias. -/
theorem no_model_of_stored_alias_projection {env : Env .anon}
    {T aliasKey : Key .anon} {levels : List Level} {cvT rawT : ConstantVal .anon}
    {caps : IndCaps .anon}
    (former : env.find? T = some (.indInfo cvT caps))
    (storedFormer : IxVM.Consistency.ValStored cvT rawT)
    (typeAlias : rawT.type = .const aliasKey levels)
    {cv : ConstantVal .anon} {body value : Expr .anon} {hint : ReducibilityHint} {i : Nat}
    (present : ConstantInfo.defnInfo cv body hint ∈ env.consts)
    (storedValue : IxVM.Consistency.Annotates body (.proj T i value)) (beyondPair : 2 ≤ i) :
    ¬ Nonempty (Model V env) := by
  rintro ⟨model⟩
  cases storedValue with
  | proj _ =>
    exact stored_alias_former_no_projection model former storedFormer typeAlias beyondPair
      (model.defn_value cv _ hint present (fun _ => 0) (fun _ => SetTheory.empty))

end IxVM.Refinement.Assembly
