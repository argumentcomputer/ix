import Aiur.Runtime
import Aiur.ExceptFacts

namespace Aiur

@[simp] theorem Value.wellFormed_field (decls : Declarations) (x : F) :
    (@Value.field F A x).wellFormed decls = true := by simp [wellFormed]

@[simp] theorem Value.wellFormed_ptr (decls : Declarations) (target : Ty) (x : A) :
    (@Value.ptr F A target x).wellFormed decls = true := by simp [wellFormed]

@[simp] theorem Value.wellFormed_tuple (decls : Declarations) (values : List (Value F A)) :
    (.tuple values : Value F A).wellFormed decls = true ↔ ∀ value ∈ values, value.wellFormed decls = true := by
  simp [wellFormed]

theorem Value.wellFormed_construct (decls : Declarations) (name ctor : String) (values : List (Value F A)) :
    (.construct name ctor values : Value F A).wellFormed decls = true ↔
      ∃ definition, decls.findConstructor? name ctor = some definition ∧
        values.map Value.type = definition.fields ∧ ∀ value ∈ values, value.wellFormed decls = true := by
  cases found : decls.findConstructor? name ctor <;> simp [wellFormed, found]

/-- Environments contain values with valid constructor payloads. -/
def Environment.WellFormed (decls : Declarations) (locals : Environment F A) : Prop :=
  ∀ binding ∈ locals, binding.2.wellFormed decls = true

@[simp] theorem Environment.wellFormed_append {decls : Declarations} {left right : Environment F A} :
    (left ++ right).WellFormed decls ↔ left.WellFormed decls ∧ right.WellFormed decls := by
  simp [WellFormed, or_imp, forall_and]

mutual
  theorem Pattern.bindings_wellFormed [DecidableEq F] {decls : Declarations}
      {pattern : Pattern F} {value : Value F A} {locals : Environment F A}
      (formed : value.wellFormed decls = true) (matched : pattern.bindings value = some locals) :
      locals.WellFormed decls := by
    cases pattern with
    | wildcard => simp only [Pattern.bindings, Option.some.injEq] at matched; subst locals; simp [Environment.WellFormed]
    | bind name =>
        simp only [Pattern.bindings, Option.some.injEq] at matched
        subst locals
        simpa [Environment.WellFormed] using formed
    | literal literal =>
        cases value with
        | tuple | ptr | construct => simp [Pattern.bindings] at matched
        | field x =>
            simp only [Pattern.bindings] at matched
            split at matched
            · cases matched; simp [Environment.WellFormed]
            · cases matched
    | tuple patterns =>
        cases value with
        | field | ptr | construct => simp [Pattern.bindings] at matched
        | tuple values =>
            simp only [Pattern.bindings] at matched
            exact Pattern.bindingsList_wellFormed ((Value.wellFormed_tuple _ _).mp formed) matched
    | construct name ctor patterns =>
        cases value with
        | field | tuple | ptr => simp [Pattern.bindings] at matched
        | construct actual constructor values =>
            obtain ⟨definition, _, _, valuesFormed⟩ := (Value.wellFormed_construct _ _ _ _).mp formed
            simp only [Pattern.bindings] at matched
            split at matched
            · exact Pattern.bindingsList_wellFormed valuesFormed matched
            · cases matched
  termination_by sizeOf pattern

  theorem Pattern.bindingsList_wellFormed [DecidableEq F] {decls : Declarations}
      {patterns : List (Pattern F)} {values : List (Value F A)} {locals : Environment F A}
      (formed : ∀ value ∈ values, value.wellFormed decls = true)
      (matched : Pattern.bindingsList patterns values = some locals) : locals.WellFormed decls := by
    cases patterns with
    | nil => cases values <;> simp_all [Pattern.bindingsList, Environment.WellFormed]
    | cons pattern patterns =>
        cases values with
        | nil => simp [Pattern.bindingsList] at matched
        | cons value values =>
            simp only [Pattern.bindingsList] at matched
            obtain ⟨head, headRun, rest⟩ := Option.bind_eq_some_iff.mp matched
            obtain ⟨tail, tailRun, finished⟩ := Option.bind_eq_some_iff.mp rest
            simp only [Option.pure_def, Option.some.injEq] at finished
            subst locals
            exact Environment.wellFormed_append.mpr
              ⟨Pattern.bindings_wellFormed (formed _ (by simp)) headRun,
                Pattern.bindingsList_wellFormed (fun v h => formed v (by simp [h])) tailRun⟩
  termination_by sizeOf patterns
end

theorem selectArm_wellFormed [DecidableEq F] {decls : Declarations}
    {value : Value F A} {arms : List (Pattern F × Expr F)} {locals : Environment F A} {body : Expr F}
    (formed : value.wellFormed decls = true) (selected : selectArm value arms = some (locals, body)) :
    locals.WellFormed decls := by
  induction arms with
  | nil => simp [selectArm] at selected
  | cons arm arms ih =>
      rcases arm with ⟨pattern, branch⟩
      cases matched : pattern.bindings value with
      | none => exact ih (by simpa [selectArm, matched] using selected)
      | some bindings =>
          simp [selectArm, matched] at selected
          rcases selected with ⟨rfl, rfl⟩
          exact Pattern.bindings_wellFormed formed matched

end Aiur
