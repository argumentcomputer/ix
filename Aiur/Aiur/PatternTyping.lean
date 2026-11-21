import Aiur.ValueFormed

namespace Aiur

variable {F : Type}

def environmentTypes (locals : Environment F A) : List (String × Ty) :=
  locals.map fun binding => (binding.1, binding.2.type)

@[simp] theorem environmentTypes_append (left right : Environment F A) :
    environmentTypes (left ++ right) = environmentTypes left ++ environmentTypes right := List.map_append

theorem requireType_ok {caller : String} {expected actual : Ty}
    (checked : requireType caller expected actual = .ok ()) : expected = actual := by
  simpa [requireType] using checked

theorem checkPattern_types {decls : Declarations} {caller : String} {pattern : Pattern F} {type : Ty}
    {bindings : List (String × Ty)} (checked : checkPattern decls caller pattern type = .ok bindings) :
    patternTypes decls caller pattern type = .ok bindings := by
  unfold checkPattern at checked
  obtain ⟨types, typed, rest⟩ := except_bind_ok.mp checked
  split at rest
  · cases rest
  · simp only [pure_bind, except_pure_ok] at rest
    subst bindings
    exact typed

mutual
  /-- Matching collects exactly the binding types computed by the typechecker. -/
  theorem patternTypes_bindings [DecidableEq F] {decls : Declarations} {caller : String} {pattern : Pattern F}
      {value : Value F A} {types : List (String × Ty)} {bindings : Environment F A}
      (checked : patternTypes decls caller pattern value.type = .ok types)
      (formed : value.wellFormed decls = true)
      (matched : pattern.bindings value = some bindings) : environmentTypes bindings = types := by
    cases pattern with
    | wildcard =>
        simp only [patternTypes, except_pure_ok] at checked
        simp only [Pattern.bindings, Option.some.injEq] at matched
        subst types; subst bindings; rfl
    | bind name =>
        simp only [patternTypes, except_pure_ok] at checked
        simp only [Pattern.bindings, Option.some.injEq] at matched
        subst types; subst bindings; rfl
    | literal literal =>
        cases value with
        | tuple values | ptr | construct => simp [Pattern.bindings] at matched
        | field value =>
            simp [patternTypes, Value.type, requireType, bind, Except.bind, pure, Except.pure] at checked
            subst types
            simp only [Pattern.bindings] at matched
            split at matched
            · cases matched; rfl
            · cases matched
    | tuple patterns =>
        cases value with
        | field | ptr | construct => simp [Pattern.bindings] at matched
        | tuple values =>
            simp only [Pattern.bindings] at matched
            simp only [patternTypes, Value.type] at checked
            split at checked
            · cases checked
            · simp only [pure_bind] at checked
              exact patternTypesList_bindings checked ((Value.wellFormed_tuple _ _).mp formed) matched
    | construct name ctor patterns =>
        cases value with
        | field | ptr | tuple => simp [Pattern.bindings] at matched
        | construct actual actualCtor values =>
            simp only [Pattern.bindings] at matched
            split at matched
            · rename_i same
              rcases same with ⟨rfl, rfl⟩
              obtain ⟨definition, found, shapes, valuesFormed⟩ :=
                (Value.wellFormed_construct _ _ _ _).mp formed
              simp only [patternTypes, Value.type, requireType, ↓reduceIte, pure_bind, found] at checked
              split at checked
              · cases checked
              · rw [← shapes] at checked
                exact patternTypesList_bindings checked valuesFormed matched
            · cases matched
  termination_by sizeOf pattern

  theorem patternTypesList_bindings [DecidableEq F] {decls : Declarations} {caller : String}
      {patterns : List (Pattern F)} {values : List (Value F A)}
      {types : List (String × Ty)} {bindings : Environment F A}
      (checked : patternTypesList decls caller patterns (values.map Value.type) = .ok types)
      (formed : ∀ value ∈ values, value.wellFormed decls = true)
      (matched : Pattern.bindingsList patterns values = some bindings) : environmentTypes bindings = types := by
    cases patterns with
    | nil =>
        cases values with
        | nil =>
            simp only [patternTypesList, List.map_nil, except_pure_ok] at checked
            simp only [Pattern.bindingsList, Option.some.injEq] at matched
            subst types; subst bindings; rfl
        | cons => simp [Pattern.bindingsList] at matched
    | cons pattern patterns =>
        cases values with
        | nil => simp [Pattern.bindingsList] at matched
        | cons value values =>
            simp only [patternTypesList, List.map_cons] at checked
            obtain ⟨headTypes, headRun, rest⟩ := except_bind_ok.mp checked
            obtain ⟨tailTypes, tailRun, finished⟩ := except_bind_ok.mp rest
            obtain rfl := except_pure_ok.mp finished
            cases headMatch : pattern.bindings value with
            | none => simp [Pattern.bindingsList, headMatch] at matched
            | some headBindings =>
                cases tailMatch : Pattern.bindingsList patterns values with
                | none => simp [Pattern.bindingsList, headMatch, tailMatch] at matched
                | some tailBindings =>
                    simp [Pattern.bindingsList, headMatch, tailMatch] at matched
                    subst bindings
                    rw [environmentTypes_append, patternTypes_bindings headRun (formed _ (by simp)) headMatch,
                      patternTypesList_bindings tailRun (fun v h => formed v (by simp [h])) tailMatch]
  termination_by sizeOf patterns
end

theorem checkArms_selected [DecidableEq F] {program : Program F} {caller : String}
    {locals : List (String × Ty)} {value : Value F A} {type : Ty}
    {arms : List (Pattern F × Expr F)} {bindings : Environment F A} {body : Expr F}
    (checked : checkArms program caller locals value.type type arms = .ok ())
    (formed : value.wellFormed program.enums = true)
    (selected : selectArm value arms = some (bindings, body)) :
    inferType program caller (environmentTypes bindings ++ locals) body = .ok type := by
  induction arms with
  | nil => simp [selectArm] at selected
  | cons arm arms ih =>
      rcases arm with ⟨pattern, branch⟩
      simp only [checkArms] at checked
      obtain ⟨types, patternRun, rest⟩ := except_bind_ok.mp checked
      obtain ⟨branchType, branchRun, rest⟩ := except_bind_ok.mp rest
      obtain ⟨finished, sameRun, tailRun⟩ := except_bind_ok.mp rest
      cases finished
      have same := requireType_ok sameRun
      subst branchType
      cases matched : pattern.bindings value with
      | none => exact ih tailRun (by simpa only [selectArm, matched] using selected)
      | some actual =>
          simp only [selectArm, matched, Option.some.injEq, Prod.mk.injEq] at selected
          obtain ⟨rfl, rfl⟩ := selected
          rw [patternTypes_bindings (checkPattern_types patternRun) formed matched]
          exact branchRun

end Aiur
