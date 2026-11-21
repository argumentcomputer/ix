import Aiur.Tuple.Semantics.WithCalls
import Aiur.Tuple.ValueFacts
import Mathlib.Data.List.Basic

namespace Aiur.Tuple

theorem except_bind_ok {first : Except ε α} {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔ ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [bind, Except.bind]

theorem forIn_ok {action : α → Except ε Unit} {items : List α}
    (checked : (do for item in items do action item : Except ε Unit) = .ok ()) :
    ∀ item ∈ items, action item = .ok () := by
  induction items with
  | nil => simp
  | cons item items ih =>
      cases first : action item with
      | error error => simp [List.forIn_cons, first, bind, Except.bind] at checked
      | ok finished =>
          cases finished
          simp only [List.forIn_cons, first, bind, Except.bind, pure, Except.pure] at checked
          intro value member
          rcases List.mem_cons.mp member with rfl | member
          · exact first
          · exact ih checked value member

@[simp] theorem except_pure_ok {value result : α} :
    (pure value : Except ε α) = .ok result ↔ value = result := by simp [pure, Except.pure]

@[simp] theorem except_throw_eq (error : ε) : (throw error : Except ε α) = .error error := rfl

def environmentTypes (locals : Environment F) : List (String × Ty) :=
  locals.map fun binding => (binding.1, binding.2.type)

@[simp] theorem environmentTypes_append (left right : Environment F) :
    environmentTypes (left ++ right) = environmentTypes left ++ environmentTypes right := List.map_append

theorem requireType_ok {caller : String} {expected actual : Ty}
    (checked : requireType caller expected actual = .ok ()) : expected = actual := by
  simpa [requireType] using checked

theorem checkPattern_types {caller : String} {pattern : Pattern F} {type : Ty}
    {bindings : List (String × Ty)} (checked : checkPattern caller pattern type = .ok bindings) :
    patternTypes caller pattern type = .ok bindings := by
  unfold checkPattern at checked
  obtain ⟨types, typed, rest⟩ := except_bind_ok.mp checked
  split at rest
  · cases rest
  · simp only [pure_bind, except_pure_ok] at rest
    subst bindings
    exact typed

mutual
  /-- Matching collects exactly the binding types computed by the typechecker. -/
  theorem patternTypes_bindings [DecidableEq F] {caller : String} {pattern : Pattern F}
      {value : Value F} {types : List (String × Ty)} {bindings : Environment F}
      (checked : patternTypes caller pattern value.type = .ok types)
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
        | tuple values => simp [Pattern.bindings] at matched
        | field value =>
            simp [patternTypes, Value.type, requireType, bind, Except.bind, pure, Except.pure] at checked
            subst types
            simp only [Pattern.bindings] at matched
            split at matched
            · cases matched; rfl
            · cases matched
    | tuple patterns =>
        cases value with
        | field => simp [Pattern.bindings] at matched
        | tuple values =>
            simp only [Pattern.bindings] at matched
            simp only [patternTypes, Value.type] at checked
            split at checked
            · cases checked
            · simp only [pure_bind] at checked
              exact patternTypesList_bindings checked matched
  termination_by sizeOf pattern

  theorem patternTypesList_bindings [DecidableEq F] {caller : String}
      {patterns : List (Pattern F)} {values : List (Value F)}
      {types : List (String × Ty)} {bindings : Environment F}
      (checked : patternTypesList caller patterns (values.map Value.type) = .ok types)
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
                    rw [environmentTypes_append, patternTypes_bindings headRun headMatch,
                      patternTypesList_bindings tailRun tailMatch]
  termination_by sizeOf patterns
end

theorem checkArms_selected [DecidableEq F] {program : Program F} {caller : String}
    {locals : List (String × Ty)} {value : Value F} {type : Ty}
    {arms : List (Pattern F × Expr F)} {bindings : Environment F} {body : Expr F}
    (checked : checkArms program caller locals value.type type arms = .ok ())
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
          rw [patternTypes_bindings (checkPattern_types patternRun) matched]
          exact branchRun

/-- A call premise has the result shape of the function it names. -/
def CallsTyped (program : Program F) (calls : CallRelation F) : Prop :=
  ∀ name args result, calls name args result →
    ∀ fn, program.findFunction? name = some fn → result.type = fn.result

private theorem checked_functions (program : Program F) (fns : List (Function F))
    (checked : (do
      for fn in fns do
        if let some name := findDuplicate (fn.params.map Prod.fst) [] then
          throw (.duplicateParameter fn.name name)
        requireType fn.name fn.result (← inferType program fn.name fn.params fn.body)
      : Except CheckError Unit) = .ok ()) :
    ∀ fn ∈ fns, inferType program fn.name fn.params fn.body = .ok fn.result := by
  induction fns with
  | nil => simp
  | cons fn fns ih =>
      cases duplicate : findDuplicate (fn.params.map Prod.fst) [] with
      | some name => simp [List.forIn_cons, duplicate, bind, Except.bind] at checked
      | none =>
          cases inferred : inferType program fn.name fn.params fn.body with
          | error error => simp [List.forIn_cons, duplicate, inferred, bind, Except.bind, pure, Except.pure] at checked
          | ok type =>
              by_cases same : fn.result = type
              · subst type
                simp only [List.forIn_cons, duplicate, inferred, requireType, ↓reduceIte,
                  bind, Except.bind, pure, Except.pure] at checked
                intro next member
                rcases List.mem_cons.mp member with rfl | member
                · exact inferred
                · exact ih checked next member
              · simp [List.forIn_cons, duplicate, inferred, requireType, same,
                  bind, Except.bind, pure, Except.pure] at checked

theorem typecheck_function {program : Program F} (checked : typecheck program = .ok ())
    {fn : Function F} (member : fn ∈ program.functions) :
    inferType program fn.name fn.params fn.body = .ok fn.result := by
  unfold typecheck at checked
  split at checked
  · cases checked
  · simp only [pure_bind] at checked
    exact checked_functions program program.functions checked fn member

/-- Successful evaluation preserves inferred tuple shape when call premises have their declared shapes. -/
theorem EvalExprWith.type [Field F] [DecidableEq F] {program : Program F} {calls : CallRelation F}
    (typed : CallsTyped program calls) {locals : Environment F} {expr : Expr F} {result : Value F}
    (evaluated : EvalExprWith calls locals expr result) :
    ∀ caller type, inferType program caller (environmentTypes locals) expr = .ok type → result.type = type := by
  induction evaluated using EvalExprWith.rec
    (motive_2 := fun locals exprs values _ => ∀ caller types,
      inferTypes program caller (environmentTypes locals) exprs = .ok types → values.map Value.type = types) with
  | literal =>
      intro caller type checked
      simpa [inferType, Value.type, pure, Except.pure] using checked
  | var lookup =>
      intro caller type checked
      simpa [inferType, environmentTypes, List.find?_map, Function.comp_def, lookup,
        pure, Except.pure] using checked
  | tuple _ ih =>
      intro caller type checked
      simp only [inferType] at checked
      obtain ⟨types, itemsRun, finished⟩ := except_bind_ok.mp checked
      obtain rfl := except_pure_ok.mp finished
      simp [Value.type, ih caller types itemsRun]
  | @project locals expr input index result _ projected ih =>
      intro caller type checked
      simp only [inferType] at checked
      obtain ⟨inputType, inputRun, rest⟩ := except_bind_ok.mp checked
      have inputShape := ih caller inputType inputRun
      cases input with
      | field => cases projected
      | tuple values =>
          simp only [Value.type] at inputShape
          subst inputType
          cases found : (values.map Value.type)[index]? with
          | none => simp [found] at rest
          | some itemType =>
              simp only [found, except_pure_ok] at rest
              subst type
              cases source : values[index]? with
              | none => simp [projectValue, source] at projected
              | some value =>
                  simp [projectValue, source, pure, Except.pure] at projected
                  subst result
                  simpa [List.getElem?_map, source] using found
  | letValue _ matched _ valueIH bodyIH =>
      intro caller type checked
      simp only [inferType] at checked
      obtain ⟨valueType, valueRun, rest⟩ := except_bind_ok.mp checked
      obtain ⟨bindingTypes, patternRun, rest⟩ := except_bind_ok.mp rest
      split at rest
      · cases rest
      · simp only [pure_bind] at rest
        have shape := valueIH caller valueType valueRun
        have bindings := patternTypes_bindings (caller := caller)
          (by rw [shape]; exact checkPattern_types patternRun) matched
        exact bodyIH caller type (by simpa only [environmentTypes_append, bindings] using rest)
  | @neg locals expr input result _ operation ih =>
      intro caller type checked
      simp only [inferType] at checked
      obtain ⟨inputType, _, rest⟩ := except_bind_ok.mp checked
      obtain ⟨finished, _, rest⟩ := except_bind_ok.mp rest
      obtain rfl := except_pure_ok.mp rest
      cases input with
      | field x => cases operation; simp [Value.type]
      | tuple => cases operation
  | @binary locals lhs x rhs y op result _ _ operation leftIH rightIH =>
      intro caller type checked
      simp only [inferType] at checked
      obtain ⟨leftType, _, rest⟩ := except_bind_ok.mp checked
      obtain ⟨finished, _, rest⟩ := except_bind_ok.mp rest
      obtain ⟨rightType, _, rest⟩ := except_bind_ok.mp rest
      obtain ⟨finished, _, rest⟩ := except_bind_ok.mp rest
      obtain rfl := except_pure_ok.mp rest
      cases x with
      | tuple => cases operation
      | field x =>
          cases y with
          | tuple => cases operation
          | field y =>
              cases op <;> simp only [evalBinOp] at operation
              all_goals first
                | (split at operation <;> cases operation; simp [Value.type])
                | (cases operation; simp [Value.type])
  | @call locals args values name result _ callee ih =>
      intro caller type checked
      cases found : program.findFunction? name with
      | none => simp [inferType, found] at checked
      | some fn =>
          simp only [inferType, found] at checked
          split at checked
          · cases checked
          · simp only [pure_bind] at checked
            obtain ⟨types, _, rest⟩ := except_bind_ok.mp checked
            obtain ⟨finished, _, rest⟩ := except_bind_ok.mp rest
            obtain rfl := except_pure_ok.mp rest
            exact typed name values result callee fn found
  | @matchValue locals expr input arms bindings body result _ selected _ valueIH bodyIH =>
      intro caller type checked
      simp only [inferType] at checked
      obtain ⟨inputType, inputRun, rest⟩ := except_bind_ok.mp checked
      have shape := valueIH caller inputType inputRun
      cases arms with
      | nil => simp [selectArm] at selected
      | cons arm arms =>
          rcases arm with ⟨pattern, branch⟩
          obtain ⟨bindingTypes, patternRun, rest⟩ := except_bind_ok.mp rest
          obtain ⟨branchType, branchRun, rest⟩ := except_bind_ok.mp rest
          obtain ⟨finished, armsRun, rest⟩ := except_bind_ok.mp rest
          cases finished
          obtain rfl := except_pure_ok.mp rest
          have allChecked : checkArms program caller (environmentTypes locals) input.type branchType
              ((pattern, branch) :: arms) = .ok () := by
            rw [shape]
            simp [checkArms, patternRun, branchRun, requireType, armsRun, bind, Except.bind]
          exact bodyIH caller branchType (by
            simpa only [environmentTypes_append] using checkArms_selected allChecked selected)
  | nil =>
      rename_i caller types checked
      simpa [inferTypes, pure, Except.pure] using checked
  | cons _ _ headIH tailIH =>
      rename_i caller types checked
      simp only [inferTypes] at checked
      obtain ⟨headType, headRun, rest⟩ := except_bind_ok.mp checked
      obtain ⟨tailTypes, tailRun, rest⟩ := except_bind_ok.mp rest
      obtain rfl := except_pure_ok.mp rest
      simp [headIH caller headType headRun, tailIH caller tailTypes tailRun]

end Aiur.Tuple
