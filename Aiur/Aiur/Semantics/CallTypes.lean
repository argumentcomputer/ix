import Aiur.Semantics.CallFacts
import Aiur.ExceptFacts

namespace Aiur

variable {F : Type} {rom : ROM F}

theorem checked_arguments_types (decls : Declarations) (name : String) (params : List (String × Ty))
    (args : List (Value F A)) (arity : params.length = args.length)
    (checked : (forIn (params.zip args) PUnit.unit (fun pair _ =>
      if pair.1.2 ≠ pair.2.type then Except.error (.argumentTypeMismatch name pair.1.2 pair.2.type)
      else if !pair.2.wellFormed decls then Except.error (.malformedValue pair.2.type)
      else Except.ok (ForInStep.yield PUnit.unit))
      : Except EvalError PUnit) = .ok PUnit.unit) :
    params.map Prod.snd = args.map Value.type ∧ (∀ arg ∈ args, arg.wellFormed decls = true) := by
  induction params generalizing args with
  | nil =>
      cases args <;> simp_all
  | cons param params ih =>
      cases args with
      | nil => simp at arity
      | cons arg args =>
          have restArity : params.length = args.length := by simpa using arity
          by_cases same : param.2 = arg.type
          · cases formed : arg.wellFormed decls with
            | false => simp [List.zip_cons_cons, List.forIn_cons, same, formed, bind, Except.bind] at checked
            | true =>
                simp [List.zip_cons_cons, List.forIn_cons, same, formed, bind, Except.bind] at checked
                obtain ⟨types, forms⟩ := ih args restArity (by simpa using checked)
                exact ⟨by simp [same, types], by simpa [formed] using forms⟩
          · simp [List.zip_cons_cons, List.forIn_cons, same, bind, Except.bind] at checked

/-- A prepared call selects a typed function body or a successfully looked-up constant. -/
theorem prepareCall_spec [DecidableEq F] {program : Program F} {name : String} {args : List (Value F A)}
    {locals : Environment F A} {body : Expr F}
    (prepared : prepareCall program name args = .ok (locals, body)) :
    (∃ fn, program.findFunction? name = some fn ∧ fn.params.map Prod.snd = args.map Value.type ∧
      (∀ arg ∈ args, arg.wellFormed program.enums = true) ∧
      locals = (fn.params.map Prod.fst).zip args ∧ body = fn.body) ∨
    (∃ value, program.findFunction? name = none ∧ lookupMap program name args = .ok value ∧
      locals = [] ∧ body = value.toExpr) := by
  cases found : program.findFunction? name with
  | none =>
      right
      simp only [prepareCall, found] at prepared
      obtain ⟨value, lookup, finished⟩ := except_bind_ok.mp prepared
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (except_pure_ok.mp finished)
      exact ⟨value, rfl, lookup, rfl, rfl⟩
  | some fn =>
      left
      by_cases arity : fn.params.length = args.length
      · simp only [prepareCall, found, arity, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
          pure_bind] at prepared
        obtain ⟨done, checked, finished⟩ := except_bind_ok.mp prepared
        cases done
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (except_pure_ok.mp finished)
        have spec := checked_arguments_types program.enums name fn.params args arity (by
          simpa [bind, Except.bind, pure, Except.pure] using checked)
        exact ⟨fn, rfl, spec.1, spec.2, rfl, rfl⟩
      · simp [prepareCall, found, arity, bind, Except.bind] at prepared

end Aiur
