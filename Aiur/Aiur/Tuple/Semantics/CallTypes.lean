import Aiur.Tuple.Semantics.CallFacts
import Aiur.Tuple.TypecheckFacts

namespace Aiur.Tuple

private theorem checked_arguments_types (name : String) (params : List (String × Ty))
    (args : List (Value F)) (arity : params.length = args.length)
    (checked : (forIn (params.zip args) PUnit.unit (fun pair _ =>
      if pair.1.2 = pair.2.type then Except.ok (ForInStep.yield PUnit.unit)
      else Except.error (.argumentTypeMismatch name pair.1.2 pair.2.type))
      : Except EvalError PUnit) = .ok PUnit.unit) :
    params.map Prod.snd = args.map Value.type := by
  induction params generalizing args with
  | nil =>
      cases args <;> simp_all
  | cons param params ih =>
      cases args with
      | nil => simp at arity
      | cons arg args =>
          have restArity : params.length = args.length := by simpa using arity
          by_cases same : param.2 = arg.type
          · simp [List.zip_cons_cons, List.forIn_cons, same, bind, Except.bind] at checked
            simp [same, ih args restArity checked]
          · simp [List.zip_cons_cons, List.forIn_cons, same, bind, Except.bind] at checked

/-- Successful entry preparation supplies the declared argument shapes and exact body environment. -/
theorem prepareCall_spec {program : Program F} {name : String} {args : List (Value F)}
    {locals : Environment F} {body : Expr F}
    (prepared : prepareCall program name args = .ok (locals, body)) :
    ∃ fn, program.findFunction? name = some fn ∧ fn.params.map Prod.snd = args.map Value.type ∧
      locals = (fn.params.map Prod.fst).zip args ∧ body = fn.body := by
  cases found : program.findFunction? name with
  | none => simp [prepareCall, found] at prepared
  | some fn =>
      by_cases arity : fn.params.length = args.length
      · simp only [prepareCall, found, arity, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
          pure_bind] at prepared
        obtain ⟨done, checked, finished⟩ := except_bind_ok.mp prepared
        cases done
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (except_pure_ok.mp finished)
        exact ⟨fn, rfl, checked_arguments_types name fn.params args arity (by
          simpa [bind, Except.bind, pure, Except.pure] using checked), rfl, rfl⟩
      · simp [prepareCall, found, arity, bind, Except.bind] at prepared

end Aiur.Tuple
