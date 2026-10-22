import Aiur.Tuple.Semantics.WithCalls
import Aiur.Tuple.ValueFacts

namespace Aiur.Tuple

private theorem checked_arguments (name : String) (params : List (String × Ty))
    (args : List (Value F)) (types : params.map Prod.snd = args.map Value.type) :
    (do
      for (param, arg) in params.zip args do
        if param.2 ≠ arg.type then throw (.argumentTypeMismatch name param.2 arg.type)
      pure () : Except EvalError Unit) = .ok () := by
  induction params generalizing args with
  | nil => cases args <;> simp_all [pure, Except.pure, bind, Except.bind]
  | cons param params ih =>
      cases args with
      | nil => simp at types
      | cons arg args =>
          simp only [List.map_cons, List.cons.injEq] at types
          simp only [List.zip_cons_cons, List.forIn_cons]
          simp [types.1, bind, Except.bind, pure, Except.pure] at ih ⊢
          exact ih args types.2

/-- Structural argument types are exactly the shape check performed at a source call. -/
theorem prepareCall_of_types {program : Program F} {name : String} {fn : Function F}
    {args : List (Value F)} (found : program.findFunction? name = some fn)
    (types : fn.params.map Prod.snd = args.map Value.type) :
    prepareCall program name args = .ok ((fn.params.map Prod.fst).zip args, fn.body) := by
  have arity : fn.params.length = args.length := by
    simpa using congrArg List.length types
  simp only [prepareCall, found, arity, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  have checked := checked_arguments name fn.params args types
  have combined := congrArg (fun result => result >>= fun _ =>
    (Except.ok ((fn.params.map Prod.fst).zip args, fn.body) : Except EvalError _)) checked
  simp only [bind_assoc, pure_bind] at combined
  simpa only [bind, Except.bind, pure, Except.pure] using combined

end Aiur.Tuple
