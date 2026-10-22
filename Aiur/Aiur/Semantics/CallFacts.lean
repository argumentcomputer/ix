import Aiur.Semantics.WithCalls
import Aiur.ValueFacts
import Aiur.ExceptFacts

namespace Aiur

variable {F : Type} {rom : ROM F}

theorem checked_arguments (decls : Declarations) (name : String) (params : List (String × Ty))
    (args : List (Value F A)) (types : params.map Prod.snd = args.map Value.type)
    (formed : ∀ arg ∈ args, arg.wellFormed decls = true) :
    (do
      for (param, arg) in params.zip args do
        if param.2 ≠ arg.type then throw (.argumentTypeMismatch name param.2 arg.type)
        if !arg.wellFormed decls then throw (.malformedValue arg.type)
      pure () : Except EvalError Unit) = .ok () := by
  induction params generalizing args with
  | nil => cases args <;> simp_all [pure, Except.pure, bind, Except.bind]
  | cons param params ih =>
      cases args with
      | nil => simp at types
      | cons arg args =>
          simp only [List.map_cons, List.cons.injEq] at types
          simp only [List.zip_cons_cons, List.forIn_cons]
          simp [types.1, formed arg (by simp), bind, Except.bind, pure, Except.pure] at ih ⊢
          exact ih args types.2 (fun v h => formed v (by simp [h]))

/-- Structural argument types are exactly the shape check performed at a source call. -/
theorem prepareCall_of_types [DecidableEq F] {program : Program F} {name : String} {fn : Function F}
    {args : List (Value F A)} (found : program.findFunction? name = some fn)
    (types : fn.params.map Prod.snd = args.map Value.type)
    (formed : ∀ arg ∈ args, arg.wellFormed program.enums = true) :
    prepareCall program name args = .ok ((fn.params.map Prod.fst).zip args, fn.body) := by
  have arity : fn.params.length = args.length := by
    simpa using congrArg List.length types
  simp only [prepareCall, found, arity, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  have checked := checked_arguments program.enums name fn.params args types formed
  have combined := congrArg (fun result => result >>= fun _ =>
    (Except.ok ((fn.params.map Prod.fst).zip args, fn.body) : Except EvalError _)) checked
  simp only [bind_assoc, pure_bind] at combined
  simpa only [bind, Except.bind, pure, Except.pure] using combined

end Aiur
