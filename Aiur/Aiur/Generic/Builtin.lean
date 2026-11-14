import Aiur.Generic.AST
import Aiur.Runtime

namespace Aiur.Generic

/-- Type annotations have no runtime test. Debug output is executor-only;
evaluating its arguments is part of the ordinary source semantics. -/
def Builtin.apply [DecidableEq F] (op : Builtin) (values : List (SourceValue F)) : Except EvalError (SourceValue F) :=
  match op with
  | .ascribe _ => match values with
    | [value] => .ok value
    | _ => .error (.arityMismatch "type annotation" 1 values.length)
  | .debug _ => .ok (.tuple [])
  | .assertEq message => match values with
    | [left, right] => evalAssertEq message left right
    | _ => .error (.arityMismatch "assert_eq!" 2 values.length)

@[simp] theorem Builtin.apply_subst [DecidableEq F] (op : Builtin) (types) (values : List (SourceValue F)) :
    (op.subst types).apply values = op.apply values := by cases op <;> rfl

end Aiur.Generic
