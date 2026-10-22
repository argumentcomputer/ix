import Aiur.Runtime

namespace Aiur

abbrev Evaluation (F : Type) := StateT (Heap F) (Except EvalError)

/-- Eager evaluation threads the allocation heap through operands and internal calls. -/
def evalExprWith [Field F] [DecidableEq F] (program : Program F) (hints : HintProvider F program.enums)
    (locals : Environment F Nat) : Nat → Expr F → Evaluation F (SourceValue F)
  | 0, _ => throw .outOfFuel
  | fuel + 1, expr => do
      match expr with
      | .literal value => return .field value
      | .var name =>
          let some (_, value) := locals.find? (·.1 == name) | throw (.unboundVariable name)
          return value
      | .tuple items => return .tuple (← items.mapM (evalExprWith program hints locals fuel))
      | .construct name ctor args =>
          return .construct name ctor (← args.mapM (evalExprWith program hints locals fuel))
      | .project value index => liftM (projectValue (← evalExprWith program hints locals fuel value) index)
      | .letValue pattern value body =>
          let value ← evalExprWith program hints locals fuel value
          let some bindings := pattern.bindings value | throw .patternMismatch
          evalExprWith program hints (bindings ++ locals) fuel body
      | .store value =>
          let value ← evalExprWith program hints locals fuel value
          let heap ← get
          set (heap ++ [value])
          return .ptr value.type heap.length
      | .load pointer =>
          let pointer ← evalExprWith program hints locals fuel pointer
          liftM (loadValue (← get) pointer)
      | .hint type key channel =>
          let key ← evalExprWith program hints locals fuel key
          let value ← liftM ((hints channel key type).mapError EvalError.hint)
          return value.val.toValue
      | .neg value => liftM (evalNeg (← evalExprWith program hints locals fuel value))
      | .assertEq op left right =>
          liftM (evalAssertEq op (← evalExprWith program hints locals fuel left) (← evalExprWith program hints locals fuel right))
      | .binary op left right =>
          liftM (evalBinOp op (← evalExprWith program hints locals fuel left) (← evalExprWith program hints locals fuel right))
      | .call name args =>
          let values ← args.mapM (evalExprWith program hints locals fuel)
          let (bindings, body) ← liftM (prepareCall program name values)
          evalExprWith program hints bindings fuel body
      | .matchValue scrutinee arms =>
          let value ← evalExprWith program hints locals fuel scrutinee
          let some (bindings, body) := selectArm value arms | throw .noMatchingArm
          evalExprWith program hints (bindings ++ locals) fuel body

/-- The original evaluator uses a provider that reports unavailable hints. -/
abbrev evalExpr [Field F] [DecidableEq F] (program : Program F)
    (locals : Environment F Nat) (fuel : Nat) (expr : Expr F) : Evaluation F (SourceValue F) :=
  evalExprWith program HintProvider.unavailable locals fuel expr

/-- Entry calls start with an empty heap and require entirely pointer-free argument types. -/
def run [Field F] [DecidableEq F] (program : Program F) (name : String)
    (args : List (SourceValue F)) (fuel : Nat := 1000)
    (hints : HintProvider F program.enums := HintProvider.unavailable) : Except EvalError (SourceValue F × Heap F) := do
  match typecheck program with
  | .error error => throw (.invalidProgram error)
  | .ok () => pure ()
  checkEntry program name
  let (bindings, body) ← prepareCall program name args
  evalExprWith program hints bindings fuel body []

/-- Return the program result; `run` also exposes its heap for inspecting pointer results. -/
def eval [Field F] [DecidableEq F] (program : Program F) (name : String)
    (args : List (SourceValue F)) (fuel : Nat := 1000)
    (hints : HintProvider F program.enums := HintProvider.unavailable) : Except EvalError (SourceValue F) :=
  (run program name args fuel hints).map Prod.fst

end Aiur
