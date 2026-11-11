import Aiur.Generic.SourceSemantics

namespace Aiur.Generic.SourceSemantics

abbrev Outcome (F : Type) := Except (ExitTarget × SourceValue F) (SourceValue F)

/-- The control effect is above the heap state: leaving a scope retains every
allocation already performed, while skipping the rest of its computation. -/
abbrev FlowEvaluation (F : Type) := ExceptT (ExitTarget × SourceValue F) (Evaluation F)

def Outcome.catch (target : ExitTarget) : Outcome F → Outcome F
  | .ok value => .ok value
  | .error (actual, value) =>
      if actual = target then .ok value else .error (actual, value)

def flowError (error : EvalError) : FlowEvaluation F A :=
  ExceptT.mk (throw error)

def catchExit (target : ExitTarget) (body : FlowEvaluation F (SourceValue F)) :
    FlowEvaluation F (SourceValue F) := ExceptT.mk do
  return Outcome.catch target (← body.run)

def finishFunction (body : FlowEvaluation F (SourceValue F)) : Evaluation F (SourceValue F) := do
  match ← (catchExit .function body).run with
  | .ok value => return value
  | .error (target, _) => throw (.unhandledExit (reprStr target))

def finishExpression (body : FlowEvaluation F (SourceValue F)) : Evaluation F (SourceValue F) := do
  match ← body.run with
  | .ok value => return value
  | .error (target, _) => throw (.unhandledExit (reprStr target))

/-- Direct source execution. Neither exit propagation nor catching a block
invokes a source rewriting or circuit preparation pass. -/
def evalOutcomeWith [Field F] [DecidableEq F] (world : World F) (hints : HintProvider world)
    (types : Types) (locals : Environment F Nat) : Nat → Expr F → FlowEvaluation F (SourceValue F)
  | 0, _ => flowError .outOfFuel
  | fuel + 1, expr => do
      match expr with
      | .control (.block label) body =>
          catchExit (.block label) (evalOutcomeWith world hints types locals fuel body)
      | .control (.exit target) value =>
          let value ← evalOutcomeWith world hints types locals fuel value
          throw (target, value)
      | .literal x => return .field x
      | .var name =>
          let some (_, value) := locals.find? (·.1 == name) | flowError (.unboundVariable name)
          return value
      | .global name annotation =>
          let some type := annotation | flowError (.unboundVariable ("::" ++ name))
          let pattern ← liftM (world.constant name (type.subst types))
          let body ← liftM ((Consts.toExpr pattern).mapError (fun _ => EvalError.unboundVariable ("::" ++ name)))
          evalOutcomeWith world hints [] [] fuel body
      | .tuple items | .array items => return .tuple (← items.mapM (evalOutcomeWith world hints types locals fuel))
      | .repeat value n => return .tuple (List.replicate n (← evalOutcomeWith world hints types locals fuel value))
      | .index value i | .project value i => liftM (projectValue (← evalOutcomeWith world hints types locals fuel value) i)
      | .slice value start stop => liftM (sliceValue (← evalOutcomeWith world hints types locals fuel value) start stop)
      | .builtin op items =>
          liftM (op.apply (← items.mapM (evalOutcomeWith world hints types locals fuel)))
      | .update paths items =>
          liftM (Update.value types paths (← items.mapM (evalOutcomeWith world hints types locals fuel)))
      | .record head items =>
          let values ← items.mapM (evalOutcomeWith world hints types locals fuel)
          return .construct (constructorName types head.type) structConstructor (head.order values (.tuple []))
      | .member value field => liftM (memberValue types field (← evalOutcomeWith world hints types locals fuel value))
      | .construct name args ctor items =>
          return .construct (instanceName types name args) ctor (← items.mapM (evalOutcomeWith world hints types locals fuel))
      | .constructAs _ t ctor items =>
          return .construct (constructorName types t) ctor (← items.mapM (evalOutcomeWith world hints types locals fuel))
      | .letValue pattern value body =>
          let value ← evalOutcomeWith world hints types locals fuel value
          let some bindings ← liftM (world.matchPattern types (← get) pattern value) | flowError .patternMismatch
          evalOutcomeWith world hints types (bindings ++ locals) fuel body
      | .store value =>
          let value ← evalOutcomeWith world hints types locals fuel value
          let heap ← get
          set (heap ++ [value])
          return .ptr value.type heap.length
      | .load pointer =>
          let pointer ← evalOutcomeWith world hints types locals fuel pointer
          liftM (loadValue (← get) pointer)
      | .hint t key channel =>
          let key ← evalOutcomeWith world hints types locals fuel key
          let value ← liftM ((hints channel key (t.subst types).toCore).mapError EvalError.hint)
          return value.val.toValue
      | .neg value => liftM (evalNeg (← evalOutcomeWith world hints types locals fuel value))
      | .binary op left right =>
          liftM (evalBinOp op (← evalOutcomeWith world hints types locals fuel left)
            (← evalOutcomeWith world hints types locals fuel right))
      | .call name args inputs =>
          let values ← inputs.mapM (evalOutcomeWith world hints types locals fuel)
          let (calleeTypes, bindings, body) ← liftM (world.prepare (instanceName types name args) values)
          liftM (finishFunction (evalOutcomeWith world hints calleeTypes bindings fuel body))
      | .matchValue scrutinee arms =>
          let value ← evalOutcomeWith world hints types locals fuel scrutinee
          let some (bindings, body) ← liftM (selectArm world types (← get) value arms) | flowError .noMatchingArm
          evalOutcomeWith world hints types (bindings ++ locals) fuel body

/-- Execute a function body, handling its own return and rejecting an uncaught
block exit in an unchecked AST. The checker prevents the latter. -/
def evalFunctionWith [Field F] [DecidableEq F] (world : World F) (hints : HintProvider world)
    (types : Types) (locals : Environment F Nat) (fuel : Nat) (expr : Expr F) : Evaluation F (SourceValue F) :=
  finishFunction (evalOutcomeWith world hints types locals fuel expr)

def evalExprWith [Field F] [DecidableEq F] (world : World F) (hints : HintProvider world)
    (types : Types) (locals : Environment F Nat) (fuel : Nat) (expr : Expr F) : Evaluation F (SourceValue F) :=
  finishExpression (evalOutcomeWith world hints types locals fuel expr)

end Aiur.Generic.SourceSemantics
