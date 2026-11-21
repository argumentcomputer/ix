import Aiur.Generic.ControlEval

namespace Aiur.Generic

/-- Diagnostic values are observed, never fed back into Aiur computation. A
missing leave event identifies the active call stack when execution fails. -/
inductive TraceEvent (F : Type) where
  | message (text : String) (values : List (SourceValue F))
  | enter (function : String) (arguments : List (SourceValue F))
  | leave (function : String) (result : SourceValue F)
  deriving Repr, BEq

namespace Traced
open SourceSemantics

/-- Trace state is below failure, so earlier messages survive a failed load,
assertion, hint, or fuel limit. Entries are accumulated in reverse order. -/
abbrev Eval (F : Type) := StateT (Heap F) (ExceptT EvalError (StateM (List (TraceEvent F))))
abbrev Flow (F : Type) := ExceptT (ExitTarget × SourceValue F) (Eval F)

def emit (event : TraceEvent F) : Flow F Unit :=
  fun heap events => (.ok (.ok (), heap), event :: events)

def error (err : EvalError) : Flow F A := ExceptT.mk (throw err)

def catchExit (target : ExitTarget) (body : Flow F (SourceValue F)) : Flow F (SourceValue F) := ExceptT.mk do
  return Outcome.catch target (← body.run)

def finishFunction (body : Flow F (SourceValue F)) : Eval F (SourceValue F) := do
  match ← (catchExit .function body).run with
  | .ok value => return value
  | .error (target, _) => throw (.unhandledExit (reprStr target))

def evalWithTrace [Field F] [DecidableEq F] (world : World F) (hints : SourceSemantics.HintProvider world)
    (types : Types) (locals : Environment F Nat) : Nat → Expr F → Flow F (SourceValue F)
  | 0, _ => error .outOfFuel
  | fuel + 1, expr => do
      match expr with
      | .control (.block label) body =>
          catchExit (.block label) (evalWithTrace world hints types locals fuel body)
      | .control (.exit target) value =>
          let value ← evalWithTrace world hints types locals fuel value
          throw (target, value)
      | .literal x => return .field x
      | .var name =>
          let some (_, value) := locals.find? (·.1 == name) | error (.unboundVariable name)
          return value
      | .global name annotation =>
          let some type := annotation | error (.unboundVariable ("::" ++ name))
          let pattern ← liftM (world.constant name (type.subst types))
          let body ← liftM ((Consts.toExpr pattern).mapError (fun _ => EvalError.unboundVariable ("::" ++ name)))
          evalWithTrace world hints [] [] fuel body
      | .tuple items | .array items => return .tuple (← items.mapM (evalWithTrace world hints types locals fuel))
      | .repeat value n => return .tuple (List.replicate n (← evalWithTrace world hints types locals fuel value))
      | .index value i | .project value i => liftM (projectValue (← evalWithTrace world hints types locals fuel value) i)
      | .slice value start stop => liftM (sliceValue (← evalWithTrace world hints types locals fuel value) start stop)
      | .builtin op items =>
          let values ← items.mapM (evalWithTrace world hints types locals fuel)
          if let .debug message := op then emit (.message message values)
          liftM (op.apply values)
      | .update paths items =>
          liftM (Update.value types paths (← items.mapM (evalWithTrace world hints types locals fuel)))
      | .record head items =>
          let values ← items.mapM (evalWithTrace world hints types locals fuel)
          return .construct (constructorName types head.type) structConstructor (head.order values (.tuple []))
      | .member value field => liftM (memberValue types field (← evalWithTrace world hints types locals fuel value))
      | .construct name args ctor items =>
          return .construct (instanceName types name args) ctor (← items.mapM (evalWithTrace world hints types locals fuel))
      | .constructAs _ t ctor items =>
          return .construct (constructorName types t) ctor (← items.mapM (evalWithTrace world hints types locals fuel))
      | .letValue pattern value body =>
          let value ← evalWithTrace world hints types locals fuel value
          let some bindings ← liftM (world.matchPattern types (← get) pattern value) | error .patternMismatch
          evalWithTrace world hints types (bindings ++ locals) fuel body
      | .store value =>
          let value ← evalWithTrace world hints types locals fuel value
          let heap ← get
          set (heap ++ [value])
          return .ptr value.type heap.length
      | .load pointer =>
          let pointer ← evalWithTrace world hints types locals fuel pointer
          liftM (loadValue (← get) pointer)
      | .hint t key channel =>
          let key ← evalWithTrace world hints types locals fuel key
          let value ← liftM ((hints channel key (t.subst types).toCore).mapError EvalError.hint)
          return value.val.toValue
      | .neg value => liftM (evalNeg (← evalWithTrace world hints types locals fuel value))
      | .binary op left right =>
          liftM (evalBinOp op (← evalWithTrace world hints types locals fuel left)
            (← evalWithTrace world hints types locals fuel right))
      | .call name args inputs =>
          let values ← inputs.mapM (evalWithTrace world hints types locals fuel)
          let callee := instanceName types name args
          emit (.enter callee values)
          let (calleeTypes, bindings, body) ← liftM (world.prepare callee values)
          let result ← liftM (finishFunction (evalWithTrace world hints calleeTypes bindings fuel body))
          emit (.leave callee result)
          return result
      | .matchValue scrutinee arms =>
          let value ← evalWithTrace world hints types locals fuel scrutinee
          let some (bindings, body) ← liftM (SourceSemantics.selectArm world types (← get) value arms) | error .noMatchingArm
          evalWithTrace world hints types (bindings ++ locals) fuel body

end Traced
end Aiur.Generic
