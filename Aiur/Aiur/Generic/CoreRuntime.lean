import Aiur.Generic.Preparation
import Aiur.Generic.Engine

/-! Reference execution of the lowered compiler language. These definitions
are separate from source evaluation; their correctness statements must not be
used as a replacement for a source-to-core lowering theorem. -/
namespace Aiur.Generic

def prepareFunction (enums : String → Option Aiur.EnumDecl) (fn : Aiur.Function F)
    (args : List (SourceValue F)) : Except EvalError (Environment F Nat × Aiur.Expr F) :=
  if fn.params.map Prod.snd = args.map Value.type ∧ (args.map (wellFormed enums)).all id = true then
    .ok ((fn.params.map Prod.fst).zip args, fn.body)
  else .error (.malformedValue (.tuple (args.map Value.type)))

def Source.coreWorld [DecidableEq F] (s : Source F) : Engine.World F where
  prepare name args := match s.compilerFunction? name with
    | some fn => prepareFunction s.program.enum? fn args
    | none => return ([], (← lookupMap s.tables name args).toExpr)
  typed t v := hasType s.program.enum? t v

abbrev Source.CoreHintProvider [DecidableEq F] (s : Source F) := Engine.HintProvider s.coreWorld

def Source.coreCheckedHints [DecidableEq F] (s : Source F)
    (dispatcher : HintDispatcher F) : s.CoreHintProvider := fun channel key t => do
  let v ← dispatcher.provide channel key
  if typed : s.coreWorld.typed t v = true then return ⟨v, typed⟩
  else throw (.invalidValue t v.type)

def Source.coreRun [Field F] [DecidableEq F] (s : Source F) (name : String)
    (args : List (SourceValue F)) (fuel : Nat := 1000)
    (hints : s.CoreHintProvider := Engine.unavailable) : Except String (SourceValue F × Heap F) := do
  s.checkEntry name
  let (locals, body) ← (s.coreWorld.prepare name args).mapError reprStr
  (Engine.evalExprWith s.coreWorld hints locals fuel body []).mapError reprStr

def Source.CoreEvalCall [Field F] [DecidableEq F] (s : Source F) (name : String)
    (args : List (SourceValue F)) (result : SourceValue F) : Prop :=
  s.checkEntry name = .ok () ∧ ∃ heap, Engine.EvalFn s.coreWorld name args [] result heap

/-- Successful execution of the lowered reference runtime has a core
relational evaluation with the same value and heap. -/
theorem Source.coreRun_spec [Field F] [DecidableEq F] {s : Source F}
    {hints : s.CoreHintProvider} {name args fuel result heap}
    (run : s.coreRun name args fuel hints = .ok (result, heap)) :
    s.checkEntry name = .ok () ∧ Engine.EvalFn s.coreWorld name args [] result heap := by
  cases entry : s.checkEntry name with
  | error e => simp [Source.coreRun, entry, bind, Except.bind] at run
  | ok u =>
      cases u
      cases prepared : s.coreWorld.prepare name args with
      | error e => simp [Source.coreRun, entry, prepared, Except.mapError, bind, Except.bind] at run
      | ok pair =>
          rcases pair with ⟨locals, body⟩
          have executed : Engine.evalExprWith s.coreWorld hints locals fuel body [] = .ok (result, heap) := by
            cases h : Engine.evalExprWith s.coreWorld hints locals fuel body [] <;>
              simpa [Source.coreRun, entry, prepared, h, Except.mapError, bind, Except.bind] using run
          exact ⟨rfl, .intro prepared (Engine.evalExpr_spec executed)⟩

end Aiur.Generic
