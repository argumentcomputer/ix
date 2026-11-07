import Aiur.Generic.Elaborate
import Aiur.Generic.SourceEvalFacts
import Aiur.Generic.PatternChecks

namespace Aiur.Generic

def wellFormed (enums : String → Option Aiur.EnumDecl) : Value F A → Bool
  | .field _ | .ptr _ _ => true
  | .tuple xs => (xs.map (wellFormed enums)).all id
  | .construct n c xs =>
      match enums n >>= (fun d => d.constructors.find? (·.name == c)) with
      | none => false
      | some ctor => decide (xs.map Value.type = ctor.fields) && (xs.map (wellFormed enums)).all id
termination_by v => sizeOf v

def hasType (enums : String → Option Aiur.EnumDecl) (t : Aiur.Ty) (v : Value F A) : Bool :=
  decide (v.type = t) && wellFormed enums v

def constantOfExpr : Aiur.Expr α → Except String (Constant α)
  | .literal x => pure (.field x)
  | .tuple xs => return .tuple (← xs.mapM constantOfExpr)
  | .construct n c xs => return .construct n c (← xs.mapM constantOfExpr)
  | _ => throw "table rows must be constant literals, tuples, or constructors"
termination_by e => sizeOf e

/-- Static array repeats copy a checked constant. No execution, allocation, or
hinting is performed while constructing precommitted table rows. -/
def constantOfSource : Expr α → Except String (Constant α)
  | .literal x => pure (.field x)
  | .tuple xs | .array xs => return .tuple (← xs.mapM constantOfSource)
  | .repeat x n => do
      checkArrayLength n
      return .tuple (List.replicate n (← constantOfSource x))
  | .record head xs => return .construct (StructLowering.nominalName [] head.type) structConstructor (head.order (← xs.mapM constantOfSource) (.tuple []))
  | .construct n ts c xs =>
      return .construct (Instance.symbol ⟨n, ts.getD []⟩) c (← xs.mapM constantOfSource)
  | _ => throw "table rows must be constant literals, tuples, arrays, or constructors"
termination_by e => sizeOf e

def staticProgram (p : Program α) : Except String (Aiur.Program α) := do
  let tables ← p.tables.mapM fun t => do
    let rows ← t.rows.mapM constantOfSource
    return { name := t.name, rowType := t.rowType.toCore, rows : Aiur.Table α }
  let maps := p.maps.map fun m => {
    name := m.name, params := m.params.map fun (n, t) => (n, t.toCore)
    result := m.result.toCore, input := m.input, output := m.output : Aiur.MapDecl }
  let enums ← collectEnums p [] 1024 []
    ((tables.flatMap fun t => coreTypeNames t.rowType) ++
      (maps.flatMap fun m => (m.params.map Prod.snd ++ [m.result]).flatMap coreTypeNames))
  return { functions := [], enums, tables, maps }

/-- Checked source plus its static tables. Generic functions remain templates;
there is no entrypoint choice or function-instance cache here. -/
structure Source (F : Type) [DecidableEq F] where
  program : Program F
  tables : Aiur.Program F
  tablesChecked : typecheck tables = .ok ()

def prepare [DecidableEq F] (p : Program F) : Except String (Source F) := do
  let p ← elaborate p
  for fn in p.functions do checkLoadPatterns p fn.name fn.body
  let staticSource ← prepareTemplates { p with functions := [] }
  let tables ← staticProgram staticSource
  if checked : typecheck tables = .ok () then return ⟨p, tables, checked⟩
  else match typecheck tables with
    | .error e => throw (toString e)
    | .ok _ => throw "invalid static tables"


def Source.checkEntry [DecidableEq F] (s : Source F) (name : String) : Except String Unit := do
  let some fn := s.program.findFunction? name | throw s!"unknown entrypoint '{name}'"
  if fn.isInline then throw s!"inline function '{name}' cannot be an entrypoint"
  if !fn.typeParams.isEmpty then throw s!"entrypoint '{name}' must be non-generic"
  (fn.params.map Prod.snd).forM (checkPointerFree s.program s!"entrypoint '{name}'" 1024 [])
  let fn : Aiur.Function F := {
    name, params := fn.params.map fun (n, t) => (n, t.toCore)
    result := fn.result.toCore, body := .tuple [] }
  let enums ← collectEnums s.program [] 1024 [] ((fn.params.map Prod.snd).flatMap coreTypeNames)
  (Aiur.checkEntry ({ functions := [fn], enums } : Aiur.Program F) name).mapError (fun e => reprStr e)

/-- A closed function instance retains the source body and its type environment.
This is a runtime closure for a first-order function, not a function value in Aiur. -/
structure SourceFunction (F : Type) where
  types : SourceSemantics.Types
  params : List (String × Aiur.Ty)
  body : Expr F

def Program.sourceFunction? (p : Program F) (name : String) : Option (SourceFunction F) := do
  let key ← (Instance.ofSymbol name).toOption
  let fn ← p.findFunction? key.name
  let types ← (arguments fn.typeParams key.types).toOption
  return { types, params := fn.params.map fun (n, t) => (n, (t.subst types).toCore), body := fn.body }

def SourceFunction.prepare (enums : String → Option Aiur.EnumDecl) (fn : SourceFunction F)
    (args : List (SourceValue F)) : Except EvalError (SourceSemantics.Types × Environment F Nat × Expr F) :=
  if fn.params.map Prod.snd = args.map Value.type ∧ (args.map (wellFormed enums)).all id = true then
    .ok (fn.types, (fn.params.map Prod.fst).zip args, fn.body)
  else .error (.malformedValue (.tuple (args.map Value.type)))

def constantExpr : Constant F → Expr F
  | .field x => .literal x
  | .tuple xs => .tuple (xs.map constantExpr)
  | .construct n c xs => .construct n (some []) c (xs.map constantExpr)
  | .ptr _ a => Empty.elim a
termination_by v => sizeOf v

/-- Ordinary calls resolve the original body without rewriting it. The finite
specialized runtime uses this same operation with a cached function lookup. -/
def sourceWorld [DecidableEq F] (s : Source F)
    (functions : String → Option (SourceFunction F)) : SourceSemantics.World F where
  prepare name args := match functions name with
    | some fn => fn.prepare s.program.enum? args
    | none => return ([], [], constantExpr (← lookupMap s.tables name args))
  typed t v := hasType s.program.enum? t v
  constant name t := (elaborateConst s.program name t).mapError
    (fun _ => EvalError.unboundVariable ("::" ++ name))
  constDepth := s.program.consts.length + 1

def Source.world [DecidableEq F] (s : Source F) : SourceSemantics.World F :=
  sourceWorld s s.program.sourceFunction?

abbrev Source.HintProvider [DecidableEq F] (s : Source F) := SourceSemantics.HintProvider s.world

def Source.checkedHints [DecidableEq F] (s : Source F)
    (dispatcher : HintDispatcher F) : s.HintProvider := fun channel key t => do
  let v ← dispatcher.provide channel key
  if typed : s.world.typed t v = true then return ⟨v, typed⟩
  else throw (.invalidValue t v.type)

def Source.run [Field F] [DecidableEq F] (s : Source F) (name : String)
    (args : List (SourceValue F)) (fuel : Nat := 1000)
    (hints : s.HintProvider := SourceSemantics.unavailable) : Except String (SourceValue F × Heap F) := do
  s.checkEntry name
  let (types, locals, body) ← (s.world.prepare name args).mapError reprStr
  (SourceSemantics.evalFunctionWith s.world hints types locals fuel body []).mapError reprStr

def Source.EvalCall [Field F] [DecidableEq F] (s : Source F) (name : String)
    (args : List (SourceValue F)) (result : SourceValue F) : Prop :=
  s.checkEntry name = .ok () ∧ ∃ heap, SourceSemantics.EvalFn s.world name args [] result heap

/-- Successful execution implies the independent, fuel-free source relation.
The statement does not mention specialization or expression lowering. -/
theorem Source.run_spec [Field F] [DecidableEq F] {s : Source F}
    {hints : s.HintProvider} {name args fuel result heap}
    (run : s.run name args fuel hints = .ok (result, heap)) :
    s.checkEntry name = .ok () ∧ SourceSemantics.EvalFn s.world name args [] result heap := by
  cases entry : s.checkEntry name with
  | error e => simp [Source.run, entry, bind, Except.bind] at run
  | ok u =>
      cases u
      cases prepared : s.world.prepare name args with
      | error e => simp [Source.run, entry, prepared, Except.mapError, bind, Except.bind] at run
      | ok triple =>
          rcases triple with ⟨types, locals, body⟩
          have executed : SourceSemantics.evalFunctionWith s.world hints types locals fuel body [] = .ok (result, heap) := by
            cases h : SourceSemantics.evalFunctionWith s.world hints types locals fuel body [] <;>
              simpa [Source.run, entry, prepared, h, Except.mapError, bind, Except.bind] using run
          exact ⟨rfl, SourceSemantics.evalFunction_spec prepared executed⟩

end Aiur.Generic
