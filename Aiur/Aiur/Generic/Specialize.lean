import Aiur.Generic.Preparation
import Aiur.Generic.Equality
import Aiur.Generic.ValueTyping
import Aiur.Generic.Simulation
import Aiur.Generic.SourceSimulation
import Aiur.Generic.LoweringTypes

namespace Aiur.Generic

def callableNames (p : Aiur.Program α) : List String := p.functions.map (·.name) ++ p.maps.map (·.name)

/-- Every condition is a finite syntactic/type check. In particular this does
not ask a validator to decide semantic equivalence. -/
def Valid [DecidableEq F] (s : Source F) (p : Aiur.Program F) (entries : List String) : Prop :=
  typecheck p = .ok () ∧
  p.tables = s.tables.tables ∧ p.maps = s.tables.maps ∧
  (∀ n ∈ callableNames p, s.compilerFunction? n = p.findFunction? n) ∧
  (∀ d ∈ p.enums, s.program.enum? d.name = some d) ∧
  closedEnums p.enums ∧
  (∀ fn ∈ p.functions, (∀ param ∈ fn.params, knownType p.enums param.2 = true) ∧
    Engine.inScope (callableNames p) (knownType p.enums) fn.body = true) ∧
  (∀ n ∈ entries, n ∈ callableNames p ∧ s.checkEntry n = .ok () ∧ Aiur.checkEntry p n = .ok ())

deriving instance DecidableEq for Aiur.Table

instance [DecidableEq F] (s : Source F) (p : Aiur.Program F) (entries : List String) :
    Decidable (Valid s p entries) := by unfold Valid; infer_instance

/-- Every source call in every selected instance is in the finite cache.
This check sees source arrays and pointer patterns; it does not lower a body. -/
def SourceClosed [DecidableEq F] (s : Source F) (p : Aiur.Program F) : Prop :=
  ∀ n ∈ callableNames p, ((s.program.sourceFunction? n).all fun fn =>
    SourceSemantics.inScope (callableNames p) (fun _ => true) fn.types fn.body) = true

instance [DecidableEq F] (s : Source F) (p : Aiur.Program F) : Decidable (SourceClosed s p) := by
  unfold SourceClosed
  infer_instance

/-- Source functions and maps must retain the same lookup priority. This is a
finite syntax check, including for manually constructed `Source` values. -/
def LoweringReady [DecidableEq F] (s : Source F) (p : Aiur.Program F) : Prop :=
  ∀ n ∈ callableNames p,
    (s.program.sourceFunction? n).isSome = (s.compilerFunction? n).isSome

instance [DecidableEq F] (s : Source F) (p : Aiur.Program F) : Decidable (LoweringReady s p) := by
  unfold LoweringReady; infer_instance

def TypedLowering [DecidableEq F] (s : Source F) (p : Aiur.Program F) : Prop :=
  ∀ n ∈ callableNames p, ((s.program.sourceFunction? n).all fun fn =>
    match Preparation.expression s.program (s.program.consts.length + 1) fn.types fn.body with
    | .error _ => false
    | .ok prepared => match ControlLower.function prepared (fn.params.map Prod.fst) with
      | .error _ => false
      | .ok body => (body.checkLowerTypes p [] fn.params).isSome) = true

instance [DecidableEq F] (s : Source F) (p : Aiur.Program F) : Decidable (TypedLowering s p) := by
  unfold TypedLowering; infer_instance

/-- The artifact retains its public entrypoint whitelist. Reachable helpers
are deliberately not made public merely by being present in `program`. -/
structure Specialized [DecidableEq F] (s : Source F) (entries : List String) where
  program : Aiur.Program F
  valid : Valid s program entries
  sourceClosed : SourceClosed s program
  loweringReady : LoweringReady s program
  typedLowering : TypedLowering s program

structure Limits where
  instances : Nat := 1024
  enumDepth : Nat := 1024
  deriving Repr

private structure Collect (F : Type) where
  functions : List (Aiur.Function F) := []
  remaining : Nat

private def visit [DecidableEq F] (s : Source F) : Nat → List Instance → String → StateT (Collect F) (Except String) Unit
  | 0, _, _ => throw "function dependency depth limit exceeded"
  | fuel + 1, path, name => do
      let key ← liftM (Instance.ofSymbol name)
      if (s.program.findFunction? key.name).isSome then
        if !key.types.all Ty.concrete then throw "cannot specialize an abstract type argument"
        if let some ancestor := path.find? (·.name == key.name) then
          if ancestor != key then throw s!"recursive call to '{key.name}' changes type arguments"
          return
        if (← get).functions.any (·.name == name) then return
        let fn ← liftM (Preparation.function s.program key)
        let state : Collect F ← get
        if state.remaining == 0 then throw "function instance limit exceeded"
        set ({ functions := state.functions ++ [fn], remaining := state.remaining - 1 } : Collect F)
        let some original := s.program.sourceFunction? name | throw "source closure disappeared"
        let dependencies := (sourceCalls original.types original.body).map Instance.symbol ++ coreCalls fn.body
        for callee in dependencies.eraseDups do visit s fuel (key :: path) callee
      else
        if !key.types.isEmpty || !(s.program.maps.any (·.name == key.name)) then
          throw s!"unknown function or map '{key.name}'"

/-- Reachability is checked again after collection. Cache reuse on a different
DFS path must not hide a change of recursive type arguments. -/
private def reachable (p : Aiur.Program F) : Nat → List String → List String → List String
  | 0, seen, _ => seen
  | fuel + 1, seen, pending =>
      let fresh := (pending.filter (fun n => !seen.contains n)).eraseDups
      if fresh.isEmpty then seen
      else reachable p fuel (seen ++ fresh) (fresh.flatMap fun n =>
        ((p.findFunction? n).map (fun fn => coreCalls fn.body)).getD [])

private def checkRecursion (p : Aiur.Program F) : Except String Unit := do
  for fn in p.functions do
    let start ← Instance.ofSymbol fn.name
    for name in reachable p (p.functions.length + 2) [] (coreCalls fn.body) do
      let key ← Instance.ofSymbol name
      if key.name == start.name && key != start then
        throw s!"recursive path revisits '{key.name}' with different type arguments"

def specialize [DecidableEq F] (s : Source F) (entries : List String) (limits : Limits := {}) :
    Except String (Specialized s entries) := do
  for name in entries do s.checkEntry name
  let (_, collected) ← (entries.forM (visit s (s.program.functions.length + 2) [])).run
    { remaining := limits.instances }
  let names := collected.functions.flatMap fun fn =>
    ((fn.params.map Prod.snd ++ [fn.result]).flatMap coreTypeNames) ++ coreExprNames fn.body
  let enums ← collectEnums s.program [] limits.enumDepth [] (names ++ s.tables.enums.map (·.name))
  let p := { s.tables with functions := collected.functions, enums }
  checkRecursion p
  -- Recheck after instantiation: enum layouts, pointer-free inputs, maps, and
  -- ordinary typing all belong to the existing core checker.
  (typecheck p).mapError toString
  if valid : Valid s p entries then
    if closed : SourceClosed s p then
      if ready : LoweringReady s p then
        if typed : TypedLowering s p then return ⟨p, valid, closed, ready, typed⟩
        else throw "specialization failed its source-scope typing check"
      else throw "specialization changed a source function lookup"
    else throw "specialization failed its source dependency check"
  else throw "specialization failed its structural certificate check"

def Specialized.checkEntry [DecidableEq F] {s : Source F} {entries : List String}
    (q : Specialized s entries) (name : String) : Except String Unit :=
  if name ∈ entries then (Aiur.checkEntry q.program name).mapError reprStr
  else .error s!"'{name}' is not a selected entrypoint"

theorem Specialized.checkEntry_iff [DecidableEq F] {s : Source F} {entries : List String}
    (q : Specialized s entries) : q.checkEntry name = .ok () ↔ name ∈ entries := by
  by_cases selected : name ∈ entries
  · have entry := (q.valid.2.2.2.2.2.2.2 name selected).2.2
    simp [Specialized.checkEntry, selected, entry, Except.mapError]
  · simp [Specialized.checkEntry, selected]

def Specialized.coreRun [Field F] [DecidableEq F] {s : Source F} {entries : List String}
    (q : Specialized s entries) (name : String) (args : List (SourceValue F)) (fuel : Nat := 1000)
    (hints : HintProvider F q.program.enums := HintProvider.unavailable) : Except String (SourceValue F × Heap F) := do
  q.checkEntry name
  (Aiur.run q.program name args fuel hints).mapError reprStr

/-- A finite cache of source bodies paired with their concrete type environments.
Array operations and pointer patterns remain present in these bodies. -/
def Specialized.instances [DecidableEq F] {s : Source F} {entries : List String}
    (q : Specialized s entries) : List (String × Option (SourceFunction F)) :=
  (callableNames q.program).map fun n => (n, s.program.sourceFunction? n)

def Specialized.world [DecidableEq F] {s : Source F} {entries : List String}
    (q : Specialized s entries) : SourceSemantics.World F :=
  let cache := q.instances
  sourceWorld s fun n => (cache.find? (·.1 == n)).bind Prod.snd

def Specialized.run [Field F] [DecidableEq F] {s : Source F} {entries : List String}
    (q : Specialized s entries) (name : String) (args : List (SourceValue F)) (fuel : Nat := 1000)
    (hints : s.HintProvider := SourceSemantics.unavailable) : Except String (SourceValue F × Heap F) := do
  q.checkEntry name
  let (types, locals, body) ← (q.world.prepare name args).mapError reprStr
  (SourceSemantics.evalFunctionWith q.world hints types locals fuel body []).mapError reprStr

def Specialized.EvalCall [Field F] [DecidableEq F] {s : Source F} {entries : List String}
    (q : Specialized s entries) (name : String) (args : List (SourceValue F)) (result : SourceValue F) : Prop :=
  q.checkEntry name = .ok () ∧ ∃ heap, SourceSemantics.EvalFn q.world name args [] result heap

end Aiur.Generic
