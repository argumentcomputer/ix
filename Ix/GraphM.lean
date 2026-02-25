module

public import Ix.Common
public import Ix.Environment

public section

namespace Ix

/-!
  # GraphM - Build dependency graph from Ix.Environment

  This module builds a reference graph from an already-canonicalized Ix.Environment.
  The canonicalization should be done first (ideally via fast Rust FFI).
-/

structure GraphState where
  exprCache: Map Ix.Expr (Set Ix.Name)

def GraphState.init : GraphState := ⟨{}⟩

abbrev GraphM := ReaderT Ix.Environment <| StateT GraphState Id

/-- Extract constant references from an Ix.Expr.
    NOTE: Aligned with Rust's get_expr_references for cross-impl testing. -/
def graphExpr (expr: Ix.Expr) : GraphM (Set Ix.Name) := do
  match (<- get).exprCache.get? expr with
  | some x => pure x
  | none =>
    let refs <- go expr
    modifyGet fun stt => (refs, { stt with
      exprCache := stt.exprCache.insert expr refs
    })
  where
    go : Ix.Expr -> GraphM (Set Ix.Name)
    | .mdata _ x _ => graphExpr x
    | .const name _ _ => pure {name}
    | .app f a _ => .union <$> graphExpr f <*> graphExpr a
    | .lam _ t b _ _ => .union <$> graphExpr t <*> graphExpr b
    | .forallE _ t b _ _ => .union <$> graphExpr t <*> graphExpr b
    | .letE _ t v b _ _ =>
      .union <$> graphExpr t <*> (.union <$> graphExpr v <*> graphExpr b)
    | .proj typeName _ s _ => (.insert · typeName) <$> graphExpr s
    | _ => pure {}

/-- Extract constant references from an Ix.ConstantInfo.
    NOTE: Aligned with Rust's get_constant_info_references for cross-impl testing. -/
def graphConst: Ix.ConstantInfo -> GraphM (Set Ix.Name)
| .axiomInfo val => graphExpr val.cnst.type
| .defnInfo val => .union <$> graphExpr val.cnst.type <*> graphExpr val.value
| .thmInfo val => .union <$> graphExpr val.cnst.type <*> graphExpr val.value
| .opaqueInfo val => .union <$> graphExpr val.cnst.type <*> graphExpr val.value
| .quotInfo val => graphExpr val.cnst.type
| .inductInfo val => do
  -- Rust: type refs + constructor names (NOT constructor type refs)
  let ctorNames : Set Ix.Name := val.ctors.foldl (init := {}) fun s n => s.insert n
  let type <- graphExpr val.cnst.type
  return .union type ctorNames
| .ctorInfo val => do
  -- Rust: type refs + induct name
  let typeRefs <- graphExpr val.cnst.type
  return typeRefs.insert val.induct
| .recInfo val => do
  -- Rust: type refs + (ctor names + rhs refs for each rule)
  let t <- graphExpr val.cnst.type
  let mut rs := t
  for rule in val.rules do
    rs := rs.insert rule.ctor
    let rhsRefs <- graphExpr rule.rhs
    rs := rs.union rhsRefs
  return rs

def GraphM.run (env: Ix.Environment) (stt: GraphState) (g: GraphM α)
  : α × GraphState
  := StateT.run (ReaderT.run (Id.run g env)) stt

/-- Build dependency graph from Ix.Environment.
    Returns a map from Ix.Name to the set of Ix.Names it references.
    Pass `dbg := true` and `total` (constant count) to enable progress tracing. -/
def GraphM.env (env: Ix.Environment) (dbg : Bool := false) (total : Nat := 0)
    : Map Ix.Name (Set Ix.Name) := Id.run do
  let mut stt : GraphState := .init
  let mut refs: Map Ix.Name (Set Ix.Name) := {}
  let mut i : Nat := 0
  let mut lastPct : Nat := 0
  for (name, const) in env.consts do
    let (rs, stt') := GraphM.run env stt (graphConst const)
    refs := refs.insert name rs
    stt := stt'
    i := i + 1
    if dbg && total > 0 then
      let pct := (i * 100) / total
      if pct >= lastPct + 10 then
        dbg_trace s!"  [Graph] {pct}% ({i}/{total})"
        lastPct := pct
  return refs

def GraphM.envParallel (env: Ix.Environment) : Map Ix.Name (Set Ix.Name) := Id.run do
  let mut tasks : Array (Ix.Name × Task (Set Ix.Name)) := #[]
  for (name, const) in env.consts do
    let task := Task.spawn fun () =>
      let (rs, _) := GraphM.run env .init (graphConst const)
      rs
    tasks := tasks.push (name, task)
  let mut refs : Map Ix.Name (Set Ix.Name) := {}
  for (name, task) in tasks do
    refs := refs.insert name task.get
  return refs

def GraphM.envSerial (env: Ix.Environment) : Map Ix.Name (Set Ix.Name) := Id.run do
  let mut refs: Map Ix.Name (Set Ix.Name) := {}
  for (name, const) in env.consts do
    let (rs, _) := GraphM.run env .init (graphConst const)
    refs := refs.insert name rs
  return refs

end Ix

end
