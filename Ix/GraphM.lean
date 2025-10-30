
import Lean
import Ix.Common

namespace Ix

structure GraphState where
  exprCache: Map Lean.Expr (Set Lean.Name)

def GraphState.init : GraphState := ⟨{}⟩

abbrev GraphM := ReaderT Lean.Environment <| StateT GraphState Id

def graphExpr (expr: Lean.Expr) : GraphM (Set Lean.Name) := do
  match (<- get).exprCache.find? expr with
  | some x => pure x
  | none => 
    let refs <- go expr
    modifyGet fun stt => (refs, { stt with
      exprCache := stt.exprCache.insert expr refs
    })
  where
    go : Lean.Expr -> GraphM (Set Lean.Name)
    | .mdata _ x => graphExpr x
    | .const name _ => pure {name}
    | .app f a => .union <$> graphExpr f <*> graphExpr a
    | .lam _ t b _ => .union <$> graphExpr t <*> graphExpr b
    | .forallE _ t b _ => .union <$> graphExpr t <*> graphExpr b
    | .letE _ t v b _ =>
      .union <$> graphExpr t <*> (.union <$> graphExpr v <*> graphExpr b)
    | .proj typeName _ s => (.insert · typeName) <$> graphExpr s
    | _ => pure {}

def graphConst: Lean.ConstantInfo -> GraphM (Set Lean.Name)
| .axiomInfo val => graphExpr val.type
| .defnInfo val => .union <$> graphExpr val.type <*> graphExpr val.value
| .thmInfo val => .union <$> graphExpr val.type <*> graphExpr val.value
| .opaqueInfo val => .union <$> graphExpr val.type <*> graphExpr val.value
| .quotInfo val => graphExpr val.type
| .inductInfo val => do
  let env <- read
  let mut ctorRefs := {}
  for ctor in val.ctors do
    let rs <- match env.find? ctor with
    | .some (.ctorInfo ctorVal) => graphExpr ctorVal.type
    | _ => continue
    ctorRefs := ctorRefs.union rs
  let type <- graphExpr val.type
  return .union (.union (.ofList val.ctors) ctorRefs) type
| .ctorInfo val => graphExpr val.type
| .recInfo val => do
  let t <- graphExpr val.type
  let rs <- val.rules.foldrM (fun r s => .union s <$> graphExpr r.rhs) {}
  return .union t rs

def GraphM.run (env: Lean.Environment) (g: GraphM α)
  : α × GraphState
  := StateT.run (ReaderT.run (Id.run g env)) GraphState.init

def GraphM.env (env: Lean.Environment) : Map Lean.Name (Set Lean.Name) := Id.run do
  let mut tasks : Map Lean.Name (Task (Set Lean.Name)) := {}
  for (name, const) in env.constants do
    let task <- Task.spawn fun () => (GraphM.run env (graphConst const)).1
    tasks := tasks.insert name task
  return tasks.map fun _ t => t.get

end Ix
