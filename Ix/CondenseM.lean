import Lean
import Ix.Common

namespace Ix

structure CondenseState where
  exprRefs: Map Lean.Expr (Set Lean.Name)
  refs: Map Lean.Name (Set Lean.Name)
  names: Map Lean.Name UInt64
  ids: Map UInt64 Lean.Name
  lowLink: Map UInt64 UInt64
  stack: Array UInt64
  onStack: Set UInt64
  id : UInt64

def CondenseState.init : CondenseState := ⟨{}, {}, {}, {}, {}, #[], {}, 0⟩

abbrev CondenseM := ReaderT Lean.Environment <| StateT CondenseState Id

def refsExpr : Lean.Expr -> CondenseM (Set Lean.Name)
| expr => do match (<- get).exprRefs.find? expr with
  | some x => pure x
  | none => do
    let refs <- go expr
    modifyGet fun stt => (refs, { stt with
      exprRefs := stt.exprRefs.insert expr refs
    })
  where
    go : Lean.Expr -> CondenseM (Set Lean.Name)
    | .const name _ => pure {name}
    | .app f a => .union <$> refsExpr f <*> refsExpr a
    | .lam _ t b _ => .union <$> refsExpr t <*> refsExpr b
    | .forallE _ t b _ => .union <$> refsExpr t <*> refsExpr b
    | .letE _ t v b _ => do
      let t' <- refsExpr t
      let v' <- refsExpr v
      let b' <- refsExpr b
      return t'.union (v'.union b')
    | .proj n _ s => do return (<- refsExpr s).insert n
    | .mdata _ x => refsExpr x
    | _ => return {}

partial def refsConst : Lean.ConstantInfo -> CondenseM (Set Lean.Name)
| const => do match (<- get).refs.find? const.name with
  | some x => pure x
  | none => do
    let constRefs <- go const
    modifyGet fun stt => (constRefs, { stt with
      refs := stt.refs.insert const.name constRefs
    })
  where
    go : Lean.ConstantInfo -> CondenseM (Set Lean.Name)
    | .axiomInfo val => refsExpr val.type
    | .defnInfo val => .union <$> refsExpr val.type <*> refsExpr val.value
    | .thmInfo val => .union <$> refsExpr val.type <*> refsExpr val.value
    | .opaqueInfo val => .union <$> refsExpr val.type <*> refsExpr val.value
    | .quotInfo val => refsExpr val.type
    | .inductInfo val => do
      let env := (<- read).constants
      let ctorTypes: Set Lean.Name <- val.ctors.foldrM (fun n acc => do
        acc.union <$> refsConst (env.find! n)) {}
      let type <- refsExpr val.type
      return .union (.ofList val.ctors) (.union ctorTypes type)
    | .ctorInfo val => refsExpr val.type
    | .recInfo val => do
      let t <- refsExpr val.type
      let rs <- val.rules.foldrM (fun r s => .union s <$> refsExpr r.rhs) {}
      return .union t rs

partial def visit : Lean.Name -> CondenseM Unit
| name => do match (<- read).constants.find? name with
  | .none => return ()
  | .some c => do
    let refs <- refsConst c
    let id := (<- get).id
    modify fun stt => { stt with
      names := stt.names.insert name id
      ids := stt.ids.insert id name
      stack := stt.stack.push id
      onStack := stt.onStack.insert id
      lowLink := stt.lowLink.insert id id
      id := id + 1
    }
    for ref in refs do
      match (<- read).constants.find? ref with
      | none => continue
      | some _ => do match (<- get).names.get? ref with
        | .none => do
          visit ref
          modify fun stt =>
            let ll := stt.lowLink.get! id
            let rll := stt.lowLink.get! (stt.names.get! ref)
            { stt with lowLink := stt.lowLink.insert id (min ll rll) }
        | .some id' => if (<- get).onStack.contains id' then
          modify fun stt =>
            let ll := stt.lowLink.get! id
            { stt with lowLink := stt.lowLink.insert id (min ll id') }
    if id == (<- get).lowLink.get! id then
      let mut stack := (<- get).stack
      if !stack.isEmpty then
        while true do
          let top := stack.back!
          stack := stack.pop
          modify fun stt => { stt with
            lowLink := stt.lowLink.insert top id
            onStack := stt.onStack.erase top
          }
          if top == id then break
      modify fun stt => { stt with stack := stack }

def condense: CondenseM (Map Lean.Name (Set Lean.Name)) := do
  let mut idx := 0
  for (name,_) in (<- read).constants do
    idx := idx + 1
    match (<- get).names.get? name with
    | .some _ => continue
    | .none => visit name
  let mut blocks : Map Lean.Name (Set Lean.Name) := {}
  for (i, low) in (<- get).lowLink do
    let name := (<- get).ids.get! i
    let lowName := (<- get).ids.get! low
    blocks := blocks.alter lowName fun x => match x with
      | .some s => .some (s.insert name)
      | .none => .some {name}
  for (_, set) in blocks do
    for n in set do
      blocks := blocks.insert n set
  return blocks

def CondenseM.run (env: Lean.Environment): Map Lean.Name (Set Lean.Name) :=
 Id.run (StateT.run (ReaderT.run condense env) CondenseState.init).1

end Ix
