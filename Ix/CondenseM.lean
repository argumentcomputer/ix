import Lean
import Ix.Common

namespace Ix

structure CondenseEnv where
  env : Lean.Environment
  outRefs: Map Lean.Name (Set Lean.Name)

structure CondenseState where
  names: Map Lean.Name UInt64
  ids: Map UInt64 Lean.Name
  lowLink: Map UInt64 UInt64
  stack: Array UInt64
  onStack: Set UInt64
  id : UInt64

def CondenseState.init : CondenseState := ⟨{}, {}, {}, #[], {}, 0⟩

abbrev CondenseM := ReaderT CondenseEnv <| StateT CondenseState Id

partial def visit : Lean.Name -> CondenseM Unit
| name => do match (<- read).env.constants.find? name with
  | .none => return ()
  | .some _ => do
    let refs := match (<- read).outRefs.find? name with
    | .some x => x
    | .none => {}
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
      match (<- read).env.constants.find? ref with
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

structure CondensedBlocks where
  lowLinks: Map Lean.Name Lean.Name -- map constants to their lowlinks
  blocks: Map Lean.Name (Set Lean.Name) -- map lowlinks to blocks
  blockRefs: Map Lean.Name (Set Lean.Name) -- map lowlinks to block out-references
  deriving Inhabited, Nonempty

def condense (dbg : Bool) (total : Nat): CondenseM CondensedBlocks := do
  let mut idx : Nat := 0
  let mut lastPct : Nat := 0
  for (name,_) in (<- read).env.constants do
    idx := idx + 1
    if dbg && total > 0 then
      let pct := (idx * 100) / total
      if pct >= lastPct + 10 then
        dbg_trace s!"  [Condense] {pct}% ({idx}/{total})"
        lastPct := pct
    match (<- get).names.get? name with
    | .some _ => continue
    | .none => visit name
  let mut blocks : Map Lean.Name (Set Lean.Name) := {}
  let mut lowLinks := {}
  for (i, low) in (<- get).lowLink do
    let name := (<- get).ids.get! i
    let lowName := (<- get).ids.get! low
    lowLinks := lowLinks.insert name lowName
    blocks := blocks.alter lowName fun x => match x with
      | .some s => .some (s.insert name)
      | .none => .some {name}
  let mut blockRefs := {}
  let refs := (<- read).outRefs
  for (lo, all) in blocks do
    let mut rs: Set Lean.Name := {}
    for a in all do
      rs := rs.union (refs.get! a)
    rs := rs.filter (!all.contains ·)
    blockRefs := blockRefs.insert lo rs
  return ⟨lowLinks, blocks, blockRefs⟩

/-- Run SCC condensation on dependency graph.
    Pass `dbg := true` and `total` (constant count) to enable progress tracing. -/
def CondenseM.run (env: Lean.Environment) (refs: Map Lean.Name (Set Lean.Name))
    (dbg : Bool := false) (total : Nat := 0) : CondensedBlocks :=
  Id.run (StateT.run (ReaderT.run (condense dbg total) ⟨env, refs⟩) CondenseState.init).1

end Ix
