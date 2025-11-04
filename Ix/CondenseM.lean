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
  count: Nat -- number of blocks
  lowLinks: Map Lean.Name Lean.Name -- map constants to their lowlinks
  alls: Map Lean.Name (Set Lean.Name) -- map constants to their mutual blocks
  deriving Inhabited, Nonempty

def condense: CondenseM CondensedBlocks := do
  let mut idx := 0
  for (name,_) in (<- read).env.constants do
    idx := idx + 1
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
  let blockCount := blocks.size
  let mut alls := {}
  for (_, set) in blocks do
    for n in set do
      alls := alls.insert n set
  return ⟨blockCount, lowLinks, alls⟩

def CondenseM.run (env: Lean.Environment) (refs: Map Lean.Name (Set Lean.Name))
  : CondensedBlocks :=
  Id.run (StateT.run (ReaderT.run condense ⟨env, refs⟩) CondenseState.init).1

end Ix
