import Lean
import Ix.Common
import Ix.Environment

namespace Ix

structure CondenseEnv where
  /-- Set of valid names (names that exist in the environment) -/
  validNames: Set Ix.Name
  /-- Reference graph: map from Ix.Name to the set of names it references -/
  outRefs: Map Ix.Name (Set Ix.Name)

structure CondenseState where
  names: Map Ix.Name UInt64
  ids: Map UInt64 Ix.Name
  lowLink: Map UInt64 UInt64
  stack: Array UInt64
  onStack: Set UInt64
  id : UInt64

def CondenseState.init : CondenseState := ⟨{}, {}, {}, #[], {}, 0⟩

abbrev CondenseM := ReaderT CondenseEnv <| StateT CondenseState Id

partial def visit : Ix.Name -> CondenseM Unit
| name => do
  -- Check if name exists in our valid set
  if !(<- read).validNames.contains name then return ()
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
    -- Check if ref exists in our valid set
    if !(<- read).validNames.contains ref then continue
    match (<- get).names.get? ref with
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
  lowLinks: Map Ix.Name Ix.Name -- map constants to their lowlinks
  blocks: Map Ix.Name (Set Ix.Name) -- map lowlinks to blocks
  blockRefs: Map Ix.Name (Set Ix.Name) -- map lowlinks to block out-references
  deriving Inhabited, Nonempty

def condense (dbg : Bool) (total : Nat): CondenseM CondensedBlocks := do
  let mut idx : Nat := 0
  let mut lastPct : Nat := 0
  -- Iterate over all names in the ref graph
  for (name, _) in (<- read).outRefs do
    idx := idx + 1
    if dbg && total > 0 then
      let pct := (idx * 100) / total
      if pct >= lastPct + 10 then
        dbg_trace s!"  [Condense] {pct}% ({idx}/{total})"
        lastPct := pct
    match (<- get).names.get? name with
    | .some _ => continue
    | .none => visit name
  let mut blocks : Map Ix.Name (Set Ix.Name) := {}
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
    let mut rs: Set Ix.Name := {}
    for a in all do
      rs := rs.union (refs.get! a)
    rs := rs.filter (!all.contains ·)
    blockRefs := blockRefs.insert lo rs
  return ⟨lowLinks, blocks, blockRefs⟩

/-- Run SCC condensation on dependency graph (Ix.Name-based).
    Takes the reference graph (map from Ix.Name to set of referenced Ix.Names).
    Pass `dbg := true` and `total` (constant count) to enable progress tracing. -/
def CondenseM.run (refs: Map Ix.Name (Set Ix.Name))
    (dbg : Bool := false) (total : Nat := 0) : CondensedBlocks :=
  -- Build the set of valid names from the ref graph keys
  let validNames : Set Ix.Name := refs.fold (init := {}) fun acc k _ => acc.insert k
  Id.run (StateT.run (ReaderT.run (condense dbg total) ⟨validNames, refs⟩) CondenseState.init).1

/-- Rust's CondensedBlocks structure (mirroring Rust's output format).
    Used for FFI round-tripping with array-based representation. -/
structure RustCondensedBlocks where
  lowLinks : Array (Ix.Name × Ix.Name)
  blocks : Array (Ix.Name × Array Ix.Name)
  blockRefs : Array (Ix.Name × Array Ix.Name)
  deriving Inhabited, Nonempty, Repr

/-- Convert Rust's array-based format to Lean's map-based CondensedBlocks. -/
def RustCondensedBlocks.toCondensedBlocks (rust : RustCondensedBlocks) : CondensedBlocks :=
  let lowLinks := rust.lowLinks.foldl (init := {}) fun m (k, v) => m.insert k v
  let blocks := rust.blocks.foldl (init := {}) fun m (k, v) =>
    m.insert k (v.foldl (init := {}) fun s n => s.insert n)
  let blockRefs := rust.blockRefs.foldl (init := {}) fun m (k, v) =>
    m.insert k (v.foldl (init := {}) fun s n => s.insert n)
  { lowLinks, blocks, blockRefs }

end Ix
