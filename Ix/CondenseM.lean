/-!
  # CondenseM: Strongly Connected Component Condensation

  Implements Tarjan's SCC algorithm to condense a dependency graph of Ix.Names
  into its strongly connected components (mutual blocks). Each SCC becomes a
  single node in the condensed DAG.

  The algorithm assigns each node a numeric `id` (discovery order) and tracks
  a `lowLink` — the smallest id reachable from that node via back-edges. When
  `lowLink[id] == id`, the node is the root of an SCC, and all nodes on the
  stack down to it form the component.

  The output `CondensedBlocks` provides:
  - `lowLinks`: maps each constant to its SCC representative
  - `blocks`: maps each SCC representative to all members
  - `blockRefs`: maps each SCC representative to its external references
-/

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
  /-- Map from name to its discovery id -/
  names: Map Ix.Name UInt64
  /-- Reverse map from discovery id to name -/
  ids: Map UInt64 Ix.Name
  /-- Smallest reachable discovery id for each node (determines SCC roots) -/
  lowLink: Map UInt64 UInt64
  /-- Tarjan's working stack of node ids being processed -/
  stack: Array UInt64
  /-- Set of ids currently on the stack (for O(1) membership checks) -/
  onStack: Set UInt64
  /-- Next discovery id to assign -/
  id : UInt64

def CondenseState.init : CondenseState := ⟨{}, {}, {}, #[], {}, 0⟩

abbrev CondenseM := ReaderT CondenseEnv <| StateT CondenseState Id

/-- Tarjan's DFS visit. Assigns a discovery `id`, pushes onto the SCC stack,
    then recurses on neighbors. After visiting neighbors, if `lowLink[id] == id`
    this node is the root of an SCC — pop the stack to collect all members. -/
partial def visit : Ix.Name -> CondenseM Unit
| name => do
  if !(<- read).validNames.contains name then return ()
  let refs := match (<- read).outRefs.find? name with
    | .some x => x
    | .none => {}
  -- Assign discovery id and initialize lowLink to self
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
    if !(<- read).validNames.contains ref then continue
    match (<- get).names.get? ref with
    | .none => do
      -- Tree edge: recurse, then propagate lowLink upward
      visit ref
      modify fun stt =>
        let ll := stt.lowLink.get! id
        let rll := stt.lowLink.get! (stt.names.get! ref)
        { stt with lowLink := stt.lowLink.insert id (min ll rll) }
    | .some id' => if (<- get).onStack.contains id' then
      -- Back edge: update lowLink to the earlier discovery id
      modify fun stt =>
        let ll := stt.lowLink.get! id
        { stt with lowLink := stt.lowLink.insert id (min ll id') }
  -- If lowLink equals our own id, we are the root of an SCC.
  -- Pop the stack until we reach ourselves to collect all SCC members.
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
