module
/-
  # CondenseM: strongly connected components of the reference graph

  The compiler's split (Pass 1, design document §2.1) is
  `Ix.Compile.Canon.condensation`, Tarjan's algorithm as a total function.
  This module only converts: it presents the compiler's reference graph to
  it, and its result back as the compiler's `CondensedBlocks`:
  - `lowLinks`: maps each constant to its SCC representative
  - `blocks`: maps each SCC representative to all members
  - `blockRefs`: maps each SCC representative to its external references

  **Presentation, kept byte for byte.** The graph is presented in the
  iteration order of the reference map (roots) and of each reference set
  (successors), and the three maps are filled in the order the former
  `partial` Tarjan filled them (members by discovery number through a
  `UInt64`-keyed map). So the representative of a block (the Tarjan root,
  its first-discovered member), the maps' iteration orders and every
  member set's iteration order are exactly what the compiler saw before
  Pass 1 was wired in. The partition does not depend on the presentation;
  the representative and the iteration orders do (design document §6.1,
  D9), and removing that dependence is A7's, not this module's.
-/

public import Ix.Common
public import Ix.Environment
public import Ix.Compile.Canon.Graph

public section

namespace Ix

structure CondensedBlocks where
  lowLinks: Map Ix.Name Ix.Name -- map constants to their lowlinks
  blocks: Map Ix.Name (Set Ix.Name) -- map lowlinks to blocks
  blockRefs: Map Ix.Name (Set Ix.Name) -- map lowlinks to block out-references
  deriving Inhabited, Nonempty

/-- Condense the reference graph (a map from each constant to the set of
names it references; references outside the map's keys are ignored) into
its strongly connected components. An error only if the total Tarjan's fuel
bound were wrong. -/
def CondenseM.run (refs : Map Ix.Name (Set Ix.Name)) : Except String CondensedBlocks := do
  -- Nodes in the map's iteration order; successors in each set's order.
  let mut names : Array Ix.Name := #[]
  let mut idx : Std.HashMap Ix.Name Nat := {}
  for (name, _) in refs do
    idx := idx.insert name names.size
    names := names.push name
  let mut adj : Array (Array Nat) := #[]
  for name in names do
    let mut succs : Array Nat := #[]
    for ref in refs.getD name {} do
      if let some j := idx.get? ref then
        succs := succs.push j
    adj := adj.push succs
  let some c := Ix.Compile.Canon.condensation adj
    | throw "condense: Tarjan ran out of fuel"
  -- The root of each node's component.
  let mut rootOf : Array Nat := Array.replicate names.size 0
  for (comp, root) in c.comps.zip c.roots do
    for v in comp do
      rootOf := rootOf.set! v root
  -- Members in the former `lowLink` map's iteration order: discovery
  -- numbers `0, 1, …` inserted in that order into a `UInt64`-keyed map.
  let mut byDiscovery : Std.HashMap UInt64 UInt64 := {}
  for d in [0:c.order.size] do
    byDiscovery := byDiscovery.insert d.toUInt64 d.toUInt64
  let mut blocks : Map Ix.Name (Set Ix.Name) := {}
  let mut lowLinks : Map Ix.Name Ix.Name := {}
  for (d, _) in byDiscovery do
    let some v := c.order[d.toNat]? | throw "condense: discovery number out of range"
    let some name := names[v]? | throw "condense: node out of range"
    let some lowName := names[rootOf[v]?.getD v]? | throw "condense: root out of range"
    lowLinks := lowLinks.insert name lowName
    blocks := blocks.alter lowName fun x => match x with
      | .some s => .some (s.insert name)
      | .none => .some {name}
  let mut blockRefs : Map Ix.Name (Set Ix.Name) := {}
  for (lo, all) in blocks do
    let mut rs : Set Ix.Name := {}
    for a in all do
      rs := rs.union (refs.getD a {})
    rs := rs.filter (!all.contains ·)
    blockRefs := blockRefs.insert lo rs
  return ⟨lowLinks, blocks, blockRefs⟩

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

end
