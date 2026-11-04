module
/-
  # CondenseM: strongly connected components of the reference graph

  Condenses a dependency graph of `Ix.Name`s into its strongly connected
  components (mutual blocks). The components are
  `Ix.Compile.Canon.condensation`'s: Tarjan's algorithm as a total function,
  whose fuel is proved sufficient (`Ix.CompileCert.Canon.condensation_isSome`).
  This module only converts: it presents the reference graph to it, and its
  result back as `CondensedBlocks`:
  - `lowLinks`: maps each constant to its SCC representative
  - `blocks`: maps each SCC representative to all members
  - `blockRefs`: maps each SCC representative to its external references

  **Presentation, kept byte for byte.** The graph is presented in the
  iteration order of the reference map (roots) and of each reference set
  (successors), as the former `partial` Tarjan visited it, and the three maps
  are filled in the order that implementation filled them (members by
  discovery number through a `UInt64`-keyed map, whose iteration order
  depends only on its keys and the order they were first inserted). So the
  representative of a block (the Tarjan root, its first-discovered member),
  the maps' contents, their iteration orders and every member set's
  iteration order are what the former implementation produced. The
  partition does not depend on the presentation; the representatives and
  the iteration orders do.
-/

public import Ix.Common
public import Ix.Environment
public import Ix.Compile.Canon.Graph
import Ix.CompileCert.Canon.SccRange

public section

namespace Ix

structure CondensedBlocks where
  lowLinks: Map Ix.Name Ix.Name -- map constants to their lowlinks
  blocks: Map Ix.Name (Set Ix.Name) -- map lowlinks to blocks
  blockRefs: Map Ix.Name (Set Ix.Name) -- map lowlinks to block out-references
  deriving Inhabited, Nonempty

/-- Run SCC condensation on the dependency graph (`Ix.Name`-based): a map from
each constant to the set of names it references. References outside the
map's keys are not edges of the graph, but are kept in `blockRefs`.
Pass `dbg := true` and `total` (constant count) to trace progress. -/
def CondenseM.run (refs : Map Ix.Name (Set Ix.Name))
    (dbg : Bool := false) (total : Nat := 0) : CondensedBlocks := Id.run do
  -- The nodes: the map's entries in its iteration order.
  let mut entries : Array (Ix.Name × Set Ix.Name) := #[]
  let mut idx : Std.HashMap Ix.Name Nat := {}
  let mut lastPct : Nat := 0
  for (name, rs) in refs do
    idx := idx.insert name entries.size
    entries := entries.push (name, rs)
    if dbg && total > 0 then
      let pct := (entries.size * 100) / total
      if pct >= lastPct + 10 then
        dbg_trace s!"  [Condense] {pct}% ({entries.size}/{total})"
        lastPct := pct
  let names := entries.map (·.1)
  -- The edges: each set's references to nodes, in the set's iteration order.
  let adj := entries.map fun (_, rs) => Id.run do
    let mut succs : Array Nat := #[]
    for ref in rs do
      if let some j := idx.get? ref then
        succs := succs.push j
    return succs
  have hsize : names.size = adj.size := by simp only [names, adj, Array.size_map]
  let c := (Ix.Compile.Canon.condensation adj).get
    (Ix.CompileCert.Canon.condensation_isSome adj)
  have hc : Ix.Compile.Canon.condensation adj = some c := (Option.some_get _).symm
  -- Each node's representative: the name of its component's root.
  let mut rootName : Vector Ix.Name names.size := names.toVector
  for h : p in c.comps.zip c.roots do
    have hr : p.2 < names.size := by
      rw [hsize]
      exact Ix.CompileCert.Canon.condensation_roots_lt hc
        (Array.of_mem_zip (a := p.1) (b := p.2) h).2
    let rn := names[p.2]
    for v in p.1 do
      rootName := rootName.setIfInBounds v rn
  -- The nodes in the former `lowLink` map's iteration order: discovery
  -- numbers `0, 1, …` inserted in that order into a `UInt64`-keyed map.
  let mut byDiscovery : Std.HashMap UInt64 (Ix.Name × Ix.Name) := {}
  let mut d : Nat := 0
  for h : v in c.order do
    have hv : v < names.size := by
      rw [hsize]; exact Ix.CompileCert.Canon.condensation_order_lt hc h
    byDiscovery := byDiscovery.insert d.toUInt64 (names[v], rootName[v])
    d := d + 1
  let mut blocks : Map Ix.Name (Set Ix.Name) := {}
  let mut lowLinks : Map Ix.Name Ix.Name := {}
  for (_, (name, lowName)) in byDiscovery do
    lowLinks := lowLinks.insert name lowName
    blocks := blocks.alter lowName fun x => match x with
      | .some s => .some (s.insert name)
      | .none => .some {name}
  let mut blockRefs : Map Ix.Name (Set Ix.Name) := {}
  for (lo, all) in blocks do
    let mut rs : Set Ix.Name := {}
    for a in all do
      -- every member is a key of `refs`
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
