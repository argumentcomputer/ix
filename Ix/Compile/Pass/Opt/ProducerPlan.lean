/- Static producer dependencies for occurrence passes. The source condensation
is retained; this module changes only its scheduling references. -/
module
public import Ix.CondenseM
public import Ix.Compile.ExactKey

public section
namespace Ix.Compile.Pass.Opt
open Ix (Name)
open Ix.Compile.ExactKey (ExactName)
abbrev ProducerGraph := Std.HashMap ExactName (Array Name)
abbrev ProducerSet := Std.HashSet ExactName
abbrev ProducerRefusals := Std.HashMap ExactName (Std.HashMap ExactName String)

/-- Updating the reverse adjacency in place preserves every lookup, including
the complete caller array's order and duplicates. -/
theorem producerReverseAppend_lookup (reverse : ProducerGraph) (producer query : ExactName)
    (caller : Name) :
    (reverse.alter producer (fun callers => some ((callers.getD #[]).push caller)))[query]? =
      (reverse.insert producer ((reverse.getD producer #[]).push caller))[query]? := by
  simp only [Std.HashMap.getElem?_alter, Std.HashMap.getElem?_insert,
    Std.HashMap.getD_eq_getD_getElem?]

/-- Reachability including the start node. Enqueue-once bounds the walk by
the graph's number of vertices, including isolated producer vertices. -/
def producerReach (graph : ProducerGraph) (start : Name) (bound : Nat) : ProducerSet := Id.run do
  let mut seen : ProducerSet := {start}
  let mut queue := #[start]
  for i in [0:bound] do
    if i ≥ queue.size then break
    for n in graph.getD queue[i]! #[] do
      if !seen.contains n then
        seen := seen.insert n
        queue := queue.push n
  return seen

/-- The existing SCC dependency graph and its reverse, after clique-owner
union. External names do not make vertices; all original SCCs remain intact. -/
def producerBase (blocks : Ix.CondensedBlocks) : ProducerGraph × ProducerGraph := Id.run do
  let mut graph : ProducerGraph := {}
  let mut reverse : ProducerGraph := {}
  for (lo, refs) in blocks.blockRefs do
    let mut deps : ProducerSet := {}
    for n in refs do
      if let some p := blocks.lowLinks.get? n then
        if !Ix.Compile.ExactKey.nameEq p lo then deps := deps.insert p
    graph := graph.insert lo deps.toArray
    -- Update inside the map so a growing caller array is not retained across `push`.
    for p in deps do
      reverse := reverse.alter p fun callers => some ((callers.getD #[]).push lo)
  return (graph, reverse)

/-- Plan proposed caller-to-producer dependencies without consulting readiness.

Requirements are first propagated to every existing transitive caller (after
clique-owner union), covering recursively expanded heads and early publication.
For every producer Q, walk its existing dependencies, including zero-length
reachability Q=C. A proposed edge C→P induces Q→P when Q reaches C. Every new
cycle alternates an existing path Q→…→C with such a proposed edge.

A proposed C→P is cyclic iff some Q reaching C lies in P's producer SCC;
singleton self-loops count. Remove ALL these proposed edges simultaneously,
never greedily. The original DAG plus the remaining additions is acyclic.
An actual rewrite needing a removed edge must decline, using the returned
enclosing-block report. Missing grounded producers also receive a static cause.
No source SCC, representative, or classification reference is changed. -/
def planProducerDeps (blocks : Ix.CondensedBlocks) (seeds : Array (Name × Name)) :
    Ix.CondensedBlocks × ProducerRefusals := Id.run do
  if seeds.isEmpty then return (blocks, {})
  let (base, reverse) := producerBase blocks
  let mut required : Array (Name × Name) := #[]
  let mut seen : Std.HashSet (ExactName × ExactName) := {}
  let mut producers : ProducerSet := {}
  for pair in seeds do
    unless seen.contains pair do
      seen := seen.insert pair
      required := required.push pair
      producers := producers.insert pair.2
  for i in [0:blocks.blocks.size * producers.size] do
    if i ≥ required.size then break
    let (caller, producer) := required[i]!
    for parent in reverse.getD caller #[] do
      unless seen.contains (parent, producer) do
        seen := seen.insert (parent, producer)
        required := required.push (parent, producer)
  let mut oldReach : Std.HashMap ExactName ProducerSet := {}
  for p in producers do
    if let some lo := blocks.lowLinks.get? p then
      oldReach := oldReach.insert p (producerReach base lo blocks.blocks.size)
  let mut projected : ProducerGraph := {}
  for q in producers do
    let reach := oldReach.getD q {}
    let mut next : ProducerSet := {}
    for (caller, p) in required do
      if blocks.lowLinks.contains p && reach.contains caller then next := next.insert p
    projected := projected.insert q next.toArray
  let mut reach : Std.HashMap ExactName ProducerSet := {}
  for p in producers do reach := reach.insert p (producerReach projected p producers.size)
  let mut refs := blocks.blockRefs
  let mut refusedByBlock : ProducerRefusals := {}
  for (caller, p) in required do
    let reason := if !blocks.lowLinks.contains p then
        some s!"producer {p.pretty} is outside the grounded input"
      else if producers.toArray.any (fun q =>
          (oldReach.getD q {}).contains caller && (reach.getD p {}).contains q) then
        let cycle := (producers.toArray.filter fun q =>
          (reach.getD p {}).contains q && (reach.getD q {}).contains p).map (·.pretty)
        some s!"producer {p.pretty} would close a dependency cycle through \
[{String.intercalate ", " (cycle.qsort (· < ·)).toList}]"
      else none
    match reason with
    | some why =>
      refusedByBlock := refusedByBlock.insert caller
        ((refusedByBlock.getD caller {}).insert p why)
    | none =>
      refs := refs.alter caller fun rs => some ((rs.getD {}).insert p)
  -- Any representative of an enclosing source block selects the same plan.
  let mut refused : ProducerRefusals := {}
  for (caller, reasons) in refusedByBlock do
    for n in blocks.blocks.getD caller {} do refused := refused.insert n reasons
  return ({ blocks with blockRefs := refs }, refused)

end Ix.Compile.Pass.Opt
end
