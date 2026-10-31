module

public import Ix.Ixon
public import IxC.Kernel.Ixon.Reader
public import IxC.Kernel.Ixon.Prelude

/-!
# An Ixon environment's check order (executable; not a statement)

The order the certified Ixon entry checks a whole environment's records in:
primary records (a projection replaced by its owner) in dependency order, an
iterative depth-first postorder over table references and the extra edges
(the `Nat` operations' certificate ground, `groundEdges`, and the literal
edges), with a given prefix first (the prelude's owners). Moved verbatim
from the environment-check harness (`Benchmarks.Kernel.CheckIxeStep`, which
re-exports these names) for the resource validator's adapter (step 10),
which submits a whole environment in the order `wholeEnv` gives. Nothing here
is trusted: a wrong order is a decline at the entry, never an acceptance.
-/

public section
@[expose] section

namespace Ixon.CheckOrder

open Ix.Kernel (ConstRef)
open Ix.Kernel.Reader

abbrev RecordStore := Std.HashMap Address Ixon.Constant

def owner (address : Address) (source : Ixon.Constant) : Address :=
  match source.info with
  | .dPrj p => p.block
  | .iPrj p => p.block
  | .rPrj p => p.block
  | .cPrj p => p.block
  | _ => address

/-- Primary records in dependency order: an iterative depth-first postorder
over table references (and the `extra` edges), with projections replaced by
their owners; `first` comes first, in its own order. -/
def order (store : RecordStore) (extra : Std.HashMap Address (Array Address))
    (first : Array Address) : Array Address := Id.run do
  let mut done : Std.HashSet Address := {}
  let mut active : Std.HashSet Address := {}
  let mut out : Array Address := #[]
  let roots := first ++ (store.toArray.qsort (fun a b => a.1.cmpBytes b.1 == .lt)).map (·.1)
  for address in roots do
    let some source := store[address]? | continue
    let root := owner address source
    if done.contains root then continue
    let mut stack : Array (Address × Bool) := #[(root, false)]
    while !stack.isEmpty do
      let (node, expanded) := stack.back!
      stack := stack.pop
      if expanded then
        active := active.erase node
        unless done.contains node do
          done := done.insert node
          out := out.push node
      else unless done.contains node || active.contains node do
        active := active.insert node
        stack := stack.push (node, true)
        let refs := (store[node]?.map (·.refs)).getD #[]
        for ref in refs ++ extra.getD node #[] do
          if let some target := store[ref]? then
            let dependency := owner ref target
            unless dependency == node || done.contains dependency || active.contains dependency do
              stack := stack.push (dependency, false)
  return out

/-- Only the records reachable from `roots` (with projections replaced by
owners), in dependency order. -/
def closure (store : RecordStore) (extra : Std.HashMap Address (Array Address))
    (roots : Array Address) : Array Address := Id.run do
  let sub := order store extra roots
  -- `order` continues with every other record after the roots' closures;
  -- keep the prefix the roots reach
  let mut reach : Std.HashSet Address := {}
  let mut todo := roots
  while h : todo.size > 0 do
    let a := todo[todo.size - 1]
    todo := todo.pop
    let some c := store[a]? | continue
    let o := owner a c
    if reach.contains o then continue
    reach := reach.insert o
    for r in ((store[o]?.map (·.refs)).getD #[]) ++ extra.getD o #[] do
      if store.contains r then todo := todo.push r
  return sub.filter reach.contains


/-- The recursor records read with an inductive block. -/
def recursorRecords (index : RecIndex) (block : Address) : Array Address :=
  ((index.blocks[block]?.map (·.recs)).getD #[]).foldl (fun acc r =>
    let a := r.block
    if a == block || acc.contains a then acc else acc.push a) #[]

/-- The record owners a record depends on: its references' owners, its
recursor records' references' owners, and the extra edges. -/
def dependencies (store : RecordStore) (index : RecIndex) (extra : Std.HashMap Address (Array Address))
    (address : Address) (source : Ixon.Constant) : Array Address := Std.HashSet.toArray <| Id.run do
  let recs := recursorRecords index address
  let mut out : Std.HashSet Address := {}
  for r in #[address] ++ recs do
    let refs := if r == address then source.refs else ((store[r]?.map (·.refs)).getD #[])
    for ref in refs ++ extra.getD r #[] do
      if let some target := store[ref]? then
        let o := owner ref target
        unless o == address || recs.contains o do out := out.insert o
  return out

/-- The certified `Nat` operations' certificate ground as extra edges
(`Frontend/NatOpGround.lean`): an operation's record depends on the records
of the operations its recurrences name. -/
def groundEdges (roles : Std.HashMap (ConstRef Address) (CName .anon)) : Std.HashMap Address (Array Address) :=
  Id.run do
  let byName : Std.HashMap (CName .anon) (ConstRef Address) := roles.fold (fun m r n => m.insert n r) {}
  let mut out : Std.HashMap Address (Array Address) := {}
  for (r, n) in roles.toList do
    if Ix.Kernel.natOpNames.contains n || Ix.Kernel.natDivModNames.contains n then
      for g in Ix.Kernel.natOpDeps n do
        if let some gr := byName[g]? then
          if gr.block != r.block then
            out := out.insert r.block ((out.getD r.block #[]).push gr.block)
  return out

/-- The union of two edge maps. -/
def mergeEdges (a b : Std.HashMap Address (Array Address)) : Std.HashMap Address (Array Address) :=
  b.fold (fun m k vs => m.insert k ((m.getD k #[]) ++ vs.filter (!(m.getD k #[]).contains ·))) a

/-- **A whole environment's records in check order**, as the environment-check
harness submits the records it selects (`Benchmarks.Kernel.CheckIxeStep.setup`
and `CheckIxeFold.acceptedRecords`, without the reading filter): every primary
record in `order` (the prelude's owners first, then a dependency order over
table references, the certified `Nat` operations' certificate ground and the
literal edges), each followed by its block's recursor records, then every
projection record, by address. The store is backed by the prelude's records
and its evidence, as the entry's reader is. The result holds the addresses of
`constants` only, each once: a prelude record the input lacks is the entry's
own. -/
def wholeEnv (t : Ix.Kernel.RoleTable) (pre : Prelude .anon)
    (constants : Array (Address × Ixon.Constant)) : Array Address := Id.run do
  let input : RecordStore := constants.foldl (fun m (a, c) => m.insert a c) {}
  let mut store := input
  for (a, c) in pre.records do
    unless store.contains a do store := store.insert a c
  let evidence : RecordStore := pre.evidence.foldl
    (fun m (a, c) => if store.contains a then m else m.insert a c) {}
  let records := store.toArray
  let look : Store := fun a => store[a]? <|> evidence[a]?
  let roles : Bindings .anon := bindingsOf look t
  let index := buildIndex look records
  let extra := mergeEdges (groundEdges roles.names) (literalEdges roles.names records)
  let first := pre.records.foldl (fun acc (a, c) =>
    let o := owner a c
    if acc.contains o then acc else acc.push o) #[]
  let mut seen : Std.HashSet Address := {}
  let mut out : Array Address := #[]
  for address in order store extra first do
    if seen.contains address then continue
    seen := seen.insert address
    out := out.push address
    for r in recursorRecords index address do
      unless seen.contains r || !store.contains r do
        seen := seen.insert r
        out := out.push r
  let mut projections : Array Address := #[]
  for (a, c) in records do
    let o := owner a c
    if o != a && seen.contains o && !seen.contains a then projections := projections.push a
  projections := projections.qsort (fun x y => x.cmpBytes y == .lt)
  return (out ++ projections).filter input.contains

end Ixon.CheckOrder

end
end
