import IxCK.Kernel.Ixon.Prelude

/-! # The order the kernel's entry reads a closure in (untrusted)

The certified kernel's entry (`Ix.Kernel.Admission.checkBytesWith`) reads its
records in the order its host supplies, which must be a dependency order: each
record after the records it references, a certified `Nat` operation after its
certificate's ground, a literal after the constants its literals reference.
The `.ixe` envelope stores records by address, so the host chooses the order.
This module is that choice, for the kernel front end
(`IxCC.Src.KernelFront.Accept`): the prelude's records first (the artifact's
own copies of the roles `Ix.Kernel.preludeShape` names, selected through the
role table), then an iterative depth-first postorder over table references and
the extra edges, each block followed by its recursor records, then the
projection records by address.

It follows ix's own whole-environment order, the one `ix check-lean` admits an
artifact in (`Ixon.CheckOrder.wholeEnv` and `Ix.RoleBinding.preludeRecords` in
ix's root package, which IxCC does not import), so the kernel front end and
`ix check-lean` submit the same records in the same order. Nothing here is
trusted: the entry's theorems hold for every order, and a wrong one is a
decline at the entry, never an acceptance. Every loop is iterative and bounded
by the records' references, which ingress caps. -/

namespace IxCC.Src.KernelFront

open Ix.Kernel (ConstRef Role)
open Ix.Kernel.Reader

/-- The kernel's address type (IxCC's own is `IxCC.Ixon.Address`). -/
abbrev KAddr := _root_.Address
/-- A decoded Ixon record, in the kernel's codec's types. -/
abbrev KConstant := _root_.Ixon.Constant
/-- Decoded records by address. -/
abbrev RecordStore := Std.HashMap KAddr KConstant

namespace Order

/-- The record a record belongs to: a projection record's block, otherwise
itself. -/
def owner (address : KAddr) (source : KConstant) : KAddr :=
  match source.info with
  | .dPrj p => p.block
  | .iPrj p => p.block
  | .rPrj p => p.block
  | .cPrj p => p.block
  | _ => address

/-- Primary records in dependency order: an iterative depth-first postorder
over table references and the `extra` edges, with projections replaced by
their owners; `first` comes first, in its own order. -/
def order (store : RecordStore) (extra : Std.HashMap KAddr (Array KAddr))
    (first : Array KAddr) : Array KAddr := Id.run do
  let mut done : Std.HashSet KAddr := Std.HashSet.emptyWithCapacity store.size
  let mut active : Std.HashSet KAddr := Std.HashSet.emptyWithCapacity 256
  let mut out : Array KAddr := Array.mkEmpty store.size
  let mut keys : Array KAddr := Array.mkEmpty store.size
  for (a, _) in store do keys := keys.push a
  let roots := first ++ keys.qsort (fun a b => a.cmpBytes b == .lt)
  for address in roots do
    let some source := store[address]? | continue
    let root := owner address source
    if done.contains root then continue
    let mut stack : Array (KAddr × Bool) := #[(root, false)]
    while !stack.isEmpty do
      let some (node, expanded) := stack.back? | break
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
        for ref in refs do
          if let some target := store[ref]? then
            let dependency := owner ref target
            unless dependency == node || done.contains dependency || active.contains dependency do
              stack := stack.push (dependency, false)
        if let some ex := extra[node]? then
          for ref in ex do
            if let some target := store[ref]? then
              let dependency := owner ref target
              unless dependency == node || done.contains dependency || active.contains dependency do
                stack := stack.push (dependency, false)
  return out

/-- The recursor records read with an inductive block. -/
def recursorRecords (index : RecIndex) (block : KAddr) : Array KAddr :=
  ((index.blocks[block]?.map (·.recs)).getD #[]).foldl (fun acc r =>
    let a := r.block
    if a == block || acc.contains a then acc else acc.push a) #[]

/-- The certified `Nat` operations' certificate ground as extra edges: an
operation's record depends on the records of the operations its recurrences
name. -/
def groundEdges (roles : Std.HashMap (ConstRef KAddr) (CName .anon)) :
    Std.HashMap KAddr (Array KAddr) := Id.run do
  let byName : Std.HashMap (CName .anon) (ConstRef KAddr) := roles.fold (fun m r n => m.insert n r) {}
  let mut out : Std.HashMap KAddr (Array KAddr) := {}
  for (r, n) in roles.toList do
    if (Ix.Kernel.natOpNames (md := .anon)).contains n ||
        (Ix.Kernel.natDivModNames (md := .anon)).contains n then
      for g in Ix.Kernel.natOpDeps n do
        if let some gr := byName[g]? then
          if gr.block != r.block then
            out := out.insert r.block ((out.getD r.block #[]).push gr.block)
  return out

/-- The union of two edge maps. -/
def mergeEdges (a b : Std.HashMap KAddr (Array KAddr)) : Std.HashMap KAddr (Array KAddr) :=
  b.fold (fun m k vs => m.insert k ((m.getD k #[]) ++ vs.filter (!(m.getD k #[]).contains ·))) a

/-- **A whole closure's records in check order**: every primary record in
`order` (the prelude's owners first, then a dependency order over table
references, the certified `Nat` operations' certificate ground and the literal
edges), each followed by its block's recursor records, then every projection
record, by address. The result holds the addresses of `constants` only, each
once. -/
def wholeEnv (t : Ix.Kernel.RoleTable) (pre : Prelude .anon)
    (constants : Array (KAddr × KConstant)) : Array KAddr := Id.run do
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
  let mut seen : Std.HashSet KAddr := {}
  let mut out : Array KAddr := #[]
  for address in order store extra first do
    if seen.contains address then continue
    seen := seen.insert address
    out := out.push address
    for r in recursorRecords index address do
      unless seen.contains r || !store.contains r do
        seen := seen.insert r
        out := out.push r
  let mut projections : Array KAddr := #[]
  for (a, c) in records do
    let o := owner a c
    if o != a && seen.contains o && !seen.contains a then projections := projections.push a
  projections := projections.qsort (fun x y => x.cmpBytes y == .lt)
  return (out ++ projections).filter input.contains

/-- **The artifact's own prelude records**: for each role group of
`Ix.Kernel.preludeShape`, the records the role table binds those roles to,
each owner before its projection. Every role and record must be present; the
order is the prelude's, and whether it reads as the prelude is the kernel's
`checkPreludeShape`. -/
def preludeRecords (table : Ix.Kernel.RoleTable) (store : Store) (groups : List (List Role)) :
    Except String (Array (KAddr × KConstant)) := do
  let mut addresses : Array KAddr := #[]
  let mut records : Array (KAddr × KConstant) := #[]
  for group in groups do
    for role in group do
      let some address := table.addressOf? role
        | throw s!"role prelude: no binding for {repr role}"
      let some record := store address
        | throw s!"role prelude: no record for {repr role} at {address}"
      let some ref := resolveSource store address record
        | throw s!"role prelude: {repr role} at {address} does not resolve"
      for selected in #[ref.block, address] do
        unless addresses.contains selected do
          let some value := store selected
            | throw s!"role prelude: missing owner {selected} for {repr role}"
          addresses := addresses.push selected
          records := records.push (selected, value)
  return records

/-- **Every role the table binds designates a member of the closure**, no two
roles the same member, and every proof the table names as evidence is a
record of the closure. Table well-formedness alone admits a bound role whose
record is absent; this is a coverage check before the kernel runs. -/
def checkBindings (table : Ix.Kernel.RoleTable) (store : RecordStore) : Except String Unit := do
  let mut seen : Std.HashMap (ConstRef KAddr) Role := {}
  for (role, address) in table.bound do
    let some record := store[address]? | throw s!"missing record for {repr role}: {address}"
    let some ref := resolveSource (store[·]?) address record
      | throw s!"unresolved member for {repr role}: {address}"
    if let some other := seen[ref]? then
      throw s!"{repr role} and {repr other} designate the same member"
    seen := seen.insert ref role
  for (role, entries) in table.evidence do
    for entry in entries do
      if let .proof address := entry then
        unless store.contains address do
          throw s!"missing proof record for {repr role}: {address}"

end Order

end IxCC.Src.KernelFront
