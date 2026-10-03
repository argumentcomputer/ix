/- # Pass 3: the side-car of a changed block (D14, `Named.original`)

## Contract
Input: the registrations the aux tail made for one compiled component of a
changed Lean block (Pass 2's canonical auxiliaries under Lean's names:
`Named` entries, the resolution map, the aux-gen name set), and the display
name of each (`Ix.Compile.Pass.Names.ixAuxName`).

Output, under the switch:
* every Ix auxiliary is also registered under its display name `x._ix.S`
  (D14), with its metadata renamed into the `_ix` view (`renameMeta`: the
  constant's own name, `all`, `ctx`, constructor names, and every reference
  in its arena, so the entry reads consistently);
* a Lean name that is an image kind (`Ix.Compile.Pass.imageKinds`: the
  block's recursors, `casesOn`, `recOn`, and the Type-level `below`/`brecOn`
  family) keeps its entry pointing at the Ix auxiliary of its class, which is
  the name map's canonical position for it (`Canon.NameMap`: `T.rec` ↦ the
  member's class), and gets `Named.original` from the promotion pass as
  today, computed from Lean's form **without** any call-site rewrite (A0's
  recommendation: originals are no longer surgered);
* every other Lean name the tail registered (the canonical `IndPredBelow`
  family: Lean's `x.below` inductive, its constructors and its recursor) is
  **moved** to its display name only, so that Lean's own form of it is
  compiled as an ordinary block (design document §4.6); references to moved
  names in the kept entries' metadata are renamed too.

## Faithfulness
Metadata only: no constant's bytes change. Lean's names keep resolving to the
constants they resolved to (or, for moved names, to Lean's own forms).

## Canonicity
The display names follow the canonical form (`Names`).

## Side condition and fallback
A registered name that hangs off no member of the Lean block keeps its Lean
name and gets no display name (none occur: aux-gen names everything after a
member or `all₀`).

## Non-canonical set and evidence
None. Evidence: `pass3` (the `_ix` entries of every changed block; check-lean
on the renamed metadata).
-/
module
public import Ix.Ixon
public import Ix.Compile.Pass.Names
public section

namespace Ix.Compile.Pass

open Ix (Name)

/-- Rename name-hash addresses in one metadata arena node. Binder names are
not constant names and stay. -/
def renameNode (m : Std.HashMap Address Address) (n : Ixon.ExprMetaData) : Ixon.ExprMetaData :=
  let r := fun a => (m.get? a).getD a
  match n with
  | .ref a => .ref (r a)
  | .prj a c => .prj (r a) c
  | .callSite a es cm oh => .callSite (r a) es cm oh
  | .etaCallSite k a es cm w => .etaCallSite k (r a) es cm w
  | n => n

/-- Rename name-hash addresses throughout a constant's metadata. -/
def renameMeta (m : Std.HashMap Address Address) (cm : Ixon.ConstantMeta) : Ixon.ConstantMeta :=
  if m.isEmpty then cm else
  let r := fun a => (m.get? a).getD a
  let arena := fun (a : Ixon.ExprMetaArena) => ({ nodes := a.nodes.map (renameNode m) } : Ixon.ExprMetaArena)
  let info : Ixon.ConstantMetaInfo := match cm.info with
    | .empty => .empty
    | .defn n l al cx ar t v => .defn (r n) l (al.map r) (cx.map r) (arena ar) t v
    | .axio n l ar t => .axio (r n) l (arena ar) t
    | .quot n l ar t => .quot (r n) l (arena ar) t
    | .indc n l cs al cx ar t => .indc (r n) l (cs.map r) (al.map r) (cx.map r) (arena ar) t
    | .ctor n l ind ar t => .ctor (r n) l (r ind) (arena ar) t
    | .recr n l rs al cx ar t rr => .recr (r n) l (rs.map r) (al.map r) (cx.map r) (arena ar) t rr
    | .muts al lay => .muts (al.map (·.map r)) lay
  { cm with info }

/-- Rename a `Named` entry's metadata (and its `original`'s). -/
def renameNamed (m : Std.HashMap Address Address) (n : Ixon.Named) : Ixon.Named :=
  { n with constMeta := renameMeta m n.constMeta
           original := n.original.map fun (a, cm) => (a, renameMeta m cm) }

/-- The side-car edit of one changed component's aux registrations. -/
structure SideCarEdit where
  /-- Lean name ↦ display name, for every registration that has one. -/
  display : Std.HashMap Name Name
  /-- Lean names that keep their entry (image kinds). -/
  kept : Std.HashSet Name

/-- Apply the edit to the tail's registrations, in registration order:
`(named, nameToAddr, extraNames)` become the edited lists. Synthetic `Muts`
entries (keyed by block address) keep their keys, with their member lists
renamed for moved names. -/
def SideCarEdit.apply (e : SideCarEdit) (named : Array (Name × Ixon.Named))
    (nameToAddr : Std.HashMap Name Address) (extra : Std.HashSet Name) :
    Array (Name × Ixon.Named) × Std.HashMap Name Address × Std.HashSet Name := Id.run do
  let full : Std.HashMap Address Address := e.display.fold (init := {}) fun m k v =>
    m.insert k.getHash v.getHash
  let moved : Std.HashMap Address Address := e.display.fold (init := {}) fun m k v =>
    if e.kept.contains k then m else m.insert k.getHash v.getHash
  let mut named' : Array (Name × Ixon.Named) := #[]
  for (n, nd) in named do
    match e.display.get? n with
    | some d =>
      if e.kept.contains n then named' := named'.push (n, renameNamed moved nd)
      named' := named'.push (d, renameNamed full nd)
    | none => named' := named'.push (n, renameNamed moved nd)
  let mut n2a := nameToAddr
  for (n, a) in nameToAddr do
    if let some d := e.display.get? n then
      n2a := n2a.insert d a
      if !e.kept.contains n then n2a := n2a.erase n
  let mut extra' := extra
  for n in extra do
    if e.display.contains n && !e.kept.contains n then extra' := extra'.erase n
  return (named', n2a, extra')

end Ix.Compile.Pass

end
