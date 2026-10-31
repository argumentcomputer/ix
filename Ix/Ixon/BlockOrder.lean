module

public import Ix.Ixon.Projection
public import Ix.Ixon.ReduceUniverse

@[expose] public section

/-! Recursor-block order, outside the hash-free kernel.

The compiler stores every block in its source's order: an inductive block in
the order of Lean's `all`, a definition block in its members' order there,
and a block of recursors in its family's order (`T.rec` for each member, then
`T.rec_1`, …), which is the order of its motives. Any member order of a
non-recursor block is admissible, so only a recursor block's order is checked
(`checkMotives`): member `j` eliminates motive `j` and declares one motive per
member. That is the order in which the Ixon reader regroups a block's
recursors (`Reader.buildIndex` reads each recursor's motive off its type).

This is an ordering check, not a second typechecker or a complete validator
of unused tables: the final kernel admission still checks the entire input.
-/

namespace Ixon.BlockOrder

open Ix.Kernel hiding Expr  -- `Expr` is Ixon's here (the kernel's is `Ix.Kernel.Expr`)
open Ixon (Univ Expr MutConst)

inductive Error where
  | malformed (reason : String)
  /-- a recursor block's member `position` does not eliminate motive
  `position` of a block with one motive per member (`motive`: the motive its
  type eliminates, if it has the recursor shape) -/
  | motiveOrder (owner : Address) (position : Nat) (motive : Option Nat)
  deriving Repr, DecidableEq

/-! ## Recursor blocks: motive order -/

def isRecursor : MutConst → Bool
  | .recr _ => true
  | _ => false

/-- The motive a recursor eliminates, read off its type exactly as the Ixon
reader does (the first component of `Reader.analyseRecursor`): after
the parameters, motives, minors, indices and the major premise, the head of
the result is the bound variable of one of the motives. -/
def recursorMotive (source : Ixon.Constant) (r : Ixon.Recursor) : Option Nat := do
  let nP := r.params.toNat
  let nM := r.motives.toNat
  let depth := nP + nM + r.minors.toNat + r.indices.toNat + 1
  let (_, body) ← Reader.stripAll source depth r.typ
  let .var k := Reader.appHead source Reader.spineFuel body | none
  let pos := depth - 1 - k.toNat
  guard (k.toNat < depth && nP ≤ pos && pos < nP + nM)
  pure (pos - nP)

/-- The members from `position` on are recursors in motive order: the one at
`position` eliminates motive `position`, of `size` motives. -/
def checkMotives (owner : Address) (source : Ixon.Constant) (size : Nat) :
    Nat → List MutConst → Except Error Unit
  | _, [] => .ok ()
  | position, member :: rest => do
    match member with
    | .recr r =>
      let motive := recursorMotive source r
      unless r.motives.toNat == size && motive == some position do
        throw (.motiveOrder owner position motive)
    | _ => throw (.malformed "expected a recursor")
    checkMotives owner source size (position + 1) rest

/-- One record's order check: a recursor block in motive order, nothing
else. -/
def checkRecord (owner : Address) (source : Ixon.Constant) : Except Error Unit :=
  match source.info with
  | .muts members =>
    if members.all isRecursor then checkMotives owner source members.size 0 members.toList
    else .ok ()
  | _ => .ok ()

end Ixon.BlockOrder
