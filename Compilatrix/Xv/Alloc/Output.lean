import Compilatrix.Xv.Syntax

/-!
# An allocation: the allocator's certificate

What the untrusted allocator emits for one Xv function (05 §5, D17): a
location for every operand, the moves it inserts, and the abstract state
at each block's entry. `Alloc.apply` turns it into Xl; the validator
re-checks it. Everything is plain data in lists, in label order, so the
validator can walk it structurally in the kernel.

**Edits.** `edits` holds `(i, move dst src)`: before body instruction `i`,
or before the terminator when `i` is the body size, in order. Edge moves
are edits too: an edge `b → s` whose target has one predecessor puts them
first among `s`'s edits at 0; otherwise its source has one successor (no
critical edges) and they come last among `b`'s edits before the
terminator. This is where 05 §5's `edgeEdits` would go, so the validator
needs no separate case (a divergence in form, not in meaning).

**Certificates** (`cert`): the facts that hold on entry to the block, after
the incoming edge has bound its parameters and before any of its edits, as
`(location, registers)` pairs. The validator checks them against the entry
convention (block 0) and against every incoming edge, instead of computing
a fixpoint; a wrong certificate is rejected, never trusted.
-/

namespace Compilatrix.Xv.Alloc

open Compilatrix.Lir (VReg)

/-- An inserted copy; never from one stack cell to another. -/
inductive Edit where
  | move (dst src : Loc)
  deriving DecidableEq, Repr, Inhabited

structure BlockOut where
  /-- One list per body instruction: its operands' locations, in
  `Inst.operands` order (uses, then definitions). -/
  locs : List (List Loc) := []
  /-- The terminator's operands' locations, in `Term.operands` order. -/
  termLocs : List Loc := []
  /-- Moves before body instruction `i` (the body size: the terminator). -/
  edits : List (Nat × Edit) := []
  /-- The facts on entry, after parameter binding and before any edit. -/
  cert : List (Loc × List VReg) := []
  deriving DecidableEq, Repr, Inhabited

/-- The allocation of one function. -/
structure Output where
  /-- One entry per block, in label order. -/
  blocks : List BlockOut
  /-- Frame slots `0 … numSlots − 1`. -/
  numSlots : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Counts of the edits, for reports (MEAS-4 wants spills, reloads and moves). -/
structure EditCounts where
  /-- Register to stack cell. -/
  spills : Nat := 0
  /-- Stack cell to register. -/
  reloads : Nat := 0
  /-- Register to register. -/
  moves : Nat := 0
  deriving Repr, Inhabited, BEq

def EditCounts.add (a b : EditCounts) : EditCounts :=
  { spills := a.spills + b.spills, reloads := a.reloads + b.reloads, moves := a.moves + b.moves }

def Edit.counts : Edit → EditCounts
  | .move dst src =>
      match dst.isCell, src.isCell with
      | true, false => { spills := 1 }
      | false, true => { reloads := 1 }
      | _, _ => { moves := 1 }

def Output.counts (o : Output) : EditCounts :=
  o.blocks.foldl (fun c b => b.edits.foldl (fun c (_, e) => c.add e.counts) c) {}

def Output.editCount (o : Output) : Nat := o.blocks.foldl (fun n b => n + b.edits.length) 0

end Compilatrix.Xv.Alloc
