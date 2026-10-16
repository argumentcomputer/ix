/-
  Ix.Compile.Canon.Classes: classes (collapse) and canonical order by
  partition refinement, total.

  The compiler's `sortConsts` (Rust `sort_consts`):

  1. start from one class holding every member, in the seed order
     (`Seed.byNameHash`: sorted by the blake3 hash of the name, an insertion
     sort; `Seed.allOrder`: the caller's order, Lean's `all`);
  2. in each round, every class of two or more members is sorted with the
     comparator of `Order.lean` under the context that maps each member to
     its current class index (`Ix.MutConst.ctx`), and adjacent equal members
     are grouped (`List.sortByM`, a stable natural merge sort, and
     `List.groupByM`, both total, from `Ix.Common`);
  3. every group is then re-sorted by name hash, so the first member has the
     least name hash;
  4. stop when a round leaves the number of classes unchanged (refinement
     only splits, so this is the fixed point; Rust's stopping rule, an
     unchanged class list, agrees). The fuel is the member count plus one;
     exhausting it is an error.

  Collapse is the "equal" relation at the fixed point: members of one class
  are structurally equal once in-block references are read as class indices.
  The representative of a class is its first member.
-/
module
public import Ix.Environment
public import Ix.Mutual
public import Ix.Common
public import Ix.Compile.Canon.Order
@[expose] public section

namespace Ix.Compile.Canon

open Ix (Name MutConst MutCtx)

/-- Insert into name-hash order. -/
def insertByName (x : MutConst) : List MutConst → List MutConst
  | [] => [x]
  | y :: ys => if compare x.name y.name == .gt then y :: insertByName x ys else x :: y :: ys

/-- Name-hash insertion sort. -/
def sortByName : List MutConst → List MutConst
  | [] => []
  | x :: xs => insertByName x (sortByName xs)

/-- Statistics of one refinement. -/
structure SortStats where
  rounds : Nat := 0
  deriving Repr, Inhabited

def refineClass (addr? : Name → Option Address) (ctx : MutCtx) :
    List MutConst → CmpM (List (List MutConst))
  | [] => liftE (.error (.refinement "empty class in sortConsts"))
  | [x] => pure [[x]]
  | xs => do
    let sorted ← xs.sortByM (compareConst addr? ctx)
    -- `groupByM` compares each element with the previous group's head, the
    -- reverse of the sort's orientation; only equality is read.
    let groups ← List.groupByM
      (fun a b => do return (← compareConst addr? ctx a b) == .eq) sorted
    pure (groups.map sortByName)

def refineClasses (addr? : Name → Option Address) (ctx : MutCtx) :
    List (List MutConst) → CmpM (List (List MutConst))
  | [] => pure []
  | c :: cs => do
    let gs ← refineClass addr? ctx c
    let rest ← refineClasses addr? ctx cs
    pure (gs ++ rest)

def sortLoop (addr? : Name → Option Address) :
    Nat → Nat → List (List MutConst) → CmpM (List (List MutConst) × Nat)
  | 0, _, _ => liftE (.error (.refinement "sortConsts did not converge"))
  | fuel + 1, round, classes => do
    let refined ← refineClasses addr? (MutConst.ctx classes) classes
    if classes.length == refined.length then pure (refined, round + 1)
    else sortLoop addr? fuel (round + 1) refined

/-- The classes of `sources` in canonical order, each class's first member
its representative, from the seed `rules.seed`. `addr?` gives external
constants' compiled addresses. No members, no classes. -/
def sortClasses (rules : Rules) (addr? : Name → Option Address)
    (sources : List MutConst) : Except CmpError (List (List MutConst) × SortStats) := do
  if sources.isEmpty then return ([], {})
  let seed := match rules.seed with
    | .byNameHash => sortByName sources
    | .allOrder => sources
  let ((classes, rounds), _) ←
    (sortLoop addr? (sources.length + 1) 0 [seed]).run {}
  if classes.any (·.isEmpty) then .error (.refinement "empty class after sortConsts")
  if sources.length < classes.length then
    .error (.refinement "too many classes after sortConsts")
  return (classes, { rounds })

/-- Class names, for comparison and reporting. -/
def classNames (classes : List (List MutConst)) : Array (Array Name) :=
  classes.toArray.map fun c => c.toArray.map (·.name)

end Ix.Compile.Canon

end
