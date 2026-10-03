/-
  Ix.Compile.Canon.Classes: classes (collapse) and canonical order by
  partition refinement, total.

  Same algorithm as today's `sortConsts` (`Ix/CompileM.lean:2246-2353`;
  Rust `sort_consts`, `compile.rs:3723`):

  1. start from one class holding every member, in the seed order
     (`Seed.byNameHash`: sorted by the blake3 hash of the name, the same
     insertion sort as `sortMutConstMembersByName`; `Seed.structural`: the
     caller's order, Lean's `all`);
  2. in each round, every class of two or more members is sorted with the
     comparator of `Order.lean` under the context that maps each member to
     its current class index (`Ix.MutConst.ctx`), and adjacent equal members
     are grouped (`List.sortByM`, a stable natural merge sort, and
     `List.groupByM`, both total, from `Ix.Common`);
  3. today every group is then re-sorted by name hash
     (`Representative.leastNameHash`); Phase A keeps the stable order
     (`firstInCanonicalOrder`);
  4. stop when a round leaves the number of classes unchanged (refinement
     only splits, so this is the fixed point; Rust's stopping rule, an
     unchanged class list, agrees). The fuel is the member count plus one;
     exhausting it is an error, as today.

  Collapse is the "equal" relation at the fixed point: members of one class
  are structurally equal once in-block references are read as class indices.
  The representative of a class is its first member.

  `preorderViolations` is the comparator study's exhaustive check on one
  block: at the fixed-point context, every pair must be antisymmetric and
  every triple transitive.
-/
module
public import Ix.Environment
public import Ix.Mutual
public import Ix.Common
public import Ix.Compile.Canon.Order
public section

namespace Ix.Compile.Canon

open Ix (Name MutConst MutCtx)

/-- Insert into name-hash order (`insertSortMutConstMemberByName`). -/
def insertByName (x : MutConst) : List MutConst → List MutConst
  | [] => [x]
  | y :: ys => if compare x.name y.name == .gt then y :: insertByName x ys else x :: y :: ys

/-- Name-hash insertion sort (`sortMutConstMembersByName`). -/
def sortByName : List MutConst → List MutConst
  | [] => []
  | x :: xs => insertByName x (sortByName xs)

/-- Statistics of one refinement. -/
structure SortStats where
  rounds : Nat := 0
  /-- `byAddress` comparisons decided by addresses. -/
  addrDecided : Nat := 0
  /-- Reversed non-equal cache hits (see `Order.lean`). -/
  hazards : Nat := 0
  deriving Repr, Inhabited

def refineClass (rules : Rules) (addr? : Name → Option Address) (ctx : MutCtx) :
    List MutConst → CmpM (List (List MutConst))
  | [] => liftE (.error "empty class in sortConsts")
  | [x] => pure [[x]]
  | xs => do
    let sorted ← xs.sortByM (compareConst rules addr? ctx)
    let groups ← List.groupByM
      (fun a b => do return (← compareConst rules addr? ctx a b) == .eq) sorted
    pure <| match rules.representative with
      | .leastNameHash => groups.map sortByName
      | .firstInCanonicalOrder => groups

def refineClasses (rules : Rules) (addr? : Name → Option Address) (ctx : MutCtx) :
    List (List MutConst) → CmpM (List (List MutConst))
  | [] => pure []
  | c :: cs => do
    let gs ← refineClass rules addr? ctx c
    let rest ← refineClasses rules addr? ctx cs
    pure (gs ++ rest)

def sortLoop (rules : Rules) (addr? : Name → Option Address) :
    Nat → Nat → List (List MutConst) → CmpM (List (List MutConst) × Nat)
  | 0, _, _ => liftE (.error "sortConsts did not converge")
  | fuel + 1, round, classes => do
    let refined ← refineClasses rules addr? (MutConst.ctx classes) classes
    if classes.length == refined.length then pure (refined, round + 1)
    else sortLoop rules addr? fuel (round + 1) refined

/-- The classes of `sources` in canonical order, each class's first member
its representative. `addr?` gives external constants' compiled addresses
(unused under `TieBreak.blind`). -/
def sortClasses (rules : Rules) (addr? : Name → Option Address)
    (sources : List MutConst) : Except String (List (List MutConst) × SortStats) := do
  if sources.isEmpty then return ([], {})
  let seed := match rules.seed with
    | .byNameHash => sortByName sources
    | .structural => sources
  let ((classes, rounds), st) ←
    (sortLoop rules addr? (sources.length + 1) 0 [seed]).run {}
  if classes.any (·.isEmpty) then .error "empty class after sortConsts"
  if sources.length < classes.length then .error "too many classes after sortConsts"
  return (classes, { rounds, addrDecided := st.addrDecided, hazards := st.hazards })

/-- Class names, for comparison and reporting. -/
def classNames (classes : List (List MutConst)) : Array (Array Name) :=
  classes.toArray.map fun c => c.toArray.map (·.name)

/-- The same refinement with every external reference equal: if it yields
the same classes, the order is decided without addresses. -/
def sortClassesBlind (rules : Rules) (sources : List MutConst) :
    Except String (List (List MutConst)) :=
  (·.1) <$> sortClasses { rules with tieBreak := .blind } (fun _ => none) sources

/-! ## Comparator study -/

/-- Uncached comparison under `rules` at context `ctx`. -/
def compareFresh (rules : Rules) (addr? : Name → Option Address) (ctx : MutCtx)
    (x y : MutConst) : Except String Ordering :=
  (·.1) <$> (compareConst rules addr? ctx x y).run {}

/-- Pairs that are not antisymmetric and triples that are not transitive at
the fixed-point context of `classes` (members flattened), each as a short
description. Exhaustive: cubic in the member count. -/
def preorderViolations (rules : Rules) (addr? : Name → Option Address)
    (classes : List (List MutConst)) : Except String (Array String) := do
  let ctx := MutConst.ctx classes
  let ms := classes.flatten.toArray
  let n := ms.size
  let mut tbl : Array (Array Ordering) := #[]
  for i in [0:n] do
    let mut row : Array Ordering := #[]
    for j in [0:n] do
      row := row.push (← compareFresh rules addr? ctx ms[i]! ms[j]!)
    tbl := tbl.push row
  let mut out : Array String := #[]
  let nm := fun (i : Nat) => namePretty ms[i]!.name
  for i in [0:n] do
    if tbl[i]![i]! != .eq then out := out.push s!"irreflexive: {nm i}"
    for j in [0:n] do
      if tbl[i]![j]! != tbl[j]![i]!.swap then
        out := out.push s!"not antisymmetric: {nm i} vs {nm j}"
      for k in [0:n] do
        let le := fun (a b : Nat) => tbl[a]![b]! != .gt
        if le i j && le j k && !le i k then
          out := out.push s!"not transitive: {nm i} ≤ {nm j} ≤ {nm k}"
  return out

end Ix.Compile.Canon

end
