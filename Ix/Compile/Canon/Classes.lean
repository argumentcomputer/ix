/-
  Ix.Compile.Canon.Classes: classes (collapse) and canonical order by
  partition refinement, total.

  Same algorithm as today's `sortConsts` (`Ix/CompileM.lean:2246-2353`;
  Rust `sort_consts`, `compile.rs:3723`):

  1. start from one class holding every member, in the seed order
     (`Seed.byNameHash`: sorted by the blake3 hash of the name, the same
     insertion sort as `sortMutConstMembersByName`; `Seed.allOrder`: the
     caller's order, Lean's `all`);
  2. in each round, every class of two or more members is sorted with the
     comparator of `Order.lean` under the context that maps each member to
     its current class index (`Ix.MutConst.ctx`), and adjacent equal members
     are grouped (`List.sortByM`, a stable natural merge sort, and
     `groupAdjacent`, both total);
  3. today every group is then re-sorted by name hash
     (`Representative.leastNameHash`, today and Phase A); the measurement
     switch `firstInCanonicalOrder` keeps the stable order;
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

/-- Group adjacent equal members, each group in input order. Each element is
compared with its predecessor, `eq later earlier`, the calls
`List.groupByM` makes; unlike it (whose last group comes out reversed), every
group keeps the order of the input, so a class lists its members in the
order the sort left them. -/
def groupAdjacent (eq : MutConst → MutConst → CmpM Bool) :
    List MutConst → CmpM (List (List MutConst))
  | [] => pure []
  | x :: xs => go x [x] [] xs
where
  go (prev : MutConst) (cur : List MutConst) (acc : List (List MutConst)) :
      List MutConst → CmpM (List (List MutConst))
    | [] => pure (cur.reverse :: acc).reverse
    | a :: as => do
      if ← eq a prev then go a (a :: cur) acc as
      else go a [a] (cur.reverse :: acc) as

def refineClass (rules : Rules) (addr? : Name → Option Address) (ctx : MutCtx) :
    List MutConst → CmpM (List (List MutConst))
  | [] => liftE (.error "empty class in sortConsts")
  | [x] => pure [[x]]
  | xs => do
    let sorted ← xs.sortByM (compareConst rules addr? ctx)
    -- `groupAdjacent` compares each element with its predecessor, the
    -- reverse of the sort's orientation; only equality is read, so a reversed
    -- cache hit there is harmless and is not counted as a hazard.
    let h0 := (← get).hazards
    let groups ← groupAdjacent
      (fun a b => do return (← compareConst rules addr? ctx a b) == .eq) sorted
    modify fun st => { st with hazards := h0 }
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
    | .allOrder => sources
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
  -- A7 (D8): no `]!`: the loops carry their bounds and the table is read
  -- through `at2`, a named error out of range.
  let mut tbl : Array (Array Ordering) := #[]
  for hi : i in [0:ms.size] do
    let mut row : Array Ordering := #[]
    for hj : j in [0:ms.size] do
      row := row.push (← compareFresh rules addr? ctx ms[i] ms[j])
    tbl := tbl.push row
  let mut out : Array String := #[]
  let nm := fun (i : Nat) => ((ms[i]?).map (namePretty ·.name)).getD s!"#{i}"
  let at2 := fun (a b : Nat) => match tbl[a]? >>= (·[b]?) with
    | some o => (pure o : Except String Ordering)
    | none => throw s!"preorderViolations: table entry ({a}, {b}) out of range"
  for i in [0:n] do
    if (← at2 i i) != .eq then out := out.push s!"irreflexive: {nm i}"
    for j in [0:n] do
      if (← at2 i j) != (← at2 j i).swap then
        out := out.push s!"not antisymmetric: {nm i} vs {nm j}"
      for k in [0:n] do
        let le := fun (a b : Nat) => do return (← at2 a b) != .gt
        if (← le i j) && (← le j k) && !(← le i k) then
          out := out.push s!"not transitive: {nm i} ≤ {nm j} ≤ {nm k}"
  return out

/-! ## Seed sweep (design document §3.6, leg 3) -/

/-- A deterministic pseudo-random permutation (linear congruential draws,
Fisher-Yates). -/
def shuffle (seed : Nat) (xs : Array α) : Array α := Id.run do
  let mut a := xs
  let mut s := seed * 2654435761 + 12345
  for i' in [0:a.size] do
    let i := a.size - 1 - i'
    s := (s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
    let j := (s / 65536) % (i + 1)
    a := a.swapIfInBounds i j
  return a

/-- Classes as sets (names sorted by hash), in class order. -/
def classSets (classes : List (List MutConst)) : Array (Array Name) :=
  (classNames classes).map (·.qsort fun a b => compare a b == .lt)

/-- Run the refinement from the identity, reverse, name-hash and `random`
pseudo-random presentations of `sources` (seed `allOrder`, so the
presentation is the seed) and report the first presentation whose class
list differs, as sets in order, from the identity's. -/
def seedSweep (rules : Rules) (addr? : Name → Option Address) (sources : List MutConst)
    (random : Nat := 10) : Except String (Option String) := do
  let r := { rules with seed := .allOrder, portFixes := true }
  let run := fun (xs : List MutConst) => do
    let (cls, _) ← sortClasses r addr? xs
    pure (classSets cls)
  let base ← run sources
  let arr := sources.toArray
  let mut presentations : List (String × List MutConst) :=
    [("reverse", sources.reverse), ("name-hash", sortByName sources)]
  for k in [0:random] do
    presentations := presentations ++ [(s!"random {k}", (shuffle k arr).toList)]
  for (label, xs) in presentations do
    let got ← run xs
    if got != base then
      return some s!"{label}: {got.map (·.map namePretty)} vs identity {base.map (·.map namePretty)}"
  return none

end Ix.Compile.Canon

end
