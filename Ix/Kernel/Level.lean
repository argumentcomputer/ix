/-
  Level normalization and comparison for `Level m`.

  Generic over MetaMode — metadata on `.param` is ignored.
  Adapted from Yatima.Datatypes.Univ + Ix.IxVM.Level.

  Complete normalization based on Yoan Géran,
  "A Canonical Form for Universe Levels in Impredicative Type Theory"
  <https://lmf.cnrs.fr/downloads/Perso/long.pdf>.
  Ported from lean4lean `Lean4Lean/Level.lean`.
-/
import Init.Data.Int
import Ix.Kernel.Types

namespace Ix.Kernel

namespace Level

/-! ## Reduction -/

/-- Reduce `max a b` assuming `a` and `b` are already reduced. -/
def reduceMax (a b : Level m) : Level m :=
  match a, b with
  | .zero, _ => b
  | _, .zero => a
  | .succ a, .succ b => .succ (reduceMax a b)
  | .param idx _, .param idx' _ => if idx == idx' then a else .max a b
  | _, _ => .max a b

/-- Reduce `imax a b` assuming `a` and `b` are already reduced. -/
def reduceIMax (a b : Level m) : Level m :=
  match b with
  | .zero => .zero
  | .succ _ => reduceMax a b
  | _ =>
    match a with
    | .zero => b
    | .succ .zero => b -- imax(1, b) = b
    | .param idx' _ => match b with
      | .param idx _ => if idx == idx' then a else .imax a b
      | _ => .imax a b
    | _ => .imax a b

/-- Reduce a level to normal form. -/
def reduce : Level m → Level m
  | .succ u => .succ (reduce u)
  | .max a b => reduceMax (reduce a) (reduce b)
  | .imax a b => reduceIMax (reduce a) (reduce b)
  | u => u

/-! ## Instantiation -/

/-- Instantiate a single variable and reduce. Assumes `subst` is already reduced.
    Does not shift variables (used only in comparison algorithm). -/
def instReduce (u : Level m) (idx : Nat) (subst : Level m) : Level m :=
  match u with
  | .succ u => .succ (instReduce u idx subst)
  | .max a b => reduceMax (instReduce a idx subst) (instReduce b idx subst)
  | .imax a b => reduceIMax (instReduce a idx subst) (instReduce b idx subst)
  | .param idx' _ => if idx' == idx then subst else u
  | .zero => u

/-- Instantiate multiple variables at once and reduce. Substitutes `.param idx` by `substs[idx]`.
    Assumes already reduced `substs`. -/
def instBulkReduce (substs : Array (Level m)) : Level m → Level m
  | z@(.zero ..) => z
  | .succ u => .succ (instBulkReduce substs u)
  | .max a b => reduceMax (instBulkReduce substs a) (instBulkReduce substs b)
  | .imax a b => reduceIMax (instBulkReduce substs a) (instBulkReduce substs b)
  | .param idx name =>
    if h : idx < substs.size then substs[idx]
    else .param (idx - substs.size) name

/-! ## Heuristic comparison (C++ style) -/

/-- Heuristic comparison: `a <= b + diff`. Sound but incomplete on nested imax.
    Assumes `a` and `b` are already reduced. -/
partial def leqHeuristic (a b : Level m) (diff : _root_.Int) : Bool :=
  if diff >= 0 && match a with | .zero => true | _ => false then true
  else match a, b with
  | .zero, .zero => diff >= 0
  -- Succ cases
  | .succ a, _ => leqHeuristic a b (diff - 1)
  | _, .succ b => leqHeuristic a b (diff + 1)
  | .param .., .zero => false
  | .zero, .param .. => diff >= 0
  | .param x _, .param y _ => x == y && diff >= 0
  -- IMax cases
  | .imax _ (.param idx _), _ =>
    leqHeuristic .zero (instReduce b idx .zero) diff &&
    let s := .succ (.param idx default)
    leqHeuristic (instReduce a idx s) (instReduce b idx s) diff
  | .imax c (.max e f), _ =>
    let newMax := reduceMax (reduceIMax c e) (reduceIMax c f)
    leqHeuristic newMax b diff
  | .imax c (.imax e f), _ =>
    let newMax := reduceMax (reduceIMax c f) (.imax e f)
    leqHeuristic newMax b diff
  | _, .imax _ (.param idx _) =>
    leqHeuristic (instReduce a idx .zero) .zero diff &&
    let s := .succ (.param idx default)
    leqHeuristic (instReduce a idx s) (instReduce b idx s) diff
  | _, .imax c (.max e f) =>
    let newMax := reduceMax (reduceIMax c e) (reduceIMax c f)
    leqHeuristic a newMax diff
  | _, .imax c (.imax e f) =>
    let newMax := reduceMax (reduceIMax c f) (.imax e f)
    leqHeuristic a newMax diff
  -- Max cases
  | .max c d, _ => leqHeuristic c b diff && leqHeuristic d b diff
  | _, .max c d => leqHeuristic a c diff || leqHeuristic a d diff
  | _, _ => false

/-- Heuristic semantic equality of levels. Sound but incomplete. -/
def equalLevelHeuristic (a b : Level m) : Bool :=
  leqHeuristic a b 0 && leqHeuristic b a 0

/-! ## Complete canonical-form normalization -/

namespace Normalize

-- Explicit compare references to avoid Level.compare shadowing
private abbrev cmpNat : Nat → Nat → Ordering := _root_.Ord.compare
private abbrev cmpNatList : List Nat → List Nat → Ordering := _root_.Ord.compare

/-- Represents variable `idx + offset` in the canonical form. -/
structure VarNode where
  idx : Nat
  offset : Nat
  deriving BEq, Repr

instance : Ord VarNode where
  compare a b := (cmpNat a.idx b.idx).then <| cmpNat a.offset b.offset

/-- A node in the canonical form: the max of a constant and a list of variable offsets. -/
structure Node where
  const : Nat := 0
  var : List VarNode := []
  deriving Repr, Inhabited

instance : BEq Node where
  beq n₁ n₂ := n₁.const == n₂.const && n₁.var == n₂.var

/-- Check if sorted list `xs` is a subset of sorted list `ys`. -/
def subset (cmp : α → α → Ordering) : List α → List α → Bool
  | [], _ => true
  | _, [] => false
  | x :: xs, y :: ys =>
    match cmp x y with
    | .lt => false
    | .eq => subset cmp xs ys
    | .gt => subset cmp (x :: xs) ys

/-- Insert into a sorted list. Returns `none` if element already present. -/
def orderedInsert (a : Nat) : List Nat → Option (List Nat)
  | [] => some [a]
  | b :: l =>
    match cmpNat a b with
    | .lt => some (a :: b :: l)
    | .eq => none
    | .gt => (orderedInsert a l).map (b :: ·)

/-- Canonical form: a map from sorted paths (lists of param indices) to nodes. -/
def NormLevel := Std.TreeMap (List Nat) Node cmpNatList
  deriving Repr

instance : BEq NormLevel where
  beq l₁ l₂ :=
    (l₁.all fun p n => l₂.get? p == some n) &&
    (l₂.all fun p n => l₁.get? p == some n)

/-- Merge a variable into a sorted list of VarNodes (by idx, taking max offset). -/
def VarNode.addVar (idx : Nat) (k : Nat) : List VarNode → List VarNode
  | [] => [⟨idx, k⟩]
  | v :: l =>
    match cmpNat idx v.idx with
    | .lt => ⟨idx, k⟩ :: v :: l
    | .eq => ⟨idx, v.offset.max k⟩ :: l
    | .gt => v :: addVar idx k l

def NormLevel.addVar (idx : Nat) (k : Nat) (path : List Nat) (s : NormLevel) : NormLevel :=
  s.modify path fun n => { n with var := VarNode.addVar idx k n.var }

def NormLevel.addNode (idx : Nat) (path : List Nat) (s : NormLevel) : NormLevel :=
  s.alter path fun
    | none => some { var := [⟨idx, 0⟩] }
    | some n => some { n with var := VarNode.addVar idx 0 n.var }

def NormLevel.addConst (k : Nat) (path : List Nat) (acc : NormLevel) : NormLevel :=
  if k = 0 || k = 1 && !path.isEmpty then acc else
  acc.modify path fun n => { n with const := k.max n.const }

/-- Core recursive normalizer. Converts a level expression into canonical form.
    `path` tracks the imax-guard variables, `k` is the accumulated succ offset. -/
def normalizeAux (l : Level m) (path : List Nat) (k : Nat) (acc : NormLevel) : NormLevel :=
  match l with
  | .zero | .imax _ .zero => acc.addConst k path
  | .succ u => normalizeAux u path (k+1) acc
  | .max u v => normalizeAux u path k acc |> normalizeAux v path k
  | .imax u (.succ v) => normalizeAux u path k acc |> normalizeAux v path (k+1)
  | .imax u (.max v w) => normalizeAux (.imax u v) path k acc |> normalizeAux (.imax u w) path k
  | .imax u (.imax v w) => normalizeAux (.imax u w) path k acc |> normalizeAux (.imax v w) path k
  | .imax u (.param idx _) =>
    match orderedInsert idx path with
    | some path' => acc.addNode idx path' |> normalizeAux u path' k
    | none => normalizeAux u path k acc
  | .param idx _ =>
    match orderedInsert idx path with
    | some path' =>
      let acc := acc.addConst k path |>.addNode idx path'
      if k = 0 then acc else acc.addVar idx k path'
    | none => if k = 0 then acc else acc.addVar idx k path

/-- Remove variables from `xs` that are subsumed by `ys` (same idx, offset ≤). -/
def subsumeVars : List VarNode → List VarNode → List VarNode
  | [], _ => []
  | xs, [] => xs
  | x :: xs, y :: ys =>
    match cmpNat x.idx y.idx with
    | .lt => x :: subsumeVars xs (y :: ys)
    | .eq => if x.offset ≤ y.offset then subsumeVars xs ys else x :: subsumeVars xs ys
    | .gt => subsumeVars (x :: xs) ys

/-- Apply subsumption to remove redundant terms in the canonical form. -/
def NormLevel.subsumption (acc : NormLevel) : NormLevel :=
  acc.foldl (init := acc) fun acc p₁ n₁ =>
    let n₁ := acc.foldl (init := n₁) fun n₁ p₂ n₂ =>
      if !subset cmpNat p₂ p₁ then n₁ else
      let same := p₁.length == p₂.length
      let n₁ :=
        if n₁.const = 0 ||
          (same || n₁.const > n₂.const) &&
          (n₂.var.isEmpty || n₁.const > n₁.var.foldl (·.max ·.offset) 0 + 1)
        then n₁ else { n₁ with const := 0 }
      if same || n₂.var.isEmpty then n₁ else { n₁ with var := subsumeVars n₁.var n₂.var }
    acc.insert p₁ n₁

/-- Normalize a level to canonical form. -/
def normalize (l : Level m) : NormLevel :=
  let init : NormLevel := (Std.TreeMap.empty).insert [] default
  normalizeAux l [] 0 init |>.subsumption

/-- Check if all variables in `xs` are dominated by variables in `ys`. -/
def leVars : List VarNode → List VarNode → Bool
  | [], _ => true
  | _, [] => false
  | x :: xs, y :: ys =>
    match cmpNat x.idx y.idx with
    | .lt => false
    | .eq => x.offset ≤ y.offset && leVars xs ys
    | .gt => leVars (x :: xs) ys

/-- Check `l₁ ≤ l₂` on canonical forms. -/
def NormLevel.le (l₁ l₂ : NormLevel) : Bool :=
  l₁.all fun p₁ n₁ =>
    if n₁.const = 0 && n₁.var.isEmpty then true else
    l₂.any fun p₂ n₂ =>
      (!n₂.var.isEmpty || n₁.var.isEmpty) &&
      subset cmpNat p₂ p₁ &&
      (n₁.const ≤ n₂.const || n₂.var.any (n₁.const ≤ ·.offset + 1)) &&
      leVars n₁.var n₂.var

end Normalize

/-! ## Comparison with fallback -/

/-- Comparison algorithm: `a <= b + diff`. Assumes `a` and `b` are already reduced.
    Uses heuristic as fast path, with complete normalization as fallback for `diff = 0`. -/
partial def leq (a b : Level m) (diff : _root_.Int) : Bool :=
  leqHeuristic a b diff ||
  (diff == 0 && (Normalize.normalize a).le (Normalize.normalize b))

/-- Semantic equality of levels. Assumes `a` and `b` are already reduced.
    Uses heuristic as fast path, with complete normalization as fallback. -/
def equalLevel (a b : Level m) : Bool :=
  equalLevelHeuristic a b ||
  Normalize.normalize a == Normalize.normalize b

/-- Faster equality for zero, assumes input is already reduced. -/
def isZero : Level m → Bool
  | .zero => true
  | _ => false

end Level

end Ix.Kernel
