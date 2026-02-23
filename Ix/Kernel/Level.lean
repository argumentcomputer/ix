/-
  Level normalization and comparison for `Level m`.

  Generic over MetaMode — metadata on `.param` is ignored.
  Adapted from Yatima.Datatypes.Univ + Ix.IxVM.Level.
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
  | .param idx _ => match a with
    | .param idx' _ => if idx == idx' then a else .imax a b
    | _ => .imax a b
  | _ => .imax a b

/-- Reduce a level to normal form. -/
def reduce : Level m → Level m
  | .succ u => .succ (reduce u)
  | .max a b => reduceMax (reduce a) (reduce b)
  | .imax a b =>
    let b' := reduce b
    match b' with
    | .zero => .zero
    | .succ _ => reduceMax (reduce a) b'
    | _ => .imax (reduce a) b'
  | u => u

/-! ## Instantiation -/

/-- Instantiate a single variable and reduce. Assumes `subst` is already reduced.
    Does not shift variables (used only in comparison algorithm). -/
def instReduce (u : Level m) (idx : Nat) (subst : Level m) : Level m :=
  match u with
  | .succ u => .succ (instReduce u idx subst)
  | .max a b => reduceMax (instReduce a idx subst) (instReduce b idx subst)
  | .imax a b =>
    let a' := instReduce a idx subst
    let b' := instReduce b idx subst
    match b' with
    | .zero => .zero
    | .succ _ => reduceMax a' b'
    | _ => .imax a' b'
  | .param idx' _ => if idx' == idx then subst else u
  | .zero => u

/-- Instantiate multiple variables at once and reduce. Substitutes `.param idx` by `substs[idx]`.
    Assumes already reduced `substs`. -/
def instBulkReduce (substs : Array (Level m)) : Level m → Level m
  | z@(.zero ..) => z
  | .succ u => .succ (instBulkReduce substs u)
  | .max a b => reduceMax (instBulkReduce substs a) (instBulkReduce substs b)
  | .imax a b =>
    let b' := instBulkReduce substs b
    match b' with
    | .zero => .zero
    | .succ _ => reduceMax (instBulkReduce substs a) b'
    | _ => .imax (instBulkReduce substs a) b'
  | .param idx name =>
    if h : idx < substs.size then substs[idx]
    else .param (idx - substs.size) name

/-! ## Comparison -/

/-- Comparison algorithm: `a <= b + diff`. Assumes `a` and `b` are already reduced. -/
partial def leq (a b : Level m) (diff : _root_.Int) : Bool :=
  if diff >= 0 && match a with | .zero => true | _ => false then true
  else match a, b with
  | .zero, .zero => diff >= 0
  -- Succ cases
  | .succ a, _ => leq a b (diff - 1)
  | _, .succ b => leq a b (diff + 1)
  | .param .., .zero => false
  | .zero, .param .. => diff >= 0
  | .param x _, .param y _ => x == y && diff >= 0
  -- IMax cases
  | .imax _ (.param idx _), _ =>
    leq .zero (instReduce b idx .zero) diff &&
    let s := .succ (.param idx default)
    leq (instReduce a idx s) (instReduce b idx s) diff
  | .imax c (.max e f), _ =>
    let newMax := reduceMax (reduceIMax c e) (reduceIMax c f)
    leq newMax b diff
  | .imax c (.imax e f), _ =>
    let newMax := reduceMax (reduceIMax c f) (.imax e f)
    leq newMax b diff
  | _, .imax _ (.param idx _) =>
    leq (instReduce a idx .zero) .zero diff &&
    let s := .succ (.param idx default)
    leq (instReduce a idx s) (instReduce b idx s) diff
  | _, .imax c (.max e f) =>
    let newMax := reduceMax (reduceIMax c e) (reduceIMax c f)
    leq a newMax diff
  | _, .imax c (.imax e f) =>
    let newMax := reduceMax (reduceIMax c f) (.imax e f)
    leq a newMax diff
  -- Max cases
  | .max c d, _ => leq c b diff && leq d b diff
  | _, .max c d => leq a c diff || leq a d diff
  | _, _ => false

/-- Semantic equality of levels. Assumes `a` and `b` are already reduced. -/
def equalLevel (a b : Level m) : Bool :=
  leq a b 0 && leq b a 0

/-- Faster equality for zero, assumes input is already reduced. -/
def isZero : Level m → Bool
  | .zero => true
  | _ => false

end Level

end Ix.Kernel
