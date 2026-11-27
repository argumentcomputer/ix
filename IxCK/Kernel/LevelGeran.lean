module

public import IxCK.Kernel.Expr

@[expose] public section

/-!
# Géran's sublevels: a complete decision of `l ≤ r + diff`

Yoan Géran, "A Canonical Form for Universe Levels in Impredicative Type
Theory", decomposes a level into *sublevels*. `C(p, c)` is `c` when every
parameter in the condition set `p` is nonzero, and `0` otherwise.
`V(p, x, k)` is `x + k` under the same condition, with `x ∈ p`. A level is
the maximum of its sublevels, and `l ≤ r` holds at every valuation exactly
when each nonzero sublevel of `l` is dominated by a single sublevel of `r`.

`Level.rest` (`IxCK/Kernel/Level.lean`, nanoda's `leq_core`) falls back
on `leq` here when both branches of its `(param, max)` case fail. That case
is the one where nanoda's algorithm is incomplete. It tries each branch of
the `max` on its own, but `x + k` is two sublevels (`x + k` once `x` is
nonzero, `k` otherwise), and they may be dominated in different branches.
An example is `v + 1 ≤ max (imax (max (u+2) (v+1)) v) 1`, Ixon's canonical
form of a level in Mathlib's `RatFunc.liftOn_def`.

The algorithm is the one of the retired intrinsic kernel's level normalizer
(`docs/kernel.md`, "The retired intrinsic kernel"), on the kernel's `Level`,
with named parameters, and structurally recursive. An `imax u v`
is decomposed through the condition sets under which `v` is nonzero
(`nzConds`), not by the distributing rewrites, so no termination measure
is needed. `IxCK/Kernel/Verify/LevelGeran.lean` proves `leq` sound and
complete: `leq l r diff = true` exactly when `l ≤ r + diff` at every
valuation. -/

namespace Ix.Kernel.Level.Geran

/-- A sublevel: `const p c` is Géran's `C(p, c)` and `var p x k` is
`V(p, x, k)`. -/
inductive Sub where
  | const (path : List LevelParam) (c : Nat)
  | var (path : List LevelParam) (x : LevelParam) (k : Nat)

/-- Condition sets under which `l` is nonzero: `l` is nonzero exactly when
every parameter of one of them is nonzero. -/
def nzConds : Level → List (List LevelParam)
  | .zero => []
  | .succ _ => [[]]
  | .param x => [[x]]
  | .max a b => nzConds a ++ nzConds b
  | .imax _ b => nzConds b

/-- The sublevels of `l + k` under the condition set `path`, prepended to
`acc`. `imax u v` is `v`, together with `u` under each condition set that
makes `v` nonzero. -/
def decomposeAux : List LevelParam → Nat → Level → List Sub → List Sub
  | path, k, .zero, acc => .const path k :: acc
  | path, k, .succ u, acc => decomposeAux path (k + 1) u acc
  | path, k, .max u v, acc => decomposeAux path k v (decomposeAux path k u acc)
  | path, k, .imax u v, acc =>
    (nzConds v).foldl (fun acc c => decomposeAux (c ++ path) k u acc)
      (decomposeAux path k v acc)
  | path, k, .param x, acc =>
    if path.contains x then .var path x k :: acc
    else .var (x :: path) x k :: .const path k :: acc

/-- Every parameter of `p` is in `q`. -/
def subset (p q : List LevelParam) : Bool := p.all (q.contains ·)

/-- `C(p, 0)` is `0` under every valuation. -/
def Sub.isZero : Sub → Bool
  | .const _ 0 => true
  | _ => false

/-- `t` dominates `s` under every valuation. -/
def dominates : Sub → Sub → Bool
  | .const p c, .const q c' => subset q p && decide (c ≤ c')
  | .const p c, .var q y k' => subset q p && q.contains y && decide (c ≤ k' + 1)
  | .var _ _ _, .const _ _ => false
  | .var p x k, .var q y k' => subset q p && x == y && decide (k ≤ k')

/-- Every sublevel of `s` is zero or dominated by a sublevel of `t`. -/
def le (s t : List Sub) : Bool := s.all fun a => a.isZero || t.any (dominates a)

/-- **The fallback's budget**: the sublevels of both
sides together. `le` compares them pairwise, so this bounds one fallback's work
by a few million path comparisons; the levels Lean writes decompose into a
handful. -/
def budget : Nat := 2048

/-- Number of condition sets in `nzConds`, computed without allocating
condition-set lists and saturated at `cap + 1` so deep `max`/`imax` chains
never construct bignums. -/
def nzCondCountAt (cap : Nat) : Level → Nat
  | .zero => 0
  | .succ _ => 1
  | .param _ => 1
  | .max a b =>
    let na := nzCondCountAt cap a
    if na > cap then cap + 1
    else min (cap + 1) (na + nzCondCountAt cap b)
  | .imax _ b => nzCondCountAt cap b

/-- Number of condition sets in `nzConds`, saturated at `budget + 1`. -/
def nzCondCount (l : Level) : Nat := nzCondCountAt budget l

/-- The number of sublevels `decomposeAux` produces for a level, at most
(`.param` gives one or two), computed without producing them and saturated at
`cap + 1`: an `imax u v` repeats `u`'s once per condition set of `v`, so the
raw count is exponential in the nesting of such `imax`es while this saturating
computation stays in `O(|level|)` with small machine integers. -/
def sizeBoundAt (cap : Nat) : Level → Nat
  | .zero => 1
  | .succ u => sizeBoundAt cap u
  | .max u v =>
    let su := sizeBoundAt cap u
    if su > cap then cap + 1
    else min (cap + 1) (su + sizeBoundAt cap v)
  | .imax u v =>
    let sv := sizeBoundAt cap v
    if sv > cap then cap + 1
    else
      let nv := nzCondCountAt cap v
      if nv == 0 then sv
      else if nv > cap then cap + 1
      else min (cap + 1) (sv + nv * sizeBoundAt cap u)
  | .param _ => 2

/-- The number of sublevels `decomposeAux` produces for a level, saturated at
`budget + 1`. -/
def sizeBound (l : Level) : Nat := sizeBoundAt budget l

/-- Whether `leq l r _` is within the budget (`sizeBound`, `budget`).
Beyond it `Level.rest` answers as upstream con-leche's comparison does. -/
def withinBudget (l r : Level) : Bool := decide (sizeBound l + sizeBound r ≤ budget)

/-- Decide `l ≤ r + diff` at every valuation, on sublevels: the offset goes
to `l` when `diff` is negative, to `r` otherwise. -/
def leq (l r : Level) (diff : Int) : Bool :=
  if 0 ≤ diff then le (decomposeAux [] 0 l []) (decomposeAux [] diff.natAbs r [])
  else le (decomposeAux [] diff.natAbs l []) (decomposeAux [] 0 r [])

end Ix.Kernel.Level.Geran
