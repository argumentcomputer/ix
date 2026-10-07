/-
  Ix.Compile.Clique.Dag: the de Bruijn and locally nameless helpers of the
  clique transport, walked over distinct subterms.

  A theorem clique's proof is a heavily shared DAG. The helpers of
  `Ix.Compile.Canon.Expr` (`liftLoose`, `lowerLoose`, `looseAtLeast`,
  `instantiateRev`) and `Ix.Compile.Image.Expr` (`instLocals`,
  `abstractFVars`, `mkLambda`, `mkForall`) are structural recursions that walk
  such a term as its unshared tree and rebuild every node: the transport of
  one large theorem clique can repeat the same node in many branches. The functions here
  have the same names, arguments and results; the transport
  (`Ix/Compile/Clique/**`) uses them in place of those helpers, which are
  unchanged (Pass 1 and the image generator keep theirs).

  For hash-consistent terms built by the hashing constructors, these walks
  preserve the original results using two devices:
  * **a memo by subterm and binder depth** within one call: each helper is a
    function of the subterm and the depth below the call's root (its other
    arguments are fixed during the call), and `Ix.Expr`'s equality is the
    equality of its Blake3 hashes;
  * **a subterm the helper rebuilds unchanged is returned as it is**: one
    with no loose bound variable at or above the cutoff (`looseRange`, a
    memo by the subterm) for `liftLoose`, `lowerLoose` and `instantiateRev`,
    and one without free variables for `abstractFVars`. The helpers rebuild
    such a subterm through the hashing constructors (`Expr.mkApp`, …) from the
    same parts; the transport's terms are built by the same constructors
    (`Ix.CanonM.canonExpr` and the transport itself), so the rebuilt node is
    the same term with the same hash.

  Total: structural recursion. Each call allocates its own tables.
-/
module
public import Ix.Environment
public import Ix.Compile.Image.Expr
public section

namespace Ix.Compile.Clique

open Ix (Name Expr)
open Ix.Compile.Image (Local)

/-- The tables of one call. -/
structure DagMemo where
  /-- `1 +` the greatest loose bound variable of the subterm (`0`: none) -/
  range : Std.HashMap Expr Nat := {}
  /-- the subterm has a free variable -/
  fvars : Std.HashMap Expr Bool := {}
  /-- a helper's result by subterm and depth -/
  out : Std.HashMap (Expr × Nat) Expr := {}
  /-- a Boolean helper's result by subterm and depth -/
  bools : Std.HashMap (Expr × Nat) Bool := {}

abbrev DagM := StateM DagMemo

/-- `1 +` the greatest loose bound variable of `e`, `0` when `e` is closed
(Lean's `looseBVarRange`), memoised by the subterm. -/
def looseRangeM : Expr → DagM Nat
  | .bvar i _ => pure (i + 1)
  | e@(.app f a _) => cached e do
    let rf ← looseRangeM f
    let ra ← looseRangeM a
    pure (Nat.max rf ra)
  | e@(.lam _ t b _ _) => cached e do
    let rt ← looseRangeM t
    let rb ← looseRangeM b
    pure (Nat.max rt (rb - 1))
  | e@(.forallE _ t b _ _) => cached e do
    let rt ← looseRangeM t
    let rb ← looseRangeM b
    pure (Nat.max rt (rb - 1))
  | e@(.letE _ t v b _ _) => cached e do
    let rt ← looseRangeM t
    let rv ← looseRangeM v
    let rb ← looseRangeM b
    pure (Nat.max (Nat.max rt rv) (rb - 1))
  | e@(.proj _ _ s _) => cached e (looseRangeM s)
  | e@(.mdata _ s _) => cached e (looseRangeM s)
  | _ => pure 0
where
  cached (e : Expr) (k : DagM Nat) : DagM Nat := do
    if let some r := (← get).range.get? e then return r
    let r ← k
    modify fun m => { m with range := m.range.insert e r }
    return r

/-- `e` has a free variable, memoised by the subterm. -/
def hasFVarM : Expr → DagM Bool
  | .fvar .. => pure true
  | e@(.app f a _) => cached e do
    if ← hasFVarM f then pure true else hasFVarM a
  | e@(.lam _ t b _ _) => cached e do
    if ← hasFVarM t then pure true else hasFVarM b
  | e@(.forallE _ t b _ _) => cached e do
    if ← hasFVarM t then pure true else hasFVarM b
  | e@(.letE _ t v b _ _) => cached e do
    if ← hasFVarM t then pure true else if ← hasFVarM v then pure true else hasFVarM b
  | e@(.proj _ _ s _) => cached e (hasFVarM s)
  | e@(.mdata _ s _) => cached e (hasFVarM s)
  | _ => pure false
where
  cached (e : Expr) (k : DagM Bool) : DagM Bool := do
    if let some r := (← get).fvars.get? e then return r
    let r ← k
    modify fun m => { m with fvars := m.fvars.insert e r }
    return r

/-- The result `k ()` of a helper at the subterm `e`, depth `d`, memoised;
`e` itself when every loose bound variable of `e` is below `bound` (the
helper rebuilds such a subterm unchanged). -/
@[inline] def memoAt (e : Expr) (d bound : Nat) (k : Unit → DagM Expr) : DagM Expr := do
  if (← looseRangeM e) ≤ bound then return e
  if let some r := (← get).out.get? (e, d) then return r
  let r ← k ()
  modify fun m => { m with out := m.out.insert (e, d) r }
  return r

/-! ## de Bruijn arithmetic (`Ix.Compile.Canon.Expr`) -/

/-- `Canon.liftLoose`: add `n` to every loose bound variable `≥ cutoff`. -/
def liftLooseM (n : Nat) : Expr → Nat → DagM Expr
  | .bvar i _, c => pure (if i ≥ c then Expr.mkBVar (i + n) else Expr.mkBVar i)
  | e@(.app f a _), c => memoAt e c c fun _ => do
    let f' ← liftLooseM n f c
    let a' ← liftLooseM n a c
    pure (Expr.mkApp f' a')
  | e@(.lam nm t b bi _), c => memoAt e c c fun _ => do
    let t' ← liftLooseM n t c
    let b' ← liftLooseM n b (c + 1)
    pure (Expr.mkLam nm t' b' bi)
  | e@(.forallE nm t b bi _), c => memoAt e c c fun _ => do
    let t' ← liftLooseM n t c
    let b' ← liftLooseM n b (c + 1)
    pure (Expr.mkForallE nm t' b' bi)
  | e@(.letE nm t v b nd _), c => memoAt e c c fun _ => do
    let t' ← liftLooseM n t c
    let v' ← liftLooseM n v c
    let b' ← liftLooseM n b (c + 1)
    pure (Expr.mkLetE nm t' v' b' nd)
  | e@(.proj nm i s _), c => memoAt e c c fun _ => do
    let s' ← liftLooseM n s c
    pure (Expr.mkProj nm i s')
  | e@(.mdata md x _), c => memoAt e c c fun _ => do
    let x' ← liftLooseM n x c
    pure (Expr.mkMData md x')
  | e, _ => pure e

/-- `Canon.liftLoose`, over distinct subterms. -/
def liftLoose (e : Expr) (n : Nat) (cutoff : Nat := 0) : Expr :=
  if n == 0 then e else (liftLooseM n e cutoff).run' {}

/-- `Canon.lowerLoose`: subtract `n` from every loose bound variable
`≥ cutoff + n`. -/
def lowerLooseM (n : Nat) : Expr → Nat → DagM Expr
  | .bvar i _, c => pure (if i ≥ c + n then Expr.mkBVar (i - n) else Expr.mkBVar i)
  | e@(.app f a _), c => memoAt e c (c + n) fun _ => do
    let f' ← lowerLooseM n f c
    let a' ← lowerLooseM n a c
    pure (Expr.mkApp f' a')
  | e@(.lam nm t b bi _), c => memoAt e c (c + n) fun _ => do
    let t' ← lowerLooseM n t c
    let b' ← lowerLooseM n b (c + 1)
    pure (Expr.mkLam nm t' b' bi)
  | e@(.forallE nm t b bi _), c => memoAt e c (c + n) fun _ => do
    let t' ← lowerLooseM n t c
    let b' ← lowerLooseM n b (c + 1)
    pure (Expr.mkForallE nm t' b' bi)
  | e@(.letE nm t v b nd _), c => memoAt e c (c + n) fun _ => do
    let t' ← lowerLooseM n t c
    let v' ← lowerLooseM n v c
    let b' ← lowerLooseM n b (c + 1)
    pure (Expr.mkLetE nm t' v' b' nd)
  | e@(.proj nm i s _), c => memoAt e c (c + n) fun _ => do
    let s' ← lowerLooseM n s c
    pure (Expr.mkProj nm i s')
  | e@(.mdata md x _), c => memoAt e c (c + n) fun _ => do
    let x' ← lowerLooseM n x c
    pure (Expr.mkMData md x')
  | e, _ => pure e

/-- `Canon.lowerLoose`, over distinct subterms. -/
def lowerLoose (e : Expr) (n : Nat) (cutoff : Nat := 0) : Expr :=
  if n == 0 then e else (lowerLooseM n e cutoff).run' {}

/-- `Canon.looseAtLeast`'s walk at depth `k`: every loose bound variable of
`e` that is loose for the root is at least `d` above it. -/
def looseAtLeastM (d : Nat) : Expr → Nat → DagM Bool
  | .bvar i _, k => pure (i < k || i - k ≥ d)
  | e@(.app f a _), k => cached e k do
    if !(← looseAtLeastM d f k) then pure false else looseAtLeastM d a k
  | e@(.lam _ t b _ _), k => cached e k do
    if !(← looseAtLeastM d t k) then pure false else looseAtLeastM d b (k + 1)
  | e@(.forallE _ t b _ _), k => cached e k do
    if !(← looseAtLeastM d t k) then pure false else looseAtLeastM d b (k + 1)
  | e@(.letE _ t v b _ _), k => cached e k do
    if !(← looseAtLeastM d t k) then pure false
    else if !(← looseAtLeastM d v k) then pure false
    else looseAtLeastM d b (k + 1)
  | e@(.proj _ _ s _), k => cached e k (looseAtLeastM d s k)
  | e@(.mdata _ s _), k => cached e k (looseAtLeastM d s k)
  | _, _ => pure true
where
  /-- a subterm with no bound variable loose for the root is `true` -/
  cached (e : Expr) (k : Nat) (act : DagM Bool) : DagM Bool := do
    if (← looseRangeM e) ≤ k then return true
    if let some r := (← get).bools.get? (e, k) then return r
    let r ← act
    modify fun m => { m with bools := m.bools.insert (e, k) r }
    return r

/-- `Canon.looseAtLeast`, over distinct subterms. -/
def looseAtLeast (e : Expr) (d : Nat) : Bool := (looseAtLeastM d e 0).run' {}

/-- `Canon.instantiateRevAt` at depth `depth`. -/
def instantiateRevAtM (args : Array Expr) : Expr → Nat → DagM Expr
  | e@(.bvar i _), depth => memoAt e depth depth fun _ =>
    if i ≥ depth then
      let r := i - depth
      if h : r < args.size then pure (liftLoose args[r] depth)
      else pure (Expr.mkBVar (i - args.size))
    else pure (Expr.mkBVar i)
  | e@(.app f a _), d => memoAt e d d fun _ => do
    let f' ← instantiateRevAtM args f d
    let a' ← instantiateRevAtM args a d
    pure (Expr.mkApp f' a')
  | e@(.lam nm t b bi _), d => memoAt e d d fun _ => do
    let t' ← instantiateRevAtM args t d
    let b' ← instantiateRevAtM args b (d + 1)
    pure (Expr.mkLam nm t' b' bi)
  | e@(.forallE nm t b bi _), d => memoAt e d d fun _ => do
    let t' ← instantiateRevAtM args t d
    let b' ← instantiateRevAtM args b (d + 1)
    pure (Expr.mkForallE nm t' b' bi)
  | e@(.letE nm t v b nd _), d => memoAt e d d fun _ => do
    let t' ← instantiateRevAtM args t d
    let v' ← instantiateRevAtM args v d
    let b' ← instantiateRevAtM args b (d + 1)
    pure (Expr.mkLetE nm t' v' b' nd)
  | e@(.proj nm i s _), d => memoAt e d d fun _ => do
    let s' ← instantiateRevAtM args s d
    pure (Expr.mkProj nm i s')
  | e@(.mdata md x _), d => memoAt e d d fun _ => do
    let x' ← instantiateRevAtM args x d
    pure (Expr.mkMData md x')
  | e, _ => pure e

/-- `Canon.instantiateRev`: `args[i]` for loose `bvar i`, over distinct
subterms. -/
def instantiateRev (body : Expr) (args : Array Expr) : Expr :=
  if args.isEmpty then body else (instantiateRevAtM args body 0).run' {}

/-! ## Locally nameless (`Ix.Compile.Image.Expr`) -/

/-- `Image.instLocals`: the loose variables of `e` instantiated with `xs`,
the last one for `bvar 0`. -/
def instLocals (e : Expr) (xs : Array Expr) : Expr := instantiateRev e xs.reverse

/-- `Image.abstractFVars`'s walk: the free variable `xs[i]` becomes
`bvar (d + (xs.size - 1 - i))` (`idx` its first index). -/
def abstractFVarsM (idx : Std.HashMap Name Nat) (size : Nat) : Expr → Nat → DagM Expr
  | e@(.fvar n _), d => pure (match idx.get? n with
    | some i => Expr.mkBVar (d + (size - 1 - i))
    | none => e)
  | e@(.app f a _), d => memo e d do
    let f' ← abstractFVarsM idx size f d
    let a' ← abstractFVarsM idx size a d
    pure (Expr.mkApp f' a')
  | e@(.lam nm t b bi _), d => memo e d do
    let t' ← abstractFVarsM idx size t d
    let b' ← abstractFVarsM idx size b (d + 1)
    pure (Expr.mkLam nm t' b' bi)
  | e@(.forallE nm t b bi _), d => memo e d do
    let t' ← abstractFVarsM idx size t d
    let b' ← abstractFVarsM idx size b (d + 1)
    pure (Expr.mkForallE nm t' b' bi)
  | e@(.letE nm t v b nd _), d => memo e d do
    let t' ← abstractFVarsM idx size t d
    let v' ← abstractFVarsM idx size v d
    let b' ← abstractFVarsM idx size b (d + 1)
    pure (Expr.mkLetE nm t' v' b' nd)
  | e@(.proj nm i s _), d => memo e d do
    let s' ← abstractFVarsM idx size s d
    pure (Expr.mkProj nm i s')
  | e@(.mdata md x _), d => memo e d do
    let x' ← abstractFVarsM idx size x d
    pure (Expr.mkMData md x')
  | e, _ => pure e
where
  /-- a subterm without free variables is rebuilt unchanged -/
  memo (e : Expr) (d : Nat) (k : DagM Expr) : DagM Expr := do
    if !(← hasFVarM e) then return e
    if let some r := (← get).out.get? (e, d) then return r
    let r ← k
    modify fun m => { m with out := m.out.insert (e, d) r }
    return r

/-- `Image.abstractFVars`: the free variables `xs` replaced by loose bound
variables, `xs.back` the innermost, over distinct subterms. -/
def abstractFVars (xs : Array Name) (e : Expr) : Expr :=
  if xs.isEmpty then e else
  let idx : Std.HashMap Name Nat := xs.zipIdx.foldl (init := {}) fun m (x, i) =>
    if m.contains x then m else m.insert x i
  (abstractFVarsM idx xs.size e 0).run' {}

/-- `Image.mkBinders`: `λ xs, b` (`isLam`) or `∀ xs, b`. -/
def mkBinders (isLam : Bool) (xs : Array Local) (b : Expr) : Expr := Id.run do
  let names := xs.map (·.fvar)
  let mut acc := abstractFVars names b
  for (x, i) in xs.zipIdx.reverse do
    let ty := abstractFVars (names.extract 0 i) x.type
    acc := if isLam then Expr.mkLam x.userName ty acc x.bi
      else Expr.mkForallE x.userName ty acc x.bi
  return acc

def mkLambda (xs : Array Local) (b : Expr) : Expr := mkBinders true xs b
def mkForall (xs : Array Local) (b : Expr) : Expr := mkBinders false xs b

/-- `e` mentions the free variable `x` (a walk over distinct subterms). -/
def mentionsFVar (x : Name) (e : Expr) : Bool := Id.run do
  let mut seen : Std.HashSet Expr := {}
  let mut stack : Array Expr := #[e]
  while !stack.isEmpty do
    let y := stack.back!
    stack := stack.pop
    if seen.contains y then continue
    seen := seen.insert y
    match y with
    | .fvar z _ => if x == z then return true
    | .app f a _ => stack := stack.push a |>.push f
    | .lam _ t b _ _ | .forallE _ t b _ _ => stack := stack.push b |>.push t
    | .letE _ t v b _ _ => stack := stack.push b |>.push v |>.push t
    | .proj _ _ s _ | .mdata _ s _ => stack := stack.push s
    | _ => pure ()
  return false

end Ix.Compile.Clique

end
