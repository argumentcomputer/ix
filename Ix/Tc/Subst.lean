module

public import Ix.Tc.Env

/-!
Mirror: crates/kernel/src/subst.rs

Substitution and lifting for kernel expressions. All functions intern results
through `InternTable` for value deduplication, and the traversal itself is
memoized by content hash **per call** — expressions are content-addressed
DAGs and the same sub-expression may appear many times; without per-call
memoization a DAG walk becomes a tree walk (O(2^k) blowup). Depth/cutoff is
part of every memo key: traversing under a binder changes the substitution's
semantics, so two subtrees with the same address visited at different depths
must not share a result.

`lbr` fast paths are semantic, not just performance: returning the original
node avoids gratuitous re-interning.
-/

public section
@[expose] section

namespace Ix.Tc

/-- State monad over the intern table — the Lean face of Rust's
    `&mut InternTable` threading. -/
abbrev InternM (m : Mode) := StateM (InternTable m)

@[inline] def internExprM (e : KExpr m) : InternM m (KExpr m) :=
  fun it => it.internExpr e

@[inline] def internUnivM (u : KUniv m) : InternM m (KUniv m) :=
  fun it => it.internUniv u

/-- Per-call memoization scratch, keyed by `(addr, depth-or-cutoff)`. -/
abbrev Scratch (m : Mode) := Std.HashMap (Address × UInt64) (KExpr m)

/-- Walker monad: intern table + per-call scratch. -/
abbrev WalkM (m : Mode) := StateM (InternTable m × Scratch m)

@[inline] def liftInternW (x : InternM m α) : WalkM m α :=
  fun (it, sc) => let (a, it') := x it; (a, (it', sc))

@[inline] def scratchGet? (key : Address × UInt64) :
    WalkM m (Option (KExpr m)) :=
  fun s => (s.2[key]?, s)

@[inline] def scratchInsert (key : Address × UInt64) (e : KExpr m) :
    WalkM m Unit :=
  fun (it, sc) => ((), (it, sc.insert key e))

/-- Run a cached walker with a fresh scratch, returning to `InternM`. -/
@[inline] def runWalk (x : WalkM m α) : InternM m α := fun it =>
  let (a, (it', _)) := x (it, {})
  (a, it')

/-- Rebuilt-node anonymous name (hash-neutral metadata). -/
@[inline] def anonName : {m : Mode} → m.F Name
  | .anon => ()
  | .«meta» => Ix.Name.mkAnon

/-- Inner recursive worker for `lift`, memoized by `(addr, cutoff)`
    (`shift` is fixed across a call). -/
def liftCached (e : KExpr m) (shift cutoff : UInt64) :
    WalkM m (KExpr m) := do
  if shift == 0 || e.lbr ≤ cutoff then
    return e
  let key := (e.addr, cutoff)
  if let some cached ← scratchGet? key then
    return cached
  let result ← match e with
    | .var i name _ =>
      if i ≥ cutoff then
        pure (KExpr.mkVar (i + shift) name)
      else do
        scratchInsert key e
        return e
    -- Structural arms MUST `pure` into `result` (NOT `return`): in
    -- do-notation `return` exits the whole function, skipping the
    -- intern + `scratchInsert` tail below — the memo then never holds
    -- interior nodes and shared-DAG walks go exponential (the
    -- `denote_blastDivSubtractShift_q` hang). Same pitfall family as
    -- Rust-`&&` vs `(← _) && (← _)`: type-correct, semantics off.
    | .app f x _ =>
      pure (KExpr.mkApp (← liftCached f shift cutoff)
        (← liftCached x shift cutoff))
    | .lam name bi ty body _ =>
      pure (KExpr.mkLam name bi (← liftCached ty shift cutoff)
        (← liftCached body shift (cutoff + 1)))
    | .all name bi ty body _ =>
      pure (KExpr.mkAll name bi (← liftCached ty shift cutoff)
        (← liftCached body shift (cutoff + 1)))
    | .letE name ty val body nd _ =>
      pure (KExpr.mkLet name (← liftCached ty shift cutoff)
        (← liftCached val shift cutoff)
        (← liftCached body shift (cutoff + 1)) nd)
    | .prj id field val _ =>
      pure (KExpr.mkPrj id field (← liftCached val shift cutoff))
    | _ => do
      -- FVar / Sort / Const / Nat / Str: closed atoms.
      scratchInsert key e
      return e
  let interned ← liftInternW (internExprM result)
  scratchInsert key interned
  return interned
termination_by structural e

/-- Shift free de Bruijn indices ≥ `cutoff` up by `shift`. -/
def lift (e : KExpr m) (shift cutoff : UInt64) : InternM m (KExpr m) :=
  if shift == 0 || e.lbr ≤ cutoff then pure e
  else runWalk (liftCached e shift cutoff)

def substCached (body arg : KExpr m) (depth : UInt64) :
    WalkM m (KExpr m) := do
  if body.lbr ≤ depth then
    return body
  let key := (body.addr, depth)
  if let some cached ← scratchGet? key then
    return cached
  let result ← match body with
    | .var i name _ =>
      if i == depth then
        -- Fresh lift scratch per lift call (mirrors the separate
        -- `lift_scratch` in Rust — the two memo spaces must not mix).
        liftInternW (lift arg depth 0)
      else if i > depth then
        pure (KExpr.mkVar (i - 1) name)
      else do
        -- Unreachable under the `lbr ≤ depth` guard; kept for clarity.
        scratchInsert key body
        return body
    -- `pure`, not `return` — see the note in `liftCached`.
    | .app f x _ =>
      pure (KExpr.mkApp (← substCached f arg depth)
        (← substCached x arg depth))
    | .lam name bi ty inner _ =>
      pure (KExpr.mkLam name bi (← substCached ty arg depth)
        (← substCached inner arg (depth + 1)))
    | .all name bi ty inner _ =>
      pure (KExpr.mkAll name bi (← substCached ty arg depth)
        (← substCached inner arg (depth + 1)))
    | .letE name ty val inner nd _ =>
      pure (KExpr.mkLet name (← substCached ty arg depth)
        (← substCached val arg depth)
        (← substCached inner arg (depth + 1)) nd)
    | .prj id field val _ =>
      pure (KExpr.mkPrj id field (← substCached val arg depth))
    | _ => do
      scratchInsert key body
      return body
  let interned ← liftInternW (internExprM result)
  scratchInsert key interned
  return interned
termination_by structural body

/-- Single substitution `body[arg/Var(depth)]`: replaces `Var(depth)` with
    `arg` (lifted by `depth`), shifts free variables above `depth` down
    by 1. -/
def subst (body arg : KExpr m) (depth : UInt64) : InternM m (KExpr m) :=
  if body.lbr ≤ depth then pure body
  else runWalk (substCached body arg depth)

def simulSubstCached (body : KExpr m)
    (substs : Array (KExpr m)) (depth : UInt64) : WalkM m (KExpr m) := do
  if body.lbr ≤ depth then
    return body
  let key := (body.addr, depth)
  if let some cached ← scratchGet? key then
    return cached
  let n : UInt64 := substs.size.toUInt64
  let result ← match body with
    | .var i _ _ =>
      if i ≥ depth && i < depth + n then do
        let r ← liftInternW (lift substs[(i - depth).toNat]! depth 0)
        scratchInsert key r
        return r
      else if i ≥ depth + n then
        pure (KExpr.mkVar (i - n) (anonName (m := m)))
      else do
        scratchInsert key body
        return body
    -- `pure`, not `return` — see the note in `liftCached`.
    | .app f x _ =>
      pure (KExpr.mkApp (← simulSubstCached f substs depth)
        (← simulSubstCached x substs depth))
    | .lam name bi ty inner _ =>
      pure (KExpr.mkLam name bi (← simulSubstCached ty substs depth)
        (← simulSubstCached inner substs (depth + 1)))
    | .all name bi ty inner _ =>
      pure (KExpr.mkAll name bi (← simulSubstCached ty substs depth)
        (← simulSubstCached inner substs (depth + 1)))
    | .letE name ty val inner nd _ =>
      pure (KExpr.mkLet name (← simulSubstCached ty substs depth)
        (← simulSubstCached val substs depth)
        (← simulSubstCached inner substs (depth + 1)) nd)
    | .prj id field val _ =>
      pure (KExpr.mkPrj id field (← simulSubstCached val substs depth))
    | _ => do
      scratchInsert key body
      return body
  let interned ← liftInternW (internExprM result)
  scratchInsert key interned
  return interned
termination_by structural body

/-- Simultaneous substitution: replace `Var(depth)..Var(depth+n-1)` with
    `substs[0]..substs[n-1]`, shifting free variables above by `-n`. -/
def simulSubst (body : KExpr m) (substs : Array (KExpr m)) (depth : UInt64) :
    InternM m (KExpr m) :=
  if body.lbr ≤ depth then pure body
  else runWalk (simulSubstCached body substs depth)

/-- Substitution variant for short-lived WHNF intermediates (Nat literal
    recursor peeling). Deliberately does NOT intern: interning a long chain
    of distinct never-reused nodes keeps every predecessor alive for the
    whole environment check. -/
def substNoIntern (body arg : KExpr m) (depth : UInt64) : KExpr m :=
  if body.lbr ≤ depth then body
  else match body with
    | .var i name _ =>
      if i == depth then liftNoIntern arg depth 0
      else if i > depth then KExpr.mkVar (i - 1) name
      else body
    | .app f x _ =>
      KExpr.mkApp (substNoIntern f arg depth) (substNoIntern x arg depth)
    | .lam name bi ty inner _ =>
      KExpr.mkLam name bi (substNoIntern ty arg depth)
        (substNoIntern inner arg (depth + 1))
    | .all name bi ty inner _ =>
      KExpr.mkAll name bi (substNoIntern ty arg depth)
        (substNoIntern inner arg (depth + 1))
    | .letE name ty val inner nd _ =>
      KExpr.mkLet name (substNoIntern ty arg depth)
        (substNoIntern val arg depth)
        (substNoIntern inner arg (depth + 1)) nd
    | .prj id field val _ =>
      KExpr.mkPrj id field (substNoIntern val arg depth)
    | _ => body
termination_by structural body
where
  liftNoIntern (e : KExpr m) (shift cutoff : UInt64) : KExpr m :=
    if shift == 0 || e.lbr ≤ cutoff then e
    else match e with
      | .var i name _ =>
        if i ≥ cutoff then KExpr.mkVar (i + shift) name else e
      | .app f x _ =>
        KExpr.mkApp (liftNoIntern f shift cutoff) (liftNoIntern x shift cutoff)
      | .lam name bi ty body _ =>
        KExpr.mkLam name bi (liftNoIntern ty shift cutoff)
          (liftNoIntern body shift (cutoff + 1))
      | .all name bi ty body _ =>
        KExpr.mkAll name bi (liftNoIntern ty shift cutoff)
          (liftNoIntern body shift (cutoff + 1))
      | .letE name ty val body nd _ =>
        KExpr.mkLet name (liftNoIntern ty shift cutoff)
          (liftNoIntern val shift cutoff)
          (liftNoIntern body shift (cutoff + 1)) nd
      | .prj id field val _ =>
        KExpr.mkPrj id field (liftNoIntern val shift cutoff)
      | _ => e
  termination_by structural e

def instantiateRevCached (body : KExpr m)
    (fvars : Array (KExpr m)) (depth : UInt64) : WalkM m (KExpr m) := do
  if body.lbr ≤ depth then
    return body
  let key := (body.addr, depth)
  if let some cached ← scratchGet? key then
    return cached
  let n : UInt64 := fvars.size.toUInt64
  let result ← match body with
    | .var i _ _ =>
      if i ≥ depth && i < depth + n then do
        -- `Var(depth)` is the innermost peeled binder → `fvars[n-1]`;
        -- `Var(depth+n-1)` the outermost → `fvars[0]`.
        let r := fvars[(n - 1 - (i - depth)).toNat]!
        scratchInsert key r
        return r
      else if i ≥ depth + n then
        pure (KExpr.mkVar (i - n) (anonName (m := m)))
      else do
        scratchInsert key body
        return body
    -- `pure`, not `return` — see the note in `liftCached`.
    | .app f x _ =>
      pure (KExpr.mkApp (← instantiateRevCached f fvars depth)
        (← instantiateRevCached x fvars depth))
    | .lam name bi ty inner _ =>
      pure (KExpr.mkLam name bi (← instantiateRevCached ty fvars depth)
        (← instantiateRevCached inner fvars (depth + 1)))
    | .all name bi ty inner _ =>
      pure (KExpr.mkAll name bi (← instantiateRevCached ty fvars depth)
        (← instantiateRevCached inner fvars (depth + 1)))
    | .letE name ty val inner nd _ =>
      pure (KExpr.mkLet name (← instantiateRevCached ty fvars depth)
        (← instantiateRevCached val fvars depth)
        (← instantiateRevCached inner fvars (depth + 1)) nd)
    | .prj id field val _ =>
      pure (KExpr.mkPrj id field (← instantiateRevCached val fvars depth))
    | _ => do
      scratchInsert key body
      return body
  let interned ← liftInternW (internExprM result)
  scratchInsert key interned
  return interned
termination_by structural body

/-- Instantiate the outermost `n = fvars.size` loose bound variables in
    `body` by the corresponding fvars, in reverse order (`Var(0) →
    fvars[n-1]`, …, `Var(n-1) → fvars[0]`); `Var(k)` with `k ≥ n` shifts
    down by `n`. Replacements must be fvar-shaped (closed, `lbr = 0`) —
    other shapes need `simulSubst`'s lifting. -/
def instantiateRev (body : KExpr m) (fvars : Array (KExpr m)) :
    InternM m (KExpr m) :=
  if fvars.isEmpty || body.lbr == 0 then pure body
  else runWalk (instantiateRevCached body fvars 0)

def abstractFVarsCached (body : KExpr m)
    (pos : Std.HashMap FVarId UInt64) (n depth : UInt64) :
    WalkM m (KExpr m) := do
  -- Subtrees with neither fvars nor loose bvars ≥ depth are unchanged.
  if !body.hasFVars && body.lbr ≤ depth then
    return body
  let key := (body.addr, depth)
  if let some cached ← scratchGet? key then
    return cached
  let result ← match body with
    | .fvar id _ _ =>
      match pos[id]? with
      | some p => do
        let newVar := KExpr.mkVar (depth + p) (anonName (m := m))
        let interned ← liftInternW (internExprM newVar)
        scratchInsert key interned
        return interned
      | none => do
        -- Other fvars pass through (they belong to outer abstractions).
        scratchInsert key body
        return body
    | .var i name _ =>
      if i ≥ depth then
        pure (KExpr.mkVar (i + n) name)
      else do
        scratchInsert key body
        return body
    -- `pure`, not `return` — see the note in `liftCached`.
    | .app f x _ =>
      pure (KExpr.mkApp (← abstractFVarsCached f pos n depth)
        (← abstractFVarsCached x pos n depth))
    | .lam name bi ty inner _ =>
      pure (KExpr.mkLam name bi (← abstractFVarsCached ty pos n depth)
        (← abstractFVarsCached inner pos n (depth + 1)))
    | .all name bi ty inner _ =>
      pure (KExpr.mkAll name bi (← abstractFVarsCached ty pos n depth)
        (← abstractFVarsCached inner pos n (depth + 1)))
    | .letE name ty val inner nd _ =>
      pure (KExpr.mkLet name (← abstractFVarsCached ty pos n depth)
        (← abstractFVarsCached val pos n depth)
        (← abstractFVarsCached inner pos n (depth + 1)) nd)
    | .prj id field val _ =>
      pure (KExpr.mkPrj id field (← abstractFVarsCached val pos n depth))
    | _ => do
      scratchInsert key body
      return body
  let interned ← liftInternW (internExprM result)
  scratchInsert key interned
  return interned
termination_by structural body

/-- Inverse of `instantiateRev`: replace each listed fvar with the
    appropriate `Var(level)` and shift other loose bvars up by `n` so the
    result is closed under `n` new binders. `fvars[0]` becomes the outermost
    (`Var(n-1)`), `fvars[n-1]` the innermost (`Var(0)`). -/
def abstractFVars (body : KExpr m) (fvars : Array FVarId) :
    InternM m (KExpr m) :=
  if fvars.isEmpty || !body.hasFVars then pure body
  else
    let n : UInt64 := fvars.size.toUInt64
    -- Innermost (last) fvar gets position 0; outermost (first) gets `n-1`,
    -- matching the `instantiateRev` convention.
    let pos : Std.HashMap FVarId UInt64 := Id.run do
      let mut pos : Std.HashMap FVarId UInt64 := {}
      let mut i : UInt64 := 0
      for fv in fvars do
        pos := pos.insert fv (n - 1 - i)
        i := i + 1
      return pos
    runWalk (abstractFVarsCached body pos n 0)

/-- Peel up to `n` outermost lambdas, counting from `i`: returns the exposed
    body and the final count. Structural rewrite of `cheapBetaReduce`'s
    counting `while` (Tier A — the loop and the recursion exit on exactly the
    same states, so the traversal is unchanged). -/
def peelLams (n : Nat) (head : KExpr m) (i : Nat) : KExpr m × Nat :=
  match head with
  | .lam _ _ _ inner _ =>
    if i < n then peelLams n inner (i + 1) else (head, i)
  | _ => (head, i)
termination_by structural head

/-- Cheap beta reduction: peephole-reduce `App(λ…λ. body, args)` without full
    `subst` in trivial cases (closed body, or single-bvar body). Otherwise
    returns the input unchanged (full WHNF handles it). Mirrors lean4lean's
    `Expr.cheapBetaReduce`. -/
def cheapBetaReduce (e : KExpr m) : InternM m (KExpr m) := do
  match e with
  | .app .. => pure ()
  | _ => return e
  let (head₀, args) := e.collectSpine
  match head₀ with
  | .lam .. => pure ()
  | _ => return e
  -- Peel up to `args.size` lambdas.
  let (head, i) := peelLams args.size head₀ 0
  -- Case A: closed body — drop the peeled binders, apply remaining args.
  if head.lbr == 0 then
    let mut result := head
    for arg in args.extract i args.size do
      result ← internExprM (KExpr.mkApp result arg)
    return result
  -- Case B: body is Var(k) selecting a peeled arg.
  if let .var k _ _ := head then
    if k < i.toUInt64 then
      let mut result := args[i - k.toNat - 1]!
      for arg in args.extract i args.size do
        result ← internExprM (KExpr.mkApp result arg)
      return result
  return e

end Ix.Tc

end
end
