/-
  Ix.Frontend.Elab.Meta: Pure, deterministic, fuel-bounded kernel and meta-level
  operations for the Ix Frontend:
  - De Bruijn & FVar abstraction/instantiation (`instantiate1`, `abstractFVar`, `mkLambdaFVars`, `mkForallFVars`)
  - Universe level normalization, substitution, and unification (`isLevelDefEq`)
  - Metavariable creation, instantiation, and Miller-pattern occurs-checked assignment
  - Weak-head normal form (`whnf`) supporting β, ζ, δ, ι (recursor), structure projection, and `Nat` reduction
  - Type inference (`inferType`, `ensureSort`, `ensureForall`)
  - Higher-order unification (`isDefEq`)
  - Bounded backtracking typeclass synthesis (`synthInstance?`)
-/
module

public import Ix.Frontend.Elab.Monad

@[expose] public section

namespace Ix.Frontend.Elab

open Ix.Frontend

/-! ## Pure Expression & De Bruijn Utilities -/

/-- Strip outer `.mdata` wrappers from an `Ix.Expr`. -/
def stripMData : Ix.Expr → Ix.Expr
  | .mdata _ e _ => stripMData e
  | e            => e

/-- Decompose `f a₁ ... aₙ` into `(f, #[a₁, ..., aₙ])`, stripping `.mdata` on spine nodes. -/
def getAppFnArgsAux : Ix.Expr → List Ix.Expr → Ix.Expr × Array Ix.Expr
  | .mdata _ e _, acc => getAppFnArgsAux e acc
  | .app f a _, acc   => getAppFnArgsAux f (a :: acc)
  | e, acc            => (e, Array.mk acc)

def getAppFnArgs (e : Ix.Expr) : Ix.Expr × Array Ix.Expr :=
  getAppFnArgsAux e []

def getAppFn : Ix.Expr → Ix.Expr
  | .mdata _ e _ => getAppFn e
  | .app f _ _   => getAppFn f
  | e            => e

def getAppArgs (e : Ix.Expr) : Array Ix.Expr :=
  (getAppFnArgs e).2

/-- True if `e` contains any loose `.bvar i` with `i ≥ cutoff`. -/
def hasLooseBVarsAt : Ix.Expr → Nat → Bool
  | .bvar i _, c        => Nat.ble c i
  | .app f a _, c       => hasLooseBVarsAt f c || hasLooseBVarsAt a c
  | .lam _ t b _ _, c   => hasLooseBVarsAt t c || hasLooseBVarsAt b (c + 1)
  | .forallE _ t b _ _, c => hasLooseBVarsAt t c || hasLooseBVarsAt b (c + 1)
  | .letE _ t v b _ _, c => hasLooseBVarsAt t c || hasLooseBVarsAt v c || hasLooseBVarsAt b (c + 1)
  | .proj _ _ s _, c    => hasLooseBVarsAt s c
  | .mdata _ x _, c     => hasLooseBVarsAt x c
  | _, _                => false

def hasLooseBVars (e : Ix.Expr) : Bool :=
  hasLooseBVarsAt e 0

/-- True if `e` mentions free variable `fvarId`. -/
def containsFVar (fvarId : Ix.Name) : Ix.Expr → Bool
  | .fvar n _           => n == fvarId
  | .app f a _          => containsFVar fvarId f || containsFVar fvarId a
  | .lam _ t b _ _      => containsFVar fvarId t || containsFVar fvarId b
  | .forallE _ t b _ _  => containsFVar fvarId t || containsFVar fvarId b
  | .letE _ t v b _ _   => containsFVar fvarId t || containsFVar fvarId v || containsFVar fvarId b
  | .proj _ _ s _       => containsFVar fvarId s
  | .mdata _ x _        => containsFVar fvarId x
  | _                   => false

/-- Shift loose `.bvar i` (`i ≥ cutoff`) up by `delta`. -/
def liftLooseBVars (e : Ix.Expr) (delta : Nat) (cutoff : Nat := 0) : Ix.Expr :=
  if Nat.beq delta 0 || !hasLooseBVarsAt e cutoff then e else go e cutoff
where
  go : Ix.Expr → Nat → Ix.Expr
    | .bvar i _, c        => if Nat.ble c i then Expr.mkBVar (i + delta) else Expr.mkBVar i
    | .app f a _, c       => Expr.mkApp (go f c) (go a c)
    | .lam nm t b bi _, c => Expr.mkLam nm (go t c) (go b (c + 1)) bi
    | .forallE nm t b bi _, c => Expr.mkForallE nm (go t c) (go b (c + 1)) bi
    | .letE nm t v b nd _, c => Expr.mkLetE nm (go t c) (go v c) (go b (c + 1)) nd
    | .proj nm i s _, c   => Expr.mkProj nm i (go s c)
    | .mdata md x _, c    => Expr.mkMData md (go x c)
    | other, _            => other

/-- Substitute `args` for loose `.bvar (depth + i)` (`i < args.size`, where `bvar depth`
    is replaced by `args[0]`), and lower loose `.bvar`s above `depth + args.size`. -/
def instantiateRevAt (args : Array Ix.Expr) (e : Ix.Expr) (depth : Nat) : Ix.Expr :=
  if !hasLooseBVarsAt e depth then e
  else match e with
  | .bvar i _ =>
    if Nat.ble depth i then
      let idx := i - depth
      match Syntax.listGet? args.toList idx with
      | some arg => liftLooseBVars arg depth
      | none     => Expr.mkBVar (i - args.size)
    else
      Expr.mkBVar i
  | .app f a _       => Expr.mkApp (instantiateRevAt args f depth) (instantiateRevAt args a depth)
  | .lam nm t b bi _ => Expr.mkLam nm (instantiateRevAt args t depth) (instantiateRevAt args b (depth + 1)) bi
  | .forallE nm t b bi _ => Expr.mkForallE nm (instantiateRevAt args t depth) (instantiateRevAt args b (depth + 1)) bi
  | .letE nm t v b nd _ =>
    Expr.mkLetE nm (instantiateRevAt args t depth) (instantiateRevAt args v depth) (instantiateRevAt args b (depth + 1)) nd
  | .proj nm i s _   => Expr.mkProj nm i (instantiateRevAt args s depth)
  | .mdata md x _    => Expr.mkMData md (instantiateRevAt args x depth)
  | other            => other

/-- Substitute `args[0]` for `bvar 0`, `args[1]` for `bvar 1`, etc. -/
def instantiateRev (body : Ix.Expr) (args : Array Ix.Expr) : Ix.Expr :=
  if args.isEmpty then body else instantiateRevAt args body 0

/-- Substitute a single `arg` for loose `.bvar depth` in `e` without `Array` or proof terms. -/
def instantiate1At (arg : Ix.Expr) (e : Ix.Expr) (depth : Nat) : Ix.Expr :=
  if !hasLooseBVarsAt e depth then e
  else match e with
  | .bvar i _ =>
    if Nat.beq i depth then
      liftLooseBVars arg depth
    else if Nat.ble (depth + 1) i then
      Expr.mkBVar (i - 1)
    else
      Expr.mkBVar i
  | .app f a _       => Expr.mkApp (instantiate1At arg f depth) (instantiate1At arg a depth)
  | .lam nm t b bi _ => Expr.mkLam nm (instantiate1At arg t depth) (instantiate1At arg b (depth + 1)) bi
  | .forallE nm t b bi _ => Expr.mkForallE nm (instantiate1At arg t depth) (instantiate1At arg b (depth + 1)) bi
  | .letE nm t v b nd _ =>
    Expr.mkLetE nm (instantiate1At arg t depth) (instantiate1At arg v depth) (instantiate1At arg b (depth + 1)) nd
  | .proj nm i s _   => Expr.mkProj nm i (instantiate1At arg s depth)
  | .mdata md x _    => Expr.mkMData md (instantiate1At arg x depth)
  | other            => other

/-- Substitute `arg` for `bvar 0` in `body`. -/
def instantiate1 (body : Ix.Expr) (arg : Ix.Expr) : Ix.Expr :=
  instantiate1At arg body 0

/-- Replace free variable `fvarId` in `e` with `bvar depth` (lifting existing loose `bvar ≥ depth` by 1). -/
def abstractFVarAt (fvarId : Ix.Name) (e : Ix.Expr) (d : Nat) : Ix.Expr :=
  if !containsFVar fvarId e && !hasLooseBVarsAt e d then e
  else match e with
  | .bvar i _ =>
    if Nat.ble d i then Expr.mkBVar (i + 1) else Expr.mkBVar i
  | .fvar n _ =>
    if n == fvarId then Expr.mkBVar d else e
  | .app f a _       => Expr.mkApp (abstractFVarAt fvarId f d) (abstractFVarAt fvarId a d)
  | .lam nm t b bi _ => Expr.mkLam nm (abstractFVarAt fvarId t d) (abstractFVarAt fvarId b (d + 1)) bi
  | .forallE nm t b bi _ => Expr.mkForallE nm (abstractFVarAt fvarId t d) (abstractFVarAt fvarId b (d + 1)) bi
  | .letE nm t v b nd _ =>
    Expr.mkLetE nm (abstractFVarAt fvarId t d) (abstractFVarAt fvarId v d) (abstractFVarAt fvarId b (d + 1)) nd
  | .proj nm i s _   => Expr.mkProj nm i (abstractFVarAt fvarId s d)
  | .mdata md x _    => Expr.mkMData md (abstractFVarAt fvarId x d)
  | other            => other

def abstractFVar (fvarId : Ix.Name) (body : Ix.Expr) : Ix.Expr :=
  abstractFVarAt fvarId body 0

/-- Replace simultaneous FVars `fvars[i]` with `vals[i]` in `e`. -/
def replaceFVars (e : Ix.Expr) (fvars : Array Ix.Name) (vals : Array Ix.Expr) : Ix.Expr :=
  if fvars.isEmpty then e else go e
where
  go : Ix.Expr → Ix.Expr
    | ex@(.fvar n _) =>
      match fvars.idxOf? n with
      | some idx => vals.getD idx ex
      | none     => ex
    | .app f a _          => Expr.mkApp (go f) (go a)
    | .lam nm t b bi _    => Expr.mkLam nm (go t) (go b) bi
    | .forallE nm t b bi _ => Expr.mkForallE nm (go t) (go b) bi
    | .letE nm t v b nd _ => Expr.mkLetE nm (go t) (go v) (go b) nd
    | .proj nm i s _      => Expr.mkProj nm i (go s)
    | .mdata md x _       => Expr.mkMData md (go x)
    | other               => other

/-- Replace constant names (and `.proj` structure type names) in `e` according to `map`. -/
def replaceConstNames (map : NameMap Ix.Name) (e : Ix.Expr) : Ix.Expr :=
  if map.isEmpty then e else go e
where
  go : Ix.Expr → Ix.Expr
    | .const nm us _      => Expr.mkConst ((map.get? nm).getD nm) us
    | .app f a _          => Expr.mkApp (go f) (go a)
    | .lam nm t b bi _    => Expr.mkLam nm (go t) (go b) bi
    | .forallE nm t b bi _ => Expr.mkForallE nm (go t) (go b) bi
    | .letE nm t v b nd _ => Expr.mkLetE nm (go t) (go v) (go b) nd
    | .proj nm i s _      => Expr.mkProj ((map.get? nm).getD nm) i (go s)
    | .mdata md x _       => Expr.mkMData md (go x)
    | other               => other

/-- Close a list of FVar IDs into a telescope of `.lam` / `.letE` binders using `lctx`. -/
def mkLambdaFVarsList (lctx : LocalContext) : List Ix.Name → Ix.Expr → Ix.Expr
  | [], body => body
  | fvarId :: rest, body =>
    let acc := mkLambdaFVarsList lctx rest body
    match lctx.findFVar? fvarId with
    | none => acc
    | some decl =>
      let bName := if Name.isAnonymous decl.userName then Name.simple "x" else decl.userName
      let absBody := abstractFVar fvarId acc
      match decl.value? with
      | some val =>
        let letKind := decl.letKind?.getD .value
        let nonDep := !containsFVar fvarId acc
        Expr.mkLetContract bName decl.type val absBody nonDep decl.contract letKind
      | none =>
        Expr.mkLamContract bName decl.type absBody decl.binderInfo decl.contract

/-- Close an array of FVar IDs into a telescope of `.lam` / `.letE` binders using `lctx`,
    attaching `ix.contract` metadata frames whenever a binder has non-default substructural contract. -/
def mkLambdaFVars (fvars : Array Ix.Name) (body : Ix.Expr) : IxElabM Ix.Expr := do
  let ctx ← read
  return mkLambdaFVarsList ctx.lctx fvars.toList body

/-- Close a list of FVar IDs into a telescope of `.forallE` / `.letE` binders using `lctx`. -/
def mkForallFVarsList (lctx : LocalContext) (retContract : Ixon.ValueContract) :
    List Ix.Name → Ix.Expr → Ix.Expr
  | [], body => body
  | fvarId :: rest, body =>
    let acc := mkForallFVarsList lctx retContract rest body
    let resContract : Ixon.ValueContract := match rest with
      | [] => retContract
      | _  => .shared
    match lctx.findFVar? fvarId with
    | none => acc
    | some decl =>
      let bName := if Name.isAnonymous decl.userName then Name.simple "x" else decl.userName
      let absBody := abstractFVar fvarId acc
      match decl.value? with
      | some val =>
        let letKind := decl.letKind?.getD .value
        let nonDep := !containsFVar fvarId acc
        Expr.mkLetContract bName decl.type val absBody nonDep decl.contract letKind
      | none =>
        Expr.mkForallContract bName decl.type absBody decl.binderInfo decl.contract resContract

/-- Close an array of FVar IDs into a telescope of `.forallE` / `.letE` binders using `lctx`,
    attaching `ix.contract` metadata frames for binder contracts and `retContract` on the innermost arrow. -/
def mkForallFVars (fvars : Array Ix.Name) (body : Ix.Expr)
    (retContract : Ixon.ValueContract := .shared) : IxElabM Ix.Expr := do
  let ctx ← read
  return mkForallFVarsList ctx.lctx retContract fvars.toList body

/-! ## Universe Level Operations & Unification -/

/-- Proof-free lookup of universe parameter `n` in parallel lists `(params, lvls)`. -/
def lookupLevelParam : List Ix.Name → List Ix.Level → Ix.Name → Option Ix.Level
  | p :: ps, v :: vs, n => if p == n then some v else lookupLevelParam ps vs n
  | _, _, _             => none

/-- Substitute universe parameter names `params` with `lvls` in `u`. -/
def substLevelParamsList (params : List Ix.Name) (lvls : List Ix.Level) : Ix.Level → Ix.Level
  | .zero h     => .zero h
  | .succ x _   => Level.mkSucc (substLevelParamsList params lvls x)
  | .max x y _  => Level.mkMax (substLevelParamsList params lvls x) (substLevelParamsList params lvls y)
  | .imax x y _ => Level.mkIMax (substLevelParamsList params lvls x) (substLevelParamsList params lvls y)
  | l@(.param n _) =>
    match lookupLevelParam params lvls n with
    | some v => v
    | none   => l
  | l@(.mvar _ _) => l

def substLevelParams (params : Array Ix.Name) (lvls : Array Ix.Level) (u : Ix.Level) : Ix.Level :=
  substLevelParamsList params.toList lvls.toList u

/-- Substitute universe parameter names `params` with `lvls` throughout an `Ix.Expr`. -/
def substExprLevelParams (params : Array Ix.Name) (lvls : Array Ix.Level) (e : Ix.Expr) : Ix.Expr :=
  match params.toList, lvls.toList with
  | [], _ | _, [] => e
  | pList, lList =>
    let rec go : Ix.Expr → Ix.Expr
      | .sort u _           => Expr.mkSort (substLevelParamsList pList lList u)
      | c@(.const nm us _)  =>
        match us.toList with
        | []  => c
        | uls => Expr.mkConst nm (Array.mk (uls.map (substLevelParamsList pList lList)))
      | .app f a _          => Expr.mkApp (go f) (go a)
      | .lam nm t b bi _    => Expr.mkLam nm (go t) (go b) bi
      | .forallE nm t b bi _ => Expr.mkForallE nm (go t) (go b) bi
      | .letE nm t v b nd _ => Expr.mkLetE nm (go t) (go v) (go b) nd
      | .proj nm i s _      => Expr.mkProj nm i (go s)
      | .mdata md x _       => Expr.mkMData md (go x)
      | other               => other
    go e

/-- True if universe level `u` contains any `.mvar`. -/
def hasLevelMVar : Ix.Level → Bool
  | .zero _ | .param _ _ => false
  | .mvar _ _   => true
  | .succ x _   => hasLevelMVar x
  | .max x y _  => hasLevelMVar x || hasLevelMVar y
  | .imax x y _ => hasLevelMVar x || hasLevelMVar y

/-- True if expression `e` contains any expression `.mvar` or universe level `.mvar`. -/
def hasExprOrLevelMVar : Ix.Expr → Bool
  | .bvar _ _ | .fvar _ _ | .lit _ _ => false
  | .mvar _ _          => true
  | .sort u _          => hasLevelMVar u
  | .const _ us _      => us.toList.any hasLevelMVar
  | .app f a _         => hasExprOrLevelMVar f || hasExprOrLevelMVar a
  | .lam _ t b _ _     => hasExprOrLevelMVar t || hasExprOrLevelMVar b
  | .forallE _ t b _ _ => hasExprOrLevelMVar t || hasExprOrLevelMVar b
  | .letE _ t v b _ _  => hasExprOrLevelMVar t || hasExprOrLevelMVar v || hasExprOrLevelMVar b
  | .proj _ _ s _      => hasExprOrLevelMVar s
  | .mdata _ x _       => hasExprOrLevelMVar x

/-- Helper for `instantiateLevelMVars` (assumes `u` contains at least one level mvar). -/
def instantiateLevelMVarsCore : Nat → Ix.Level → IxElabM Ix.Level
  | 0, u => return u
  | fuel + 1, u => do
    match u with
    | .zero _ | .param _ _ => return u
    | .succ x _ =>
      let x' ← instantiateLevelMVarsCore fuel x
      return Level.mkSucc x'
    | .max x y _ =>
      let x' ← instantiateLevelMVarsCore fuel x
      let y' ← instantiateLevelMVarsCore fuel y
      return Level.mkMax x' y'
    | .imax x y _ =>
      let x' ← instantiateLevelMVarsCore fuel x
      let y' ← instantiateLevelMVarsCore fuel y
      return Level.mkIMax x' y'
    | .mvar id _ =>
      let st ← get
      match st.mctx.getLevelAssignment? id with
      | some assigned =>
        if hasLevelMVar assigned then instantiateLevelMVarsCore fuel assigned else return assigned
      | none          => return u

/-- Instantiate assigned level metavariables in `u` (structurally recursive on `fuel`). -/
def instantiateLevelMVars (fuel : Nat) (u : Ix.Level) : IxElabM Ix.Level := do
  if !hasLevelMVar u then return u
  let st ← get
  if st.mctx.lvlAssigns.isEmpty then return u
  instantiateLevelMVarsCore fuel u

/-- Smart `max` constructor on already-normalized levels. -/
def mkMaxNorm (a b : Ix.Level) : Ix.Level :=
  if a == b then a
  else match a, b with
    | .zero _, _ => b
    | _, .zero _ => a
    | .succ x _, .succ y _ => Level.mkSucc (mkMaxNorm x y)
    | _, _ => Level.mkMax a b

/-- Smart `imax` constructor on already-normalized levels. -/
def mkIMaxNorm (a b : Ix.Level) : Ix.Level :=
  match b with
  | .zero _ => b
  | .succ _ _ => mkMaxNorm a b
  | _ =>
    if a == b then a
    else match a with
      | .zero _ | .succ (.zero _) _ => b
      | _ => Level.mkIMax a b

/-- Simplify `max` and `imax` universe levels where statically reducible. -/
def normalizeLevel : Ix.Level → Ix.Level
  | .zero h => .zero h
  | .succ x _ => Level.mkSucc (normalizeLevel x)
  | .max a b _ => mkMaxNorm (normalizeLevel a) (normalizeLevel b)
  | .imax a b _ => mkIMaxNorm (normalizeLevel a) (normalizeLevel b)
  | u => u

/-- Check whether `uvarId` occurs in `u`. -/
def occursLevelMVar (uvarId : Ix.Name) : Ix.Level → Bool
  | .zero _ | .param _ _ => false
  | .succ x _   => occursLevelMVar uvarId x
  | .max x y _  => occursLevelMVar uvarId x || occursLevelMVar uvarId y
  | .imax x y _ => occursLevelMVar uvarId x || occursLevelMVar uvarId y
  | .mvar id _  => id == uvarId

/-- Unify two universe levels `u` and `v`, assigning level metavariables when needed. -/
def isLevelDefEq : Nat → Ix.Level → Ix.Level → IxElabM Bool
  | 0, u, v => return (normalizeLevel u == normalizeLevel v)
  | fuel + 1, u, v => do
    let u ← instantiateLevelMVars 32 u
    let v ← instantiateLevelMVars 32 v
    let u := normalizeLevel u
    let v := normalizeLevel v
    if u == v then return true
    match u, v with
    | .mvar id _, _ =>
      if occursLevelMVar id v then return false
      modifyMCtx (·.assignLevel id v)
      return true
    | _, .mvar id _ =>
      if occursLevelMVar id u then return false
      modifyMCtx (·.assignLevel id u)
      return true
    | .succ a _, .succ b _ =>
      isLevelDefEq fuel a b
    | .max a1 a2 _, .max b1 b2 _ => do
      let ok1 ← isLevelDefEq fuel a1 b1
      if ok1 then isLevelDefEq fuel a2 b2 else return false
    | .imax a1 a2 _, .imax b1 b2 _ => do
      let ok1 ← isLevelDefEq fuel a1 b1
      if ok1 then isLevelDefEq fuel a2 b2 else return false
    | _, _ => return false

/-- Create a fresh universe level metavariable `?u`. -/
def mkFreshLevelMVar : IxElabM Ix.Level := do
  let id ← mkFreshName "_uvar"
  return Level.mkMVar id

/-- Create a fresh expression metavariable `?m : type` in the current `LocalContext`. -/
def mkFreshExprMVar (type : Ix.Expr) (userName : Ix.Name := Name.mkAnon) : IxElabM Ix.Expr := do
  let ctx ← read
  let mvarId ← mkFreshName "_mvar"
  let decl : MetavarDecl := { mvarId, userName, lctx := ctx.lctx, type }
  modifyMCtx (·.addExprMVarDecl decl)
  return Expr.mkMVar mvarId

/-- Single bottom-up pass for `instantiateMVars` without repeating `hasExprOrLevelMVar` at internal nodes. -/
def instantiateMVarsCore : Nat → Ix.Expr → IxElabM Ix.Expr
  | 0, e => return e
  | fuel + 1, e => do
    match e with
    | .bvar _ _ | .fvar _ _ | .lit _ _ => return e
    | .sort u _ =>
      if !hasLevelMVar u then return e
      let u' ← instantiateLevelMVars 32 u
      return Expr.mkSort (normalizeLevel u')
    | .const nm us _ =>
      if !(us.toList.any hasLevelMVar) then return e
      let us' ← us.toList.mapM fun u => do
        let u' ← instantiateLevelMVars 32 u
        return normalizeLevel u'
      return Expr.mkConst nm (Array.mk us')
    | .mvar id _ =>
      let st ← get
      match st.mctx.getExprAssignment? id with
      | some val =>
        if hasExprOrLevelMVar val then instantiateMVarsCore fuel val else return val
      | none     => return e
    | .app f a _ =>
      let f' ← instantiateMVarsCore fuel f
      let a' ← instantiateMVarsCore fuel a
      return Expr.mkApp f' a'
    | .lam nm t b bi _ =>
      let t' ← instantiateMVarsCore fuel t
      let b' ← instantiateMVarsCore fuel b
      return Expr.mkLam nm t' b' bi
    | .forallE nm t b bi _ =>
      let t' ← instantiateMVarsCore fuel t
      let b' ← instantiateMVarsCore fuel b
      return Expr.mkForallE nm t' b' bi
    | .letE nm t v b nd _ =>
      let t' ← instantiateMVarsCore fuel t
      let v' ← instantiateMVarsCore fuel v
      let b' ← instantiateMVarsCore fuel b
      return Expr.mkLetE nm t' v' b' nd
    | .proj nm i s _ =>
      let s' ← instantiateMVarsCore fuel s
      return Expr.mkProj nm i s'
    | .mdata md x _ =>
      let x' ← instantiateMVarsCore fuel x
      return Expr.mkMData md x'

/-- Instantiate assigned expression and universe level metavariables throughout `e`. -/
def instantiateMVars (fuel : Nat) (e : Ix.Expr) : IxElabM Ix.Expr := do
  let st ← get
  if st.mctx.exprAssigns.isEmpty && st.mctx.lvlAssigns.isEmpty then return e
  if !hasExprOrLevelMVar e then return e
  instantiateMVarsCore fuel e

/-- Check whether `mvarId` occurs in `e` (returns `true` if `mvarId` occurs). -/
def occursCheckMVar (mvarId : Ix.Name) : Ix.Expr → Bool
  | .mvar id _          => id == mvarId
  | .app f a _          => occursCheckMVar mvarId f || occursCheckMVar mvarId a
  | .lam _ t b _ _      => occursCheckMVar mvarId t || occursCheckMVar mvarId b
  | .forallE _ t b _ _  => occursCheckMVar mvarId t || occursCheckMVar mvarId b
  | .letE _ t v b _ _   => occursCheckMVar mvarId t || occursCheckMVar mvarId v || occursCheckMVar mvarId b
  | .proj _ _ s _       => occursCheckMVar mvarId s
  | .mdata _ x _        => occursCheckMVar mvarId x
  | _                   => false

/-- Collect any unassigned level metavariables in `u` and replace them with `.zero`
    (used when finalizing top-level declarations if a level mvar remained unconstrained). -/
def defaultUnassignedLevelMVars : Ix.Level → Ix.Level
  | .zero h     => .zero h
  | .param n h  => .param n h
  | .mvar _ _   => Level.mkZero
  | .succ x _   => Level.mkSucc (defaultUnassignedLevelMVars x)
  | .max x y _  => normalizeLevel (Level.mkMax (defaultUnassignedLevelMVars x) (defaultUnassignedLevelMVars y))
  | .imax x y _ => normalizeLevel (Level.mkIMax (defaultUnassignedLevelMVars x) (defaultUnassignedLevelMVars y))

def defaultUnassignedExprLevelMVars : Ix.Expr → Ix.Expr
  | .sort u _           => Expr.mkSort (defaultUnassignedLevelMVars u)
  | c@(.const nm us _)  =>
    match us.toList with
    | []  => c
    | uls => Expr.mkConst nm (Array.mk (uls.map defaultUnassignedLevelMVars))
  | .app f a _          => Expr.mkApp (defaultUnassignedExprLevelMVars f) (defaultUnassignedExprLevelMVars a)
  | .lam nm t b bi _    => Expr.mkLam nm (defaultUnassignedExprLevelMVars t) (defaultUnassignedExprLevelMVars b) bi
  | .forallE nm t b bi _ => Expr.mkForallE nm (defaultUnassignedExprLevelMVars t) (defaultUnassignedExprLevelMVars b) bi
  | .letE nm t v b nd _ => Expr.mkLetE nm (defaultUnassignedExprLevelMVars t) (defaultUnassignedExprLevelMVars v) (defaultUnassignedExprLevelMVars b) nd
  | .proj nm i s _      => Expr.mkProj nm i (defaultUnassignedExprLevelMVars s)
  | .mdata md x _       => Expr.mkMData md (defaultUnassignedExprLevelMVars x)
  | other               => other

/-! ## Weak-Head Normal Form (`whnf`) -/

/-- Decode a `Nat` value from an `Ix.Expr` (either `.lit (.natVal n)` or `Nat.zero` / `Nat.succ`). -/
def evalNatLit? : Nat → Ix.Expr → Option Nat
  | 0, _ => none
  | fuel + 1, e =>
    match stripMData e with
    | .lit (.natVal n) _ => some n
    | .const nm _ _ =>
      if nm == Name.mkStr2 "Nat" "zero" then some 0 else none
    | .app fn arg _ =>
      match stripMData fn with
      | .const nm _ _ =>
        if nm == Name.mkStr2 "Nat" "succ" then
          (evalNatLit? fuel arg).map (· + 1)
        else none
      | _ => none
    | _ => none

/-- Decode a `Char` value from `Char.ofNat n`. -/
def evalCharLit? (fuel : Nat) (e : Ix.Expr) : Option Char :=
  match stripMData e with
  | .app fn arg _ =>
    match stripMData fn with
    | .const nm _ _ =>
      if nm == Name.mkStr2 "Char" "ofNat" then
        (evalNatLit? fuel arg).map Char.ofNat
      else none
    | _ => none
  | _ => none

/-- Decode a `List Char` from `List.nil` / `List.cons Char c tail`. -/
def evalCharList? : Nat → Ix.Expr → Option (List Char)
  | 0, _ => none
  | fuel + 1, e =>
    let (fn, args) := getAppFnArgs (stripMData e)
    match fn with
    | .const nm _ _ =>
      if nm == Name.mkStr2 "List" "nil" && args.size == 1 then
        some []
      else if nm == Name.mkStr2 "List" "cons" && args.size == 3 then
        match evalCharLit? 16 (args.getD 1 e), evalCharList? fuel (args.getD 2 e) with
        | some c, some cs => some (c :: cs)
        | _, _ => none
      else none
    | _ => none

/-- Build a `List Char` expression from `cs : List Char`. -/
def mkCharListExpr (cs : List Char) : Ix.Expr :=
  let charTy := Expr.mkConst (Name.simple "Char") #[]
  let nilExpr := Expr.mkApp (Expr.mkConst (Name.mkStr2 "List" "nil") #[Level.mkZero]) charTy
  let consConst := Expr.mkApp (Expr.mkConst (Name.mkStr2 "List" "cons") #[Level.mkZero]) charTy
  let charOfNat := Expr.mkConst (Name.mkStr2 "Char" "ofNat") #[]
  cs.foldr (fun c acc =>
    let cExpr := Expr.mkApp charOfNat (Expr.mkNatLit c.toNat)
    Expr.mkApp (Expr.mkApp consConst cExpr) acc) nilExpr

/-- Expand a string literal `s` into constructor form `String.mk [Char.ofNat c₁, ...]`. -/
def strLitToCtorExpr (s : String) : Ix.Expr :=
  Expr.mkApp (Expr.mkConst (Name.mkStr2 "String" "mk") #[]) (mkCharListExpr s.toList)

/-- Construct `Bool.true` or `Bool.false` as an `Ix.Expr`. -/
def mkBoolExpr (b : Bool) : Ix.Expr :=
  Expr.mkConst (Name.mkStr2 "Bool" (if b then "true" else "false")) #[]

/-- Fast-path reduction for unary `Nat` / `String` / `Char` primitives on WHNF argument `a0`. -/
def tryReduceUnaryPrim (nm : Ix.Name) (a0 : Ix.Expr) : Option Ix.Expr :=
  if nm == Name.mkStr2 "Nat" "pred" then
    (evalNatLit? 16 a0).map fun n => Expr.mkNatLit (n - 1)
  else if nm == Name.mkStr2 "Nat" "succ" then
    (evalNatLit? 16 a0).map fun n => Expr.mkNatLit (n + 1)
  else if nm == Name.mkStr2 "Char" "toNat" then
    (evalCharLit? 16 a0).map fun c => Expr.mkNatLit c.toNat
  else if nm == Name.mkStr2 "Char" "utf8Size" then
    (evalCharLit? 16 a0).map fun c => Expr.mkNatLit c.utf8Size
  else if nm == Name.mkStr2 "String" "utf8ByteSize" then
    match stripMData a0 with
    | .lit (.strVal s) _ => some (Expr.mkNatLit s.utf8ByteSize)
    | _ => none
  else if nm == Name.mkStr2 "String" "length" then
    match stripMData a0 with
    | .lit (.strVal s) _ => some (Expr.mkNatLit s.length)
    | _ => none
  else if nm == Name.mkStr2 "String" "isEmpty" then
    match stripMData a0 with
    | .lit (.strVal s) _ => some (mkBoolExpr s.isEmpty)
    | _ => none
  else if nm == Name.mkStr2 "String" "toList" then
    match stripMData a0 with
    | .lit (.strVal s) _ => some (mkCharListExpr s.toList)
    | _ => none
  else if nm == Name.mkStr2 "String" "ofList" || nm == Name.mkStr2 "String" "mk" then
    (evalCharList? 128 a0).map fun cs => Expr.mkStrLit (String.ofList cs)
  else if nm == Name.mkStr2 "String" "singleton" then
    (evalCharLit? 16 a0).map fun c => Expr.mkStrLit (String.singleton c)
  else if nm == Name.mkStr2 "String" "back" then
    match stripMData a0 with
    | .lit (.strVal s) _ =>
      let c := s.toList.getLastD (Char.ofNat 65)
      some (Expr.mkApp (Expr.mkConst (Name.mkStr2 "Char" "ofNat") #[]) (Expr.mkNatLit c.toNat))
    | _ => none
  else none

/-- Fast-path reduction for binary `Nat` / `String` primitives on WHNF arguments `a0`, `a1`. -/
def tryReduceBinaryPrim (nm : Ix.Name) (a0 a1 : Ix.Expr) : Option Ix.Expr :=
  if nm == Name.mkStr2 "Nat" "add" then
    match evalNatLit? 16 a0, evalNatLit? 16 a1 with
    | some n1, some n2 => some (Expr.mkNatLit (n1 + n2))
    | _, _ => none
  else if nm == Name.mkStr2 "Nat" "sub" then
    match evalNatLit? 16 a0, evalNatLit? 16 a1 with
    | some n1, some n2 => some (Expr.mkNatLit (n1 - n2))
    | _, _ => none
  else if nm == Name.mkStr2 "Nat" "mul" then
    match evalNatLit? 16 a0, evalNatLit? 16 a1 with
    | some n1, some n2 => some (Expr.mkNatLit (n1 * n2))
    | _, _ => none
  else if nm == Name.mkStr2 "Nat" "div" then
    match evalNatLit? 16 a0, evalNatLit? 16 a1 with
    | some n1, some n2 => some (Expr.mkNatLit (n1 / n2))
    | _, _ => none
  else if nm == Name.mkStr2 "Nat" "mod" then
    match evalNatLit? 16 a0, evalNatLit? 16 a1 with
    | some n1, some n2 => some (Expr.mkNatLit (n1 % n2))
    | _, _ => none
  else if nm == Name.mkStr2 "Nat" "pow" then
    match evalNatLit? 16 a0, evalNatLit? 16 a1 with
    | some n1, some n2 => if n2 ≤ 256 then some (Expr.mkNatLit (n1 ^ n2)) else none
    | _, _ => none
  else if nm == Name.mkStr2 "Nat" "beq" then
    match evalNatLit? 16 a0, evalNatLit? 16 a1 with
    | some n1, some n2 => some (mkBoolExpr (n1 == n2))
    | _, _ => none
  else if nm == Name.mkStr2 "Nat" "ble" then
    match evalNatLit? 16 a0, evalNatLit? 16 a1 with
    | some n1, some n2 => some (mkBoolExpr (n1 ≤ n2))
    | _, _ => none
  else if nm == Name.mkStr2 "String" "append" then
    match stripMData a0, stripMData a1 with
    | .lit (.strVal s1) _, .lit (.strVal s2) _ => some (Expr.mkStrLit (s1 ++ s2))
    | _, _ => none
  else if nm == Name.mkStr2 "String" "push" then
    match stripMData a0, evalCharLit? 16 a1 with
    | .lit (.strVal s) _, some c => some (Expr.mkStrLit (s.push c))
    | _, _ => none
  else none

/-- Compute Weak-Head Normal Form (`whnf`) of `e`, bounded by `fuel : Nat`.
    Supports β, ζ (let + local ldecl), δ (definition unfolding), ι (recursor rules),
    structure projections `.proj`, and `Nat` / `String` / `Char` kernel primitives. -/
def whnf : Nat → Ix.Expr → IxElabM Ix.Expr
  | 0, e => return stripMData e
  | fuel + 1, e => do
    let e := stripMData e
    match e with
    -- 0. Assigned expression metavariable unfolding
    | .mvar mvarId _ =>
      let st ← get
      match st.mctx.getExprAssignment? mvarId with
      | some val => whnf fuel val
      | none     => return e
    -- 1. Local `let` free variable unfolding (ζ-local)
    | .fvar fvarId _ =>
      let ctx ← read
      match ctx.lctx.findFVar? fvarId with
      | some decl =>
        match decl.value? with
        | some val => whnf fuel val
        | none     => return e
      | none => return e
    -- 2. `let x : t := v in b` (ζ-reduction)
    | .letE _ _ v b _ _ =>
      whnf fuel (instantiate1 b v)
    -- 3. Structure projection `.proj typeName idx s`
    | .proj typeName idx s _ =>
      let sWhnf ← whnf fuel s
      let sExpanded := match sWhnf with
        | .lit (.strVal str) _ => strLitToCtorExpr str
        | other => other
      let (ctorFn, ctorArgs) := getAppFnArgs sExpanded
      match ctorFn with
      | .const ctorName _ _ =>
        let st ← get
        match st.env.find? ctorName with
        | some (.ctorInfo cval) =>
          if cval.induct == typeName && cval.numParams + idx < ctorArgs.size then
            whnf fuel (ctorArgs.getD (cval.numParams + idx) e)
          else
            return Expr.mkProj typeName idx sWhnf
        | _ => return Expr.mkProj typeName idx sWhnf
      | _ => return Expr.mkProj typeName idx sWhnf
    -- 4. Constant unfolding (δ-reduction)
    | .const nm us _ =>
      let st ← get
      match st.env.find? nm with
      | some (.defnInfo dval) =>
        let body := substExprLevelParams dval.cnst.levelParams us dval.value
        whnf fuel body
      | _ => return e
    -- 5. Application spine: β-reduction, ι-reduction, Nat/String/Char primitives, δ-unfolding
    | .app _ _ _ =>
      let (fn, args) := getAppFnArgs e
      let fnWhnf ← whnf fuel fn
      let (headFn, headArgs) := getAppFnArgs fnWhnf
      let allArgs := headArgs ++ args
      match headFn with
      -- 5a. β-reduction: `(fun x => body) a₀ a₁ ...`
      | .lam _ _ body _ _ =>
        if allArgs.isEmpty then return headFn
        else
          let firstArg := allArgs.getD 0 headFn
          let restArgs := allArgs.extract 1 allArgs.size
          let reduced := Expr.mkAppN (instantiate1 body firstArg) restArgs
          whnf fuel reduced
      -- 5b. Constant head: primitives, ι-reduction (`.recInfo`), or δ-unfolding (`.defnInfo`)
      | .const nm us _ =>
        -- First check unary/binary Nat, String, and Char primitives
        if allArgs.size == 1 then
          let a0 ← whnf fuel (allArgs.getD 0 headFn)
          if let some res := tryReduceUnaryPrim nm a0 then
            return res
        else if allArgs.size == 2 then
          let a0 ← whnf fuel (allArgs.getD 0 headFn)
          let a1 ← whnf fuel (allArgs.getD 1 headFn)
          if let some res := tryReduceBinaryPrim nm a0 a1 then
            return res
        let st ← get
        match st.env.find? nm with
        | some (.recInfo rval) =>
          let majorIdx := rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices
          if majorIdx < allArgs.size then
            let majorWhnf ← whnf fuel (allArgs.getD majorIdx headFn)
            -- If major premise is a Nat or String literal, expand to constructor form
            let majorExpanded := match majorWhnf with
              | .lit (.natVal 0) _ => Expr.mkConst (Name.mkStr2 "Nat" "zero") #[]
              | .lit (.natVal (k + 1)) _ =>
                Expr.mkApp (Expr.mkConst (Name.mkStr2 "Nat" "succ") #[]) (Expr.mkNatLit k)
              | .lit (.strVal str) _ => strLitToCtorExpr str
              | other => other
            let (mFn, mArgs) := getAppFnArgs majorExpanded
            match mFn with
            | .const ctorName _ _ =>
              match rval.rules.find? (fun r => r.ctor == ctorName) with
              | some rule =>
                if mArgs.size ≥ mArgs.size - rule.nfields then
                  let fields := mArgs.extract (mArgs.size - rule.nfields) mArgs.size
                  let paramsMotivesMinors := allArgs.extract 0 (rval.numParams + rval.numMotives + rval.numMinors)
                  let extraArgs := allArgs.extract (majorIdx + 1) allArgs.size
                  let rhsInst := substExprLevelParams rval.cnst.levelParams us rule.rhs
                  let applied := Expr.mkAppN rhsInst (paramsMotivesMinors ++ fields ++ extraArgs)
                  whnf fuel applied
                else
                  return Expr.mkAppN headFn allArgs
              | none => return Expr.mkAppN headFn allArgs
            | _ => return Expr.mkAppN headFn allArgs
          else
            return Expr.mkAppN headFn allArgs
        | some (.defnInfo dval) =>
          let body := substExprLevelParams dval.cnst.levelParams us dval.value
          whnf fuel (Expr.mkAppN body allArgs)
        | _ =>
          return Expr.mkAppN headFn allArgs
      | _ =>
        return Expr.mkAppN headFn allArgs
    | _ => return e

/-! ## Type Inference (`inferType`, `ensureSort`, `ensureForall`) -/

/-- Infer the universe level `u` of `type`, where `whnf type = .sort u`. -/
def inferType : Nat → Ix.Expr → IxElabM Ix.Expr
  | 0, _ => throwElabError "elaborator fuel exhausted in inferType"
  | fuel + 1, e => do
    let e := stripMData e
    match e with
    | .bvar idx _ =>
      throwElabError s!"unexpected loose bound variable #{idx} in inferType"
    | .fvar fvarId _ =>
      let ctx ← read
      match ctx.lctx.findFVar? fvarId with
      | some decl => return decl.type
      | none      => throwElabError s!"unknown free variable '{Name.toStringTotal fvarId}'"
    | .mvar mvarId _ =>
      let st ← get
      match st.mctx.getExprAssignment? mvarId with
      | some val => inferType fuel val
      | none =>
        match st.mctx.findDecl? mvarId with
        | some decl => return decl.type
        | none      => throwElabError s!"unknown metavariable '?{Name.toStringTotal mvarId}'"
    | .sort u _ =>
      let u' ← instantiateLevelMVars 32 u
      return Expr.mkSort (Level.mkSucc (normalizeLevel u'))
    | .lit (.natVal _) _ =>
      return Expr.mkConst (Name.simple "Nat") #[]
    | .lit (.strVal _) _ =>
      return Expr.mkConst (Name.simple "String") #[]
    | .const nm us _ =>
      let st ← get
      match st.env.find? nm with
      | some ci =>
        let cnst := Expr.ConstantInfo.getCnstPure ci
        match cnst.levelParams.toList, us.toList with
        | [], [] => return cnst.type
        | pList, uList =>
          if pList.length != uList.length then
            throwElabError s!"universe level count mismatch for '{Name.toStringTotal nm}': expected {pList.length}, got {uList.length}"
          let us' ←
            if uList.any hasLevelMVar then
              let ls ← uList.mapM fun u => do
                let u' ← instantiateLevelMVars 32 u
                return normalizeLevel u'
              pure (Array.mk ls)
            else pure us
          return substExprLevelParams cnst.levelParams us' cnst.type
      | none =>
        throwElabError s!"unknown constant '{Name.toStringTotal nm}'"
    | .app f a _ =>
      let fType ← inferType fuel f
      let fTypeWhnf ← whnf fuel fType
      match stripMData fTypeWhnf with
      | .forallE _ _ body _ _ =>
        return instantiate1 body a
      | _ =>
        -- If `fTypeWhnf` is a metavariable `?m`, return a fresh codomain metavariable
        let codLvl ← mkFreshLevelMVar
        let codTy ← mkFreshExprMVar (Expr.mkSort codLvl)
        return codTy
    | .lam nm dom body bi _ =>
      let domSort ← inferType fuel dom
      let _ ← whnf fuel domSort
      withLocalDecl nm dom bi default fun fvarId fvarExpr => do
        let bodyInst := instantiate1 body fvarExpr
        let bodyTy ← inferType fuel bodyInst
        let absBodyTy := abstractFVar fvarId bodyTy
        return Expr.mkForallE nm dom absBodyTy bi
    | .forallE nm dom body bi _ =>
      let domTy ← inferType fuel dom
      let domTyWhnf ← whnf fuel domTy
      let u1 ← match stripMData domTyWhnf with
        | .sort u _ =>
          let u' ← instantiateLevelMVars 32 u
          pure (normalizeLevel u')
        | _         => mkFreshLevelMVar
      if !hasLooseBVars body then
        let bodyTy ← inferType fuel body
        let bodyTyWhnf ← whnf fuel bodyTy
        let u2 ← match stripMData bodyTyWhnf with
          | .sort v _ =>
            let v' ← instantiateLevelMVars 32 v
            pure (normalizeLevel v')
          | _         => mkFreshLevelMVar
        return Expr.mkSort (normalizeLevel (Level.mkIMax u1 u2))
      else
        withLocalDecl nm dom bi default fun _ fvarExpr => do
          let bodyInst := instantiate1 body fvarExpr
          let bodyTy ← inferType fuel bodyInst
          let bodyTyWhnf ← whnf fuel bodyTy
          let u2 ← match stripMData bodyTyWhnf with
            | .sort v _ =>
              let v' ← instantiateLevelMVars 32 v
              pure (normalizeLevel v')
            | _         => mkFreshLevelMVar
          return Expr.mkSort (normalizeLevel (Level.mkIMax u1 u2))
    | .letE nm ty val body _ _ =>
      withLetDecl nm ty val default .value false fun _ fvarExpr => do
        let bodyInst := instantiate1 body fvarExpr
        inferType fuel bodyInst
    | .proj structName idx s _ =>
      let sTy ← inferType fuel s
      let sTyWhnf ← whnf fuel sTy
      let (sHead, sArgs) := getAppFnArgs sTyWhnf
      let st ← get
      match sHead with
      | .const indName us _ =>
        match st.env.find? indName with
        | some (.inductInfo ival) =>
          match ival.ctors[0]? with
          | some ctorName =>
            match st.env.find? ctorName with
            | some (.ctorInfo cval) =>
              let mut currTy := substExprLevelParams cval.cnst.levelParams us cval.cnst.type
              let params := sArgs.extract 0 ival.numParams
              for p in params do
                match stripMData (← whnf fuel currTy) with
                | .forallE _ _ b _ _ => currTy := instantiate1 b p
                | _ => pure ()
              for i in [:idx] do
                match stripMData (← whnf fuel currTy) with
                | .forallE _ _ b _ _ =>
                  let prevProj := Expr.mkProj structName i s
                  currTy := instantiate1 b prevProj
                | _ => pure ()
              match stripMData (← whnf fuel currTy) with
              | .forallE _ dom _ _ _ => return dom
              | _ => throwElabError s!"invalid field projection #{idx} on '{Name.toStringTotal structName}'"
            | _ => throwElabError s!"constructor '{Name.toStringTotal ctorName}' not found for projection"
          | none => throwElabError s!"inductive '{Name.toStringTotal indName}' has no constructors for projection"
        | _ => throwElabError s!"'{Name.toStringTotal indName}' is not an inductive type in projection"
      | _ => throwElabError s!"cannot infer type of projection on '{Name.toStringTotal structName}'"
    | .mdata _ inner _ =>
      inferType fuel inner

/-! ## Higher-Order Unification & Definitional Equality (`isDefEq`) -/

/-- Attempt to solve `?m a₁ ... aₙ := rhs`:
    - If `args` is empty and `?m` does not occur in `rhs`, assign `?m := rhs`.
    - If `args` are distinct local free variables `#[fvar₁, ..., fvarₙ]` (Miller pattern),
      abstract them from `rhs` and wrap in `λ fvar₁ ... fvarₙ => rhs` if `?m` does not occur. -/
def assignMVarPattern (mvarId : Ix.Name) (args : Array Ix.Expr) (rhs : Ix.Expr) : IxElabM Bool := do
  let rhs ← instantiateMVars 32 rhs
  if occursCheckMVar mvarId rhs then
    return false
  if args.isEmpty then
    let st ← get
    if let some decl := st.mctx.findDecl? mvarId then
      if let .sort mLvl _ := stripMData decl.type then
        if hasLevelMVar mLvl then
          if let some (.sort rLvl _) ← observing? (do let t ← inferType 16 rhs; whnf 16 t) then
            let _ ← isLevelDefEq 16 mLvl rLvl
    modifyMCtx (·.assignExpr mvarId rhs)
    return true
  else
    -- Check if all `args` are distinct `.fvar`s
    let mut fvarIds : Array Ix.Name := #[]
    let mut allFVars := true
    for arg in args do
      match stripMData arg with
      | .fvar fvId _ =>
        if fvarIds.contains fvId then allFVars := false
        else fvarIds := fvarIds.push fvId
      | _ => allFVars := false
    if !allFVars then
      return false
    else
      let lamVal ← mkLambdaFVars fvarIds rhs
      if occursCheckMVar mvarId lamVal then
        return false
      modifyMCtx (·.assignExpr mvarId lamVal)
      return true

/-- Check pairwise level definitional equality on two lists of equal length. -/
def allLevelDefEq (fuel : Nat) : List Ix.Level → List Ix.Level → IxElabM Bool
  | [], [] => return true
  | u :: us, v :: vs => do
    let ok ← isLevelDefEq fuel u v
    if ok then allLevelDefEq fuel us vs else return false
  | _, _ => return false

/-- Check pairwise expression definitional equality on two lists of equal length. -/
def allExprDefEq (isDefEqFuel : Ix.Expr → Ix.Expr → IxElabM Bool) :
    List Ix.Expr → List Ix.Expr → IxElabM Bool
  | [], [] => return true
  | a :: as, b :: bs => do
    let ok ← isDefEqFuel a b
    if ok then allExprDefEq isDefEqFuel as bs else return false
  | _, _ => return false

/-- Check whether two expressions `t` and `s` are definitionally equal, solving
    expression and universe level metavariables as needed. Bounded by `fuel : Nat`. -/
def isDefEq : Nat → Ix.Expr → Ix.Expr → IxElabM Bool
  | 0, t, s => return (stripMData t == stripMData s)
  | fuel + 1, t, s => do
    let recEq (a b : Ix.Expr) : IxElabM Bool := isDefEq fuel a b
    let t ← instantiateMVars 16 (stripMData t)
    let s ← instantiateMVars 16 (stripMData s)
    if t == s then return true
    -- 1. Check if either side is an unassigned metavariable (or Miller pattern application `?m xs`)
    let (tFn, tArgs) := getAppFnArgs t
    let (sFn, sArgs) := getAppFnArgs s
    match tFn, sFn with
    | .mvar mId1 _, .mvar mId2 _ =>
      if mId1 == mId2 then
        let allOk ← allExprDefEq recEq tArgs.toList sArgs.toList
        if allOk then return true
      let ok ← assignMVarPattern mId1 tArgs s
      if ok then return true
      assignMVarPattern mId2 sArgs t
    | .mvar mId _, _ =>
      let ok ← assignMVarPattern mId tArgs s
      if ok then return true
      let sWhnf ← whnf fuel s
      assignMVarPattern mId tArgs sWhnf
    | _, .mvar mId _ =>
      let ok ← assignMVarPattern mId sArgs t
      if ok then return true
      let tWhnf ← whnf fuel t
      assignMVarPattern mId sArgs tWhnf
    | _, _ =>
      -- 2. Direct structural cases before WHNF
      match t, s with
      | .sort u _, .sort v _ =>
        isLevelDefEq 32 u v
      | .bvar i _, .bvar j _ =>
        return i == j
      | .fvar x _, .fvar y _ =>
        if x == y then return true
        else
          let tW ← whnf fuel t
          let sW ← whnf fuel s
          if tW == t && sW == s then return false
          else isDefEq fuel tW sW
      | .lit l1 _, .lit l2 _ =>
        return l1 == l2
      | .lam nm1 d1 b1 bi1 _, .lam _ d2 b2 _ _ => do
        let domOk ← isDefEq fuel d1 d2
        if !domOk then return false
        withLocalDecl nm1 d1 bi1 default fun _ fv =>
          isDefEq fuel (instantiate1 b1 fv) (instantiate1 b2 fv)
      | .forallE nm1 d1 b1 bi1 _, .forallE _ d2 b2 _ _ => do
        let domOk ← isDefEq fuel d1 d2
        if !domOk then return false
        withLocalDecl nm1 d1 bi1 default fun _ fv =>
          isDefEq fuel (instantiate1 b1 fv) (instantiate1 b2 fv)
      -- η-expansion: `λ x => body` vs `s`
      | .lam nm1 d1 b1 bi1 _, _ =>
        withLocalDecl nm1 d1 bi1 default fun _ fv =>
          isDefEq fuel (instantiate1 b1 fv) (Expr.mkApp s fv)
      | _, .lam nm2 d2 b2 bi2 _ =>
        withLocalDecl nm2 d2 bi2 default fun _ fv =>
          isDefEq fuel (Expr.mkApp t fv) (instantiate1 b2 fv)
      | _, _ =>
        -- 3. Try matching same-head constant/fvar spines first (optimistic structural unification)
        let trySpine : IxElabM Bool := do
          match tArgs.toList, sArgs.toList with
          | [], _ | _, [] => return false
          | tArgList, sArgList =>
            match tFn, sFn with
            | .const c1 us1 _, .const c2 us2 _ =>
              if c1 == c2 then
                let lOk ← allLevelDefEq 32 us1.toList us2.toList
                if lOk then allExprDefEq recEq tArgList sArgList else return false
              else return false
            | .fvar f1 _, .fvar f2 _ =>
              if f1 == f2 then
                allExprDefEq recEq tArgList sArgList
              else return false
            | _, _ => return false
        match ← observing? (do
          let ok ← trySpine
          if !ok then throwElabError "spine mismatch"
          return true) with
        | some true => return true
        | _ =>
          -- 4. Reduce both sides to WHNF and compare
          let tW ← whnf fuel t
          let sW ← whnf fuel s
          if tW == sW then return true
          -- Check Nat literal vs constructor equivalence (`0` == `Nat.zero`, `n+1` == `Nat.succ n`)
          match evalNatLit? 16 tW, evalNatLit? 16 sW with
          | some n1, some n2 => return n1 == n2
          | _, _ =>
            let (twFn, twArgs) := getAppFnArgs tW
            let (swFn, swArgs) := getAppFnArgs sW
            -- Check if WHNF exposed a metavariable head
            match twFn, swFn with
            | .mvar mId _, _ => assignMVarPattern mId twArgs sW
            | _, .mvar mId _ => assignMVarPattern mId swArgs tW
            | .sort u _, .sort v _ => isLevelDefEq 32 u v
            | .lam nm1 d1 b1 bi1 _, .lam _ d2 b2 _ _ => do
              let domOk ← isDefEq fuel d1 d2
              if !domOk then return false
              withLocalDecl nm1 d1 bi1 default fun _ fv =>
                isDefEq fuel (instantiate1 b1 fv) (instantiate1 b2 fv)
            | .forallE nm1 d1 b1 bi1 _, .forallE _ d2 b2 _ _ => do
              let domOk ← isDefEq fuel d1 d2
              if !domOk then return false
              withLocalDecl nm1 d1 bi1 default fun _ fv =>
                isDefEq fuel (instantiate1 b1 fv) (instantiate1 b2 fv)
            | .const c1 us1 _, .const c2 us2 _ =>
              if c1 == c2 then
                let lOk ← allLevelDefEq 32 us1.toList us2.toList
                if lOk then allExprDefEq recEq twArgs.toList swArgs.toList else return false
              else return false
            | .fvar f1 _, .fvar f2 _ =>
              if f1 == f2 then
                allExprDefEq recEq twArgs.toList swArgs.toList
              else return false
            | .proj sn1 idx1 e1 _, .proj sn2 idx2 e2 _ =>
              if sn1 == sn2 && idx1 == idx2 then isDefEq fuel e1 e2
              else return false
            | _, _ => return false

/-- Ensure `type` is a valid type (i.e., `inferType fuel type` is definitionally equal to `Sort ?u`) and return `?u`. -/
def ensureSort (fuel : Nat) (type : Ix.Expr) : IxElabM Ix.Level := do
  let sortExpr ← inferType fuel type
  let tyWhnf ← whnf fuel sortExpr
  match stripMData tyWhnf with
  | .sort u _ => return u
  | _ =>
    let u ← mkFreshLevelMVar
    let ok ← isDefEq fuel tyWhnf (Expr.mkSort u)
    if !ok then
      throwElabError s!"type expected, got expression of non-sort type"
    instantiateLevelMVars 16 u

/-! ## Bounded Backtracking Typeclass Synthesis (`synthInstance?`) -/

/-- Allocate one fresh universe level metavariable per parameter in `ps` without `Array.push`. -/
def mkFreshLevelMVarsFor : List Ix.Name → List Ix.Level → IxElabM (Array Ix.Level)
  | [], acc => return Array.mk acc.reverse
  | _ :: rest, acc => do
    let u ← mkFreshLevelMVar
    mkFreshLevelMVarsFor rest (u :: acc)

/-- Instantiate a constant's universe parameters with fresh level metavariables
    and return `(constExpr, instantiatedType)`. -/
def mkConstWithFreshMVarLevels (constName : Ix.Name) : IxElabM (Ix.Expr × Ix.Expr) := do
  let st ← get
  match st.env.find? constName with
  | none => throwElabError s!"unknown constant '{Name.toStringTotal constName}'"
  | some ci =>
    let cnst := Expr.ConstantInfo.getCnstPure ci
    match cnst.levelParams.toList with
    | [] =>
      return (Expr.mkConst constName #[], cnst.type)
    | ps =>
      let us ← mkFreshLevelMVarsFor ps []
      let expr := Expr.mkConst constName us
      let ty := substExprLevelParams cnst.levelParams us cnst.type
      return (expr, ty)

/-- Open all leading `.forallE` binders of `fnType` as fresh metavariables, returning
    `(appliedFn, instGoals, resultType)` where `instGoals` are `[...]` instance subgoals. -/
def openForallMVars : Nat → Ix.Expr → Ix.Expr → List Ix.Expr →
    IxElabM (Ix.Expr × List Ix.Expr × Ix.Expr)
  | 0, fn, fnTy, instGoals => return (fn, instGoals.reverse, fnTy)
  | fuel + 1, fn, fnTy, instGoals => do
    let fnTyWhnf ← match stripMData fnTy with
      | .forallE _ _ _ _ _ => pure fnTy
      | _                  => whnf 32 fnTy
    match stripMData fnTyWhnf with
    | .forallE nm dom body bi _ =>
      let mvar ← mkFreshExprMVar dom nm
      let fn' := Expr.mkApp fn mvar
      let body' := instantiate1 body mvar
      let instGoals' := if bi == .instImplicit then mvar :: instGoals else instGoals
      openForallMVars fuel fn' body' instGoals'
    | _ =>
      return (fn, instGoals.reverse, fnTyWhnf)

/-- Extract the head constant name of the return type of a telescope (without allocating mvars). -/
def returnHeadConstName? : Nat → Ix.Expr → Option Ix.Name
  | 0, _ => none
  | fuel + 1, ty =>
    match stripMData ty with
    | .forallE _ _ body _ _ => returnHeadConstName? fuel body
    | e =>
      match getAppFn e with
      | .const nm _ _ => some nm
      | _             => none

/-- Bounded backtracking typeclass synthesis for `goalType : Ix.Expr`.
    1. Checks local context declarations in reverse order (innermost first).
    2. Checks registered global `env.instancesByClass` matching the head class name. -/
def synthInstance? : Nat → Ix.Expr → IxElabM (Option Ix.Expr)
  | 0, _ => return none
  | fuel + 1, goalType => do
    let goalWhnf ← whnf 32 goalType
    match getAppFn goalWhnf with
    | .const className _ _ =>
      let ctx ← read
      -- 1. Try local context hypotheses (e.g. `[inst : Add α]`)
      for decl in ctx.lctx.revDecls do
        let mightMatch : Bool := match returnHeadConstName? 16 decl.type with
          | some cName => cName == className
          | none       => decl.binderInfo == .instImplicit
        if mightMatch then
          let hit? ← observing? do
            let fvar := Expr.mkFVar decl.fvarId
            let (cand, subGoals, resTy) ← openForallMVars 16 fvar decl.type []
            let ok ← isDefEq 32 resTy goalWhnf
            if !ok then throwElabError "local instance mismatch"
            for sg in subGoals do
              let sgTy ← inferType 32 sg
              match ← synthInstance? fuel sgTy with
              | some sgVal =>
                let sgOk ← isDefEq 32 sg sgVal
                if !sgOk then throwElabError "subgoal unification failed"
              | none => throwElabError "subgoal synthesis failed"
            instantiateMVars 32 cand
          if hit?.isSome then return hit?
      -- 2. Try global registered instances for `className`
      let st ← get
      let matchingInsts := st.env.instancesByClass.get? className |>.getD []
      for entry in matchingInsts do
        let hit? ← observing? do
          let (instConst, instTy) ← mkConstWithFreshMVarLevels entry.instName
          let (cand, subGoals, resTy) ← openForallMVars 16 instConst instTy []
          let ok ← isDefEq 32 resTy goalWhnf
          if !ok then throwElabError "global instance mismatch"
          for sg in subGoals do
            let sgTy ← inferType 32 sg
            match ← synthInstance? fuel sgTy with
            | some sgVal =>
              let sgOk ← isDefEq 32 sg sgVal
              if !sgOk then throwElabError "subgoal unification failed"
            | none => throwElabError "subgoal synthesis failed"
          instantiateMVars 32 cand
        if hit?.isSome then return hit?
      return none
    | _ => return none

end Ix.Frontend.Elab
