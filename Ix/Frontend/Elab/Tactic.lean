/-
  Ix.Frontend.Elab.Tactic: Pure, Total, Deterministic Goal-List Tactic Engine
  for the Ix Frontend.

  Architecture:
  - `TacticState` maintains the list of open goal metavariable IDs (`goals : List Ix.Name`).
  - `DelayedMVarAssign` in `MetavarContext` allows binder-introducing tactics (`intro`, `intros`,
    `have`, `let`, `funext`, `ext`, and `rw ... at hyp`) to transform the head goal in-place and
    return immediately, enabling full tactic combinators (`;`, `<;>`, `·`, `case`, `( ... )`,
    `first`, `try`, `repeat`, `all_goals`, `any_goals`).
  - Equational tactics (`rw`, `symm`, `trans`, `congr`, `simp`) construct explicit kernel proof
    terms via `@Eq.casesOn` and `@Eq.refl` (requiring zero extra prelude axioms and reducing by
    pure kernel `ι`-reduction).
  - Inductive elimination tactics (`cases`, `induction`, `contradiction`, `exfalso`) construct
    explicit `<Ind>.casesOn` and `<Ind>.recOn` applications with `kabstract`-generalized motives.
  - Every recursive loop is structurally recursive on `Nat` (`Nat.rec`) or `List` (`List.rec`),
    with zero `partial`, zero `unsafe`, and zero `WellFounded.fix`.
-/
module

public import Ix.Frontend.Elab.Meta
public import Ix.Frontend.AuxGen
public import Ix.Frontend.Parser.Term

@[expose] public section

namespace Ix.Frontend.Elab

open Ix.Frontend
open Ix.Frontend.Parser
open Ix.Frontend.AuxGen

/-! ## `TacticState` & `TacticM` Monad -/

/-- Goal-list state of the pure tactic engine. -/
structure TacticState where
  goals : List Ix.Name := []
  deriving Repr, Inhabited

/-- Pure, deterministic tactic monad over `IxElabM`. -/
abbrev TacticM (α : Type) := StateT TacticState IxElabM α

/-- Strictly update `TacticState.goals` without `{ s with ... }` projection chains. -/
@[inline] def setTacticGoals (gs : List Ix.Name) : TacticM Unit := fun _ =>
  return ((), ⟨gs⟩)

/-- Return all currently unassigned goals in `TacticState.goals`, pruning any assigned goals. -/
def getUnassignedGoals : TacticM (List Ix.Name) := do
  let tSt ← get
  let eSt ← liftM (get : IxElabM ElabState)
  let gs := tSt.goals.filter fun gId => !eSt.mctx.isExprAssigned gId
  setTacticGoals gs
  return gs

/-- Pop and return `(gId, gDecl, gTy)` for the current main goal (leaving `gId` at the head of `goals`). -/
def getMainGoal (stx? : Option Ix.Syntax := none) : TacticM (Ix.Name × MetavarDecl × Ix.Expr) := do
  let gs ← getUnassignedGoals
  match gs with
  | [] => liftM (throwElabError "no goals left to solve" stx?)
  | gId :: _ =>
    let eSt ← liftM (get : IxElabM ElabState)
    match eSt.mctx.findDecl? gId with
    | none => liftM (throwElabError s!"unknown tactic goal '?{Name.toStringTotal gId}'" stx?)
    | some gDecl =>
      let gTy ← liftM (instantiateMVars 32 gDecl.type)
      return (gId, gDecl, gTy)

/-- Run `act gId gDecl gTy` with `ElabContext.lctx` set to the main goal's `LocalContext`. -/
def withMainGoalContext (stx? : Option Ix.Syntax := none)
    (act : Ix.Name → MetavarDecl → Ix.Expr → TacticM α) : TacticM α := do
  let (gId, gDecl, gTy) ← getMainGoal stx?
  withReader (fun ctx => { ctx with lctx := gDecl.lctx }) (act gId gDecl gTy)

/-- Replace the head goal in `TacticState.goals` with `newGoals`. -/
def replaceMainGoal (newGoals : List Ix.Name) : TacticM Unit := do
  let gs ← getUnassignedGoals
  match gs with
  | [] => setTacticGoals newGoals
  | _ :: rest => setTacticGoals (newGoals ++ rest)

/-- Assign `val` to the current main goal and remove it from `TacticState.goals`. -/
def closeMainGoal (val : Ix.Expr) (stx? : Option Ix.Syntax := none) : TacticM Unit := do
  let (gId, _, _) ← getMainGoal stx?
  liftM (modifyMCtx (·.assignExpr gId val))
  replaceMainGoal []

/-- Pure O(1) snapshot of `(TacticState, ElabState)` for backtracking combinators. -/
def saveTacticSnapshot : TacticM (TacticState × ElabState) := do
  let tSt ← get
  let eSt ← liftM (get : IxElabM ElabState)
  return (tSt, eSt)

/-- Restore a previously saved `(TacticState, ElabState)` snapshot. -/
def restoreTacticSnapshot (snap : TacticState × ElabState) : TacticM Unit := do
  set snap.1
  liftM (set snap.2 : IxElabM Unit)

/-- Execute `act` speculatively; on error, roll back `(TacticState, ElabState)` and return `none`. -/
def tryTactic? (act : TacticM α) : TacticM (Option α) := fun tSt => fun ctx eSt =>
  match ((act tSt) ctx).run eSt with
  | .ok ((res, tSt'), eSt') => .ok ((some res, tSt'), eSt')
  | .error _                => .ok ((none, tSt), eSt)

/-! ## Pure `Eq.casesOn` Proof Builders & `kabstract` -/

/-- Decompose `@Eq.{u} α lhs rhs` after `whnf`, returning `some (u, α, lhs, rhs)`. -/
def matchEqType? (fuel : Nat) (ty : Ix.Expr) : IxElabM (Option (Ix.Level × Ix.Expr × Ix.Expr × Ix.Expr)) := do
  let tyW ← whnf fuel ty
  let (fn, args) := getAppFnArgs tyW
  match fn with
  | .const nm us _ =>
    if nm == Name.simple "Eq" && args.size == 3 then
      let u := us.getD 0 Level.mkZero
      return some (u, args.getD 0 tyW, args.getD 1 tyW, args.getD 2 tyW)
    else
      return none
  | _ => return none

/-- Build `@Eq.refl.{u} α a : @Eq.{u} α a a`. -/
def mkEqReflExpr (u : Ix.Level) (alpha a : Ix.Expr) : Ix.Expr :=
  Expr.mkAppN (Expr.mkConst (Name.mkStr2 "Eq" "refl") #[u]) #[alpha, a]

/-- Build a proof of `@Eq.{u} α b a` from `h : @Eq.{u} α a b` via `@Eq.casesOn.{0, u}`. -/
def mkEqSymmExpr (u : Ix.Level) (alpha a b h : Ix.Expr) : Ix.Expr :=
  let eqConst := Expr.mkConst (Name.simple "Eq") #[u]
  let eqAX := Expr.mkAppN eqConst #[liftLooseBVars alpha 1, liftLooseBVars a 1, Expr.mkBVar 0]
  let eqXA := Expr.mkAppN eqConst #[liftLooseBVars alpha 2, Expr.mkBVar 1, liftLooseBVars a 2]
  let motive :=
    Expr.mkLam (Name.simple "x") alpha
      (Expr.mkLam Name.mkAnon eqAX eqXA .default) .default
  let reflAA := mkEqReflExpr u alpha a
  Expr.mkAppN (Expr.mkConst (Name.mkStr2 "Eq" "casesOn") #[Level.mkZero, u])
    #[alpha, a, motive, b, h, reflAA]

/-- Build a proof of `@Eq.{u} α a c` from `h1 : @Eq.{u} α a b` and `h2 : @Eq.{u} α b c` via `@Eq.casesOn.{0, u}`. -/
def mkEqTransExpr (u : Ix.Level) (alpha a b c h1 h2 : Ix.Expr) : Ix.Expr :=
  let eqConst := Expr.mkConst (Name.simple "Eq") #[u]
  let eqBX := Expr.mkAppN eqConst #[liftLooseBVars alpha 1, liftLooseBVars b 1, Expr.mkBVar 0]
  let eqAX := Expr.mkAppN eqConst #[liftLooseBVars alpha 2, liftLooseBVars a 2, Expr.mkBVar 1]
  let motive :=
    Expr.mkLam (Name.simple "x") alpha
      (Expr.mkLam Name.mkAnon eqBX eqAX .default) .default
  Expr.mkAppN (Expr.mkConst (Name.mkStr2 "Eq" "casesOn") #[Level.mkZero, u])
    #[alpha, b, motive, c, h2, h1]

/-- Build a proof of `@Eq.{v} β (f a) (f b)` from `h : @Eq.{u} α a b` via `@Eq.casesOn.{0, u}`. -/
def mkEqCongrArgExpr (u v : Ix.Level) (alpha beta f a b h : Ix.Expr) : Ix.Expr :=
  let eqU := Expr.mkConst (Name.simple "Eq") #[u]
  let eqV := Expr.mkConst (Name.simple "Eq") #[v]
  let eqAX := Expr.mkAppN eqU #[liftLooseBVars alpha 1, liftLooseBVars a 1, Expr.mkBVar 0]
  let fa := Expr.mkApp f a
  let fx := Expr.mkApp (liftLooseBVars f 2) (Expr.mkBVar 1)
  let eqFAFX := Expr.mkAppN eqV #[liftLooseBVars beta 2, liftLooseBVars fa 2, fx]
  let motive :=
    Expr.mkLam (Name.simple "x") alpha
      (Expr.mkLam Name.mkAnon eqAX eqFAFX .default) .default
  let reflFAFA := mkEqReflExpr v beta fa
  Expr.mkAppN (Expr.mkConst (Name.mkStr2 "Eq" "casesOn") #[Level.mkZero, u])
    #[alpha, a, motive, b, h, reflFAFA]

/-- Transport `proofPA : instantiate1 absBody a` along `hEq : @Eq.{uEq} α a b` to produce a term
    of type `instantiate1 absBody b` (where `absBody` has sort `Sort uMotive` and loose `bvar 0 : α`). -/
def mkEqTransportExpr (uEq uMotive : Ix.Level) (alpha a b absBody hEq proofPA : Ix.Expr) : Ix.Expr :=
  let eqU := Expr.mkConst (Name.simple "Eq") #[uEq]
  let eqAX := Expr.mkAppN eqU #[liftLooseBVars alpha 1, liftLooseBVars a 1, Expr.mkBVar 0]
  -- Shift loose bvars in `absBody` up by 1 so `bvar 0` (`x : α`) becomes `bvar 1` under `_ : Eq a x`
  let bodyUnderEq := liftLooseBVars absBody 1 0
  let motive :=
    Expr.mkLam (Name.simple "x") alpha
      (Expr.mkLam Name.mkAnon eqAX bodyUnderEq .default) .default
  Expr.mkAppN (Expr.mkConst (Name.mkStr2 "Eq" "casesOn") #[uMotive, uEq])
    #[alpha, a, motive, b, hEq, proofPA]

/-- Test whether subterm `e` (without loose bvars) matches `pat` up to `isDefEq`. -/
def tryKAbstractMatch (fuel : Nat) (e pat : Ix.Expr) : IxElabM Bool := do
  if hasLooseBVarsAt e 0 then return false
  if e == pat then return true
  let ok? ← observing? do
    let eqOk ← isDefEq fuel e pat
    if !eqOk then throwElabError "kabstract mismatch"
    return true
  return (ok? == some true)

/-- Core recursive worker for `kabstract`, structurally recursive on `kFuel : Nat`. -/
def kabstractCore (fuel : Nat) : Nat → Ix.Expr → Ix.Expr → Nat → IxElabM (Bool × Ix.Expr)
  | 0, _, e, _ => return (false, e)
  | kFuel + 1, pat, e, depth => do
    let matched ← tryKAbstractMatch fuel e pat
    if matched then
      return (true, Expr.mkBVar depth)
    match e with
    | .app f a _ =>
      let (cf, f') ← kabstractCore fuel kFuel pat f depth
      let (ca, a') ← kabstractCore fuel kFuel pat a depth
      if cf || ca then
        return (true, Expr.mkApp f' a')
      else if !hasLooseBVarsAt e 0 then
        -- If `e` is a reducible application (e.g. `myAdd (Nat.succ k) 0`), reduce 1 `whnf` step
        -- so recursive calls inside unfolded `<Ind>.recOn` branches can be matched!
        let eW ← whnf fuel e
        if eW != e then
          let (cw, eW') ← kabstractCore fuel kFuel pat eW depth
          if cw then return (true, eW') else return (false, e)
        else
          return (false, e)
      else
        return (false, e)
    | .lam nm t b bi _ =>
      let (ct, t') ← kabstractCore fuel kFuel pat t depth
      let (cb, b') ← kabstractCore fuel kFuel pat b (depth + 1)
      if ct || cb then return (true, Expr.mkLam nm t' b' bi) else return (false, e)
    | .forallE nm t b bi _ =>
      let (ct, t') ← kabstractCore fuel kFuel pat t depth
      let (cb, b') ← kabstractCore fuel kFuel pat b (depth + 1)
      if ct || cb then return (true, Expr.mkForallE nm t' b' bi) else return (false, e)
    | .letE nm t v b nd _ =>
      let (ct, t') ← kabstractCore fuel kFuel pat t depth
      let (cv, v') ← kabstractCore fuel kFuel pat v depth
      let (cb, b') ← kabstractCore fuel kFuel pat b (depth + 1)
      if ct || cv || cb then return (true, Expr.mkLetE nm t' v' b' nd) else return (false, e)
    | .proj nm i s _ =>
      let (cs, s') ← kabstractCore fuel kFuel pat s depth
      if cs then return (true, Expr.mkProj nm i s') else return (false, e)
    | .mdata md x _ =>
      let (cx, x') ← kabstractCore fuel kFuel pat x depth
      if cx then return (true, Expr.mkMData md x') else return (false, e)
    | _ =>
      return (false, e)

/-- Abstract occurrences of `pat` in `e` into `bvar 0` (shifting existing loose bvars in `e` up by 1). -/
def kabstract (fuel : Nat) (pat : Ix.Expr) (e : Ix.Expr) : IxElabM (Bool × Ix.Expr) := do
  let eLifted := liftLooseBVars e 1 0
  kabstractCore fuel 64 pat eLifted 0

/-! ## Pure Beta-Reduction & Eliminator Helpers for `cases` / `induction` -/

/-- Apply `fn` to `args`, beta-reducing up to `steps` leading `.lam` binders. -/
def applyBetaSteps : Nat → Ix.Expr → List Ix.Expr → Ix.Expr
  | 0, fn, args => args.foldl Expr.mkApp fn
  | k + 1, fn, arg :: rest =>
    match stripMData fn with
    | .lam _ _ b _ _ => applyBetaSteps k (instantiate1 b arg) rest
    | _              => (arg :: rest).foldl Expr.mkApp fn
  | _, fn, [] => fn

/-- Beta-reduce any `(fun x => b) a` redexes throughout `e` (used after substituting `motiveLam`). -/
def betaReduceExpr : Ix.Expr → Ix.Expr
  | .app f a _ =>
    let f' := betaReduceExpr f
    let a' := betaReduceExpr a
    let (hd, sp) := getAppFnArgs f'
    applyBetaSteps 8 hd (sp.toList ++ [a'])
  | .lam nm t b bi _ => Expr.mkLam nm (betaReduceExpr t) (betaReduceExpr b) bi
  | .forallE nm t b bi _ => Expr.mkForallE nm (betaReduceExpr t) (betaReduceExpr b) bi
  | .letE nm t v b nd _ => Expr.mkLetE nm (betaReduceExpr t) (betaReduceExpr v) (betaReduceExpr b) nd
  | .proj nm i s _ => Expr.mkProj nm i (betaReduceExpr s)
  | .mdata md x _ => Expr.mkMData md (betaReduceExpr x)
  | other => other

/-- Count the number of leading `.forallE` binders on `e`. -/
def countLeadingForalls : Nat → Ix.Expr → Nat
  | 0, _ => 0
  | k + 1, e =>
    match stripMData e with
    | .forallE _ _ b _ _ => 1 + countLeadingForalls k b
    | _                  => 0

/-- Extract the number of minor-premise binders for each of the `numMinors` constructors
    after peeling `prefixCount` binders from the uninstantiated eliminator type `rawElimTy`. -/
def extractMinorBinderCounts (prefixCount numMinors : Nat) (rawElimTy : Ix.Expr) : Array Nat :=
  let (_, _, afterPrefix) := openForallTelescope prefixCount rawElimTy " dummy" 0 #[] #[]
  let (_, minorDecls, _) := openForallTelescope numMinors afterPrefix "m" 0 #[] #[]
  minorDecls.map fun d => countLeadingForalls 32 d.domain

/-- Return the last string component of a name (e.g. `Nat.succ` -> `"succ"`). -/
def lastNameStr : Ix.Name → String
  | .str _ s _ => s
  | _          => ""

/-- True if a user branch tag `tag` matches constructor name `ctorName`. -/
def matchesCtorTag (ctorName tag : Ix.Name) : Bool :=
  ctorName == tag || (lastNameStr ctorName != "" && lastNameStr ctorName == lastNameStr tag)

/-- Collect unassigned expression metavariable IDs occurring in `e` in left-to-right order. -/
def collectUnassignedMVarIds (mctx : MetavarContext) (e : Ix.Expr) : List Ix.Name :=
  let rec go : Ix.Expr → List Ix.Name → List Ix.Name
    | .mvar id _, acc =>
      if !mctx.isExprAssigned id && !acc.contains id then id :: acc else acc
    | .app f a _, acc => go a (go f acc)
    | .lam _ t b _ _, acc => go b (go t acc)
    | .forallE _ t b _ _, acc => go b (go t acc)
    | .letE _ t v b _ _, acc => go b (go v (go t acc))
    | .proj _ _ s _, acc => go s acc
    | .mdata _ x _, acc => go x acc
    | _, acc => acc
  (go e []).reverse

/-! ## Definitional Simplification (`dsimpExpr`) -/

/-- Normalize subterms of `e` using `whnf` (beta, iota, zeta, projections, and Nat/String primitives)
    without unfolding propositional connectives (`Eq`, `And`, `Or`, `Iff`, `Exists`, `True`, `False`). -/
def isPreservedHeadConst (nm : Ix.Name) : Bool :=
  nm == Name.simple "Eq" || nm == Name.simple "And" || nm == Name.simple "Or" ||
  nm == Name.simple "Iff" || nm == Name.simple "Exists" || nm == Name.simple "True" ||
  nm == Name.simple "False" || nm == Name.simple "Not" || nm == Name.simple "Ne"

def dsimpExpr (fuel : Nat) : Nat → Ix.Expr → IxElabM Ix.Expr
  | 0, e => return e
  | dFuel + 1, e => do
    match e with
    | .app f a _ =>
      let f' ← dsimpExpr fuel dFuel f
      let a' ← dsimpExpr fuel dFuel a
      let appExpr := Expr.mkApp f' a'
      if hasLooseBVarsAt appExpr 0 then
        return appExpr
      else
        let (hd, _) := getAppFnArgs appExpr
        match hd with
        | .const nm _ _ =>
          if isPreservedHeadConst nm then return appExpr
          else whnf fuel appExpr
        | .lam _ _ _ _ _ => whnf fuel appExpr
        | _ => return appExpr
    | .proj nm i s _ =>
      let s' ← dsimpExpr fuel dFuel s
      let pExpr := Expr.mkProj nm i s'
      if hasLooseBVarsAt pExpr 0 then return pExpr else whnf fuel pExpr
    | .letE _ _ v b _ _ =>
      let v' ← dsimpExpr fuel dFuel v
      dsimpExpr fuel dFuel (instantiate1 b v')
    | .lam nm t b bi _ =>
      let t' ← dsimpExpr fuel dFuel t
      let b' ← dsimpExpr fuel dFuel b
      return Expr.mkLam nm t' b' bi
    | .forallE nm t b bi _ =>
      let t' ← dsimpExpr fuel dFuel t
      let b' ← dsimpExpr fuel dFuel b
      return Expr.mkForallE nm t' b' bi
    | .mdata md x _ =>
      let x' ← dsimpExpr fuel dFuel x
      return Expr.mkMData md x'
    | other => return other

/-! ## Individual Tactic Implementations -/

/-- `intro` / `intros`: peel `.forallE` binders into `lctx` and link via `DelayedMVarAssign`. -/
def evalIntroTactic (fuel : Nat) (tac : Ix.Syntax) : TacticM Unit :=
  withMainGoalContext (some tac) fun gId gDecl gTy => do
    let kw := Syntax.getAtomVal (Syntax.getArg tac 0)
    let rawIds := (Syntax.getArgs (Syntax.getArg tac 1)).toList
    let rec introNamed (rem : List Ix.Syntax) (curTy : Ix.Expr) (revFVars : List Ix.Name) :
        TacticM (Ix.Expr × List Ix.Name × LocalContext) := do
      match rem with
      | [] =>
        let ctx ← read
        return (curTy, revFVars.reverse, ctx.lctx)
      | idStx :: nextIds =>
        let curW ← liftM (whnf fuel curTy)
        match stripMData curW with
        | .forallE defNm dom body bi _ =>
          let uName :=
            let id := Syntax.getId idStx
            if Name.isAnonymous id then
              if Name.isAnonymous defNm then Name.simple "h" else defNm
            else id
          let fvId ← liftM (mkFreshName "_fvar")
          let fvExpr := Expr.mkFVar fvId
          let decl : LocalDecl := { fvarId := fvId, userName := uName, type := dom, binderInfo := bi }
          withReader (fun ctx => { ctx with lctx := ctx.lctx.addDecl decl }) do
            introNamed nextIds (instantiate1 body fvExpr) (fvId :: revFVars)
        | .letE defNm ty val body _ _ =>
          let uName :=
            let id := Syntax.getId idStx
            if Name.isAnonymous id then
              if Name.isAnonymous defNm then Name.simple "h" else defNm
            else id
          let fvId ← liftM (mkFreshName "_fvar")
          let fvExpr := Expr.mkFVar fvId
          let decl : LocalDecl := { fvarId := fvId, userName := uName, type := ty, value? := some val }
          withReader (fun ctx => { ctx with lctx := ctx.lctx.addDecl decl }) do
            introNamed nextIds (instantiate1 body fvExpr) (fvId :: revFVars)
        | _ =>
          liftM (throwElabError "'intro' tactic expected a function/forall goal type" (some tac))
    let rec introsAll (k : Nat) (curTy : Ix.Expr) (revFVars : List Ix.Name) :
        TacticM (Ix.Expr × List Ix.Name × LocalContext) := do
      match k with
      | 0 =>
        let ctx ← read
        return (curTy, revFVars.reverse, ctx.lctx)
      | k' + 1 =>
        let curW ← liftM (whnf fuel curTy)
        match stripMData curW with
        | .forallE defNm dom body bi _ =>
          let uName := if Name.isAnonymous defNm then Name.simple "h" else defNm
          let fvId ← liftM (mkFreshName "_fvar")
          let fvExpr := Expr.mkFVar fvId
          let decl : LocalDecl := { fvarId := fvId, userName := uName, type := dom, binderInfo := bi }
          withReader (fun ctx => { ctx with lctx := ctx.lctx.addDecl decl }) do
            introsAll k' (instantiate1 body fvExpr) (fvId :: revFVars)
        | _ =>
          let ctx ← read
          return (curTy, revFVars.reverse, ctx.lctx)
    let (finalTy, fvars, lctx') ←
      if rawIds.isEmpty then
        if kw == "intros" then
          introsAll 32 gTy []
        else
          introNamed [Syntax.mkSimpleIdent Name.mkAnon] gTy []
      else
        introNamed rawIds gTy []
    if fvars.isEmpty then
      return ()
    else
      let subMVar ← withReader (fun ctx => { ctx with lctx := lctx' }) do
        liftM (mkFreshExprMVar finalTy gDecl.userName)
      let subId := match subMVar with | .mvar id _ => id | _ => gId
      liftM (modifyMCtx (·.assignDelayed gId { lctx := lctx', fvars, pendingMVar := subId }))
      replaceMainGoal [subId]

/-- `rfl` / `decide`: close reflexive `@Eq`, `@Iff`, or `True` goals. -/
def evalRflTactic (fuel : Nat) (tac : Ix.Syntax) : TacticM Unit :=
  withMainGoalContext (some tac) fun _ _ gTy => do
    let gTyW ← liftM (whnf fuel gTy)
    let (hFn, hArgs) := getAppFnArgs gTyW
    match hFn with
    | .const cName cUnivs _ =>
      if cName == Name.simple "Eq" && hArgs.size == 3 then
        let tyArg := hArgs.getD 0 gTyW
        let lhs   := hArgs.getD 1 gTyW
        let rhs   := hArgs.getD 2 gTyW
        let ok ← liftM (isDefEq fuel lhs rhs)
        if !ok then
          liftM (throwElabError "'rfl' failed: left-hand side and right-hand side are not definitionally equal" (some tac))
        closeMainGoal (mkEqReflExpr (cUnivs.getD 0 Level.mkZero) tyArg lhs) (some tac)
      else if cName == Name.simple "Iff" && hArgs.size == 2 then
        let a := hArgs.getD 0 gTyW
        let b := hArgs.getD 1 gTyW
        let ok ← liftM (isDefEq fuel a b)
        if !ok then
          liftM (throwElabError "'rfl' failed: Iff sides are not definitionally equal" (some tac))
        let idLam := Expr.mkLam (Name.simple "h") a (Expr.mkBVar 0) .default
        let iffRefl := Expr.mkAppN (Expr.mkConst (Name.mkStr2 "Iff" "intro") #[]) #[a, a, idLam, idLam]
        closeMainGoal iffRefl (some tac)
      else if cName == Name.simple "True" && hArgs.isEmpty then
        closeMainGoal (Expr.mkConst (Name.mkStr2 "True" "intro") #[]) (some tac)
      else
        let (reflConst, reflTy) ← liftM (mkConstWithFreshMVarLevels (Name.mkStr2 "Eq" "refl"))
        let (cand, _, resTy) ← liftM (openForallMVars 8 reflConst reflTy [])
        let ok ← liftM (isDefEq fuel resTy gTyW)
        if !ok then
          liftM (throwElabError "'rfl' failed: goal is not a reflexive equality" (some tac))
        let candInst ← liftM (instantiateMVars 32 cand)
        closeMainGoal candInst (some tac)
    | _ =>
      liftM (throwElabError "'rfl' failed: goal is not an equality" (some tac))

/-- `assumption`: close the goal using a matching hypothesis in `lctx`. -/
def evalAssumptionTactic (fuel : Nat) (tac : Ix.Syntax) : TacticM Unit :=
  withMainGoalContext (some tac) fun _ gDecl gTy => do
    let rec findMatching : List LocalDecl → IxElabM (Option Ix.Expr)
      | [] => return none
      | d :: rest => do
        let dTy ← instantiateMVars 16 d.type
        let ok? ← observing? do
          let eqOk ← isDefEq fuel dTy gTy
          if !eqOk then throwElabError "mismatch"
          return (Expr.mkFVar d.fvarId)
        match ok? with
        | some fv => return some fv
        | none    => findMatching rest
    match ← liftM (findMatching gDecl.lctx.revDecls) with
    | some fv => closeMainGoal fv (some tac)
    | none    => liftM (throwElabError "'assumption' tactic failed to find a matching local hypothesis" (some tac))

/-- Build `@False.casesOn.{uGoal} (fun _ => gTy) falseProof : gTy`. -/
def mkFalseElimExpr (uGoal : Ix.Level) (gTy falseProof : Ix.Expr) : Ix.Expr :=
  let falseConst := Expr.mkConst (Name.simple "False") #[]
  let motive := Expr.mkLam Name.mkAnon falseConst (liftLooseBVars gTy 1) .default
  Expr.mkAppN (Expr.mkConst (Name.mkStr2 "False" "casesOn") #[normalizeLevel uGoal]) #[motive, falseProof]

/-- `contradiction`: close the goal from `h : False`, `h1 : P` & `h2 : ¬ P`, `h : a ≠ a`, or distinct constructors `C₁ ... = C₂ ...`. -/
def evalContradictionTactic (fuel : Nat) (tac : Ix.Syntax) : TacticM Unit :=
  withMainGoalContext (some tac) fun _ gDecl gTy => do
    let uGoal ← liftM (ensureSort 32 gTy)
    let decls := gDecl.lctx.revDecls
    -- 1. Check for `h : False` or `h : a ≠ a` (`Eq α a b → False` with `a == b`)
    let mut falseProof? : Option Ix.Expr := none
    for d in decls do
      if falseProof?.isNone then
        let dTy ← liftM (instantiateMVars 16 d.type)
        let dTyW ← liftM (whnf fuel dTy)
        match stripMData dTyW with
        | .const nm _ _ =>
          if nm == Name.simple "False" then
            falseProof? := some (Expr.mkFVar d.fvarId)
        | .forallE _ dom body _ _ =>
          let bodyW ← liftM (whnf fuel body)
          match stripMData bodyW with
          | .const bNm _ _ =>
            if bNm == Name.simple "False" then
              -- Check if `dom` is `Eq α a b` with `isDefEq a b`
              if let some (uEq, alpha, lhs, rhs) ← liftM (matchEqType? fuel dom) then
                let eqOk? ← liftM <| observing? do
                  let ok ← isDefEq fuel lhs rhs
                  if !ok then throwElabError "not refl"
                  return true
                if eqOk? == some true then
                  falseProof? := some (Expr.mkApp (Expr.mkFVar d.fvarId) (mkEqReflExpr uEq alpha lhs))
              -- Or check if any `dPos : dom` exists in `decls`
              if falseProof?.isNone then
                for dPos in decls do
                  if falseProof?.isNone then
                    let posTy ← liftM (instantiateMVars 16 dPos.type)
                    let ok? ← liftM <| observing? do
                      let ok ← isDefEq fuel posTy dom
                      if !ok then throwElabError "mismatch"
                      return true
                    if ok? == some true then
                      falseProof? := some (Expr.mkApp (Expr.mkFVar d.fvarId) (Expr.mkFVar dPos.fvarId))
          | _ => pure ()
        | _ => pure ()
    match falseProof? with
    | some fp =>
      closeMainGoal (mkFalseElimExpr uGoal gTy fp) (some tac)
    | none =>
      liftM (throwElabError "'contradiction' tactic failed to find contradictory hypotheses" (some tac))

/-- `exfalso`: replace main goal `?g : gTy` with `?g' : False`. -/
def evalExfalsoTactic (tac : Ix.Syntax) : TacticM Unit :=
  withMainGoalContext (some tac) fun gId _ gTy => do
    let uGoal ← liftM (ensureSort 32 gTy)
    let falseConst := Expr.mkConst (Name.simple "False") #[]
    let subMVar ← liftM (mkFreshExprMVar falseConst (Name.simple "False"))
    let subId := match subMVar with | .mvar id _ => id | _ => gId
    let proof := mkFalseElimExpr uGoal gTy subMVar
    liftM (modifyMCtx (·.assignExpr gId proof))
    replaceMainGoal [subId]

/-- `trivial`: try `rfl`, then `assumption`, then `contradiction`. -/
def evalTrivialTactic (fuel : Nat) (tac : Ix.Syntax) : TacticM Unit := do
  if (← tryTactic? (evalRflTactic fuel tac)).isSome then return ()
  if (← tryTactic? (evalAssumptionTactic fuel tac)).isSome then return ()
  if (← tryTactic? (evalContradictionTactic fuel tac)).isSome then return ()
  liftM (throwElabError "'trivial' tactic failed to close goal" (some tac))

/-- Apply an already-elaborated function `(fnExpr, fnTy)` to the current main goal. -/
def applyExprToMainGoal (fuel : Nat) (tac : Ix.Syntax) (fnExpr fnTy : Ix.Expr) : TacticM Unit :=
  withMainGoalContext (some tac) fun gId _ gTy => do
    let rec applyOpen (k : Nat) (curFn : Ix.Expr) (curTy : Ix.Expr)
        (mvars : List (Ix.Expr × Lean.BinderInfo)) : IxElabM (Ix.Expr × List Ix.Name) := do
      let ok ← observing? do
        let eqOk ← isDefEq fuel curTy gTy
        if !eqOk then throwElabError "not yet matching"
        return true
      if ok == some true then
        -- Try synthesizing any `[...]` instance metavariables
        for (mv, bi) in mvars.reverse do
          if bi == .instImplicit then
            let mvTy ← inferType fuel mv
            if let some instVal ← synthInstance? 8 mvTy then
              let _ ← isDefEq fuel mv instVal
        let stNow ← get
        let openGoals := mvars.reverse.filterMap fun (mv, _) =>
          match mv with
          | .mvar mid _ =>
            if !stNow.mctx.isExprAssigned mid then some mid else none
          | _ => none
        return (curFn, openGoals)
      else
        match k with
        | 0 => throwElabError "'apply' failed to unify conclusion with goal" (some tac)
        | k' + 1 =>
          let curW ← whnf fuel curTy
          match stripMData curW with
          | .forallE nm dom body bi _ =>
            let mv ← mkFreshExprMVar dom nm
            applyOpen k' (Expr.mkApp curFn mv) (instantiate1 body mv) ((mv, bi) :: mvars)
          | _ => throwElabError "'apply' failed to match goal type" (some tac)
    let (appliedVal, subGoals) ← liftM (applyOpen 24 fnExpr fnTy [])
    liftM (modifyMCtx (·.assignExpr gId appliedVal))
    replaceMainGoal subGoals

/-- `constructor` / `split` / `left` / `right`: apply the appropriate constructor of the target inductive type. -/
def evalCtorSelectTactic (fuel : Nat) (tac : Ix.Syntax) (which : String) : TacticM Unit :=
  withMainGoalContext (some tac) fun _ _ gTy => do
    let gTyW ← liftM (whnf fuel gTy)
    let (hFn, _) := getAppFnArgs gTyW
    let stNow ← liftM (get : IxElabM ElabState)
    match hFn with
    | .const indName _ _ =>
      match stNow.env.find? indName with
      | some (.inductInfo ival) =>
        let targetCtor? : Option Ix.Name :=
          if which == "left" then
            let inl := Name.mkStr indName "inl"
            let lft := Name.mkStr indName "left"
            if ival.ctors.contains inl then some inl
            else if ival.ctors.contains lft then some lft
            else ival.ctors[0]?
          else if which == "right" then
            let inr := Name.mkStr indName "inr"
            let rgt := Name.mkStr indName "right"
            if ival.ctors.contains inr then some inr
            else if ival.ctors.contains rgt then some rgt
            else ival.ctors[1]?
          else
            ival.ctors[0]?
        match targetCtor? with
        | some ctorName =>
          let (ctorConst, ctorTy) ← liftM (mkConstWithFreshMVarLevels ctorName)
          applyExprToMainGoal fuel tac ctorConst ctorTy
        | none =>
          liftM (throwElabError s!"inductive '{Name.toStringTotal indName}' has no matching constructor for '{which}'" (some tac))
      | _ => liftM (throwElabError s!"'{which}' requires an inductive target type" (some tac))
    | _ => liftM (throwElabError s!"'{which}' requires an inductive target type" (some tac))

/-- `exists e₁, e₂, ...` (`use`): supply witness(es) to a single-constructor inductive (`Exists`, `Sigma`, `Prod`), then try `trivial`. -/
def evalExistsTactic (elabRec : Ix.Syntax → Option Ix.Expr → IxElabM Ix.Expr)
    (fuel : Nat) (tac : Ix.Syntax) : TacticM Unit := do
  let witStxs := (Syntax.getArgs (Syntax.getArg tac 1)).toList
  let rec applyWitnesses : List Ix.Syntax → TacticM Unit
    | [] => return ()
    | wStx :: rest =>
      withMainGoalContext (some tac) fun gId _ gTy => do
        let gTyW ← liftM (whnf fuel gTy)
        let (hFn, _) := getAppFnArgs gTyW
        let stNow ← liftM (get : IxElabM ElabState)
        match hFn with
        | .const indName _ _ =>
          match stNow.env.find? indName with
          | some (.inductInfo ival) =>
            match ival.ctors[0]? with
            | none => liftM (throwElabError s!"'{Name.toStringTotal indName}' has no constructors for 'exists'" (some tac))
            | some ctorName =>
              let (ctorConst, ctorTy) ← liftM (mkConstWithFreshMVarLevels ctorName)
              let (ctorApplied, instGoals, afterImplTy) ← liftM (insertImplicitArgs 16 ctorConst ctorTy [])
              let afterW ← liftM (whnf fuel afterImplTy)
              match stripMData afterW with
              | .forallE _ wDom wBody _ _ =>
                let wVal ← liftM (elabRec wStx (some wDom))
                let app1 := Expr.mkApp ctorApplied wVal
                let remTy := instantiate1 wBody wVal
                let (fullApp, moreInst, finalTy) ← liftM (openForallMVars 16 app1 remTy instGoals)
                let ok ← liftM (isDefEq fuel finalTy gTyW)
                if !ok then
                  liftM (throwElabError "'exists' failed to unify constructor conclusion with goal" (some tac))
                for ig in moreInst do
                  let igTy ← liftM (inferType fuel ig)
                  if let some iv ← liftM (synthInstance? 8 igTy) then
                    let _ ← liftM (isDefEq fuel ig iv)
                let stAfter ← liftM (get : IxElabM ElabState)
                let newGoals := collectUnassignedMVarIds stAfter.mctx fullApp
                liftM (modifyMCtx (·.assignExpr gId fullApp))
                replaceMainGoal newGoals
                applyWitnesses rest
              | _ =>
                liftM (throwElabError "'exists' constructor does not take a witness argument" (some tac))
          | _ => liftM (throwElabError "'exists' target must be an inductive type" (some tac))
        | _ => liftM (throwElabError "'exists' target must be an inductive type" (some tac))
  applyWitnesses witStxs
  let _ ← tryTactic? (evalTrivialTactic fuel tac)

/-- `symm` (`symmetry`): transform `@Eq.{u} α lhs rhs` into `@Eq.{u} α rhs lhs`. -/
def evalSymmTactic (fuel : Nat) (tac : Ix.Syntax) : TacticM Unit :=
  withMainGoalContext (some tac) fun gId gDecl gTy => do
    match ← liftM (matchEqType? fuel gTy) with
    | some (u, alpha, lhs, rhs) =>
      let symmGoalTy := Expr.mkAppN (Expr.mkConst (Name.simple "Eq") #[u]) #[alpha, rhs, lhs]
      let subMVar ← liftM (mkFreshExprMVar symmGoalTy gDecl.userName)
      let subId := match subMVar with | .mvar id _ => id | _ => gId
      let proof := mkEqSymmExpr u alpha rhs lhs subMVar
      liftM (modifyMCtx (·.assignExpr gId proof))
      replaceMainGoal [subId]
    | none =>
      liftM (throwElabError "'symm' tactic requires an equality goal" (some tac))

/-- `trans [mid]` (`transitivity`): split `@Eq.{u} α lhs rhs` into `lhs = mid` and `mid = rhs`. -/
def evalTransTactic (elabRec : Ix.Syntax → Option Ix.Expr → IxElabM Ix.Expr)
    (fuel : Nat) (tac : Ix.Syntax) : TacticM Unit :=
  withMainGoalContext (some tac) fun gId gDecl gTy => do
    match ← liftM (matchEqType? fuel gTy) with
    | some (u, alpha, lhs, rhs) =>
      let optMid := Syntax.getArg tac 1
      let (midExpr, midGoals) ←
        match Syntax.getOptional? optMid with
        | some midStx =>
          let m ← liftM (elabRec midStx (some alpha))
          pure (m, [])
        | none =>
          let m ← liftM (mkFreshExprMVar alpha (Name.simple "mid"))
          let mId := match m with | .mvar id _ => [id] | _ => []
          pure (m, mId)
      let eqConst := Expr.mkConst (Name.simple "Eq") #[u]
      let g1Ty := Expr.mkAppN eqConst #[alpha, lhs, midExpr]
      let g2Ty := Expr.mkAppN eqConst #[alpha, midExpr, rhs]
      let g1MVar ← liftM (mkFreshExprMVar g1Ty gDecl.userName)
      let g2MVar ← liftM (mkFreshExprMVar g2Ty gDecl.userName)
      let g1Id := match g1MVar with | .mvar id _ => id | _ => gId
      let g2Id := match g2MVar with | .mvar id _ => id | _ => gId
      let proof := mkEqTransExpr u alpha lhs midExpr rhs g1MVar g2MVar
      liftM (modifyMCtx (·.assignExpr gId proof))
      replaceMainGoal ([g1Id, g2Id] ++ midGoals)
    | none =>
      liftM (throwElabError "'trans' tactic requires an equality goal" (some tac))

/-- `congr`: reduce `@Eq.{v} β (f a) (f b)` to `@Eq.{u} α a b` via `@Eq.casesOn`. -/
def evalCongrTactic (fuel : Nat) (tac : Ix.Syntax) : TacticM Unit :=
  withMainGoalContext (some tac) fun gId gDecl gTy => do
    match ← liftM (matchEqType? fuel gTy) with
    | some (v, beta, lhs, rhs) =>
      match stripMData lhs, stripMData rhs with
      | .app f a _, .app g b _ =>
        let fnEq ← liftM (isDefEq fuel f g)
        if !fnEq then
          liftM (throwElabError "'congr' failed: function heads are not definitionally equal" (some tac))
        let aTy ← liftM (inferType fuel a)
        let u ← liftM (ensureSort 32 aTy)
        let subGoalTy := Expr.mkAppN (Expr.mkConst (Name.simple "Eq") #[normalizeLevel u]) #[aTy, a, b]
        let subMVar ← liftM (mkFreshExprMVar subGoalTy gDecl.userName)
        let subId := match subMVar with | .mvar id _ => id | _ => gId
        let proof := mkEqCongrArgExpr (normalizeLevel u) v aTy beta f a b subMVar
        liftM (modifyMCtx (·.assignExpr gId proof))
        replaceMainGoal [subId]
      | _, _ =>
        liftM (throwElabError "'congr' tactic requires an equality between applications 'f a = f b'" (some tac))
    | none =>
      liftM (throwElabError "'congr' tactic requires an equality goal" (some tac))

/-- True if `e` is `.const target _ _`. -/
def isExprConstOf : Ix.Expr → Ix.Name → Bool
  | .const nm _ _, target => nm == target
  | _, _ => false

/-- Append a `LetContract` to `ElabState.localLetContracts` strictly. -/
def pushLocalLetContract (lc : Ixon.LetContract) : IxElabM Unit := fun _ st =>
  match st with
  | ⟨env, mctx, nextId, autoUnivs, letContracts⟩ =>
    .ok ((), ⟨env, mctx, nextId, autoUnivs, letContracts.push lc⟩)

/-- `funext x₁ ...` / `ext x₁ ...`: apply `funext` (if in env) or `Iff.intro` and `intro` binders. -/
def evalExtTactic (fuel : Nat) (tac : Ix.Syntax) : TacticM Unit := do
  let rawIds := (Syntax.getArgs (Syntax.getArg tac 1)).toList
  let ids := if rawIds.isEmpty then [Syntax.mkSimpleIdent (Name.simple "x")] else rawIds
  let rec extStep : List Ix.Syntax → TacticM Unit
    | [] => return ()
    | idStx :: rest =>
      withMainGoalContext (some tac) fun _ _ gTy => do
        let gTyW ← liftM (whnf fuel gTy)
        let (hFn, _) := getAppFnArgs gTyW
        let st ← liftM (get : IxElabM ElabState)
        if isExprConstOf hFn (Name.simple "Iff") then
          let (iffConst, iffTy) ← liftM (mkConstWithFreshMVarLevels (Name.mkStr2 "Iff" "intro"))
          applyExprToMainGoal fuel tac iffConst iffTy
        else if st.env.contains (Name.simple "funext") then
          let (feConst, feTy) ← liftM (mkConstWithFreshMVarLevels (Name.simple "funext"))
          applyExprToMainGoal fuel tac feConst feTy
          let introNode := Syntax.mkNode SyntaxKind.tacticIntro
            #[Syntax.mkSimpleAtom "intro", Syntax.mkNullNode #[idStx]]
          evalIntroTactic fuel introNode
          extStep rest
        else
          liftM (throwElabError "'funext'/'ext' requires 'funext' in environment or an 'Iff' goal" (some tac))
  extStep ids

/-- `have [h] [: T] := v` and `let x [: T] := v` using `DelayedMVarAssign`. -/
def evalHaveOrLetTactic (elabRec : Ix.Syntax → Option Ix.Expr → IxElabM Ix.Expr)
    (fuel : Nat) (tac : Ix.Syntax) (isHave : Bool) : TacticM Unit :=
  withMainGoalContext (some tac) fun gId gDecl gTy => do
    let bId := Syntax.getId (Syntax.getArg tac 1)
    let uName := if Name.isAnonymous bId then Name.simple "this" else bId
    let optTyNode := Syntax.getArg tac 2
    let valStx := Syntax.getArg tac 4
    let expTy? ←
      if Syntax.getNumArgs optTyNode >= 2 then
        let t ← liftM (elabRec (Syntax.getArg optTyNode 1) none)
        let _ ← liftM (ensureSort 32 t)
        pure (some t)
      else
        pure none
    let valExpr ← liftM (elabRec valStx expTy?)
    let valTy ← match expTy? with
      | some t => pure t
      | none   => liftM (inferType fuel valExpr)
    let valTyInst ← liftM (instantiateMVars 32 valTy)
    let valExprInst ← liftM (instantiateMVars 32 valExpr)
    let fvId ← liftM (mkFreshName "_fvar")
    let decl : LocalDecl := {
      fvarId     := fvId
      userName   := uName
      type       := valTyInst
      value?     := some valExprInst
      binderInfo := .default
      contract   := default
      letKind?   := some .value
      nonDep     := isHave
    }
    let lctx' := gDecl.lctx.addDecl decl
    let subMVar ← withReader (fun ctx => { ctx with lctx := lctx' }) do
      liftM (mkFreshExprMVar gTy gDecl.userName)
    let subId := match subMVar with | .mvar id _ => id | _ => gId
    if isHave then
      liftM (pushLocalLetContract { nonDep := true, kind := .value, binder := default })
    liftM (modifyMCtx (·.assignDelayed gId { lctx := lctx', fvars := [fvId], pendingMVar := subId }))
    replaceMainGoal [subId]

/-- `show T` / `change T`: replace main goal type with definitionally equal `T`. -/
def evalChangeOrShowTactic (elabRec : Ix.Syntax → Option Ix.Expr → IxElabM Ix.Expr)
    (fuel : Nat) (tac : Ix.Syntax) : TacticM Unit :=
  withMainGoalContext (some tac) fun gId gDecl gTy => do
    let newTyStx := Syntax.getArg tac 1
    let newTy ← liftM (elabRec newTyStx none)
    let _ ← liftM (ensureSort 32 newTy)
    let ok ← liftM (isDefEq fuel gTy newTy)
    if !ok then
      liftM (throwElabError "'change'/'show' type is not definitionally equal to current goal" (some tac))
    let newTyInst ← liftM (instantiateMVars 32 newTy)
    let subMVar ← liftM (mkFreshExprMVar newTyInst gDecl.userName)
    let subId := match subMVar with | .mvar id _ => id | _ => gId
    liftM (modifyMCtx (·.assignExpr gId subMVar))
    replaceMainGoal [subId]

/-- Single rewrite step `rwRule` (`[←] term`) on either the main goal (`atHyp? = none`)
    or a local hypothesis (`atHyp? = some hypName`). -/
def evalOneRwRule (elabRec : Ix.Syntax → Option Ix.Expr → IxElabM Ix.Expr)
    (fuel : Nat) (ruleStx : Ix.Syntax) (atHyp? : Option Ix.Name) : TacticM Unit :=
  withMainGoalContext (some ruleStx) fun gId gDecl gTy => do
    let symmNode := Syntax.getArg ruleStx 0
    let isSymm := !Syntax.isNone symmNode && !Syntax.isMissing symmNode
    let termStx := Syntax.getArg ruleStx 1
    let rawRuleExpr ← liftM (elabRec termStx none)
    let rawRuleTy ← liftM (inferType fuel rawRuleExpr)
    let (cand, instGoals, resTy) ← liftM (openForallMVars 16 rawRuleExpr rawRuleTy [])
    let some (uEqRaw, alphaRaw, lhsRaw, rhsRaw) ← liftM (matchEqType? fuel resTy)
      | liftM (throwElabError "'rw' rule must be an equality (or quantification over an equality)" (some ruleStx))
    let patRaw := if isSymm then rhsRaw else lhsRaw
    let repRaw := if isSymm then lhsRaw else rhsRaw

    match atHyp? with
    | none =>
      -- Rewrite in the main goal `gTy`
      let (found, absGoalRaw) ← liftM (kabstract fuel patRaw gTy)
      if !found then
        liftM (throwElabError "'rw' tactic failed: did not find instance of pattern in target" (some ruleStx))
      for ig in instGoals do
        let igTy ← liftM (inferType fuel ig)
        if let some iv ← liftM (synthInstance? 8 igTy) then
          let _ ← liftM (isDefEq fuel ig iv)
      let uEq ← liftM (instantiateLevelMVars 32 uEqRaw)
      let alpha ← liftM (instantiateMVars 32 alphaRaw)
      let pat ← liftM (instantiateMVars 32 patRaw)
      let rep ← liftM (instantiateMVars 32 repRaw)
      let candInst ← liftM (instantiateMVars 32 cand)
      let absGoal ← liftM (instantiateMVars 32 absGoalRaw)
      let newGoalTy := instantiate1 absGoal rep
      let uGoal ← liftM (ensureSort 32 gTy)
      -- We need a proof of `P(pat)` (`gTy`) from `?newGoal : P(rep)`, so we transport along `rep = pat`!
      let eqRepToPat :=
        if isSymm then
          -- `candInst : lhs = rhs`, which is `rep = pat`!
          candInst
        else
          -- `candInst : pat = rep`, so invert via `mkEqSymmExpr` to get `rep = pat`!
          mkEqSymmExpr (normalizeLevel uEq) alpha pat rep candInst
      let subMVar ← liftM (mkFreshExprMVar newGoalTy gDecl.userName)
      let subId := match subMVar with | .mvar id _ => id | _ => gId
      let transportedProof :=
        mkEqTransportExpr (normalizeLevel uEq) (normalizeLevel uGoal) alpha rep pat absGoal eqRepToPat subMVar
      liftM (modifyMCtx (·.assignExpr gId transportedProof))
      replaceMainGoal [subId]
    | some hypName =>
      -- Rewrite in local hypothesis `hypName`
      let some hypDecl := gDecl.lctx.findUserName? hypName
        | liftM (throwElabError s!"unknown local hypothesis '{Name.toStringTotal hypName}' in 'rw ... at'" (some ruleStx))
      let hypTy ← liftM (instantiateMVars 32 hypDecl.type)
      let (found, absHypRaw) ← liftM (kabstract fuel patRaw hypTy)
      if !found then
        liftM (throwElabError s!"'rw' failed: pattern not found in hypothesis '{Name.toStringTotal hypName}'" (some ruleStx))
      for ig in instGoals do
        let igTy ← liftM (inferType fuel ig)
        if let some iv ← liftM (synthInstance? 8 igTy) then
          let _ ← liftM (isDefEq fuel ig iv)
      let uEq ← liftM (instantiateLevelMVars 32 uEqRaw)
      let alpha ← liftM (instantiateMVars 32 alphaRaw)
      let pat ← liftM (instantiateMVars 32 patRaw)
      let rep ← liftM (instantiateMVars 32 repRaw)
      let candInst ← liftM (instantiateMVars 32 cand)
      let absHyp ← liftM (instantiateMVars 32 absHypRaw)
      let newHypTy := instantiate1 absHyp rep
      let uHyp ← liftM (ensureSort 32 hypTy)
      let eqPatToRep :=
        if isSymm then
          mkEqSymmExpr (normalizeLevel uEq) alpha rep pat candInst
        else
          candInst
      let newHypVal :=
        mkEqTransportExpr (normalizeLevel uEq) (normalizeLevel uHyp) alpha pat rep absHyp eqPatToRep (Expr.mkFVar hypDecl.fvarId)
      let newFvId ← liftM (mkFreshName "_fvar")
      let newDecl : LocalDecl := {
        fvarId   := newFvId
        userName := hypName
        type     := newHypTy
        value?   := some newHypVal
        letKind? := some .value
        nonDep   := true
      }
      let lctx' := gDecl.lctx.addDecl newDecl
      liftM (pushLocalLetContract { nonDep := true, kind := .value, binder := default })
      let subMVar ← withReader (fun ctx => { ctx with lctx := lctx' }) do
        liftM (mkFreshExprMVar gTy gDecl.userName)
      let subId := match subMVar with | .mvar id _ => id | _ => gId
      liftM (modifyMCtx (·.assignDelayed gId { lctx := lctx', fvars := [newFvId], pendingMVar := subId }))
      replaceMainGoal [subId]

/-- `rw [rule₁, ...] [at hyp]`: apply each rewrite rule sequentially, then try `rfl` on the goal. -/
def evalRwTactic (elabRec : Ix.Syntax → Option Ix.Expr → IxElabM Ix.Expr)
    (fuel : Nat) (tac : Ix.Syntax) : TacticM Unit := do
  let rules := (Syntax.getArgs (Syntax.getArg tac 2)).toList
  let optAt := Syntax.getArg tac 4
  let atHyp? : Option Ix.Name :=
    if Syntax.getNumArgs optAt >= 2 then
      some (Syntax.getId (Syntax.getArg optAt 1))
    else
      none
  let rec loop : List Ix.Syntax → TacticM Unit
    | [] => return ()
    | r :: rs => do
      evalOneRwRule elabRec fuel r atHyp?
      loop rs
  loop rules
  if atHyp?.isNone then
    let _ ← tryTactic? (evalRflTactic fuel tac)

/-- `dsimp [[...]] [at hyp]` and `simp [[...]] [at hyp]`. -/
def evalSimpOrDSimpTactic (elabRec : Ix.Syntax → Option Ix.Expr → IxElabM Ix.Expr)
    (fuel : Nat) (tac : Ix.Syntax) (isFullSimp : Bool) : TacticM Unit := do
  let optRulesNode := Syntax.getArg tac 1
  let optAtNode    := Syntax.getArg tac 2
  let extraRules : List Ix.Syntax :=
    if Syntax.getNumArgs optRulesNode >= 2 then
      (Syntax.getArgs (Syntax.getArg optRulesNode 1)).toList
    else
      []
  let atHyp? : Option Ix.Name :=
    if Syntax.getNumArgs optAtNode >= 2 then
      some (Syntax.getId (Syntax.getArg optAtNode 1))
    else
      none
  -- Step 1: Definitional simplification (`dsimpExpr`)
  withMainGoalContext (some tac) fun gId gDecl gTy => do
    match atHyp? with
    | none =>
      let gTySimp ← liftM (dsimpExpr fuel 32 gTy)
      if gTySimp != gTy then
        let subMVar ← liftM (mkFreshExprMVar gTySimp gDecl.userName)
        let subId := match subMVar with | .mvar id _ => id | _ => gId
        liftM (modifyMCtx (·.assignExpr gId subMVar))
        replaceMainGoal [subId]
    | some hypName =>
      let some hypDecl := gDecl.lctx.findUserName? hypName
        | liftM (throwElabError s!"unknown hypothesis '{Name.toStringTotal hypName}' in 'simp/dsimp at'" (some tac))
      let hypTy ← liftM (instantiateMVars 32 hypDecl.type)
      let hypTySimp ← liftM (dsimpExpr fuel 32 hypTy)
      if hypTySimp != hypTy then
        let newFvId ← liftM (mkFreshName "_fvar")
        let newDecl : LocalDecl := {
          fvarId   := newFvId
          userName := hypName
          type     := hypTySimp
          value?   := some (Expr.mkFVar hypDecl.fvarId)
          letKind? := some .value
          nonDep   := true
        }
        let lctx' := gDecl.lctx.addDecl newDecl
        liftM (pushLocalLetContract { nonDep := true, kind := .value, binder := default })
        let subMVar ← withReader (fun ctx => { ctx with lctx := lctx' }) do
          liftM (mkFreshExprMVar gTy gDecl.userName)
        let subId := match subMVar with | .mvar id _ => id | _ => gId
        liftM (modifyMCtx (·.assignDelayed gId { lctx := lctx', fvars := [newFvId], pendingMVar := subId }))
        replaceMainGoal [subId]
  -- Step 2: If `simp [r₁, ...]`, repeatedly apply equational rewrites from `extraRules`
  if isFullSimp && !extraRules.isEmpty then
    let rwRules := extraRules.map fun tStx =>
      Syntax.mkNode SyntaxKind.tacticRwRule #[Syntax.mkNullNode #[], tStx]
    let rec simpRwLoop : Nat → TacticM Unit
      | 0 => return ()
      | k + 1 => do
        let mut anyProgress := false
        for rStx in rwRules do
          if (← tryTactic? (evalOneRwRule elabRec fuel rStx atHyp?)).isSome then
            anyProgress := true
        if anyProgress then simpRwLoop k else return ()
    simpRwLoop 8
  -- Step 3: Try closing goal if `atHyp?.isNone`
  if atHyp?.isNone then
    let _ ← tryTactic? (evalTrivialTactic fuel tac)

/-! ## `cases` and `induction` via `<Ind>.casesOn` / `<Ind>.recOn` -/

/-- Execute `cases` or `induction` (both unstructured and `with | tag xs => seq`),
    parameterized by `evalSeqRec` for structured branch sequences. -/
def evalCasesOrInductionTactic
    (elabRec : Ix.Syntax → Option Ix.Expr → IxElabM Ix.Expr)
    (evalSeqRec : Ix.Syntax → TacticM Unit)
    (fuel : Nat) (tac : Ix.Syntax) (isInd : Bool) : TacticM Unit :=
  withMainGoalContext (some tac) fun gId _ gTy => do
    let targetStx := Syntax.getArg tac 1
    let optWith := Syntax.getArg tac 2
    let alts : Array Ix.Syntax :=
      if Syntax.getNumArgs optWith >= 2 then
        Syntax.getArgs (Syntax.getArg optWith 1)
      else
        #[]
    let targetExpr ← liftM (elabRec targetStx none)
    let targetTyRaw ← liftM (inferType fuel targetExpr)
    let targetTy ← liftM (instantiateMVars 32 targetTyRaw)
    let targetTyW ← liftM (whnf fuel targetTy)
    let (hFn, headArgs) := getAppFnArgs targetTyW
    let st ← liftM (get : IxElabM ElabState)
    match hFn with
    | .const indName indUnivs _ =>
      match st.env.find? indName with
      | some (.inductInfo ival) =>
        let prefSuffix := if isInd then "recOn" else "casesOn"
        let prefName := Name.mkStr indName prefSuffix
        let elimName :=
          if st.env.contains prefName then prefName
          else Name.mkStr indName "recOn"
        match st.env.find? elimName with
        | some (.defnInfo elimDef) =>
          let elimUnivs ←
            if elimDef.cnst.levelParams.size == indUnivs.size + 1 then
              let uMot ← liftM (ensureSort 32 gTy)
              pure (#[normalizeLevel uMot] ++ indUnivs)
            else
              pure indUnivs
          let params := headArgs.extract 0 ival.numParams
          let indices := headArgs.extract ival.numParams headArgs.size
          -- Build motive `λ (i₁ : Idx₁) ... (x : I params indices) => P(i₁, ..., x)`
          let afterParamsInst := params.foldl (fun cur p =>
            match stripMData cur with
            | .forallE _ _ b _ _ => instantiate1 b p
            | other => other) (substExprLevelParams ival.cnst.levelParams indUnivs ival.cnst.type)
          let (idxFVars, idxDecls, _) := openForallTelescope ival.numIndices afterParamsInst "midx" 0 #[] #[]
          let majDom := Expr.mkAppN (Expr.mkConst indName indUnivs) (params ++ idxFVars)
          let (majFvId, majFvExpr) := mkAuxFVar "mmaj" 0
          let majDecl : AuxLocalDecl := { fvarId := majFvId, binderName := Name.simple "x", domain := majDom }
          -- Generalize `targetExpr` (and any FVar indices) in `gTy`
          let motiveBody ← match stripMData targetExpr with
            | .fvar targetFvId _ =>
              let b0 := instantiate1 (abstractFVar targetFvId gTy) majFvExpr
              let b1 := (indices.zipIdx).foldl (fun acc (idxE, k) =>
                match stripMData idxE, idxFVars[k]? with
                | .fvar iFv _, some repFv =>
                  if iFv != targetFvId then instantiate1 (abstractFVar iFv acc) repFv else acc
                | _, _ => acc) b0
              pure b1
            | _ =>
              let (_, absG) ← liftM (kabstract fuel targetExpr gTy)
              pure (instantiate1 absG majFvExpr)
          let motiveLam := closeLambdas (idxDecls.push majDecl) motiveBody

          let rawElimTy := substExprLevelParams elimDef.cnst.levelParams elimUnivs elimDef.cnst.type
          let prefixArgs := params ++ #[motiveLam] ++ indices ++ #[targetExpr]
          let minorBinderCounts := extractMinorBinderCounts prefixArgs.size ival.ctors.size rawElimTy
          let minorsTelTy := prefixArgs.foldl (fun cur arg =>
            match stripMData cur with
            | .forallE _ _ b _ _ => instantiate1 b arg
            | other => other) rawElimTy

          -- Open each constructor's minor premise in canonical `ival.ctors` order
          let mut curTel := minorsTelTy
          let mut minorLams : Array Ix.Expr := #[]
          let mut branchSubGoals : Array (Ix.Name × Ix.Name × Option Ix.Syntax) := #[]
          for (ctorName, cIdx) in ival.ctors.zipIdx do
            let minorDom ← match stripMData curTel with
              | .forallE _ d b _ _ =>
                curTel := b
                pure (betaReduceExpr d)
              | _ =>
                liftM (throwElabError s!"unexpected eliminator type in '{Name.toStringTotal elimName}'" (some tac))
            let numBinders := minorBinderCounts.getD cIdx 0
            -- Check if user supplied a `| tag xs => seq` branch matching `ctorName`
            let matchedAlt? := alts.findSome? fun altStx =>
              let tagId := Syntax.getId (Syntax.getArg altStx 1)
              if matchesCtorTag ctorName tagId then
                let bIds := (Syntax.getArgs (Syntax.getArg altStx 2)).map Syntax.getId
                let seqStx := Syntax.getArg altStx 4
                some (bIds, seqStx)
              else
                none
            if !alts.isEmpty && matchedAlt?.isNone then
              liftM (throwElabError s!"non-exhaustive '{if isInd then "induction" else "cases"}': missing branch for constructor '{Name.toStringTotal ctorName}'" (some tac))
            let userBinderNames : Array Ix.Name := match matchedAlt? with
              | some (bIds, _) => bIds
              | none           => #[]
            let finishMinorSubGoal (curTy : Ix.Expr) (revFVars : List Ix.Name) :
                IxElabM (Ix.Name × Ix.Expr) := do
              let subMVar ← mkFreshExprMVar curTy ctorName
              let subId := match subMVar with | .mvar id _ => id | _ => gId
              if revFVars.isEmpty then
                return (subId, subMVar)
              else
                let ctx ← read
                let outerMVar ← mkFreshExprMVar minorDom ctorName
                let outerId := match outerMVar with | .mvar id _ => id | _ => gId
                modifyMCtx (·.assignDelayed outerId {
                  lctx        := ctx.lctx
                  fvars       := revFVars.reverse
                  pendingMVar := subId
                })
                return (subId, outerMVar)
            let rec openMinorBinders (rem : Nat) (curTy : Ix.Expr) (bIdx : Nat)
                (revFVars : List Ix.Name) : IxElabM (Ix.Name × Ix.Expr) := do
              match rem with
              | 0 =>
                finishMinorSubGoal curTy revFVars
              | rem' + 1 =>
                let curW ← match stripMData curTy with
                  | .forallE _ _ _ _ _ => pure curTy
                  | _                  => whnf fuel curTy
                match stripMData curW with
                | .forallE defNm fDom fBody bi _ =>
                  let uName :=
                    let un := userBinderNames.getD bIdx Name.mkAnon
                    if Name.isAnonymous un then defNm else un
                  withLocalDecl uName fDom bi default fun fvId fvExpr =>
                    openMinorBinders rem' (instantiate1 fBody fvExpr) (bIdx + 1) (fvId :: revFVars)
                | _ =>
                  finishMinorSubGoal curTy revFVars
            let (subId, minorLam) ← liftM (openMinorBinders numBinders minorDom 0 [])
            minorLams := minorLams.push minorLam
            branchSubGoals := branchSubGoals.push (ctorName, subId, matchedAlt?.map Prod.snd)

          let elimApp := Expr.mkAppN (Expr.mkConst elimName elimUnivs) (prefixArgs ++ minorLams)
          liftM (modifyMCtx (·.assignExpr gId elimApp))
          if alts.isEmpty then
            -- Unstructured `cases e` / `induction e`: push all constructor subgoals onto `TacticState.goals`
            replaceMainGoal (branchSubGoals.toList.map (·.2.1))
          else
            -- Structured `with | tag xs => seq`: remove `gId`, then run each branch in user-written order
            replaceMainGoal []
            let savedRestGoals ← getUnassignedGoals
            for altStx in alts do
              let tagId := Syntax.getId (Syntax.getArg altStx 1)
              let seqStx := Syntax.getArg altStx 4
              match branchSubGoals.find? (fun (cNm, _, _) => matchesCtorTag cNm tagId) with
              | none =>
                liftM (throwElabError s!"unknown constructor branch '{Name.toStringTotal tagId}' for '{Name.toStringTotal indName}'" (some altStx))
              | some (_, subId, _) =>
                setTacticGoals [subId]
                evalSeqRec seqStx
                let remInBranch ← getUnassignedGoals
                if !remInBranch.isEmpty then
                  liftM (throwElabError s!"unsolved goals in branch '{Name.toStringTotal tagId}'" (some altStx))
            setTacticGoals savedRestGoals
        | _ =>
          liftM (throwElabError s!"eliminator '{Name.toStringTotal elimName}' not found" (some tac))
      | _ =>
        liftM (throwElabError s!"'{Name.toStringTotal indName}' is not an inductive type" (some targetStx))
    | _ =>
      liftM (throwElabError "'cases'/'induction' target must have an inductive type" (some targetStx))

/-! ## Main Tactic Evaluator (`evalTactic`, `evalTacticSeq`) -/

/-- Alias the `k` most recently introduced local declarations in `lctx` to `userNames`
    (used when `case tag x₁ ... xₖ =>` focuses a subgoal created by unstructured `cases` / `induction`). -/
def aliasRecentLocalDecls (lctx : LocalContext) (userNames : List Ix.Name) : LocalContext :=
  let recentDecls := (lctx.revDecls.take userNames.length).reverse
  let rec loop : List LocalDecl → List Ix.Name → LocalContext → LocalContext
    | d :: ds, nm :: nms, cur =>
      let cur' :=
        if Name.isAnonymous nm then cur
        else match cur with
          | ⟨rev, byId, byUser⟩ =>
            (byUser.insert nm { d with userName := nm }).bindMap fun byUser' =>
              ⟨rev, byId, byUser'⟩
      loop ds nms cur'
    | _, _, cur => cur
  loop recentDecls userNames lctx

/-- Run a list of tactics sequentially using `evalRec`. -/
def runTacticList (evalRec : Ix.Syntax → TacticM Unit) : List Ix.Syntax → TacticM Unit
  | [] => return ()
  | t :: ts => do
    evalRec t
    runTacticList evalRec ts

/-- Run `rhsTac` on each subgoal in `subGoals`, collecting resulting open goals. -/
def runTacticOnEachGoal (evalRec : Ix.Syntax → TacticM Unit) (rhsTac : Ix.Syntax) :
    List Ix.Name → List Ix.Name → TacticM (List Ix.Name)
  | [], acc => return acc
  | sg :: sgs, acc => do
    setTacticGoals [sg]
    evalRec rhsTac
    let newGs ← getUnassignedGoals
    runTacticOnEachGoal evalRec rhsTac sgs (acc ++ newGs)

/-- Try each branch in `first | seq₁ | seq₂ ...` until one succeeds. -/
def tryFirstTacticBranches (evalRec : Ix.Syntax → TacticM Unit) (refTac : Ix.Syntax) :
    List Ix.Syntax → TacticM Unit
  | [] => liftM (throwElabError "tactic 'first' failed: all branches failed" (some refTac))
  | b :: bs => do
    match ← tryTactic? (evalRec b) with
    | some () => return ()
    | none    => tryFirstTacticBranches evalRec refTac bs

/-- Repeat `innerTac` up to `k` times until it fails or all goals are solved. -/
def repeatTacticLoop (evalRec : Ix.Syntax → TacticM Unit) (innerTac : Ix.Syntax) : Nat → TacticM Unit
  | 0 => return ()
  | k + 1 => do
    let gsBefore ← getUnassignedGoals
    if gsBefore.isEmpty then return ()
    match ← tryTactic? (evalRec innerTac) with
    | some () => repeatTacticLoop evalRec innerTac k
    | none    => return ()

/-- Run `innerTac` on every goal in `any_goals`. -/
def anyGoalsLoop (evalRec : Ix.Syntax → TacticM Unit) (innerTac : Ix.Syntax) :
    List Ix.Name → Bool → List Ix.Name → TacticM (Bool × List Ix.Name)
  | [], anyOk, acc => return (anyOk, acc)
  | g :: gs, anyOk, acc => do
    setTacticGoals [g]
    match ← tryTactic? (evalRec innerTac) with
    | some () =>
      let newGs ← getUnassignedGoals
      anyGoalsLoop evalRec innerTac gs true (acc ++ newGs)
    | none =>
      anyGoalsLoop evalRec innerTac gs anyOk (acc ++ [g])

/-- Evaluate a tactic syntax node (single tactic, combinator, or `tacticSeq`),
    structurally recursive on `tacFuel : Nat`. -/
def evalTactic (elabRec : Ix.Syntax → Option Ix.Expr → IxElabM Ix.Expr) (fuel : Nat) :
    Nat → Ix.Syntax → TacticM Unit
  | 0, stx => liftM (throwElabError "tactic fuel exhausted" (some stx))
  | tacFuel + 1, tac => do
    let evalRec (s : Ix.Syntax) : TacticM Unit := evalTactic elabRec fuel tacFuel s
    let tk := Syntax.getKind tac
    -- 1. `tacticSeq`: sequential execution `tac₁; tac₂; ...`
    if tk == SyntaxKind.tacticSeq then
      runTacticList evalRec (Syntax.getArgs tac).toList
    -- 2. `( tacSeq )`
    else if tk == SyntaxKind.tacticParen then
      evalRec (Syntax.getArg tac 1)
    -- 3. `tac₁ <;> tac₂` (`tacticAndThen`)
    else if tk == SyntaxKind.tacticAndThen then
      let lhsTac := Syntax.getArg tac 0
      let rhsTac := Syntax.getArg tac 2
      let (gId, _, _) ← getMainGoal (some tac)
      let allGs ← getUnassignedGoals
      let restGoals := allGs.drop 1
      setTacticGoals [gId]
      evalRec lhsTac
      let subGoals ← getUnassignedGoals
      let resultingSubGoals ← runTacticOnEachGoal evalRec rhsTac subGoals []
      setTacticGoals (resultingSubGoals ++ restGoals)
    -- 4. `· tacSeq` (`tacticFocus`)
    else if tk == SyntaxKind.tacticFocus then
      let subSeq := Syntax.getArg tac 1
      let (gId, _, _) ← getMainGoal (some tac)
      let allGs ← getUnassignedGoals
      let restGoals := allGs.drop 1
      setTacticGoals [gId]
      evalRec subSeq
      let rem ← getUnassignedGoals
      if !rem.isEmpty then
        liftM (throwElabError "focused tactic block '·' left unsolved goals" (some tac))
      setTacticGoals restGoals
    -- 5. `case tag x₁ ... xₙ => tacSeq` (`tacticCase`)
    else if tk == SyntaxKind.tacticCase then
      let tagId := Syntax.getId (Syntax.getArg tac 1)
      let bIds := (Syntax.getArgs (Syntax.getArg tac 2)).toList.map Syntax.getId
      let subSeq := Syntax.getArg tac 4
      let allGs ← getUnassignedGoals
      let eSt ← liftM (get : IxElabM ElabState)
      let matchedGoal? := allGs.find? fun gId =>
        match eSt.mctx.findDecl? gId with
        | some d => matchesCtorTag d.userName tagId
        | none   => false
      let targetGId ← match matchedGoal?, allGs with
        | some gId, _ => pure gId
        | none, gId :: _ => pure gId
        | none, [] => liftM (throwElabError s!"no goal matching case '{Name.toStringTotal tagId}'" (some tac))
      let otherGoals := allGs.filter (· != targetGId)
      if !bIds.isEmpty then
        if let some d := eSt.mctx.findDecl? targetGId then
          let lctxAliased := aliasRecentLocalDecls d.lctx bIds
          liftM (modifyMCtx (·.addExprMVarDecl { d with lctx := lctxAliased }))
      setTacticGoals [targetGId]
      evalRec subSeq
      let rem ← getUnassignedGoals
      if !rem.isEmpty then
        liftM (throwElabError s!"'case {Name.toStringTotal tagId}' left unsolved goals" (some tac))
      setTacticGoals otherGoals
    -- 6. `first | seq₁ | seq₂ ...` (`tacticFirst`)
    else if tk == SyntaxKind.tacticFirst then
      let branches := (Syntax.getArgs (Syntax.getArg tac 1)).toList
      tryFirstTacticBranches evalRec tac branches
    -- 7. `try tac` (`tacticTry`)
    else if tk == SyntaxKind.tacticTry then
      let _ ← tryTactic? (evalRec (Syntax.getArg tac 1))
    -- 8. `repeat tac` (`tacticRepeat`)
    else if tk == SyntaxKind.tacticRepeat then
      repeatTacticLoop evalRec (Syntax.getArg tac 1) 32
    -- 9. `all_goals tac` (`tacticAllGoals`)
    else if tk == SyntaxKind.tacticAllGoals then
      let innerTac := Syntax.getArg tac 1
      let allGs ← getUnassignedGoals
      let resGs ← runTacticOnEachGoal evalRec innerTac allGs []
      setTacticGoals resGs
    -- 10. `any_goals tac` (`tacticAnyGoals`)
    else if tk == SyntaxKind.tacticAnyGoals then
      let innerTac := Syntax.getArg tac 1
      let allGs ← getUnassignedGoals
      let (anyOk, resGs) ← anyGoalsLoop evalRec innerTac allGs false []
      if !anyOk then
        liftM (throwElabError "'any_goals' failed on all goals" (some tac))
      setTacticGoals resGs
    -- 11. Atomic tactics
    else if tk == SyntaxKind.tacticIntro then
      evalIntroTactic fuel tac
    else if tk == SyntaxKind.tacticExact then
      withMainGoalContext (some tac) fun gId _ gTy => do
        let termStx := Syntax.getArg tac 1
        let val ← liftM (elabRec termStx (some gTy))
        let valInst ← liftM (instantiateMVars 32 val)
        liftM (modifyMCtx (·.assignExpr gId valInst))
        replaceMainGoal []
    else if tk == SyntaxKind.tacticRefine then
      withMainGoalContext (some tac) fun gId _ gTy => do
        let termStx := Syntax.getArg tac 1
        let val ← liftM (elabRec termStx (some gTy))
        let valInst ← liftM (instantiateMVars 32 val)
        let stNow ← liftM (get : IxElabM ElabState)
        let newGoals := collectUnassignedMVarIds stNow.mctx valInst
        liftM (modifyMCtx (·.assignExpr gId valInst))
        replaceMainGoal newGoals
    else if tk == SyntaxKind.tacticApply then
      withMainGoalContext (some tac) fun _ _ _ => do
        let termStx := Syntax.getArg tac 1
        let fnExpr ← liftM (elabRec termStx none)
        let fnTy ← liftM (inferType fuel fnExpr)
        applyExprToMainGoal fuel tac fnExpr fnTy
    else if tk == SyntaxKind.tacticRfl || tk == SyntaxKind.tacticDecide then
      evalRflTactic fuel tac
    else if tk == SyntaxKind.tacticAssumption then
      evalAssumptionTactic fuel tac
    else if tk == SyntaxKind.tacticTrivial then
      evalTrivialTactic fuel tac
    else if tk == SyntaxKind.tacticContradiction then
      evalContradictionTactic fuel tac
    else if tk == SyntaxKind.tacticExfalso then
      evalExfalsoTactic tac
    else if tk == SyntaxKind.tacticDone then
      let gs ← getUnassignedGoals
      if !gs.isEmpty then
        liftM (throwElabError "tactic 'done' failed: unsolved goals remain" (some tac))
    else if tk == SyntaxKind.tacticConstructor || tk == SyntaxKind.tacticSplit then
      evalCtorSelectTactic fuel tac "constructor"
    else if tk == SyntaxKind.tacticLeft then
      evalCtorSelectTactic fuel tac "left"
    else if tk == SyntaxKind.tacticRight then
      evalCtorSelectTactic fuel tac "right"
    else if tk == SyntaxKind.tacticExists then
      evalExistsTactic elabRec fuel tac
    else if tk == SyntaxKind.tacticSymm then
      evalSymmTactic fuel tac
    else if tk == SyntaxKind.tacticTrans then
      evalTransTactic elabRec fuel tac
    else if tk == SyntaxKind.tacticCongr then
      evalCongrTactic fuel tac
    else if tk == SyntaxKind.tacticFunext || tk == SyntaxKind.tacticExt then
      evalExtTactic fuel tac
    else if tk == SyntaxKind.tacticHave then
      evalHaveOrLetTactic elabRec fuel tac true
    else if tk == SyntaxKind.tacticLet then
      evalHaveOrLetTactic elabRec fuel tac false
    else if tk == SyntaxKind.tacticChange || tk == SyntaxKind.tacticShow then
      evalChangeOrShowTactic elabRec fuel tac
    else if tk == SyntaxKind.tacticRw then
      evalRwTactic elabRec fuel tac
    else if tk == SyntaxKind.tacticDSimp then
      evalSimpOrDSimpTactic elabRec fuel tac false
    else if tk == SyntaxKind.tacticSimp then
      evalSimpOrDSimpTactic elabRec fuel tac true
    else if tk == SyntaxKind.tacticCases then
      evalCasesOrInductionTactic elabRec evalRec fuel tac false
    else if tk == SyntaxKind.tacticInduction then
      evalCasesOrInductionTactic elabRec evalRec fuel tac true
    else if tk == SyntaxKind.tacticSorry then
      withMainGoalContext (some tac) fun _ _ gTy => do
        let st ← liftM (get : IxElabM ElabState)
        if st.env.contains (Name.simple "sorryAx") then
          let (sConst, sTy) ← liftM (mkConstWithFreshMVarLevels (Name.simple "sorryAx"))
          let (cand, _, resTy) ← liftM (openForallMVars 8 sConst sTy [])
          let _ ← liftM (isDefEq fuel resTy gTy)
          closeMainGoal cand (some tac)
        else
          liftM (throwElabError "'sorry' tactic used without 'sorryAx' in environment" (some tac))
    else
      liftM (throwElabError s!"unsupported tactic '{Name.toStringTotal tk}'" (some tac))

/-- Entry point for elaborating a `by ...` tactic sequence on `rootGoalId`. -/
def evalTacticSeq (elabRec : Ix.Syntax → Option Ix.Expr → IxElabM Ix.Expr)
    (fuel : Nat) (tacSeq : Ix.Syntax) (rootGoalId : Ix.Name) : IxElabM Unit := do
  let (_, finalState) ← (evalTactic elabRec fuel 64 tacSeq).run { goals := [rootGoalId] }
  let eSt ← get
  let remaining := finalState.goals.filter fun gId => !eSt.mctx.isExprAssigned gId
  if !remaining.isEmpty then
    throwElabError s!"unsolved tactic goals ({remaining.length} remaining)" (some tacSeq)

end Ix.Frontend.Elab
