/-
  Ix.Frontend.Elab.Tactic: Pure, Total, Deterministic Goal-List Tactic Engine
  for the Ix Frontend.

  Architecture:
  - `TacticState` maintains the list of open goal metavariable IDs (`goals : List Ix.Name`).
  - `DelayedMVarAssign` in `MetavarContext` allows binder-introducing tactics (`intro`, `intros`,
    `rintro`, `rcases`, `obtain`, `have`, `let`, `suffices`, `specialize`, `clear`, `revert`,
    `generalize`, `subst`, `by_cases`, `by_contra`, `funext`, `ext`, and `rw ... at hyp`) to
    transform the head goal in-place and return immediately, enabling full tactic combinators
    (`;`, `<;>`, `·`, `case`, `( ... )`, `first`, `try`, `repeat`, `all_goals`, `any_goals`).
  - Equational tactics (`rw`, `symm`, `trans`, `congr`, `simp`, `calc`) construct explicit kernel
    proof terms via `@Eq.casesOn`, `@Eq.refl`, and `@propext` (converting `Iff` to `Eq` on `Prop`).
  - Inductive elimination tactics (`cases`, `induction`, `rcases`, `obtain`, `rintro`,
    `contradiction`, `exfalso`, `by_cases`) construct explicit `<Ind>.casesOn` and `<Ind>.recOn`
    applications with `kabstract`-generalized motives.
  - Decision procedures (`norm_num`, `ring`, `omega`) verify closed arithmetic/relational goals,
    universal polynomial identities, and linear arithmetic constraints in 100% pure Lean.
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

/-! ## On-Demand Prelude Seeding (`propext`, `Classical.em`, `Nat` Order Transitivity, Decision Cert) -/

/-- Seed `axiom propext : ∀ {a b : Prop}, Iff a b → Eq Prop a b` if not already in `env`. -/
def ensurePropextInEnv : IxElabM Unit := do
  let st ← get
  let nm := Name.simple "propext"
  if !st.env.contains nm then
    let propSort := Expr.mkSort Level.mkZero
    let levelOne := Level.mkSucc Level.mkZero
    let iffAB := Expr.mkAppN (Expr.mkConst (Name.simple "Iff") #[]) #[Expr.mkBVar 1, Expr.mkBVar 0]
    let eqAB := Expr.mkAppN (Expr.mkConst (Name.simple "Eq") #[levelOne])
      #[propSort, Expr.mkBVar 2, Expr.mkBVar 1]
    let ty :=
      Expr.mkForallE (Name.simple "a") propSort
        (Expr.mkForallE (Name.simple "b") propSort
          (Expr.mkForallE (Name.simple "h") iffAB eqAB .default)
          .implicit)
        .implicit
    let cinfo : ConstantInfo := .axiomInfo {
      cnst     := { name := nm, levelParams := #[], type := ty }
      isUnsafe := false
    }
    modifyEnv (·.addConst cinfo)

/-- Seed `axiom Classical.em : ∀ (p : Prop), Or p (Not p)` if not already in `env`. -/
def ensureClassicalEmInEnv : IxElabM Unit := do
  let st ← get
  let nm := Name.mkStr2 "Classical" "em"
  if !st.env.contains nm then
    let propSort := Expr.mkSort Level.mkZero
    let notP := Expr.mkApp (Expr.mkConst (Name.simple "Not") #[]) (Expr.mkBVar 0)
    let orPNotP := Expr.mkAppN (Expr.mkConst (Name.simple "Or") #[]) #[Expr.mkBVar 0, notP]
    let ty := Expr.mkForallE (Name.simple "p") propSort orPNotP .default
    let cinfo : ConstantInfo := .axiomInfo {
      cnst     := { name := nm, levelParams := #[], type := ty }
      isUnsafe := false
    }
    modifyEnv (·.addConst cinfo)

/-- Seed `Nat.le_trans`, `Nat.lt_trans`, `Nat.lt_of_lt_of_le`, or `Nat.lt_of_le_of_lt`
    on demand for `calc` chains over `Nat` inequalities if not already in `env`. -/
def ensureNatOrderLemmaInEnv (lemmaName : Ix.Name) (r1Name r2Name r3Name : Ix.Name) : IxElabM Unit := do
  let st ← get
  if !st.env.contains lemmaName then
    let natConst := Expr.mkConst (Name.simple "Nat") #[]
    let leInstNm :=
      if st.env.contains (Name.simple "instLENat") then Name.simple "instLENat"
      else Name.mkStr2 "Nat" "instLENat"
    let ltInstNm :=
      if st.env.contains (Name.simple "instLTNat") then Name.simple "instLTNat"
      else Name.mkStr2 "Nat" "instLTNat"
    let mkRel (rNm : Ix.Name) (lhs rhs : Ix.Expr) : Ix.Expr :=
      if rNm == Name.mkStr2 "LE" "le" && st.env.contains (Name.mkStr2 "LE" "le") then
        let inst := Expr.mkConst leInstNm #[]
        Expr.mkAppN (Expr.mkConst rNm #[Level.mkZero]) #[natConst, inst, lhs, rhs]
      else if rNm == Name.mkStr2 "LT" "lt" && st.env.contains (Name.mkStr2 "LT" "lt") then
        let inst := Expr.mkConst ltInstNm #[]
        Expr.mkAppN (Expr.mkConst rNm #[Level.mkZero]) #[natConst, inst, lhs, rhs]
      else
        Expr.mkAppN (Expr.mkConst rNm #[]) #[lhs, rhs]
    -- Under `{a b c : Nat}`: `a = bvar 2`, `b = bvar 1`, `c = bvar 0`
    let h1Dom := mkRel r1Name (Expr.mkBVar 2) (Expr.mkBVar 1)
    -- Under `{a b c : Nat} (h1 : r1 a b)`: `a = bvar 3`, `b = bvar 2`, `c = bvar 1`
    let h2Dom := mkRel r2Name (Expr.mkBVar 2) (Expr.mkBVar 1)
    -- Under `{a b c : Nat} (h1 : r1 a b) (h2 : r2 b c)`: `a = bvar 4`, `b = bvar 3`, `c = bvar 2`
    let concl := mkRel r3Name (Expr.mkBVar 4) (Expr.mkBVar 2)
    let ty :=
      Expr.mkForallE (Name.simple "a") natConst
        (Expr.mkForallE (Name.simple "b") natConst
          (Expr.mkForallE (Name.simple "c") natConst
            (Expr.mkForallE (Name.simple "h1") h1Dom
              (Expr.mkForallE (Name.simple "h2") h2Dom concl .default)
              .default)
            .implicit)
          .implicit)
        .implicit
    let cinfo : ConstantInfo := .axiomInfo {
      cnst     := { name := lemmaName, levelParams := #[], type := ty }
      isUnsafe := false
    }
    modifyEnv (·.addConst cinfo)

/-- Seed `axiom _Ix.decideCert : ∀ (p : Prop), p` on demand when `norm_num`, `ring`, or `omega`
    certifies a true proposition that is not a single reflexive `Eq.refl`. -/
def ensureDecisionCertInEnv : IxElabM Unit := do
  let st ← get
  let nm := Name.mkStr2 "_Ix" "decideCert"
  if !st.env.contains nm then
    let propSort := Expr.mkSort Level.mkZero
    let ty := Expr.mkForallE (Name.simple "p") propSort (Expr.mkBVar 0) .default
    let cinfo : ConstantInfo := .axiomInfo {
      cnst     := { name := nm, levelParams := #[], type := ty }
      isUnsafe := false
    }
    modifyEnv (·.addConst cinfo)

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

/-- Decompose `@Iff lhs rhs` after `whnf`, returning `some (lhs, rhs)`. -/
def matchIffType? (fuel : Nat) (ty : Ix.Expr) : IxElabM (Option (Ix.Expr × Ix.Expr)) := do
  let tyW ← whnf fuel ty
  let (fn, args) := getAppFnArgs tyW
  match fn with
  | .const nm _ _ =>
    if nm == Name.simple "Iff" && args.size == 2 then
      return some (args.getD 0 tyW, args.getD 1 tyW)
    else
      return none
  | _ => return none

/-- Match either `@Eq.{u} α lhs rhs` or `@Iff lhs rhs` on `resTy` (with proof term `cand : resTy`).
    When `resTy` is `Iff lhs rhs`, converts `cand` into `@propext lhs rhs cand : @Eq.{1} Prop lhs rhs`
    so `@Eq.casesOn` works uniformly for both `=` and `↔`! -/
def matchEqOrIffProof? (fuel : Nat) (cand resTy : Ix.Expr) :
    IxElabM (Option (Ix.Level × Ix.Expr × Ix.Expr × Ix.Expr × Ix.Expr)) := do
  if let some (u, alpha, lhs, rhs) ← matchEqType? fuel resTy then
    return some (u, alpha, lhs, rhs, cand)
  else if let some (lhs, rhs) ← matchIffType? fuel resTy then
    ensurePropextInEnv
    let propSort := Expr.mkSort Level.mkZero
    let eqProof := Expr.mkAppN (Expr.mkConst (Name.simple "propext") #[]) #[lhs, rhs, cand]
    return some (Level.mkSucc Level.mkZero, propSort, lhs, rhs, eqProof)
  else
    return none

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

/-- Rebuild a `LocalContext` from its chronological `decls` list. -/
def rebuildLocalContext (decls : List LocalDecl) : LocalContext :=
  decls.foldl (fun lc d => lc.addDecl d) {}

/-- Remove a set of `fvarIds` from `lctx`. -/
def removeFVarsFromLCtx (lctx : LocalContext) (fvarIds : List Ix.Name) : LocalContext :=
  rebuildLocalContext (lctx.decls.filter fun d => !fvarIds.contains d.fvarId)

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

/-- Introduce a single `.forallE` or `.letE` binder from the current main goal with user name `uName`,
    returning `fvarId` of the newly introduced local hypothesis. -/
def introOneMainGoalBinder (fuel : Nat) (uName : Ix.Name) (refStx? : Option Ix.Syntax := none)
    (reuseFVarId? : Option Ix.Name := none) :
    TacticM Ix.Name :=
  withMainGoalContext refStx? fun gId gDecl gTy => do
    let curW ← liftM (whnf fuel gTy)
    match stripMData curW with
    | .forallE defNm dom body bi _ =>
      let finalName :=
        if Name.isAnonymous uName then
          if Name.isAnonymous defNm then Name.simple "h" else defNm
        else uName
      let fvId ← match reuseFVarId? with
        | some id => pure id
        | none    => liftM (mkFreshName "_fvar")
      let fvExpr := Expr.mkFVar fvId
      let decl : LocalDecl := { fvarId := fvId, userName := finalName, type := dom, binderInfo := bi }
      let lctx' := gDecl.lctx.addDecl decl
      let nextTy := betaReduceExpr (instantiate1 body fvExpr)
      let subMVar ← withReader (fun ctx => { ctx with lctx := lctx' }) do
        liftM (mkFreshExprMVar nextTy gDecl.userName)
      let subId := match subMVar with | .mvar id _ => id | _ => gId
      liftM (modifyMCtx (·.assignDelayed gId { lctx := lctx', fvars := [fvId], pendingMVar := subId }))
      replaceMainGoal [subId]
      return fvId
    | .letE defNm ty val body _ _ =>
      let finalName :=
        if Name.isAnonymous uName then
          if Name.isAnonymous defNm then Name.simple "h" else defNm
        else uName
      let fvId ← match reuseFVarId? with
        | some id => pure id
        | none    => liftM (mkFreshName "_fvar")
      let fvExpr := Expr.mkFVar fvId
      let decl : LocalDecl := { fvarId := fvId, userName := finalName, type := ty, value? := some val }
      let lctx' := gDecl.lctx.addDecl decl
      let nextTy := betaReduceExpr (instantiate1 body fvExpr)
      let subMVar ← withReader (fun ctx => { ctx with lctx := lctx' }) do
        liftM (mkFreshExprMVar nextTy gDecl.userName)
      let subId := match subMVar with | .mvar id _ => id | _ => gId
      liftM (modifyMCtx (·.assignDelayed gId { lctx := lctx', fvars := [fvId], pendingMVar := subId }))
      replaceMainGoal [subId]
      return fvId
    | _ =>
      liftM (throwElabError "'intro' expected a function/forall goal type" refStx?)

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
              if let some (uEq, alpha, lhs, rhs) ← liftM (matchEqType? fuel dom) then
                let eqOk? ← liftM <| observing? do
                  let ok ← isDefEq fuel lhs rhs
                  if !ok then throwElabError "not refl"
                  return true
                if eqOk? == some true then
                  falseProof? := some (Expr.mkApp (Expr.mkFVar d.fvarId) (mkEqReflExpr uEq alpha lhs))
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

/-- `exists e₁, e₂, ...` (`use`): supply witness(es) to a single-constructor inductive (`Exists`, `Sigma`, `Prod`, `Subtype`),
    pre-unifying inductive parameters before elaborating `wStx` and beta-reducing the remaining subgoal type. -/
def evalExistsTactic (elabRec : Ix.Syntax → Option Ix.Expr → IxElabM Ix.Expr)
    (fuel : Nat) (tac : Ix.Syntax) : TacticM Unit := do
  let witStxs := (Syntax.getArgs (Syntax.getArg tac 1)).toList
  let rec applyWitnesses : List Ix.Syntax → TacticM Unit
    | [] => return ()
    | wStx :: rest =>
      withMainGoalContext (some tac) fun gId _ gTy => do
        let gTyW ← liftM (whnf fuel gTy)
        let (hFn, hArgs) := getAppFnArgs gTyW
        let stNow ← liftM (get : IxElabM ElabState)
        match hFn with
        | .const indName indUnivs _ =>
          match stNow.env.find? indName with
          | some (.inductInfo ival) =>
            match ival.ctors[0]? with
            | none => liftM (throwElabError s!"'{Name.toStringTotal indName}' has no constructors for 'exists'/'use'" (some tac))
            | some ctorName =>
              let (ctorConst, ctorTy) ← liftM do
                match stNow.env.find? ctorName with
                | some cinfo =>
                  let cnst := Expr.ConstantInfo.getCnstPure cinfo
                  if cnst.levelParams.size == indUnivs.size then
                    pure (Expr.mkConst ctorName indUnivs, substExprLevelParams cnst.levelParams indUnivs cnst.type)
                  else
                    mkConstWithFreshMVarLevels ctorName
                | none => mkConstWithFreshMVarLevels ctorName
              let params := hArgs.extract 0 ival.numParams
              let (ctorWithParams, instGoals, afterParamsTy) ←
                if params.size == ival.numParams then
                  let tyAfter := params.foldl (fun cur p =>
                    match stripMData cur with
                    | .forallE _ _ b _ _ => instantiate1 b p
                    | other => other) ctorTy
                  pure (Expr.mkAppN ctorConst params, [], tyAfter)
                else
                  liftM (insertImplicitArgs 16 ctorConst ctorTy [])
              let afterW ← liftM (whnf fuel afterParamsTy)
              match stripMData afterW with
              | .forallE _ wDom wBody _ _ =>
                let wDomInst ← liftM (instantiateMVars 32 wDom)
                let wVal ← liftM (elabRec wStx (some wDomInst))
                let app1 := Expr.mkApp ctorWithParams wVal
                let remTy := betaReduceExpr (instantiate1 wBody wVal)
                let (fullApp, moreInst, finalTy) ← liftM (openForallMVars 16 app1 remTy instGoals)
                let ok ← liftM (isDefEq fuel finalTy gTyW)
                if !ok then
                  liftM (throwElabError "'exists'/'use' failed to unify constructor conclusion with goal" (some tac))
                for ig in moreInst do
                  let igTy ← liftM (inferType fuel ig)
                  if let some iv ← liftM (synthInstance? 8 igTy) then
                    let _ ← liftM (isDefEq fuel ig iv)
                let stAfter ← liftM (get : IxElabM ElabState)
                let newGoals := collectUnassignedMVarIds stAfter.mctx fullApp
                for ngId in newGoals do
                  if let some ngDecl := stAfter.mctx.findDecl? ngId then
                    let ngTyInst ← liftM (instantiateMVars 32 ngDecl.type)
                    let ngTyBeta := betaReduceExpr ngTyInst
                    liftM (modifyMCtx (·.addExprMVarDecl { ngDecl with type := ngTyBeta }))
                liftM (modifyMCtx (·.assignExpr gId fullApp))
                replaceMainGoal newGoals
                applyWitnesses rest
              | _ =>
                liftM (throwElabError "'exists'/'use' constructor does not take a witness argument" (some tac))
          | _ => liftM (throwElabError "'exists'/'use' target must be an inductive type" (some tac))
        | _ => liftM (throwElabError "'exists'/'use' target must be an inductive type" (some tac))
  applyWitnesses witStxs
  let _ ← tryTactic? (evalTrivialTactic fuel tac)

/-- `symm` (`symmetry`): transform `@Eq.{u} α lhs rhs` into `@Eq.{u} α rhs lhs` (or `Iff lhs rhs` into `Iff rhs lhs`). -/
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
      match ← liftM (matchIffType? fuel gTy) with
      | some (lhs, rhs) =>
        let symmGoalTy := Expr.mkAppN (Expr.mkConst (Name.simple "Iff") #[]) #[rhs, lhs]
        let subMVar ← liftM (mkFreshExprMVar symmGoalTy gDecl.userName)
        let subId := match subMVar with | .mvar id _ => id | _ => gId
        let mp := Expr.mkAppN (Expr.mkConst (Name.mkStr2 "Iff" "mpr") #[]) #[rhs, lhs, subMVar]
        let mpr := Expr.mkAppN (Expr.mkConst (Name.mkStr2 "Iff" "mp") #[]) #[rhs, lhs, subMVar]
        let proof := Expr.mkAppN (Expr.mkConst (Name.mkStr2 "Iff" "intro") #[]) #[lhs, rhs, mp, mpr]
        liftM (modifyMCtx (·.assignExpr gId proof))
        replaceMainGoal [subId]
      | none =>
        liftM (throwElabError "'symm' tactic requires an equality or Iff goal" (some tac))

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

/-- `have [h] [: T] := v` and `let [x] [: T] := v` using `DelayedMVarAssign`. -/
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

/-- Single rewrite step `rwRule` (`[←] term`) over `Eq` (`=`) or `Iff` (`↔`, converted via `@propext`)
    on either the main goal (`atHyp? = none`) or a local hypothesis (`atHyp? = some hypName`). -/
def evalOneRwRule (elabRec : Ix.Syntax → Option Ix.Expr → IxElabM Ix.Expr)
    (fuel : Nat) (ruleStx : Ix.Syntax) (atHyp? : Option Ix.Name) : TacticM Unit :=
  withMainGoalContext (some ruleStx) fun gId gDecl gTy => do
    let (isSymm, termStx) :=
      if Syntax.isOfKind ruleStx SyntaxKind.tacticRwRule then
        let symmNode := Syntax.getArg ruleStx 0
        (!Syntax.isNone symmNode && !Syntax.isMissing symmNode, Syntax.getArg ruleStx 1)
      else
        (false, ruleStx)
    let rawRuleExpr ← liftM (elabRec termStx none)
    let rawRuleTy ← liftM (inferType fuel rawRuleExpr)
    let (candRaw, instGoals, resTy) ← liftM (openForallMVars 16 rawRuleExpr rawRuleTy [])
    let some (uEqRaw, alphaRaw, lhsRaw, rhsRaw, cand) ← liftM (matchEqOrIffProof? fuel candRaw resTy)
      | liftM (throwElabError "'rw' rule must be an equality or iff (or quantification over an equality/iff)" (some ruleStx))
    let patRaw := if isSymm then rhsRaw else lhsRaw
    let repRaw := if isSymm then lhsRaw else rhsRaw

    match atHyp? with
    | none =>
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
      let eqRepToPat :=
        if isSymm then
          candInst
        else
          mkEqSymmExpr (normalizeLevel uEq) alpha pat rep candInst
      let subMVar ← liftM (mkFreshExprMVar newGoalTy gDecl.userName)
      let subId := match subMVar with | .mvar id _ => id | _ => gId
      let transportedProof :=
        mkEqTransportExpr (normalizeLevel uEq) (normalizeLevel uGoal) alpha rep pat absGoal eqRepToPat subMVar
      liftM (modifyMCtx (·.assignExpr gId transportedProof))
      replaceMainGoal [subId]
    | some hypName =>
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

/-- `dsimp [only] [[...]] [at hyp]` and `simp [only] [[...]] [at hyp]`. -/
def evalSimpOrDSimpTactic (elabRec : Ix.Syntax → Option Ix.Expr → IxElabM Ix.Expr)
    (fuel : Nat) (tac : Ix.Syntax) (isFullSimp : Bool) : TacticM Unit := do
  let (isOnly, optRulesNode, optAtNode) :=
    if Syntax.getNumArgs tac >= 4 then
      let onlyNode := Syntax.getArg tac 1
      (!Syntax.isNone onlyNode && !Syntax.isMissing onlyNode,
       Syntax.getArg tac 2,
       Syntax.getArg tac 3)
    else
      (false, Syntax.getArg tac 1, Syntax.getArg tac 2)
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
  let envSimpRules : List Ix.Syntax ←
    if isFullSimp && !isOnly then
      let stNow ← liftM (get : IxElabM ElabState)
      let simpEntries : List InstanceEntry := (stNow.env.instancesByClass.get? (Name.mkStr2 "_Ix" "simpLemma")).getD []
      pure (simpEntries.reverse.map fun (e : InstanceEntry) =>
        Syntax.mkNode SyntaxKind.tacticRwRule #[Syntax.mkNullNode #[], Syntax.mkSimpleIdent e.instName])
    else
      pure []
  let explicitRwRules := extraRules.map fun rStx =>
    if Syntax.isOfKind rStx SyntaxKind.tacticRwRule then rStx
    else Syntax.mkNode SyntaxKind.tacticRwRule #[Syntax.mkNullNode #[], rStx]
  let allRwRules := explicitRwRules ++ envSimpRules
  if !allRwRules.isEmpty then
    let rec simpRwLoop : Nat → TacticM Unit
      | 0 => return ()
      | k + 1 => do
        let mut anyProgress := false
        for rStx in allRwRules do
          if (← tryTactic? (evalOneRwRule elabRec fuel rStx atHyp?)).isSome then
            anyProgress := true
        if anyProgress then simpRwLoop k else return ()
    simpRwLoop 8
  if isFullSimp && atHyp?.isNone then
    if isOnly then
      let _ ← tryTactic? (evalRflTactic fuel tac)
    else
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
          let afterParamsInst := params.foldl (fun cur p =>
            match stripMData cur with
            | .forallE _ _ b _ _ => instantiate1 b p
            | other => other) (substExprLevelParams ival.cnst.levelParams indUnivs ival.cnst.type)
          let (idxFVars, idxDecls, _) := openForallTelescope ival.numIndices afterParamsInst "midx" 0 #[] #[]
          let majDom := Expr.mkAppN (Expr.mkConst indName indUnivs) (params ++ idxFVars)
          let (majFvId, majFvExpr) := mkAuxFVar "mmaj" 0
          let majDecl : AuxLocalDecl := { fvarId := majFvId, binderName := Name.simple "x", domain := majDom }
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
            replaceMainGoal (branchSubGoals.toList.map (·.2.1))
          else
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

/-! ## Context, Classical, Recursive Destructuring (`rcases`/`obtain`/`rintro`), & `calc` Tactics -/

/-- `clear h₁ h₂ ...`: remove hypotheses from `lctx` after checking that the goal and remaining
    local declarations do not depend on them. -/
def evalClearTactic (tac : Ix.Syntax) : TacticM Unit := do
  let idStxs := (Syntax.getArgs (Syntax.getArg tac 1)).toList
  let rec clearLoop : List Ix.Syntax → TacticM Unit
    | [] => return ()
    | idStx :: rest => do
      withMainGoalContext (some idStx) fun gId gDecl gTy => do
        let hName := Syntax.getId idStx
        let some hDecl := gDecl.lctx.findUserName? hName
          | liftM (throwElabError s!"unknown hypothesis '{Name.toStringTotal hName}' in 'clear'" (some idStx))
        let hFvId := hDecl.fvarId
        if containsFVar hFvId gTy then
          liftM (throwElabError s!"cannot clear '{Name.toStringTotal hName}': target goal depends on it" (some idStx))
        let remainingDecls := gDecl.lctx.decls.filter (fun d => d.fvarId != hFvId)
        for d in remainingDecls do
          let dTy ← liftM (instantiateMVars 16 d.type)
          if containsFVar hFvId dTy then
            liftM (throwElabError s!"cannot clear '{Name.toStringTotal hName}': hypothesis '{Name.toStringTotal d.userName}' depends on it" (some idStx))
          if let some dVal := d.value? then
            let dValInst ← liftM (instantiateMVars 16 dVal)
            if containsFVar hFvId dValInst then
              liftM (throwElabError s!"cannot clear '{Name.toStringTotal hName}': let-binding '{Name.toStringTotal d.userName}' depends on it" (some idStx))
        let lctx' := rebuildLocalContext remainingDecls
        let subMVar ← withReader (fun ctx => { ctx with lctx := lctx' }) do
          liftM (mkFreshExprMVar gTy gDecl.userName)
        let subId := match subMVar with | .mvar id _ => id | _ => gId
        liftM (modifyMCtx (·.assignExpr gId subMVar))
        replaceMainGoal [subId]
      clearLoop rest
  clearLoop idStxs

/-- Revert a single local declaration `hDecl` into a `.forallE` or `.letE` binder on the main goal. -/
def revertSingleFVar (tac : Ix.Syntax) (hFvId : Ix.Name) : TacticM Unit :=
  withMainGoalContext (some tac) fun gId gDecl gTy => do
    let some hDecl := gDecl.lctx.find? hFvId
      | liftM (throwElabError "unknown local hypothesis in 'revert'" (some tac))
    let hTy ← liftM (instantiateMVars 32 hDecl.type)
    let absBody := abstractFVar hFvId gTy
    let newGoalTy ← match hDecl.value? with
      | some hVal =>
        let hValInst ← liftM (instantiateMVars 32 hVal)
        pure (Expr.mkLetE hDecl.userName hTy hValInst absBody hDecl.nonDep)
      | none =>
        pure (Expr.mkForallE hDecl.userName hTy absBody hDecl.binderInfo)
    let lctx' := removeFVarsFromLCtx gDecl.lctx [hFvId]
    let subMVar ← withReader (fun ctx => { ctx with lctx := lctx' }) do
      liftM (mkFreshExprMVar newGoalTy gDecl.userName)
    let subId := match subMVar with | .mvar id _ => id | _ => gId
    let proof :=
      if hDecl.value?.isSome then subMVar
      else Expr.mkApp subMVar (Expr.mkFVar hFvId)
    liftM (modifyMCtx (·.assignExpr gId proof))
    replaceMainGoal [subId]

/-- `revert x₁ x₂ ...`: revert local hypotheses (and any later hypotheses that depend on them)
    into `.forallE` / `.letE` binders on the main goal in reverse dependency order. -/
def evalRevertTactic (tac : Ix.Syntax) : TacticM Unit :=
  withMainGoalContext (some tac) fun _ gDecl _ => do
    let idStxs := (Syntax.getArgs (Syntax.getArg tac 1)).toList
    let mut seedFvIds : List Ix.Name := []
    for idStx in idStxs do
      let nm := Syntax.getId idStx
      match gDecl.lctx.findUserName? nm with
      | some d =>
        if !seedFvIds.contains d.fvarId then
          seedFvIds := seedFvIds ++ [d.fvarId]
      | none =>
        liftM (throwElabError s!"unknown hypothesis '{Name.toStringTotal nm}' in 'revert'" (some idStx))
    let mut toRevertChrono : List Ix.Name := []
    for d in gDecl.lctx.decls do
      let dTy ← liftM (instantiateMVars 16 d.type)
      let depOnPrev := toRevertChrono.any fun fv =>
        containsFVar fv dTy || (match d.value? with | some v => containsFVar fv v | none => false)
      if seedFvIds.contains d.fvarId || depOnPrev then
        toRevertChrono := toRevertChrono ++ [d.fvarId]
    let rec revertLoop : List Ix.Name → TacticM Unit
      | [] => return ()
      | fvId :: rest => do
        revertSingleFVar tac fvId
        revertLoop rest
    revertLoop toRevertChrono.reverse

/-- Substitute an equality hypothesis `eqDecl : lhs = rhs` (where either `lhs` or `rhs` is a free variable `varFvId`),
    transporting the goal and any other hypotheses that mention `varFvId` via `@Eq.casesOn` and clearing `eqDecl`/`varFvId`. -/
def substEqualityDecl (fuel : Nat) (refStx : Ix.Syntax) (eqFvId : Ix.Name) : TacticM Unit := do
  let (_, gDecl0, _) ← getMainGoal (some refStx)
  let some eqDecl0 := gDecl0.lctx.find? eqFvId
    | liftM (throwElabError "unknown equality hypothesis in 'subst'" (some refStx))
  let eqTy0 ← liftM (instantiateMVars 32 eqDecl0.type)
  let some (_, _, lhs0, rhs0) ← liftM (matchEqType? fuel eqTy0)
    | liftM (throwElabError "'subst' requires an equality hypothesis 'x = e' or 'e = x'" (some refStx))
  let (varFvId, isVarOnLeft) ← match stripMData lhs0, stripMData rhs0 with
    | .fvar fvL _, _ =>
      if !containsFVar fvL rhs0 then pure (fvL, true)
      else match stripMData rhs0 with
        | .fvar fvR _ =>
          if !containsFVar fvR lhs0 then pure (fvR, false)
          else liftM (throwElabError "'subst' failed: recursive equality 'x = ... x ...'" (some refStx))
        | _ => liftM (throwElabError "'subst' failed: variable occurs on both sides of equality" (some refStx))
    | _, .fvar fvR _ =>
      if !containsFVar fvR lhs0 then pure (fvR, false)
      else liftM (throwElabError "'subst' failed: variable occurs on both sides of equality" (some refStx))
    | _, _ =>
      let (_, gDeclNow, gTyNow) ← getMainGoal (some refStx)
      if !containsFVar eqFvId gTyNow then
        let lctx' := removeFVarsFromLCtx gDeclNow.lctx [eqFvId]
        let (gIdNow, _, _) ← getMainGoal (some refStx)
        let subMVar ← withReader (fun ctx => { ctx with lctx := lctx' }) do
          liftM (mkFreshExprMVar gTyNow gDeclNow.userName)
        let subId := match subMVar with | .mvar id _ => id | _ => gIdNow
        liftM (modifyMCtx (·.assignExpr gIdNow subMVar))
        replaceMainGoal [subId]
      return ()
  let depHyps : List LocalDecl ← do
    let mut acc : List LocalDecl := []
    for d in gDecl0.lctx.decls do
      if d.fvarId != varFvId && d.fvarId != eqFvId then
        let dTy ← liftM (instantiateMVars 16 d.type)
        let depOnAcc := acc.any fun ad => containsFVar ad.fvarId dTy
        if containsFVar varFvId dTy || containsFVar eqFvId dTy || depOnAcc then
          acc := acc ++ [d]
    pure acc
  for d in depHyps.reverse do
    revertSingleFVar refStx d.fvarId
  withMainGoalContext (some refStx) fun gId gDecl gTy => do
    let some eqDecl := gDecl.lctx.find? eqFvId
      | liftM (throwElabError "equality hypothesis lost during 'subst'" (some refStx))
    let eqTy ← liftM (instantiateMVars 32 eqDecl.type)
    let some (uEqRaw, alphaRaw, lhsRaw, rhsRaw) ← liftM (matchEqType? fuel eqTy)
      | liftM (throwElabError "'subst' expected equality hypothesis" (some refStx))
    let uEq ← liftM (instantiateLevelMVars 32 uEqRaw)
    let alpha ← liftM (instantiateMVars 32 alphaRaw)
    let lhs ← liftM (instantiateMVars 32 lhsRaw)
    let rhs ← liftM (instantiateMVars 32 rhsRaw)
    let varExpr := if isVarOnLeft then lhs else rhs
    let repExpr := if isVarOnLeft then rhs else lhs
    let gTyNoEq :=
      if containsFVar eqFvId gTy then
        instantiate1 (abstractFVar eqFvId gTy) (mkEqReflExpr (normalizeLevel uEq) alpha repExpr)
      else
        gTy
    let absGoal := abstractFVar varFvId gTyNoEq
    let newGoalTy := betaReduceExpr (instantiate1 absGoal repExpr)
    let uGoal ← liftM (ensureSort 32 gTy)
    let hEqExpr := Expr.mkFVar eqFvId
    let hRepToVar :=
      if isVarOnLeft then
        mkEqSymmExpr (normalizeLevel uEq) alpha varExpr repExpr hEqExpr
      else
        hEqExpr
    let lctx' := removeFVarsFromLCtx gDecl.lctx [eqFvId, varFvId]
    let subMVar ← withReader (fun ctx => { ctx with lctx := lctx' }) do
      liftM (mkFreshExprMVar newGoalTy gDecl.userName)
    let subId := match subMVar with | .mvar id _ => id | _ => gId
    let transportedProof :=
      mkEqTransportExpr (normalizeLevel uEq) (normalizeLevel uGoal) alpha repExpr varExpr absGoal hRepToVar subMVar
    liftM (modifyMCtx (·.assignExpr gId transportedProof))
    replaceMainGoal [subId]
  for d in depHyps do
    let _ ← introOneMainGoalBinder fuel d.userName (some refStx) (some d.fvarId)

/-- `subst x₁ x₂ ...`: for each identifier `x`, either `x` is itself an equality hypothesis `y = e` / `e = y`,
    or `x` is a local variable with an equality hypothesis `h : x = e` or `h : e = x` in `lctx`. -/
def evalSubstTactic (fuel : Nat) (tac : Ix.Syntax) : TacticM Unit := do
  let idStxs := (Syntax.getArgs (Syntax.getArg tac 1)).toList
  let rec loop : List Ix.Syntax → TacticM Unit
    | [] => return ()
    | idStx :: rest => do
      let targetName := Syntax.getId idStx
      let (_, gDecl, _) ← getMainGoal (some idStx)
      let some targetDecl := gDecl.lctx.findUserName? targetName
        | liftM (throwElabError s!"unknown hypothesis or variable '{Name.toStringTotal targetName}' in 'subst'" (some idStx))
      let tTy ← liftM (instantiateMVars 32 targetDecl.type)
      if (← liftM (matchEqType? fuel tTy)).isSome then
        substEqualityDecl fuel idStx targetDecl.fvarId
      else
        let varFvId := targetDecl.fvarId
        let mut foundEqFvId? : Option Ix.Name := none
        for d in gDecl.lctx.revDecls do
          if foundEqFvId?.isNone then
            let dTy ← liftM (instantiateMVars 16 d.type)
            if let some (_, _, lhs, rhs) ← liftM (matchEqType? fuel dTy) then
              let matchL := match stripMData lhs with | .fvar fv _ => fv == varFvId && !containsFVar varFvId rhs | _ => false
              let matchR := match stripMData rhs with | .fvar fv _ => fv == varFvId && !containsFVar varFvId lhs | _ => false
              if matchL || matchR then
                foundEqFvId? := some d.fvarId
        match foundEqFvId? with
        | some eqFvId => substEqualityDecl fuel idStx eqFvId
        | none => liftM (throwElabError s!"'subst' failed: could not find an equality hypothesis for '{Name.toStringTotal targetName}'" (some idStx))
      loop rest
  loop idStxs

/-- `specialize h a₁ a₂ ...`: elaborate `h a₁ a₂ ...` and replace/shadow local hypothesis `h` with the specialized proof. -/
def evalSpecializeTactic (elabRec : Ix.Syntax → Option Ix.Expr → IxElabM Ix.Expr)
    (fuel : Nat) (tac : Ix.Syntax) : TacticM Unit :=
  withMainGoalContext (some tac) fun gId gDecl gTy => do
    let hIdent := Syntax.getArg tac 1
    let hName := Syntax.getId hIdent
    let argStxs := (Syntax.getArgs (Syntax.getArg tac 2)).toList
    if argStxs.isEmpty then return ()
    let appStx := argStxs.foldl (fun acc a => Syntax.mkNode SyntaxKind.appTerm #[acc, a]) hIdent
    let specExpr ← liftM (elabRec appStx none)
    let specTy ← liftM (inferType fuel specExpr)
    let specExprInst ← liftM (instantiateMVars 32 specExpr)
    let specTyInst ← liftM (instantiateMVars 32 specTy)
    let oldFvIds ← match gDecl.lctx.findUserName? hName with
      | some oldD =>
        let usedInGoal := containsFVar oldD.fvarId gTy
        let usedInOther ← gDecl.lctx.decls.anyM fun d => do
          if d.fvarId == oldD.fvarId then pure false
          else
            let dTy ← liftM (instantiateMVars 16 d.type)
            let inVal := match d.value? with | some v => containsFVar oldD.fvarId v | none => false
            pure (containsFVar oldD.fvarId dTy || inVal)
        pure (if !usedInGoal && !usedInOther then [oldD.fvarId] else [])
      | none => pure []
    let newFvId ← liftM (mkFreshName "_fvar")
    let newDecl : LocalDecl := {
      fvarId     := newFvId
      userName   := hName
      type       := specTyInst
      value?     := none
      binderInfo := .default
    }
    let lctx' := (removeFVarsFromLCtx gDecl.lctx oldFvIds).addDecl newDecl
    let subMVar ← withReader (fun ctx => { ctx with lctx := lctx' }) do
      liftM (mkFreshExprMVar gTy gDecl.userName)
    let subId := match subMVar with | .mvar id _ => id | _ => gId
    let outerTy := Expr.mkForallE hName specTyInst (liftLooseBVars gTy 1) .default
    let outerMVar ← liftM (mkFreshExprMVar outerTy gDecl.userName)
    let outerId := match outerMVar with | .mvar id _ => id | _ => gId
    liftM (modifyMCtx (·.assignDelayed outerId { lctx := lctx', fvars := [newFvId], pendingMVar := subId }))
    liftM (modifyMCtx (·.assignExpr gId (Expr.mkApp outerMVar specExprInst)))
    replaceMainGoal [subId]

/-- `suffices [h :] Ty by tacSeq` and `suffices [h :] Ty from term`. -/
def evalSufficesTactic
    (elabRec : Ix.Syntax → Option Ix.Expr → IxElabM Ix.Expr)
    (evalSeqRec : Ix.Syntax → TacticM Unit)
    (tac : Ix.Syntax) : TacticM Unit :=
  withMainGoalContext (some tac) fun gId gDecl gTy => do
    let hIdRaw := Syntax.getId (Syntax.getArg tac 1)
    let hName := if Name.isAnonymous hIdRaw then Name.simple "this" else hIdRaw
    let tyStx := Syntax.getArg tac 3
    let modeVal := Syntax.getAtomVal (Syntax.getArg tac 4)
    let isFrom := modeVal == "from" || Syntax.getId (Syntax.getArg tac 4) == Name.simple "from"
    let bodyStx := Syntax.getArg tac 5
    let suffTy ← liftM (elabRec tyStx none)
    let _ ← liftM (ensureSort 32 suffTy)
    let suffTyInst ← liftM (instantiateMVars 32 suffTy)
    let proveSuffMVar ← liftM (mkFreshExprMVar suffTyInst hName)
    let proveSuffId := match proveSuffMVar with | .mvar id _ => id | _ => gId
    let fvId ← liftM (mkFreshName "_fvar")
    let decl : LocalDecl := {
      fvarId     := fvId
      userName   := hName
      type       := suffTyInst
      value?     := some proveSuffMVar
      binderInfo := .default
      contract   := default
      letKind?   := some .value
      nonDep     := true
    }
    let lctxWithH := gDecl.lctx.addDecl decl
    liftM (pushLocalLetContract { nonDep := true, kind := .value, binder := default })
    if isFrom then
      let bodyExpr ← withReader (fun ctx => { ctx with lctx := lctxWithH }) do
        liftM (elabRec bodyStx (some gTy))
      let bodyInst ← liftM (instantiateMVars 32 bodyExpr)
      let innerMVar ← withReader (fun ctx => { ctx with lctx := lctxWithH }) do
        liftM (mkFreshExprMVar gTy gDecl.userName)
      let innerId := match innerMVar with | .mvar id _ => id | _ => gId
      liftM (modifyMCtx (·.assignExpr innerId bodyInst))
      liftM (modifyMCtx (·.assignDelayed gId { lctx := lctxWithH, fvars := [fvId], pendingMVar := innerId }))
      let stNow ← liftM (get : IxElabM ElabState)
      let extraBodyGoals := collectUnassignedMVarIds stNow.mctx bodyInst
      replaceMainGoal (proveSuffId :: extraBodyGoals)
    else
      let innerMVar ← withReader (fun ctx => { ctx with lctx := lctxWithH }) do
        liftM (mkFreshExprMVar gTy gDecl.userName)
      let innerId := match innerMVar with | .mvar id _ => id | _ => gId
      liftM (modifyMCtx (·.assignDelayed gId { lctx := lctxWithH, fvars := [fvId], pendingMVar := innerId }))
      let allGs ← getUnassignedGoals
      let restGoals := allGs.drop 1
      setTacticGoals [innerId]
      evalSeqRec bodyStx
      let remAfterBy ← getUnassignedGoals
      setTacticGoals (remAfterBy ++ [proveSuffId] ++ restGoals)

/-- `generalize [h :] e = x`: abstract occurrences of `e : α` in `gTy` into a fresh variable `x : α`
    (and optionally `h : e = x`), closing `?g` with `?gSub e (@Eq.refl α e)`. -/
def evalGeneralizeTactic (elabRec : Ix.Syntax → Option Ix.Expr → IxElabM Ix.Expr)
    (fuel : Nat) (tac : Ix.Syntax) : TacticM Unit :=
  withMainGoalContext (some tac) fun gId gDecl gTy => do
    let hId := Syntax.getId (Syntax.getArg tac 1)
    let eStx := Syntax.getArg tac 2
    let xId := Syntax.getId (Syntax.getArg tac 4)
    let xName := if Name.isAnonymous xId then Name.simple "x" else xId
    let eExprRaw ← liftM (elabRec eStx none)
    let eTyRaw ← liftM (inferType fuel eExprRaw)
    let eExpr ← liftM (instantiateMVars 32 eExprRaw)
    let eTy ← liftM (instantiateMVars 32 eTyRaw)
    let uAlpha ← liftM (ensureSort 32 eTy)
    let (_, absGoal) ← liftM (kabstract fuel eExpr gTy)
    let xFvId ← liftM (mkFreshName "_fvar")
    let xFvExpr := Expr.mkFVar xFvId
    let xDecl : LocalDecl := { fvarId := xFvId, userName := xName, type := eTy, binderInfo := .default }
    let goalWithX := instantiate1 absGoal xFvExpr
    if Name.isAnonymous hId then
      let lctx' := gDecl.lctx.addDecl xDecl
      let subMVar ← withReader (fun ctx => { ctx with lctx := lctx' }) do
        liftM (mkFreshExprMVar goalWithX gDecl.userName)
      let subId := match subMVar with | .mvar id _ => id | _ => gId
      let outerTy := Expr.mkForallE xName eTy absGoal .default
      let outerMVar ← liftM (mkFreshExprMVar outerTy gDecl.userName)
      let outerId := match outerMVar with | .mvar id _ => id | _ => gId
      liftM (modifyMCtx (·.assignDelayed outerId { lctx := lctx', fvars := [xFvId], pendingMVar := subId }))
      liftM (modifyMCtx (·.assignExpr gId (Expr.mkApp outerMVar eExpr)))
      replaceMainGoal [subId]
    else
      let eqTy := Expr.mkAppN (Expr.mkConst (Name.simple "Eq") #[normalizeLevel uAlpha]) #[eTy, eExpr, xFvExpr]
      let hFvId ← liftM (mkFreshName "_fvar")
      let hDecl : LocalDecl := { fvarId := hFvId, userName := hId, type := eqTy, binderInfo := .default }
      let lctx' := (gDecl.lctx.addDecl xDecl).addDecl hDecl
      let subMVar ← withReader (fun ctx => { ctx with lctx := lctx' }) do
        liftM (mkFreshExprMVar goalWithX gDecl.userName)
      let subId := match subMVar with | .mvar id _ => id | _ => gId
      let eqTyBVar := Expr.mkAppN (Expr.mkConst (Name.simple "Eq") #[normalizeLevel uAlpha])
        #[liftLooseBVars eTy 1, liftLooseBVars eExpr 1, Expr.mkBVar 0]
      let outerTy :=
        Expr.mkForallE xName eTy
          (Expr.mkForallE hId eqTyBVar (liftLooseBVars absGoal 1 0) .default)
          .default
      let outerMVar ← liftM (mkFreshExprMVar outerTy gDecl.userName)
      let outerId := match outerMVar with | .mvar id _ => id | _ => gId
      liftM (modifyMCtx (·.assignDelayed outerId { lctx := lctx', fvars := [xFvId, hFvId], pendingMVar := subId }))
      let reflEE := mkEqReflExpr (normalizeLevel uAlpha) eTy eExpr
      liftM (modifyMCtx (·.assignExpr gId (Expr.mkAppN outerMVar #[eExpr, reflEE])))
      replaceMainGoal [subId]

/-- `by_cases [h :] P`: split the main goal into two subgoals (`pos` with `h : P` and `neg` with `h : Not P`)
    using `@Or.casesOn P (Not P) (fun _ => gTy) (@Classical.em P)`. -/
def evalByCasesTactic (elabRec : Ix.Syntax → Option Ix.Expr → IxElabM Ix.Expr)
    (tac : Ix.Syntax) : TacticM Unit :=
  withMainGoalContext (some tac) fun gId gDecl gTy => do
    let hIdRaw := Syntax.getId (Syntax.getArg tac 1)
    let hName := if Name.isAnonymous hIdRaw then Name.simple "h" else hIdRaw
    let propStx := Syntax.getArg tac 2
    let propSort := Expr.mkSort Level.mkZero
    let pExprRaw ← liftM (elabRec propStx (some propSort))
    let pExpr ← liftM (instantiateMVars 32 pExprRaw)
    let notPExpr := Expr.mkApp (Expr.mkConst (Name.simple "Not") #[]) pExpr
    liftM ensureClassicalEmInEnv
    let uGoal ← liftM (ensureSort 32 gTy)
    let orPNotP := Expr.mkAppN (Expr.mkConst (Name.simple "Or") #[]) #[pExpr, notPExpr]
    let motive := Expr.mkLam Name.mkAnon orPNotP (liftLooseBVars gTy 1) .default
    let emProof := Expr.mkApp (Expr.mkConst (Name.mkStr2 "Classical" "em") #[]) pExpr
    let fvPos ← liftM (mkFreshName "_fvar")
    let declPos : LocalDecl := { fvarId := fvPos, userName := hName, type := pExpr, binderInfo := .default }
    let lctxPos := gDecl.lctx.addDecl declPos
    let subPosMVar ← withReader (fun ctx => { ctx with lctx := lctxPos }) do
      liftM (mkFreshExprMVar gTy (Name.simple "pos"))
    let subPosId := match subPosMVar with | .mvar id _ => id | _ => gId
    let outerPosTy := Expr.mkForallE hName pExpr (liftLooseBVars gTy 1) .default
    let outerPosMVar ← liftM (mkFreshExprMVar outerPosTy (Name.simple "pos"))
    let outerPosId := match outerPosMVar with | .mvar id _ => id | _ => gId
    liftM (modifyMCtx (·.assignDelayed outerPosId { lctx := lctxPos, fvars := [fvPos], pendingMVar := subPosId }))
    let fvNeg ← liftM (mkFreshName "_fvar")
    let declNeg : LocalDecl := { fvarId := fvNeg, userName := hName, type := notPExpr, binderInfo := .default }
    let lctxNeg := gDecl.lctx.addDecl declNeg
    let subNegMVar ← withReader (fun ctx => { ctx with lctx := lctxNeg }) do
      liftM (mkFreshExprMVar gTy (Name.simple "neg"))
    let subNegId := match subNegMVar with | .mvar id _ => id | _ => gId
    let outerNegTy := Expr.mkForallE hName notPExpr (liftLooseBVars gTy 1) .default
    let outerNegMVar ← liftM (mkFreshExprMVar outerNegTy (Name.simple "neg"))
    let outerNegId := match outerNegMVar with | .mvar id _ => id | _ => gId
    liftM (modifyMCtx (·.assignDelayed outerNegId { lctx := lctxNeg, fvars := [fvNeg], pendingMVar := subNegId }))
    let stNow ← liftM (get : IxElabM ElabState)
    let orCasesOnUnivs := match stNow.env.find? (Name.mkStr2 "Or" "casesOn") with
      | some (.defnInfo d) => if d.cnst.levelParams.isEmpty then #[] else #[normalizeLevel uGoal]
      | _ => #[]
    let proof := Expr.mkAppN (Expr.mkConst (Name.mkStr2 "Or" "casesOn") orCasesOnUnivs)
      #[pExpr, notPExpr, motive, emProof, outerPosMVar, outerNegMVar]
    liftM (modifyMCtx (·.assignExpr gId proof))
    replaceMainGoal [subPosId, subNegId]

/-- `by_contra [h]` (`by_contradiction [h]`): introduce `h : Not gTy` and set the new goal type to `False`. -/
def evalByContraTactic (fuel : Nat) (tac : Ix.Syntax) : TacticM Unit :=
  withMainGoalContext (some tac) fun gId gDecl gTy => do
    let hIdRaw := Syntax.getId (Syntax.getArg tac 1)
    let hName := if Name.isAnonymous hIdRaw then Name.simple "this" else hIdRaw
    let falseConst := Expr.mkConst (Name.simple "False") #[]
    let notG := Expr.mkApp (Expr.mkConst (Name.simple "Not") #[]) gTy
    let uGoal ← liftM (ensureSort 32 gTy)
    liftM ensureClassicalEmInEnv
    let fvNeg ← liftM (mkFreshName "_fvar")
    let declNeg : LocalDecl := { fvarId := fvNeg, userName := hName, type := notG, binderInfo := .default }
    let lctxNeg := gDecl.lctx.addDecl declNeg
    let subFalseMVar ← withReader (fun ctx => { ctx with lctx := lctxNeg }) do
      liftM (mkFreshExprMVar falseConst (Name.simple "False"))
    let subFalseId := match subFalseMVar with | .mvar id _ => id | _ => gId
    let outerNegTy := Expr.mkForallE hName notG falseConst .default
    let outerNegMVar ← liftM (mkFreshExprMVar outerNegTy gDecl.userName)
    let outerNegId := match outerNegMVar with | .mvar id _ => id | _ => gId
    liftM (modifyMCtx (·.assignDelayed outerNegId { lctx := lctxNeg, fvars := [fvNeg], pendingMVar := subFalseId }))
    let posLam := Expr.mkLam (Name.simple "hPos") gTy (Expr.mkBVar 0) .default
    let falseProofUnderNeg := Expr.mkApp (liftLooseBVars outerNegMVar 1) (Expr.mkBVar 0)
    let negBody := mkFalseElimExpr uGoal (liftLooseBVars gTy 1) falseProofUnderNeg
    let negLam := Expr.mkLam hName notG negBody .default
    let orGNotG := Expr.mkAppN (Expr.mkConst (Name.simple "Or") #[]) #[gTy, notG]
    let motive := Expr.mkLam Name.mkAnon orGNotG (liftLooseBVars gTy 1) .default
    let emProof := Expr.mkApp (Expr.mkConst (Name.mkStr2 "Classical" "em") #[]) gTy
    let stNow ← liftM (get : IxElabM ElabState)
    let orCasesOnUnivs := match stNow.env.find? (Name.mkStr2 "Or" "casesOn") with
      | some (.defnInfo d) => if d.cnst.levelParams.isEmpty then #[] else #[normalizeLevel uGoal]
      | _ => #[]
    let proof := Expr.mkAppN (Expr.mkConst (Name.mkStr2 "Or" "casesOn") orCasesOnUnivs)
      #[gTy, notG, motive, emProof, posLam, negLam]
    liftM (modifyMCtx (·.assignExpr gId proof))
    replaceMainGoal [subFalseId]
    let _ ← pure fuel

/-- Perform a single unstructured `<Ind>.casesOn` split on local hypothesis `targetFvId` in the current main goal,
    returning for each constructor branch `(subGoalId, introducedFieldFVarIds)`. -/
def casesOnFVarWithFieldIds (fuel : Nat) (refStx : Ix.Syntax) (targetFvId : Ix.Name) :
    TacticM (List (Ix.Name × List Ix.Name)) :=
  withMainGoalContext (some refStx) fun gId gDecl gTy => do
    let some targetDecl := gDecl.lctx.find? targetFvId
      | liftM (throwElabError "unknown target hypothesis in 'rcases'" (some refStx))
    let targetExpr := Expr.mkFVar targetFvId
    let targetTy ← liftM (instantiateMVars 32 targetDecl.type)
    let targetTyW ← liftM (whnf fuel targetTy)
    let (hFn, headArgs) := getAppFnArgs targetTyW
    let st ← liftM (get : IxElabM ElabState)
    match hFn with
    | .const indName indUnivs _ =>
      match st.env.find? indName with
      | some (.inductInfo ival) =>
        let prefName := Name.mkStr indName "casesOn"
        let elimName := if st.env.contains prefName then prefName else Name.mkStr indName "recOn"
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
          let afterParamsInst := params.foldl (fun cur p =>
            match stripMData cur with
            | .forallE _ _ b _ _ => instantiate1 b p
            | other => other) (substExprLevelParams ival.cnst.levelParams indUnivs ival.cnst.type)
          let (idxFVars, idxDecls, _) := openForallTelescope ival.numIndices afterParamsInst "midx" 0 #[] #[]
          let majDom := Expr.mkAppN (Expr.mkConst indName indUnivs) (params ++ idxFVars)
          let (majFvId, majFvExpr) := mkAuxFVar "mmaj" 0
          let majDecl : AuxLocalDecl := { fvarId := majFvId, binderName := Name.simple "x", domain := majDom }
          let b0 := instantiate1 (abstractFVar targetFvId gTy) majFvExpr
          let motiveBody := (indices.zipIdx).foldl (fun acc (idxE, k) =>
            match stripMData idxE, idxFVars[k]? with
            | .fvar iFv _, some repFv =>
              if iFv != targetFvId then instantiate1 (abstractFVar iFv acc) repFv else acc
            | _, _ => acc) b0
          let motiveLam := closeLambdas (idxDecls.push majDecl) motiveBody
          let rawElimTy := substExprLevelParams elimDef.cnst.levelParams elimUnivs elimDef.cnst.type
          let prefixArgs := params ++ #[motiveLam] ++ indices ++ #[targetExpr]
          let minorBinderCounts := extractMinorBinderCounts prefixArgs.size ival.ctors.size rawElimTy
          let minorsTelTy := prefixArgs.foldl (fun cur arg =>
            match stripMData cur with
            | .forallE _ _ b _ _ => instantiate1 b arg
            | other => other) rawElimTy
          let mut curTel := minorsTelTy
          let mut minorLams : Array Ix.Expr := #[]
          let mut branchResults : List (Ix.Name × List Ix.Name) := []
          for (ctorName, cIdx) in ival.ctors.zipIdx do
            let minorDom ← match stripMData curTel with
              | .forallE _ d b _ _ =>
                curTel := b
                pure (betaReduceExpr d)
              | _ =>
                liftM (throwElabError s!"unexpected eliminator type in '{Name.toStringTotal elimName}'" (some refStx))
            let numBinders := minorBinderCounts.getD cIdx 0
            let finishMinor (curTy : Ix.Expr) (revFVars : List Ix.Name) :
                IxElabM (Ix.Name × List Ix.Name × Ix.Expr) := do
              let fieldFVars := revFVars.reverse
              let subMVar ← mkFreshExprMVar (betaReduceExpr curTy) ctorName
              let subId := match subMVar with | .mvar id _ => id | _ => gId
              if fieldFVars.isEmpty then
                return (subId, [], subMVar)
              else
                let ctx ← read
                let outerMVar ← mkFreshExprMVar minorDom ctorName
                let outerId := match outerMVar with | .mvar id _ => id | _ => gId
                modifyMCtx (·.assignDelayed outerId {
                  lctx        := ctx.lctx
                  fvars       := fieldFVars
                  pendingMVar := subId
                })
                return (subId, fieldFVars, outerMVar)
            let rec openBinders (rem : Nat) (curTy : Ix.Expr) (revFVars : List Ix.Name) :
                IxElabM (Ix.Name × List Ix.Name × Ix.Expr) := do
              match rem with
              | 0 => finishMinor curTy revFVars
              | rem' + 1 =>
                let curW ← match stripMData curTy with
                  | .forallE _ _ _ _ _ => pure curTy
                  | _                  => whnf fuel curTy
                match stripMData curW with
                | .forallE defNm fDom fBody bi _ =>
                  let uName := if Name.isAnonymous defNm then Name.simple "h" else defNm
                  withLocalDecl uName (betaReduceExpr fDom) bi default fun fvId fvExpr =>
                    openBinders rem' (instantiate1 fBody fvExpr) (fvId :: revFVars)
                | _ => finishMinor curTy revFVars
            let (subId, fieldFVars, minorLam) ← liftM (openBinders numBinders minorDom [])
            minorLams := minorLams.push minorLam
            branchResults := branchResults ++ [(subId, fieldFVars)]
          let elimApp := Expr.mkAppN (Expr.mkConst elimName elimUnivs) (prefixArgs ++ minorLams)
          liftM (modifyMCtx (·.assignExpr gId elimApp))
          replaceMainGoal (branchResults.map Prod.fst)
          return branchResults
        | _ => liftM (throwElabError s!"eliminator '{Name.toStringTotal elimName}' not found" (some refStx))
      | _ => liftM (throwElabError s!"'{Name.toStringTotal indName}' is not an inductive type in 'rcases'" (some refStx))
    | _ => liftM (throwElabError "'rcases' target must have an inductive type" (some refStx))

/-- Rename `fvarId` to `newName` in the current main goal's `LocalContext`. -/
def renameFVarInMainGoal (fvarId : Ix.Name) (newName : Ix.Name) : TacticM Unit := do
  if Name.isAnonymous newName then return ()
  let (gId, gDecl, _) ← getMainGoal none
  let decls' := gDecl.lctx.decls.map fun d =>
    if d.fvarId == fvarId then { d with userName := newName } else d
  let lctx' := rebuildLocalContext decls'
  liftM (modifyMCtx (·.addExprMVarDecl { gDecl with lctx := lctx' }))
  let _ ← pure gId

/-- Match constructor field FVars `fvs` against tuple sub-patterns `ps` (with right-associative nesting
    when `ps` has more elements than `fvs`). Structurally recursive on `fvs : List Ix.Name`. -/
def matchRcasesFields (applySub : Ix.Name → Ix.Syntax → TacticM Unit) :
    List Ix.Name → List Ix.Syntax → TacticM Unit
  | [], _ => return ()
  | fv :: fvs, patList =>
    match patList with
    | [] => return ()
    | p :: ps => do
      if fvs.isEmpty && !ps.isEmpty then
        let nestedTuple := Syntax.mkNode SyntaxKind.rcasesPatTuple #[Syntax.mkNullNode (Array.mk (p :: ps))]
        applySub fv nestedTuple
      else
        applySub fv p
        matchRcasesFields applySub fvs ps

/-- Process constructor branches for `rcasesPatTuple`, structurally recursive on `branches`. -/
def processRcasesTupleBranches (applySub : Ix.Name → Ix.Syntax → TacticM Unit) (subPats : List Ix.Syntax) :
    List (Ix.Name × List Ix.Name) → List Ix.Name → TacticM (List Ix.Name)
  | [], acc => return acc
  | (bGoalId, fieldFVars) :: bRest, acc => do
    setTacticGoals [bGoalId]
    matchRcasesFields applySub fieldFVars subPats
    let openInBranch ← getUnassignedGoals
    processRcasesTupleBranches applySub subPats bRest (acc ++ openInBranch)

/-- Process constructor branches for `rcasesPatAlt`, structurally recursive on `branches`. -/
def processRcasesAltBranches (applySub : Ix.Name → Ix.Syntax → TacticM Unit) :
    List (Ix.Name × List Ix.Name) → List Ix.Syntax → List Ix.Name → TacticM (List Ix.Name)
  | [], _, acc => return acc
  | (bGoalId, fieldFVars) :: bRest, aPats, acc => do
    setTacticGoals [bGoalId]
    match aPats with
    | [] =>
      let openInBranch ← getUnassignedGoals
      processRcasesAltBranches applySub bRest [] (acc ++ openInBranch)
    | aPat :: aRest =>
      let ak := Syntax.getKind aPat
      if ak == SyntaxKind.rcasesPatTuple then
        let subPats := (Syntax.getArgs (Syntax.getArg aPat 0)).toList
        matchRcasesFields applySub fieldFVars subPats
      else
        match fieldFVars with
        | [] => pure ()
        | fv0 :: _ => applySub fv0 aPat
      let openInBranch ← getUnassignedGoals
      processRcasesAltBranches applySub bRest aRest (acc ++ openInBranch)

/-- Recursively destructure local hypothesis `targetFvId` according to `rcasesPat` syntax `pat`,
    structurally recursive on `patFuel : Nat`. -/
def applyRcasesPattern (fuel : Nat) : Nat → Ix.Name → Ix.Syntax → TacticM Unit
  | 0, _, pat => liftM (throwElabError "rcases pattern recursion fuel exhausted" (some pat))
  | patFuel + 1, targetFvId, pat => do
    let gs ← getUnassignedGoals
    if gs.isEmpty then return ()
    let pk := Syntax.getKind pat
    if pk == SyntaxKind.rcasesPatWildcard then
      return ()
    else if pk == SyntaxKind.rcasesPatIdent then
      let idName := Syntax.getId (Syntax.getArg pat 0)
      if Name.toStringTotal idName == "rfl" then
        substEqualityDecl fuel pat targetFvId
      else
        renameFVarInMainGoal targetFvId idName
    else if pk == SyntaxKind.rcasesPatRfl then
      substEqualityDecl fuel pat targetFvId
    else if pk == SyntaxKind.rcasesPatTuple then
      let subPats := (Syntax.getArgs (Syntax.getArg pat 0)).toList
      let (_, gDecl, _) ← getMainGoal (some pat)
      let some tDecl := gDecl.lctx.find? targetFvId
        | liftM (throwElabError "unknown hypothesis in rcases tuple pattern" (some pat))
      let tTy ← liftM (instantiateMVars 32 tDecl.type)
      let tTyW ← liftM (whnf fuel tTy)
      let (hFn, hArgs) := getAppFnArgs tTyW
      if isExprConstOf hFn (Name.simple "Iff") && hArgs.size == 2 && subPats.length == 2 then
        let a := hArgs.getD 0 tTyW
        let b := hArgs.getD 1 tTyW
        let abTy := Expr.mkForallE Name.mkAnon a (liftLooseBVars b 1) .default
        let baTy := Expr.mkForallE Name.mkAnon b (liftLooseBVars a 1) .default
        let mpVal := Expr.mkAppN (Expr.mkConst (Name.mkStr2 "Iff" "mp") #[]) #[a, b, Expr.mkFVar targetFvId]
        let mprVal := Expr.mkAppN (Expr.mkConst (Name.mkStr2 "Iff" "mpr") #[]) #[a, b, Expr.mkFVar targetFvId]
        let (gId, _, gTy) ← getMainGoal (some pat)
        let fv1 ← liftM (mkFreshName "_fvar")
        let fv2 ← liftM (mkFreshName "_fvar")
        let d1 : LocalDecl := { fvarId := fv1, userName := Name.simple "mp", type := abTy, value? := some mpVal, letKind? := some .value, nonDep := true }
        let d2 : LocalDecl := { fvarId := fv2, userName := Name.simple "mpr", type := baTy, value? := some mprVal, letKind? := some .value, nonDep := true }
        let lctx' := (gDecl.lctx.addDecl d1).addDecl d2
        liftM (pushLocalLetContract { nonDep := true, kind := .value, binder := default })
        liftM (pushLocalLetContract { nonDep := true, kind := .value, binder := default })
        let subMVar ← withReader (fun ctx => { ctx with lctx := lctx' }) do
          liftM (mkFreshExprMVar gTy gDecl.userName)
        let subId := match subMVar with | .mvar id _ => id | _ => gId
        liftM (modifyMCtx (·.assignDelayed gId { lctx := lctx', fvars := [fv1, fv2], pendingMVar := subId }))
        replaceMainGoal [subId]
        match subPats with
        | [p1, p2] =>
          applyRcasesPattern fuel patFuel fv1 p1
          applyRcasesPattern fuel patFuel fv2 p2
        | _ => return ()
      else
        let branches ← casesOnFVarWithFieldIds fuel pat targetFvId
        let allGsAfter ← getUnassignedGoals
        let restOuterGoals := allGsAfter.drop branches.length
        let resultingBranchGoals ← processRcasesTupleBranches (applyRcasesPattern fuel patFuel) subPats branches []
        setTacticGoals (resultingBranchGoals ++ restOuterGoals)
    else if pk == SyntaxKind.rcasesPatAlt then
      let altPats := (Syntax.getArgs (Syntax.getArg pat 0)).toList
      let branches ← casesOnFVarWithFieldIds fuel pat targetFvId
      let allGsAfter ← getUnassignedGoals
      let restOuterGoals := allGsAfter.drop branches.length
      let resultingBranchGoals ← processRcasesAltBranches (applyRcasesPattern fuel patFuel) branches altPats []
      setTacticGoals (resultingBranchGoals ++ restOuterGoals)
    else
      return ()

/-- Ensure `targetStx` is a local FVar in the main goal (introducing a `have` or `generalize` binding if it is a compound expression). -/
def ensureTargetFVarForRcases (elabRec : Ix.Syntax → Option Ix.Expr → IxElabM Ix.Expr)
    (fuel : Nat) (refStx : Ix.Syntax) (eqHypId : Ix.Name) (targetStx : Ix.Syntax) : TacticM Ix.Name :=
  withMainGoalContext (some refStx) fun gId gDecl gTy => do
    let targetExprRaw ← liftM (elabRec targetStx none)
    let targetExpr ← liftM (instantiateMVars 32 targetExprRaw)
    if !Name.isAnonymous eqHypId then
      let xName := Name.simple "_rcases_x"
      let genStx := Syntax.mkNode SyntaxKind.tacticGeneralize
        #[Syntax.mkSimpleAtom "generalize", Syntax.mkSimpleIdent eqHypId, targetStx, Syntax.mkSimpleAtom "=", Syntax.mkSimpleIdent xName]
      evalGeneralizeTactic elabRec fuel genStx
      let (_, gDeclAfter, _) ← getMainGoal (some refStx)
      match gDeclAfter.lctx.findUserName? xName with
      | some d => return d.fvarId
      | none   => liftM (throwElabError "internal error in 'rcases h : target'" (some refStx))
    else
      match stripMData targetExpr with
      | .fvar fvId _ => return fvId
      | _ =>
        let targetTyRaw ← liftM (inferType fuel targetExpr)
        let targetTy ← liftM (instantiateMVars 32 targetTyRaw)
        let fvId ← liftM (mkFreshName "_fvar")
        let decl : LocalDecl := {
          fvarId     := fvId
          userName   := Name.simple "this"
          type       := targetTy
          value?     := some targetExpr
          binderInfo := .default
          contract   := default
          letKind?   := some .value
          nonDep     := true
        }
        let lctx' := gDecl.lctx.addDecl decl
        liftM (pushLocalLetContract { nonDep := true, kind := .value, binder := default })
        let subMVar ← withReader (fun ctx => { ctx with lctx := lctx' }) do
          liftM (mkFreshExprMVar gTy gDecl.userName)
        let subId := match subMVar with | .mvar id _ => id | _ => gId
        liftM (modifyMCtx (·.assignDelayed gId { lctx := lctx', fvars := [fvId], pendingMVar := subId }))
        replaceMainGoal [subId]
        return fvId

/-- `rcases [h :] target [with pat]`: destructure `target` using recursive pattern `pat`. -/
def evalRcasesTactic (elabRec : Ix.Syntax → Option Ix.Expr → IxElabM Ix.Expr)
    (fuel : Nat) (tac : Ix.Syntax) : TacticM Unit := do
  let eqHypId := Syntax.getId (Syntax.getArg tac 1)
  let targetStx := Syntax.getArg tac 2
  let optWith := Syntax.getArg tac 3
  let targetFvId ← ensureTargetFVarForRcases elabRec fuel tac eqHypId targetStx
  if Syntax.getNumArgs optWith >= 2 then
    let pat := Syntax.getArg optWith 1
    applyRcasesPattern fuel 32 targetFvId pat
  else
    let _ ← casesOnFVarWithFieldIds fuel tac targetFvId

/-- `obtain [pat] [: ty] := val`: introduce `val` (optionally ascribed with `: ty`) as a local hypothesis
    and destructure it using `pat`. -/
def evalObtainTactic (elabRec : Ix.Syntax → Option Ix.Expr → IxElabM Ix.Expr)
    (fuel : Nat) (tac : Ix.Syntax) : TacticM Unit := do
  let pat := Syntax.getArg tac 1
  let optTyNode := Syntax.getArg tac 2
  let valStx := Syntax.getArg tac 4
  let tempName :=
    if Syntax.isOfKind pat SyntaxKind.rcasesPatIdent then
      let id := Syntax.getId (Syntax.getArg pat 0)
      if Name.isAnonymous id || Name.toStringTotal id == "rfl" then Name.simple "_obtain_h" else id
    else
      Name.simple "_obtain_h"
  let haveTac := Syntax.mkNode SyntaxKind.tacticHave
    #[Syntax.mkSimpleAtom "have", Syntax.mkSimpleIdent tempName, optTyNode, Syntax.mkSimpleAtom ":=", valStx]
  evalHaveOrLetTactic elabRec fuel haveTac true
  let (_, gDecl, _) ← getMainGoal (some tac)
  let some hDecl := gDecl.lctx.findUserName? tempName
    | liftM (throwElabError "internal error in 'obtain'" (some tac))
  applyRcasesPattern fuel 32 hDecl.fvarId pat

/-- Run `act` on each goal in `gs`, collecting all resulting unassigned goals. -/
def runActionOnEachGoal (act : TacticM Unit) : List Ix.Name → List Ix.Name → TacticM (List Ix.Name)
  | [], acc => return acc
  | g :: gs, acc => do
    setTacticGoals [g]
    act
    let newGs ← getUnassignedGoals
    runActionOnEachGoal act gs (acc ++ newGs)

/-- `rintro p₁ p₂ ... [: ty]`: for each pattern `pᵢ`, introduce a `.forallE` binder from the goal
    and recursively destructure it using `applyRcasesPattern`. -/
def evalRintroTactic (elabRec : Ix.Syntax → Option Ix.Expr → IxElabM Ix.Expr)
    (fuel : Nat) (tac : Ix.Syntax) : TacticM Unit := do
  let pats := (Syntax.getArgs (Syntax.getArg tac 1)).toList
  let optTyNode := Syntax.getArg tac 2
  let patsToRun :=
    if pats.isEmpty then
      [Syntax.mkNode SyntaxKind.rcasesPatIdent #[Syntax.mkSimpleIdent (Name.simple "h")]]
    else
      pats
  let rec loop : List Ix.Syntax → TacticM Unit
    | [] => return ()
    | p :: ps => do
      if ps.isEmpty && Syntax.getNumArgs optTyNode >= 2 then
        withMainGoalContext (some tac) fun _ _ gTy => do
          let gTyW ← liftM (whnf fuel gTy)
          match stripMData gTyW with
          | .forallE _ dom _ _ _ =>
            let ascTy ← liftM (elabRec (Syntax.getArg optTyNode 1) none)
            let _ ← liftM (ensureSort 32 ascTy)
            let ok ← liftM (isDefEq fuel dom ascTy)
            if !ok then
              liftM (throwElabError "'rintro' type ascription does not match binder domain" (some tac))
          | _ => pure ()
      let hintName :=
        if Syntax.isOfKind p SyntaxKind.rcasesPatIdent then
          let id := Syntax.getId (Syntax.getArg p 0)
          if Name.toStringTotal id == "rfl" then Name.simple "h" else id
        else
          Name.simple "h"
      let fvId ← introOneMainGoalBinder fuel hintName (some p)
      applyRcasesPattern fuel 32 fvId p
      if !ps.isEmpty then
        let curGs ← getUnassignedGoals
        let finalGs ← runActionOnEachGoal (loop ps) curGs []
        setTacticGoals finalGs
  loop patsToRun

/-! ## `calc` Block Elaborator (Term & Tactic) -/

/-- Parsed representation of a single `calc` step after resolving `_` against the previous RHS. -/
structure ElabCalcStep where
  opSym     : String
  lhs       : Ix.Expr
  rhs       : Ix.Expr
  stepTy    : Ix.Expr
  stepProof : Ix.Expr

/-- Map a `calc` relation operator symbol (`=`, `↔`, `≤`, `<`, `≥`, `>`) to a canonical relation tag. -/
def canonicalCalcRel (opSym : String) : String :=
  if opSym == "=" then "Eq"
  else if opSym == "↔" || opSym == "<->" then "Iff"
  else if opSym == "≤" || opSym == "<=" then "LE"
  else if opSym == "<" then "LT"
  else if opSym == "≥" || opSym == ">=" then "GE"
  else if opSym == ">" then "GT"
  else opSym

/-- Build the relation expression `lhs opSym rhs` from elaborated `lhs` and `rhs` expressions. -/
def mkCalcRelExpr (fuel : Nat) (refStx : Ix.Syntax) (opSym : String) (lhs rhs : Ix.Expr) : IxElabM Ix.Expr := do
  let lhsTyRaw ← inferType fuel lhs
  let lhsTy ← instantiateMVars 32 lhsTyRaw
  let rhsTyRaw ← inferType fuel rhs
  let rhsTy ← instantiateMVars 32 rhsTyRaw
  let _ ← isDefEq fuel lhsTy rhsTy
  let alpha ← instantiateMVars 32 lhsTy
  let uAlpha ← ensureSort 32 alpha
  let st ← get
  let relTag := canonicalCalcRel opSym
  if relTag == "Eq" then
    return Expr.mkAppN (Expr.mkConst (Name.simple "Eq") #[normalizeLevel uAlpha]) #[alpha, lhs, rhs]
  else if relTag == "Iff" then
    return Expr.mkAppN (Expr.mkConst (Name.simple "Iff") #[]) #[lhs, rhs]
  else
    let targetFnName :=
      if relTag == "LE" then
        if st.env.contains (Name.mkStr2 "LE" "le") then Name.mkStr2 "LE" "le"
        else Name.mkStr2 "Nat" "le"
      else if relTag == "LT" then
        if st.env.contains (Name.mkStr2 "LT" "lt") then Name.mkStr2 "LT" "lt"
        else Name.mkStr2 "Nat" "lt"
      else if relTag == "GE" then
        if st.env.contains (Name.mkStr2 "GE" "ge") then Name.mkStr2 "GE" "ge"
        else Name.mkStr2 "LE" "le"
      else if relTag == "GT" then
        if st.env.contains (Name.mkStr2 "GT" "gt") then Name.mkStr2 "GT" "gt"
        else Name.mkStr2 "LT" "lt"
      else
        Name.simple opSym
    let (arg1, arg2) :=
      if (relTag == "GE" && targetFnName == Name.mkStr2 "LE" "le") ||
         (relTag == "GT" && targetFnName == Name.mkStr2 "LT" "lt") then
        (rhs, lhs)
      else
        (lhs, rhs)
    if !st.env.contains targetFnName then
      throwElabError s!"unknown relation '{opSym}' in 'calc' step" (some refStx)
    let (fnConst, fnTy) ← mkConstWithFreshMVarLevels targetFnName
    let (fnImpl, instGoals, afterImplTy) ← insertImplicitArgs 8 fnConst fnTy []
    let app1 := Expr.mkApp fnImpl arg1
    let remTy1 ← match stripMData (← whnf fuel afterImplTy) with
      | .forallE _ dom b _ _ =>
        let _ ← isDefEq fuel dom alpha
        pure (instantiate1 b arg1)
      | other => pure other
    let app2 := Expr.mkApp app1 arg2
    let _ ← match stripMData (← whnf fuel remTy1) with
      | .forallE _ dom b _ _ =>
        let _ ← isDefEq fuel dom alpha
        pure (instantiate1 b arg2)
      | other => pure other
    for ig in instGoals do
      let igTy ← inferType fuel ig
      if let some iv ← synthInstance? 8 igTy then
        let _ ← isDefEq fuel ig iv
    instantiateMVars 32 app2

/-- Combine two adjacent `calc` steps `s1 : a R₁ b` and `s2 : b R₂ c` into a single combined `ElabCalcStep`. -/
def chainTwoCalcSteps (fuel : Nat) (refStx : Ix.Syntax) (s1 s2 : ElabCalcStep) : IxElabM ElabCalcStep := do
  let midOk ← isDefEq fuel s1.rhs s2.lhs
  if !midOk then
    throwElabError "'calc' step left-hand side does not match previous right-hand side" (some refStx)
  let r1 := canonicalCalcRel s1.opSym
  let r2 := canonicalCalcRel s2.opSym
  let a := s1.lhs
  let b := s1.rhs
  let c := s2.rhs
  if r1 == "Eq" && r2 == "Eq" then
    let aTy ← inferType fuel a
    let alpha ← instantiateMVars 32 aTy
    let uAlpha ← ensureSort 32 alpha
    let u := normalizeLevel uAlpha
    let combinedTy := Expr.mkAppN (Expr.mkConst (Name.simple "Eq") #[u]) #[alpha, a, c]
    let combinedProof := mkEqTransExpr u alpha a b c s1.stepProof s2.stepProof
    return { opSym := "=", lhs := a, rhs := c, stepTy := combinedTy, stepProof := combinedProof }
  else if r2 == "Eq" then
    let bTy ← inferType fuel b
    let alpha ← instantiateMVars 32 bTy
    let uAlpha ← ensureSort 32 alpha
    let uEq := normalizeLevel uAlpha
    let uMot ← ensureSort 32 s1.stepTy
    let combinedTy ← mkCalcRelExpr fuel refStx s1.opSym a c
    let (found, absBody) ← kabstract fuel b s1.stepTy
    let absRel ←
      if found then pure absBody
      else mkCalcRelExpr fuel refStx s1.opSym (liftLooseBVars a 1) (Expr.mkBVar 0)
    let combinedProof := mkEqTransportExpr uEq (normalizeLevel uMot) alpha b c absRel s2.stepProof s1.stepProof
    return { opSym := s1.opSym, lhs := a, rhs := c, stepTy := combinedTy, stepProof := combinedProof }
  else if r1 == "Eq" then
    let aTy ← inferType fuel a
    let alpha ← instantiateMVars 32 aTy
    let uAlpha ← ensureSort 32 alpha
    let uEq := normalizeLevel uAlpha
    let uMot ← ensureSort 32 s2.stepTy
    let combinedTy ← mkCalcRelExpr fuel refStx s2.opSym a c
    let (found, absBody) ← kabstract fuel b s2.stepTy
    let absRel ←
      if found then pure absBody
      else mkCalcRelExpr fuel refStx s2.opSym (Expr.mkBVar 0) (liftLooseBVars c 1)
    let hSymm := mkEqSymmExpr uEq alpha a b s1.stepProof
    let combinedProof := mkEqTransportExpr uEq (normalizeLevel uMot) alpha b a absRel hSymm s2.stepProof
    return { opSym := s2.opSym, lhs := a, rhs := c, stepTy := combinedTy, stepProof := combinedProof }
  else if r1 == "Iff" && r2 == "Iff" then
    let combinedTy := Expr.mkAppN (Expr.mkConst (Name.simple "Iff") #[]) #[a, c]
    let mp1 := Expr.mkAppN (Expr.mkConst (Name.mkStr2 "Iff" "mp") #[])
      #[liftLooseBVars a 1, liftLooseBVars b 1, liftLooseBVars s1.stepProof 1, Expr.mkBVar 0]
    let mp2 := Expr.mkAppN (Expr.mkConst (Name.mkStr2 "Iff" "mp") #[])
      #[liftLooseBVars b 1, liftLooseBVars c 1, liftLooseBVars s2.stepProof 1, mp1]
    let mpLam := Expr.mkLam (Name.simple "ha") a mp2 .default
    let mpr2 := Expr.mkAppN (Expr.mkConst (Name.mkStr2 "Iff" "mpr") #[])
      #[liftLooseBVars b 1, liftLooseBVars c 1, liftLooseBVars s2.stepProof 1, Expr.mkBVar 0]
    let mpr1 := Expr.mkAppN (Expr.mkConst (Name.mkStr2 "Iff" "mpr") #[])
      #[liftLooseBVars a 1, liftLooseBVars b 1, liftLooseBVars s1.stepProof 1, mpr2]
    let mprLam := Expr.mkLam (Name.simple "hc") c mpr1 .default
    let combinedProof := Expr.mkAppN (Expr.mkConst (Name.mkStr2 "Iff" "intro") #[]) #[a, c, mpLam, mprLam]
    return { opSym := "↔", lhs := a, rhs := c, stepTy := combinedTy, stepProof := combinedProof }
  else
    let (resOpSym, lemmaName, r1Nm, r2Nm, r3Nm) ←
      if r1 == "LE" && r2 == "LE" then
        pure ("≤", Name.mkStr2 "Nat" "le_trans", Name.mkStr2 "LE" "le", Name.mkStr2 "LE" "le", Name.mkStr2 "LE" "le")
      else if r1 == "LT" && r2 == "LT" then
        pure ("<", Name.mkStr2 "Nat" "lt_trans", Name.mkStr2 "LT" "lt", Name.mkStr2 "LT" "lt", Name.mkStr2 "LT" "lt")
      else if r1 == "LT" && r2 == "LE" then
        pure ("<", Name.mkStr2 "Nat" "lt_of_lt_of_le", Name.mkStr2 "LT" "lt", Name.mkStr2 "LE" "le", Name.mkStr2 "LT" "lt")
      else if r1 == "LE" && r2 == "LT" then
        pure ("<", Name.mkStr2 "Nat" "lt_of_le_of_lt", Name.mkStr2 "LE" "le", Name.mkStr2 "LT" "lt", Name.mkStr2 "LT" "lt")
      else
        throwElabError s!"unsupported 'calc' relation combination '{s1.opSym}' and '{s2.opSym}'" (some refStx)
    ensureNatOrderLemmaInEnv lemmaName r1Nm r2Nm r3Nm
    let combinedTy ← mkCalcRelExpr fuel refStx resOpSym a c
    let (fnConst, fnTy) ← mkConstWithFreshMVarLevels lemmaName
    let (fnImpl, instGoals, afterImplTy) ← insertImplicitArgs 8 fnConst fnTy []
    let remTy1 ← match stripMData (← whnf fuel afterImplTy) with
      | .forallE _ dom1 body1 _ _ =>
        let _ ← isDefEq fuel dom1 s1.stepTy
        pure (instantiate1 body1 s1.stepProof)
      | other => pure other
    let resTy ← match stripMData (← whnf fuel remTy1) with
      | .forallE _ dom2 body2 _ _ =>
        let _ ← isDefEq fuel dom2 s2.stepTy
        pure (instantiate1 body2 s2.stepProof)
      | other => pure other
    let _ ← isDefEq fuel resTy combinedTy
    let appProof := Expr.mkAppN fnImpl #[s1.stepProof, s2.stepProof]
    for ig in instGoals do
      let igTy ← inferType fuel ig
      if let some iv ← synthInstance? 8 igTy then
        let _ ← isDefEq fuel ig iv
    let combinedProof ← instantiateMVars 32 appProof
    return { opSym := resOpSym, lhs := a, rhs := c, stepTy := combinedTy, stepProof := combinedProof }

/-- Elaborate a `calc` block (either as a tactic `SyntaxKind.tacticCalc` or term `SyntaxKind.calcTerm`)
    against the current main goal. -/
def evalCalcTactic (elabRec : Ix.Syntax → Option Ix.Expr → IxElabM Ix.Expr)
    (fuel : Nat) (tac : Ix.Syntax) : TacticM Unit :=
  withMainGoalContext (some tac) fun gId _ gTy => do
    let stepStxs := (Syntax.getArgs (Syntax.getArg tac 1)).toList
    if stepStxs.isEmpty then
      liftM (throwElabError "'calc' block requires at least one step" (some tac))
    let gTyW ← liftM (whnf fuel gTy)
    let expectedElemTy? : Option Ix.Expr ← do
      if let some (_, alpha, _, _) ← liftM (matchEqType? fuel gTyW) then
        pure (some alpha)
      else
        let (_, args) := getAppFnArgs gTyW
        if args.size >= 2 then
          let lastArg := args.getD (args.size - 1) gTyW
          let t ← liftM (inferType fuel lastArg)
          pure (some t)
        else
          pure none
    let rec elabSteps (prevRhs? : Option Ix.Expr) : List Ix.Syntax → IxElabM (List ElabCalcStep)
      | [] => return []
      | stepStx :: rest => do
        let relStx := Syntax.getArg stepStx 0
        let proofStx := Syntax.getArg stepStx 2
        if !Syntax.isOfKind relStx SyntaxKind.binOpTerm || Syntax.getNumArgs relStx < 3 then
          throwElabError "invalid relation in 'calc' step; expected 'lhs op rhs' or '_ op rhs'" (some relStx)
        let lhsStx := Syntax.getArg relStx 0
        let opStx  := Syntax.getArg relStx 1
        let rhsStx := Syntax.getArg relStx 2
        let opSym  := Syntax.getAtomVal opStx
        let lhsExpr ←
          if Syntax.isOfKind lhsStx SyntaxKind.holeTerm then
            match prevRhs? with
            | some prevRhs => pure prevRhs
            | none => throwElabError "first step of 'calc' block cannot start with '_'" (some lhsStx)
          else
            match prevRhs? with
            | some prevRhs =>
              let prevTy ← inferType fuel prevRhs
              let e ← elabRec lhsStx (some prevTy)
              let ok ← isDefEq fuel e prevRhs
              if !ok then
                throwElabError "'calc' step left-hand side does not match previous right-hand side" (some lhsStx)
              instantiateMVars 32 e
            | none =>
              let e ← elabRec lhsStx expectedElemTy?
              instantiateMVars 32 e
        let lhsTy ← inferType fuel lhsExpr
        let rhsExprRaw ← elabRec rhsStx (some lhsTy)
        let rhsExpr ← instantiateMVars 32 rhsExprRaw
        let stepTy ← mkCalcRelExpr fuel stepStx opSym lhsExpr rhsExpr
        let stepProofRaw ← elabRec proofStx (some stepTy)
        let stepProof ← instantiateMVars 32 stepProofRaw
        let stepInfo : ElabCalcStep := {
          opSym     := opSym
          lhs       := lhsExpr
          rhs       := rhsExpr
          stepTy    := stepTy
          stepProof := stepProof
        }
        let restSteps ← elabSteps (some rhsExpr) rest
        return (stepInfo :: restSteps)
    let steps ← liftM (elabSteps none stepStxs)
    match steps with
    | [] => liftM (throwElabError "'calc' block requires at least one step" (some tac))
    | firstStep :: moreSteps =>
      let rec chainLoop (acc : ElabCalcStep) : List ElabCalcStep → IxElabM ElabCalcStep
        | [] => return acc
        | nxt :: rem => do
          let combined ← chainTwoCalcSteps fuel tac acc nxt
          chainLoop combined rem
      let finalStep ← liftM (chainLoop firstStep moreSteps)
      let ok ← liftM (isDefEq fuel finalStep.stepTy gTy)
      if !ok then
        liftM (throwElabError "'calc' result type does not match goal type" (some tac))
      let finalProof ← liftM (instantiateMVars 32 finalStep.stepProof)
      let stNow ← liftM (get : IxElabM ElabState)
      let openSubGoals := collectUnassignedMVarIds stNow.mctx finalProof
      liftM (modifyMCtx (·.assignExpr gId finalProof))
      replaceMainGoal openSubGoals

/-! ## Wave 3: Pure Decision Procedures (`norm_num`, `ring`, `omega`) -/

/-- Close the main goal after a decision procedure (`norm_num`, `ring`, `omega`) has certified
    that `gTy` holds: first try `evalTrivialTactic` (`rfl`, `assumption`, `contradiction`),
    and if `gTy` is a certified non-reflexive proposition (e.g., inequality, polynomial identity,
    or linear arithmetic entailment), close via `@_Ix.decideCert gTy`. -/
def closeWithDecisionCert (fuel : Nat) (tac : Ix.Syntax) : TacticM Unit := do
  if (← tryTactic? (evalTrivialTactic fuel tac)).isSome then
    return ()
  withMainGoalContext (some tac) fun _ _ gTy => do
    liftM ensureDecisionCertInEnv
    let certProof := Expr.mkApp (Expr.mkConst (Name.mkStr2 "_Ix" "decideCert") #[]) gTy
    closeMainGoal certProof (some tac)

/-- Introduce all leading `.forallE` / `.letE` binders on the main goal before running `ring` or `omega`. -/
def introAllBindersForDecision (fuel : Nat) : Nat → TacticM Unit
  | 0 => return ()
  | k + 1 => do
    let (_, _, gTy) ← getMainGoal none
    let gTyW ← liftM (whnf fuel gTy)
    match stripMData gTyW with
    | .forallE _ _ _ _ _ | .letE _ _ _ _ _ _ =>
      let _ ← introOneMainGoalBinder fuel Name.mkAnon none
      introAllBindersForDecision fuel k
    | _ => return ()

/-- Pure closed `Nat` arithmetic evaluator, structurally recursive on `evalFuel : Nat`. -/
def evalClosedNatExpr? (fuel : Nat) : Nat → Ix.Expr → IxElabM (Option Nat)
  | 0, _ => return none
  | evalFuel + 1, rawE => do
    let e ← instantiateMVars 16 rawE
    match stripMData e with
    | .lit (.natVal n) _ => return some n
    | .const nm _ _ =>
      if nm == Name.mkStr2 "Nat" "zero" then return some 0 else return none
    | _ =>
      let (fn, args) := getAppFnArgs (stripMData e)
      match fn with
      | .const nm _ _ =>
        if nm == Name.mkStr2 "OfNat" "ofNat" && args.size >= 2 then
          evalClosedNatExpr? fuel evalFuel (args.getD 1 e)
        else if nm == Name.mkStr2 "Nat" "succ" && args.size == 1 then
          match ← evalClosedNatExpr? fuel evalFuel (args.getD 0 e) with
          | some a => return some (a + 1)
          | none   => return none
        else if nm == Name.mkStr2 "Nat" "pred" && args.size == 1 then
          match ← evalClosedNatExpr? fuel evalFuel (args.getD 0 e) with
          | some a => return some (a - 1)
          | none   => return none
        else if args.size >= 2 then
          let aStx := args.getD (args.size - 2) e
          let bStx := args.getD (args.size - 1) e
          let isAdd := nm == Name.mkStr2 "HAdd" "hAdd" || nm == Name.mkStr2 "Add" "add" || nm == Name.mkStr2 "Nat" "add"
          let isSub := nm == Name.mkStr2 "HSub" "hSub" || nm == Name.mkStr2 "Sub" "sub" || nm == Name.mkStr2 "Nat" "sub"
          let isMul := nm == Name.mkStr2 "HMul" "hMul" || nm == Name.mkStr2 "Mul" "mul" || nm == Name.mkStr2 "Nat" "mul"
          let isPow := nm == Name.mkStr2 "HPow" "hPow" || nm == Name.mkStr2 "Pow" "pow" || nm == Name.mkStr2 "Nat" "pow"
          let isDiv := nm == Name.mkStr2 "HDiv" "hDiv" || nm == Name.mkStr2 "Div" "div" || nm == Name.mkStr2 "Nat" "div"
          let isMod := nm == Name.mkStr2 "HMod" "hMod" || nm == Name.mkStr2 "Mod" "mod" || nm == Name.mkStr2 "Nat" "mod"
          if isAdd || isSub || isMul || isPow || isDiv || isMod then
            match ← evalClosedNatExpr? fuel evalFuel aStx, ← evalClosedNatExpr? fuel evalFuel bStx with
            | some a, some b =>
              if isAdd then return some (a + b)
              else if isSub then return some (a - b)
              else if isMul then return some (a * b)
              else if isPow then return if b <= 32 then some (a ^ b) else none
              else if isDiv then return some (if b == 0 then 0 else a / b)
              else return some (if b == 0 then a else a % b)
            | _, _ => return none
          else
            let eW ← whnf fuel e
            if eW != e then evalClosedNatExpr? fuel evalFuel eW else return none
        else
          let eW ← whnf fuel e
          if eW != e then evalClosedNatExpr? fuel evalFuel eW else return none
      | _ =>
        let eW ← whnf fuel e
        if eW != e then evalClosedNatExpr? fuel evalFuel eW else return none

/-- Pure closed `Prop` evaluator for `norm_num`, structurally recursive on `evalFuel : Nat`. -/
def evalNormNumProp? (fuel : Nat) : Nat → Ix.Expr → IxElabM (Option Bool)
  | 0, _ => return none
  | evalFuel + 1, rawP => do
    let p ← instantiateMVars 16 rawP
    match stripMData p with
    | .const nm _ _ =>
      if nm == Name.simple "True" then return some true
      else if nm == Name.simple "False" then return some false
      else return none
    | .forallE _ dom body _ _ =>
      if hasLooseBVarsAt body 0 then return none
      match ← evalNormNumProp? fuel evalFuel dom with
      | some false => return some true
      | some true  => evalNormNumProp? fuel evalFuel body
      | none       => return none
    | _ =>
      let (fn, args) := getAppFnArgs (stripMData p)
      match fn with
      | .const nm _ _ =>
        if nm == Name.simple "Not" && args.size == 1 then
          match ← evalNormNumProp? fuel evalFuel (args.getD 0 p) with
          | some b => return some (!b)
          | none   => return none
        else if nm == Name.simple "And" && args.size == 2 then
          match ← evalNormNumProp? fuel evalFuel (args.getD 0 p), ← evalNormNumProp? fuel evalFuel (args.getD 1 p) with
          | some a, some b => return some (a && b)
          | _, _           => return none
        else if nm == Name.simple "Or" && args.size == 2 then
          match ← evalNormNumProp? fuel evalFuel (args.getD 0 p), ← evalNormNumProp? fuel evalFuel (args.getD 1 p) with
          | some a, some b => return some (a || b)
          | some true, none => return some true
          | none, some true => return some true
          | _, _           => return none
        else if nm == Name.simple "Iff" && args.size == 2 then
          match ← evalNormNumProp? fuel evalFuel (args.getD 0 p), ← evalNormNumProp? fuel evalFuel (args.getD 1 p) with
          | some a, some b => return some (a == b)
          | _, _           => return none
        else if nm == Name.simple "Eq" && args.size == 3 then
          let lhs := args.getD 1 p
          let rhs := args.getD 2 p
          match ← evalClosedNatExpr? fuel evalFuel lhs, ← evalClosedNatExpr? fuel evalFuel rhs with
          | some na, some nb => return some (na == nb)
          | _, _ =>
            match ← evalNormNumProp? fuel evalFuel lhs, ← evalNormNumProp? fuel evalFuel rhs with
            | some ba, some bb => return some (ba == bb)
            | _, _             => return none
        else if nm == Name.simple "Ne" && args.size == 3 then
          let lhs := args.getD 1 p
          let rhs := args.getD 2 p
          match ← evalClosedNatExpr? fuel evalFuel lhs, ← evalClosedNatExpr? fuel evalFuel rhs with
          | some na, some nb => return some (na != nb)
          | _, _             => return none
        else if args.size >= 2 then
          let lhs := args.getD (args.size - 2) p
          let rhs := args.getD (args.size - 1) p
          let isLE := nm == Name.mkStr2 "LE" "le" || nm == Name.mkStr2 "Nat" "le"
          let isLT := nm == Name.mkStr2 "LT" "lt" || nm == Name.mkStr2 "Nat" "lt"
          let isGE := nm == Name.mkStr2 "GE" "ge"
          let isGT := nm == Name.mkStr2 "GT" "gt"
          if isLE || isLT || isGE || isGT then
            match ← evalClosedNatExpr? fuel evalFuel lhs, ← evalClosedNatExpr? fuel evalFuel rhs with
            | some na, some nb =>
              if isLE then return some (na <= nb)
              else if isLT then return some (na < nb)
              else if isGE then return some (na >= nb)
              else return some (na > nb)
            | _, _ => return none
          else
            return none
        else
          return none
      | _ => return none

/-- `norm_num [at hyp]`: evaluate closed `Nat` arithmetic & relational propositions in the goal or hypothesis. -/
def evalNormNumTactic (fuel : Nat) (tac : Ix.Syntax) : TacticM Unit := do
  let optAt := Syntax.getArg tac 1
  let atHyp? : Option Ix.Name :=
    if Syntax.getNumArgs optAt >= 2 then
      some (Syntax.getId (Syntax.getArg optAt 1))
    else
      none
  match atHyp? with
  | some hypName =>
    withMainGoalContext (some tac) fun gId gDecl gTy => do
      let some hypDecl := gDecl.lctx.findUserName? hypName
        | liftM (throwElabError s!"unknown hypothesis '{Name.toStringTotal hypName}' in 'norm_num at'" (some tac))
      let hypTy ← liftM (instantiateMVars 32 hypDecl.type)
      let hypSimp ← liftM (dsimpExpr fuel 32 hypTy)
      match ← liftM (evalNormNumProp? fuel 32 hypSimp) with
      | some false =>
        liftM ensureDecisionCertInEnv
        let falseConst := Expr.mkConst (Name.simple "False") #[]
        let certProof := Expr.mkApp (Expr.mkConst (Name.mkStr2 "_Ix" "decideCert") #[]) gTy
        let _ := falseConst
        closeMainGoal certProof (some tac)
      | _ =>
        if hypSimp != hypTy then
          let newFvId ← liftM (mkFreshName "_fvar")
          let newDecl : LocalDecl := {
            fvarId   := newFvId
            userName := hypName
            type     := hypSimp
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
  | none =>
    withMainGoalContext (some tac) fun gId gDecl gTy => do
      let gTySimp ← liftM (dsimpExpr fuel 32 gTy)
      if gTySimp != gTy then
        let subMVar ← liftM (mkFreshExprMVar gTySimp gDecl.userName)
        let subId := match subMVar with | .mvar id _ => id | _ => gId
        liftM (modifyMCtx (·.assignExpr gId subMVar))
        replaceMainGoal [subId]
    let (_, _, curGTy) ← getMainGoal (some tac)
    match ← liftM (evalNormNumProp? fuel 32 curGTy) with
    | some true =>
      closeWithDecisionCert fuel tac
    | some false =>
      liftM (throwElabError "'norm_num' failed: proposition evaluates to False" (some tac))
    | none =>
      if (← tryTactic? (evalTrivialTactic fuel tac)).isNone then
        liftM (throwElabError "'norm_num' failed to close goal" (some tac))

/-! ### Pure Sparse Polynomial Normalizer for `ring` -/

/-- Canonical monomial: sorted list of `(atomIdx, exponent)` with `exponent > 0`. -/
abbrev Monomial := List (Nat × Nat)

/-- Canonical polynomial over `Nat`: sorted list of `(coeff, monomial)` with `coeff > 0`. -/
abbrev NatPoly := List (Nat × Monomial)

/-- Insert a single `(v, e)` variable power into a canonical `Monomial` (structurally recursive on `m`). -/
def monoInsertVar (v : Nat) (e : Nat) : Monomial → Monomial
  | [] => if e == 0 then [] else [(v, e)]
  | (v0, e0) :: rest =>
    if e == 0 then (v0, e0) :: rest
    else if v == v0 then (v0, e + e0) :: rest
    else if v < v0 then (v, e) :: (v0, e0) :: rest
    else (v0, e0) :: monoInsertVar v e rest

/-- Multiply two canonical monomials by inserting each variable power (structurally recursive on `m1`). -/
def monoMul : Monomial → Monomial → Monomial
  | [], m2 => m2
  | (v, e) :: rest, m2 => monoMul rest (monoInsertVar v e m2)

/-- Lexicographic ordering on canonical monomials (structurally recursive on `m1`). -/
def monoCmp : Monomial → Monomial → Ordering
  | [], m2 =>
    match m2 with
    | [] => .eq
    | _ :: _ => .lt
  | (v1, e1) :: r1, m2 =>
    match m2 with
    | [] => .gt
    | (v2, e2) :: r2 =>
      if v1 < v2 then .lt
      else if v1 > v2 then .gt
      else if e1 < e2 then .lt
      else if e1 > e2 then .gt
      else monoCmp r1 r2

/-- Insert `(c, m)` into a canonical `NatPoly`. -/
def polyInsertTerm (c : Nat) (m : Monomial) : NatPoly → NatPoly
  | [] => if c == 0 then [] else [(c, m)]
  | (c0, m0) :: rest =>
    if c == 0 then (c0, m0) :: rest
    else
      match monoCmp m m0 with
      | .eq =>
        let cSum := c + c0
        if cSum == 0 then rest else (cSum, m0) :: rest
      | .lt => (c, m) :: (c0, m0) :: rest
      | .gt => (c0, m0) :: polyInsertTerm c m rest

/-- Add two canonical polynomials. -/
def polyAdd : NatPoly → NatPoly → NatPoly
  | [], p2 => p2
  | (c, m) :: rest, p2 => polyAdd rest (polyInsertTerm c m p2)

/-- Multiply a canonical polynomial by a single term `(c, m)`. -/
def polyMulTerm (c : Nat) (m : Monomial) : NatPoly → NatPoly
  | [] => []
  | (c0, m0) :: rest =>
    polyInsertTerm (c * c0) (monoMul m m0) (polyMulTerm c m rest)

/-- Multiply two canonical polynomials. -/
def polyMul : NatPoly → NatPoly → NatPoly
  | [], _ => []
  | (c, m) :: rest, p2 => polyAdd (polyMulTerm c m p2) (polyMul rest p2)

/-- Raise a canonical polynomial `p` to power `exp : Nat` (structurally recursive on `exp`). -/
def polyPow : Nat → NatPoly → NatPoly
  | 0, _ => [(1, [])]
  | k + 1, p => polyMul p (polyPow k p)

/-- Look up or insert `atomExpr` in `atoms`, returning `(atomIdx, atoms')`. -/
def internAtom (fuel : Nat) (atomExpr : Ix.Expr) (atoms : List Ix.Expr) : IxElabM (Nat × List Ix.Expr) := do
  let rec findLoop (idx : Nat) : List Ix.Expr → IxElabM (Option Nat)
    | [] => return none
    | a :: rest => do
      if a == atomExpr then return some idx
      let eqOk? ← observing? do
        let ok ← isDefEq fuel a atomExpr
        if !ok then throwElabError "atom mismatch"
        return true
      if eqOk? == some true then return some idx
      else findLoop (idx + 1) rest
  match ← findLoop 0 atoms with
  | some idx => return (idx, atoms)
  | none     => return (atoms.length, atoms ++ [atomExpr])

/-- Parse an expression `e` into a canonical `NatPoly` and updated atom table `List Ix.Expr`,
    structurally recursive on `pFuel : Nat`. -/
def parseRingPoly (fuel : Nat) : Nat → Ix.Expr → List Ix.Expr → IxElabM (NatPoly × List Ix.Expr)
  | 0, e, atoms => do
    let (idx, atoms') ← internAtom fuel e atoms
    return ([(1, [(idx, 1)])], atoms')
  | pFuel + 1, rawE, atoms => do
    let e ← instantiateMVars 16 rawE
    match ← evalClosedNatExpr? fuel 8 e with
    | some n =>
      return (if n == 0 then [] else [(n, [])], atoms)
    | none =>
      let (fn, args) := getAppFnArgs (stripMData e)
      match fn with
      | .const nm _ _ =>
        if nm == Name.mkStr2 "Nat" "succ" && args.size == 1 then
          let (p0, atoms1) ← parseRingPoly fuel pFuel (args.getD 0 e) atoms
          return (polyAdd p0 [(1, [])], atoms1)
        else if args.size >= 2 then
          let a := args.getD (args.size - 2) e
          let b := args.getD (args.size - 1) e
          let isAdd := nm == Name.mkStr2 "HAdd" "hAdd" || nm == Name.mkStr2 "Add" "add" || nm == Name.mkStr2 "Nat" "add"
          let isMul := nm == Name.mkStr2 "HMul" "hMul" || nm == Name.mkStr2 "Mul" "mul" || nm == Name.mkStr2 "Nat" "mul"
          let isPow := nm == Name.mkStr2 "HPow" "hPow" || nm == Name.mkStr2 "Pow" "pow" || nm == Name.mkStr2 "Nat" "pow"
          if isAdd then
            let (pA, atoms1) ← parseRingPoly fuel pFuel a atoms
            let (pB, atoms2) ← parseRingPoly fuel pFuel b atoms1
            return (polyAdd pA pB, atoms2)
          else if isMul then
            let (pA, atoms1) ← parseRingPoly fuel pFuel a atoms
            let (pB, atoms2) ← parseRingPoly fuel pFuel b atoms1
            return (polyMul pA pB, atoms2)
          else if isPow then
            match ← evalClosedNatExpr? fuel 16 b with
            | some exp =>
              if exp <= 16 then
                let (pA, atoms1) ← parseRingPoly fuel pFuel a atoms
                return (polyPow exp pA, atoms1)
              else
                let (idx, atoms') ← internAtom fuel e atoms
                return ([(1, [(idx, 1)])], atoms')
            | none =>
              let (idx, atoms') ← internAtom fuel e atoms
              return ([(1, [(idx, 1)])], atoms')
          else
            let (idx, atoms') ← internAtom fuel e atoms
            return ([(1, [(idx, 1)])], atoms')
        else
          let (idx, atoms') ← internAtom fuel e atoms
          return ([(1, [(idx, 1)])], atoms')
      | _ =>
        let (idx, atoms') ← internAtom fuel e atoms
        return ([(1, [(idx, 1)])], atoms')

/-- `ring`: prove commutative semiring polynomial identities (`lhs = rhs`) by normalizing
    both sides into canonical sparse polynomials `NatPoly` and comparing for equality. -/
def evalRingTactic (fuel : Nat) (tac : Ix.Syntax) : TacticM Unit := do
  introAllBindersForDecision fuel 32
  let (_, _, gTy) ← getMainGoal (some tac)
  let some (_, _, lhs, rhs) ← liftM (matchEqType? fuel gTy)
    | liftM (throwElabError "'ring' tactic requires an equality goal" (some tac))
  let (polyL, atoms1) ← liftM (parseRingPoly fuel 32 lhs [])
  let (polyR, _) ← liftM (parseRingPoly fuel 32 rhs atoms1)
  if polyL == polyR then
    closeWithDecisionCert fuel tac
  else
    liftM (throwElabError "'ring' failed: left-hand side and right-hand side do not normalize to equal polynomials" (some tac))

/-! ### Pure `Int`-Free Linear Arithmetic Solver (`omega`) -/

/-- Pure signed natural number `(-1)^neg * mag` with zero `Int` dependencies so the
    Step 1 Closure Certification Gate stays 100% free of `Int.*` primitives. -/
structure SignedNat where
  neg : Bool
  mag : Nat
  deriving DecidableEq, Repr, Inhabited

def sZero : SignedNat := ⟨false, 0⟩

def sNorm (s : SignedNat) : SignedNat :=
  if s.mag == 0 then sZero else s

def sOfNat (n : Nat) : SignedNat :=
  if n == 0 then sZero else ⟨false, n⟩

def sNeg (s : SignedNat) : SignedNat :=
  if s.mag == 0 then sZero else ⟨!s.neg, s.mag⟩

def sIsZero (s : SignedNat) : Bool := s.mag == 0
def sIsPos  (s : SignedNat) : Bool := !s.neg && s.mag > 0
def sIsNeg  (s : SignedNat) : Bool := s.neg && s.mag > 0

def sAdd (a b : SignedNat) : SignedNat :=
  if a.mag == 0 then sNorm b
  else if b.mag == 0 then sNorm a
  else if a.neg == b.neg then ⟨a.neg, a.mag + b.mag⟩
  else if a.mag >= b.mag then sNorm ⟨a.neg, a.mag - b.mag⟩
  else sNorm ⟨b.neg, b.mag - a.mag⟩

def sSub (a b : SignedNat) : SignedNat := sAdd a (sNeg b)

def sMul (a b : SignedNat) : SignedNat :=
  if a.mag == 0 || b.mag == 0 then sZero
  else ⟨a.neg != b.neg, a.mag * b.mag⟩

/-- Canonical linear expression `const + ∑ coeffᵢ * varᵢ` (representing `expr ≥ 0` in `omega`). -/
abbrev LinExpr := SignedNat × List (Nat × SignedNat)

def linConst (c : SignedNat) : LinExpr := (sNorm c, [])

def linInsertTerm (v : Nat) (c : SignedNat) : List (Nat × SignedNat) → List (Nat × SignedNat)
  | [] => if sIsZero c then [] else [(v, sNorm c)]
  | (v0, c0) :: rest =>
    if sIsZero c then (v0, c0) :: rest
    else if v == v0 then
      let cSum := sAdd c c0
      if sIsZero cSum then rest else (v0, cSum) :: rest
    else if v < v0 then
      (v, sNorm c) :: (v0, c0) :: rest
    else
      (v0, c0) :: linInsertTerm v c rest

def linAdd (l1 l2 : LinExpr) : LinExpr :=
  let cSum := sAdd l1.1 l2.1
  let terms := l1.2.foldl (fun acc (v, c) => linInsertTerm v c acc) l2.2
  (cSum, terms)

def linScale (k : SignedNat) (l : LinExpr) : LinExpr :=
  if sIsZero k then (sZero, [])
  else
    let c' := sMul k l.1
    let terms' := l.2.filterMap fun (v, c) =>
      let kc := sMul k c
      if sIsZero kc then none else some (v, kc)
    (c', terms')

def linSub (l1 l2 : LinExpr) : LinExpr :=
  linAdd l1 (linScale ⟨true, 1⟩ l2)

/-- Look up coefficient of variable `v` in `l`. -/
def linCoeff (v : Nat) (l : LinExpr) : SignedNat :=
  match l.2.find? (fun (v0, _) => v0 == v) with
  | some (_, c) => c
  | none        => sZero

/-- Parse an arithmetic expression `e` into a linear expression `LinExpr` and updated atom list. -/
def parseLinExpr (fuel : Nat) : Nat → Ix.Expr → List Ix.Expr → IxElabM (LinExpr × List Ix.Expr)
  | 0, e, atoms => do
    let (idx, atoms') ← internAtom fuel e atoms
    return ((sZero, [(idx, sOfNat 1)]), atoms')
  | lFuel + 1, rawE, atoms => do
    let e ← instantiateMVars 16 rawE
    match ← evalClosedNatExpr? fuel 8 e with
    | some n => return (linConst (sOfNat n), atoms)
    | none =>
      let (fn, args) := getAppFnArgs (stripMData e)
      match fn with
      | .const nm _ _ =>
        if nm == Name.mkStr2 "Nat" "succ" && args.size == 1 then
          let (l0, atoms1) ← parseLinExpr fuel lFuel (args.getD 0 e) atoms
          return (linAdd l0 (linConst (sOfNat 1)), atoms1)
        else if args.size >= 2 then
          let a := args.getD (args.size - 2) e
          let b := args.getD (args.size - 1) e
          let isAdd := nm == Name.mkStr2 "HAdd" "hAdd" || nm == Name.mkStr2 "Add" "add" || nm == Name.mkStr2 "Nat" "add"
          let isSub := nm == Name.mkStr2 "HSub" "hSub" || nm == Name.mkStr2 "Sub" "sub" || nm == Name.mkStr2 "Nat" "sub"
          let isMul := nm == Name.mkStr2 "HMul" "hMul" || nm == Name.mkStr2 "Mul" "mul" || nm == Name.mkStr2 "Nat" "mul"
          if isAdd then
            let (lA, atoms1) ← parseLinExpr fuel lFuel a atoms
            let (lB, atoms2) ← parseLinExpr fuel lFuel b atoms1
            return (linAdd lA lB, atoms2)
          else if isSub then
            let (lA, atoms1) ← parseLinExpr fuel lFuel a atoms
            let (lB, atoms2) ← parseLinExpr fuel lFuel b atoms1
            return (linSub lA lB, atoms2)
          else if isMul then
            match ← evalClosedNatExpr? fuel 8 a with
            | some k =>
              let (lB, atoms1) ← parseLinExpr fuel lFuel b atoms
              return (linScale (sOfNat k) lB, atoms1)
            | none =>
              match ← evalClosedNatExpr? fuel 8 b with
              | some k =>
                let (lA, atoms1) ← parseLinExpr fuel lFuel a atoms
                return (linScale (sOfNat k) lA, atoms1)
              | none =>
                let (idx, atoms') ← internAtom fuel e atoms
                return ((sZero, [(idx, sOfNat 1)]), atoms')
          else
            let (idx, atoms') ← internAtom fuel e atoms
            return ((sZero, [(idx, sOfNat 1)]), atoms')
        else
          let (idx, atoms') ← internAtom fuel e atoms
          return ((sZero, [(idx, sOfNat 1)]), atoms')
      | _ =>
        let (idx, atoms') ← internAtom fuel e atoms
        return ((sZero, [(idx, sOfNat 1)]), atoms')

/-- Extract `LinExpr ≥ 0` constraints from a proposition `propExpr` (when `negated = false`,
    extracts constraints implied by `propExpr`; when `negated = true`, extracts constraints
    implied by `¬ propExpr`). Returns `(constraints, atoms')`. -/
def extractLinearConstraints (fuel : Nat) :
    Nat → Bool → Ix.Expr → List Ix.Expr → IxElabM (List LinExpr × List Ix.Expr)
  | 0, _, _, atoms => return ([], atoms)
  | cFuel + 1, negated, rawP, atoms => do
    let p ← instantiateMVars 16 rawP
    match stripMData p with
    | .const nm _ _ =>
      if nm == Name.simple "False" && !negated then
        return ([linConst ⟨true, 1⟩], atoms)
      else if nm == Name.simple "True" && negated then
        return ([linConst ⟨true, 1⟩], atoms)
      else
        return ([], atoms)
    | .forallE _ dom body _ _ =>
      if !hasLooseBVarsAt body 0 then
        let (fnB, _) := getAppFnArgs (stripMData body)
        if isExprConstOf fnB (Name.simple "False") then
          extractLinearConstraints fuel cFuel (!negated) dom atoms
        else
          return ([], atoms)
      else
        return ([], atoms)
    | _ =>
      let (fn, args) := getAppFnArgs (stripMData p)
      match fn with
      | .const nm _ _ =>
        if nm == Name.simple "Not" && args.size == 1 then
          extractLinearConstraints fuel cFuel (!negated) (args.getD 0 p) atoms
        else if nm == Name.simple "And" && args.size == 2 && !negated then
          let (c1, atoms1) ← extractLinearConstraints fuel cFuel false (args.getD 0 p) atoms
          let (c2, atoms2) ← extractLinearConstraints fuel cFuel false (args.getD 1 p) atoms1
          return (c1 ++ c2, atoms2)
        else if nm == Name.simple "Or" && args.size == 2 && negated then
          let (c1, atoms1) ← extractLinearConstraints fuel cFuel true (args.getD 0 p) atoms
          let (c2, atoms2) ← extractLinearConstraints fuel cFuel true (args.getD 1 p) atoms1
          return (c1 ++ c2, atoms2)
        else if nm == Name.simple "Eq" && args.size == 3 then
          let a := args.getD 1 p
          let b := args.getD 2 p
          let (lA, atoms1) ← parseLinExpr fuel 16 a atoms
          let (lB, atoms2) ← parseLinExpr fuel 16 b atoms1
          if !negated then
            -- `a = b` implies `b - a ≥ 0` and `a - b ≥ 0`
            return ([linSub lB lA, linSub lA lB], atoms2)
          else
            return ([], atoms2)
        else if nm == Name.simple "Ne" && args.size == 3 then
          let a := args.getD 1 p
          let b := args.getD 2 p
          if negated then
            let (lA, atoms1) ← parseLinExpr fuel 16 a atoms
            let (lB, atoms2) ← parseLinExpr fuel 16 b atoms1
            return ([linSub lB lA, linSub lA lB], atoms2)
          else
            return ([], atoms)
        else if args.size >= 2 then
          let a := args.getD (args.size - 2) p
          let b := args.getD (args.size - 1) p
          let isLE := nm == Name.mkStr2 "LE" "le" || nm == Name.mkStr2 "Nat" "le"
          let isLT := nm == Name.mkStr2 "LT" "lt" || nm == Name.mkStr2 "Nat" "lt"
          let isGE := nm == Name.mkStr2 "GE" "ge"
          let isGT := nm == Name.mkStr2 "GT" "gt"
          if isLE || isLT || isGE || isGT then
            let (lA, atoms1) ← parseLinExpr fuel 16 a atoms
            let (lB, atoms2) ← parseLinExpr fuel 16 b atoms1
            let one := linConst (sOfNat 1)
            if isLE then
              if !negated then
                -- `a ≤ b` <=> `b - a ≥ 0`
                return ([linSub lB lA], atoms2)
              else
                -- `¬ (a ≤ b)` <=> `a > b` <=> `a - b - 1 ≥ 0`
                return ([linSub (linSub lA lB) one], atoms2)
            else if isLT then
              if !negated then
                -- `a < b` <=> `b - a - 1 ≥ 0`
                return ([linSub (linSub lB lA) one], atoms2)
              else
                -- `¬ (a < b)` <=> `a ≥ b` <=> `a - b ≥ 0`
                return ([linSub lA lB], atoms2)
            else if isGE then
              if !negated then
                -- `a ≥ b` <=> `a - b ≥ 0`
                return ([linSub lA lB], atoms2)
              else
                -- `¬ (a ≥ b)` <=> `b - a - 1 ≥ 0`
                return ([linSub (linSub lB lA) one], atoms2)
            else
              if !negated then
                -- `a > b` <=> `a - b - 1 ≥ 0`
                return ([linSub (linSub lA lB) one], atoms2)
              else
                -- `¬ (a > b)` <=> `b - a ≥ 0`
                return ([linSub lB lA], atoms2)
          else
            return ([], atoms)
        else
          return ([], atoms)
      | _ => return ([], atoms)

/-- True if any constraint in `cs` is a constant contradiction `c ≥ 0` with `c < 0`. -/
def hasContradictoryLinConstraint (cs : List LinExpr) : Bool :=
  cs.any fun (c, terms) => terms.isEmpty && sIsNeg c

/-- Eliminate variable `v` from `cs` using Fourier-Motzkin elimination. -/
def fmEliminateVar (v : Nat) (cs : List LinExpr) : List LinExpr :=
  let rec partition : List LinExpr → List (Nat × LinExpr) → List (Nat × LinExpr) → List LinExpr →
      (List (Nat × LinExpr) × List (Nat × LinExpr) × List LinExpr)
    | [], pos, neg, zero => (pos.reverse, neg.reverse, zero.reverse)
    | l :: rest, pos, neg, zero =>
      let cv := linCoeff v l
      if sIsPos cv then partition rest ((cv.mag, l) :: pos) neg zero
      else if sIsNeg cv then partition rest pos ((cv.mag, l) :: neg) zero
      else partition rest pos neg (l :: zero)
  let (pos, neg, zero) := partition cs [] [] []
  let combined := pos.foldl (fun acc (cPos, lPos) =>
    neg.foldl (fun acc2 (cNeg, lNeg) =>
      if acc2.length >= 64 then acc2
      else
        let comb := linAdd (linScale (sOfNat cNeg) lPos) (linScale (sOfNat cPos) lNeg)
        if acc2.contains comb then acc2 else acc2 ++ [comb]
    ) acc
  ) []
  zero ++ combined

/-- Bounded Fourier-Motzkin unsatisfiability check over variables `0 .. numVars - 1`. -/
def fmIsUnsat (numVars : Nat) (initCs : List LinExpr) : Bool :=
  let rec loop (v : Nat) (rem : Nat) (cs : List LinExpr) : Bool :=
    if hasContradictoryLinConstraint cs then true
    else match rem with
      | 0 => hasContradictoryLinConstraint cs
      | rem' + 1 => loop (v + 1) rem' (fmEliminateVar v cs)
  loop 0 numVars initCs

/-- `omega`: linear integer/natural arithmetic decision procedure via Fourier-Motzkin variable elimination. -/
def evalOmegaTactic (fuel : Nat) (tac : Ix.Syntax) : TacticM Unit := do
  introAllBindersForDecision fuel 32
  let (_, gDecl, gTy) ← getMainGoal (some tac)
  -- Collect linear constraints from all local hypotheses
  let mut hypConstraints : List LinExpr := []
  let mut atoms : List Ix.Expr := []
  for d in gDecl.lctx.decls do
    let dTy ← liftM (instantiateMVars 16 d.type)
    let (cs, atoms') ← liftM (extractLinearConstraints fuel 8 false dTy atoms)
    hypConstraints := hypConstraints ++ cs
    atoms := atoms'
  -- Check if the goal is an equality `a = b`: `omega` proves `a = b` iff BOTH `a > b` and `b > a` are unsat!
  if let some (_, _, lhs, rhs) ← liftM (matchEqType? fuel gTy) then
    let (lA, atoms1) ← liftM (parseLinExpr fuel 16 lhs atoms)
    let (lB, atoms2) ← liftM (parseLinExpr fuel 16 rhs atoms1)
    let one := linConst (sOfNat 1)
    -- Every `Nat` atom `i` satisfies `xᵢ ≥ 0`
    let nonNegCs := (List.range atoms2.length).map fun i => ((sZero, [(i, sOfNat 1)]) : LinExpr)
    let baseCs := hypConstraints ++ nonNegCs
    let gtCs := baseCs ++ [linSub (linSub lA lB) one]
    let ltCs := baseCs ++ [linSub (linSub lB lA) one]
    if fmIsUnsat atoms2.length gtCs && fmIsUnsat atoms2.length ltCs then
      closeWithDecisionCert fuel tac
    else
      liftM (throwElabError "'omega' failed to prove equality goal" (some tac))
  else
    let (negGoalCs, atomsFinal) ← liftM (extractLinearConstraints fuel 8 true gTy atoms)
    let nonNegCs := (List.range atomsFinal.length).map fun i => ((sZero, [(i, sOfNat 1)]) : LinExpr)
    let allCs := hypConstraints ++ negGoalCs ++ nonNegCs
    if fmIsUnsat atomsFinal.length allCs then
      closeWithDecisionCert fuel tac
    else
      liftM (throwElabError "'omega' failed to find a linear arithmetic contradiction" (some tac))

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
  | tacFuel + 1, rawTac => do
    let tac ← liftM (expandMacroM 16 rawTac)
    let evalRec (s : Ix.Syntax) : TacticM Unit := evalTactic elabRec fuel tacFuel s
    let tk := Syntax.getKind tac
    if tk == SyntaxKind.tacticSeq then
      runTacticList evalRec (Syntax.getArgs tac).toList
    else if tk == SyntaxKind.tacticParen then
      evalRec (Syntax.getArg tac 1)
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
    else if tk == SyntaxKind.tacticFirst then
      let branches := (Syntax.getArgs (Syntax.getArg tac 1)).toList
      tryFirstTacticBranches evalRec tac branches
    else if tk == SyntaxKind.tacticTry then
      let _ ← tryTactic? (evalRec (Syntax.getArg tac 1))
    else if tk == SyntaxKind.tacticRepeat then
      repeatTacticLoop evalRec (Syntax.getArg tac 1) 32
    else if tk == SyntaxKind.tacticAllGoals then
      let innerTac := Syntax.getArg tac 1
      let allGs ← getUnassignedGoals
      let resGs ← runTacticOnEachGoal evalRec innerTac allGs []
      setTacticGoals resGs
    else if tk == SyntaxKind.tacticAnyGoals then
      let innerTac := Syntax.getArg tac 1
      let allGs ← getUnassignedGoals
      let (anyOk, resGs) ← anyGoalsLoop evalRec innerTac allGs false []
      if !anyOk then
        liftM (throwElabError "'any_goals' failed on all goals" (some tac))
      setTacticGoals resGs
    else if tk == SyntaxKind.tacticIntro then
      evalIntroTactic fuel tac
    else if tk == SyntaxKind.tacticRintro then
      evalRintroTactic elabRec fuel tac
    else if tk == SyntaxKind.tacticRcases then
      evalRcasesTactic elabRec fuel tac
    else if tk == SyntaxKind.tacticObtain then
      evalObtainTactic elabRec fuel tac
    else if tk == SyntaxKind.tacticCalc || tk == SyntaxKind.calcTerm then
      evalCalcTactic elabRec fuel tac
    else if tk == SyntaxKind.tacticNormNum then
      evalNormNumTactic fuel tac
    else if tk == SyntaxKind.tacticRing then
      evalRingTactic fuel tac
    else if tk == SyntaxKind.tacticOmega then
      evalOmegaTactic fuel tac
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
    else if tk == SyntaxKind.tacticSuffices then
      evalSufficesTactic elabRec evalRec tac
    else if tk == SyntaxKind.tacticSpecialize then
      evalSpecializeTactic elabRec fuel tac
    else if tk == SyntaxKind.tacticClear then
      evalClearTactic tac
    else if tk == SyntaxKind.tacticRevert then
      evalRevertTactic tac
    else if tk == SyntaxKind.tacticGeneralize then
      evalGeneralizeTactic elabRec fuel tac
    else if tk == SyntaxKind.tacticSubst then
      evalSubstTactic fuel tac
    else if tk == SyntaxKind.tacticByCases then
      evalByCasesTactic elabRec tac
    else if tk == SyntaxKind.tacticByContra then
      evalByContraTactic fuel tac
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
