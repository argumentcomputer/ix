import Ix.CompileCert.StrongEntry
import IxC.Kernel.Verify.EnvBound

/-! # The strong check indexed and on the DAG (M7 WP-F)

The strong check (`checkStrongAssociation`, through `checkAnnotatedAssociation`,
`checkInstalledAssociation` and the tower and receipt checks) decides, per source row, that
the row's type, value, rules and capabilities are the target row's under the name map. Two
things make it quadratic and worse on one global cone:

* every lookup is `Kernel.Env.find?`, a list scan, and the expression comparison
  (`checkInstalledExpr`) looks the source environment up **at every constant node**
  (`checkInstalledConstant`), the projection tables at every projection node, the literal
  pins at every literal;
* the comparison and the literal walk (`checkExprLiteralSupport`) walk the expressions as
  **trees**; the availability pass (`checkInstalledComparisonAvailability`) walks types,
  values and rules a second time only to tell `none` from `some false`.

This module decides the same functions without those costs and substitutes them by
`@[csimp]`, so `StrongCone.sound`, `artifact_strong_model_all` and every other statement and
proof keep reading the definitions in `Installed.lean`, `RuleLaws.lean`, `AnnotSupport.lean`,
`AnnotTowers.lean`, `InstalledAssociation.lean` and `StrongEntry.lean`:

* **lookups as arguments**: each check is copied with its lookups `fS fT : Lookup` as
  parameters (`…L`); at `source.find?`, `target.find?` the copy is the check (`…L_env`, by
  `rfl` or by induction for the recursive ones); the decision passes IxC's name index
  `mkFEnv` (`envFind_eq`: `(mkFEnv env).find? = env.find?`, IxC's `mkFEnv_find?`, no
  uniqueness assumed), built once per environment and check;
* **the comparison on the DAG**: `checkInstalledExprShared` is `checkInstalledExprL` with a
  memo of the pairs (source node, target node) already found equal (`some true`), keyed by
  their addresses and confirmed by identity (`withPtrEqDecEq` on both nodes), each entry
  carrying its own proof, behind `Squash` (the arrangement of IxC's `beqMemo`, whose
  `probeHit` it follows); `checkInstalledExprShared_eq` is the projection of the proof;
* **the literal walk** is skipped when both environments support `Nat` and `String`
  literals equally (`checkExprLiteralSupport_both`: it is then `true` for every
  expression), and run otherwise;
* **the availability pass** is skipped when the eight Boolean checks accept
  (`availability_of_checks`: they imply it is `some true`); otherwise it runs, indexed;
* **rows identical by pointer**: `decide (find? n = some entry)` compares a row with the
  index's row, which is the same object, through `ciDecEqShared` (`SourceExportFast.lean`).

The receipt checks (Nat, Div/Mod, reduce: a fixed list of operations, a few lookups each),
`checkInstalledPin` and `checkReservedNameMap` (one pass each) are linear already and run as
they are. Trust: the compiler's substitution on these kernel-checked equations and the
runtime's `withPtrAddr`/`withPtrEq`, as for WP-B's walks and IxC's `beqMemo`; no hash is
consulted as equality. -/

namespace Ix.CompileCert

open Kernel.Reader Kernel.Admission

/-! ## Lookups -/

abbrev Lookup := Kernel.Name → Option Kernel.ConstantInfo

/-- An environment's lookup through IxC's name index (`mkFEnv`). Inlined as a term
(`macro_inline`), so that `let f := envFind env` builds the index once: the compiled function
would otherwise be eta-expanded to arity two and rebuild the index at every lookup. -/
@[macro_inline] def envFind (env : Kernel.Env) : Lookup := (Kernel.mkFEnv env).find?

theorem envFind_eq (env : Kernel.Env) : envFind env = env.find? :=
  funext (Kernel.mkFEnv_find? env)

/-- `Kernel.Env.findProj?` through a lookup. -/
def lookupProj (find : Lookup) (T : Kernel.Name) (i : Nat) : Option Kernel.ProjEntry :=
  match find (Kernel.projTableName T) with
  | some (.projInfo tbl) => if i < tbl.numFields then some (tbl.entry i) else none
  | _ => none

theorem lookupProj_env (env : Kernel.Env) : lookupProj env.find? = env.findProj? := rfl

/-! ## The expression comparison with its lookups given -/

def checkInstalledConstantL (fS : Lookup) (names : Kernel.Name → Kernel.Name)
    (image : UniverseImage) (sourceName targetName : Kernel.Name)
    (sourceUs targetUs : List Kernel.Level) : Option Bool :=
  match fS sourceName with
  | none => some false
  | some entry =>
    if targetName = names sourceName ∧ sourceUs.length = entry.toConstantVal.levelParams.length then
      Kernel.Level.isEquivList (sourceUs.map image.level) targetUs
    else some false

theorem checkInstalledConstantL_env (source : Kernel.Env) :
    checkInstalledConstantL source.find? = checkInstalledConstant source := rfl

def checkInstalledPinsL (fS : Lookup) (names : Kernel.Name → Kernel.Name)
    (image : UniverseImage) : List (Kernel.Name × List Kernel.Level) → Option Bool
  | [] => some true
  | (name, levels) :: rest => bothChecks
      (checkInstalledConstantL fS names image name name levels levels)
      (checkInstalledPinsL fS names image rest)

theorem checkInstalledPinsL_env (source : Kernel.Env) (names : Kernel.Name → Kernel.Name)
    (image : UniverseImage) :
    ∀ pins, checkInstalledPinsL source.find? names image pins = checkInstalledPins source names image pins
  | [] => rfl
  | (name, levels) :: rest => by
    simp only [checkInstalledPinsL, checkInstalledPins, checkInstalledPinsL_env source names image rest]
    rfl

def checkInstalledProjectionL (fS fT : Lookup) (names : Kernel.Name → Kernel.Name)
    (sourceOwner targetOwner : Kernel.Name) (sourceIndex targetIndex : Nat) : Bool :=
  decide (targetOwner = names sourceOwner) &&
    match lookupProj fS sourceOwner sourceIndex, lookupProj fT targetOwner targetIndex with
    | some sourceEntry, some targetEntry => decide (sourceIndex + sourceEntry.off = targetIndex + targetEntry.off)
    | none, none => decide ((sourceIndex = 0 ∧ targetIndex = 0) ∨ (sourceIndex = 1 ∧ targetIndex = 1))
    | _, _ => false

theorem checkInstalledProjectionL_env (source target : Kernel.Env) :
    checkInstalledProjectionL source.find? target.find? = checkInstalledProjection source target := rfl

def checkInstalledExprL (fS fT : Lookup) (names : Kernel.Name → Kernel.Name)
    (image : UniverseImage) : Kernel.Expr → Kernel.Expr → Option Bool
  | .bvar source, .bvar target => some (decide (source = target))
  | .sort source, .sort target => Kernel.Level.isEquiv (image.level source) target
  | .const sourceName sourceUs, .const targetName targetUs =>
      checkInstalledConstantL fS names image sourceName targetName sourceUs targetUs
  | .app sf sa, .app tf ta => bothChecks
      (checkInstalledExprL fS fT names image sf tf)
      (checkInstalledExprL fS fT names image sa ta)
  | .lam sd sb sm, .lam td tb tm
  | .forallE sd sb sm, .forallE td tb tm => bothChecks
      (some (decide (tm.pw = image.datum sm.pw))) (bothChecks
        (checkInstalledExprL fS fT names image sd td)
        (checkInstalledExprL fS fT names image sb tb))
  | .proj so si se, .proj to ti te => bothChecks
      (some (checkInstalledProjectionL fS fT names so to si ti))
      (checkInstalledExprL fS fT names image se te)
  | .lit (.natVal source), .lit (.natVal target) => bothChecks (some (decide (source = target)))
      (checkInstalledPinsL fS names image naturalImagePins)
  | .lit (.strVal source), .lit (.strVal target) => bothChecks (some (decide (source = target)))
      (checkInstalledPinsL fS names image stringImagePins)
  | .fvar .., _ | .letE .., _ | _, .fvar .. | _, .letE .. => none
  | _, _ => some false

theorem checkInstalledExprL_env (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name)
    (image : UniverseImage) : ∀ s t : Kernel.Expr,
    checkInstalledExprL source.find? target.find? names image s t = checkInstalledExpr source target names image s t := by
  intro s
  induction s with
  | bvar _ => intro t; cases t <;> rfl
  | fvar _ _ _ => intro t; cases t <;> rfl
  | sort _ => intro t; cases t <;> rfl
  | const _ _ => intro t; cases t <;> rfl
  | app sf sa ihf iha =>
    intro t
    cases t
    case app tf ta => simp only [checkInstalledExprL, checkInstalledExpr, ihf, iha]
    all_goals rfl
  | lam sd sb sm ihd ihb =>
    intro t
    cases t
    case lam td tb tm => simp only [checkInstalledExprL, checkInstalledExpr, ihd, ihb]
    all_goals rfl
  | forallE sd sb sm ihd ihb =>
    intro t
    cases t
    case forallE td tb tm => simp only [checkInstalledExprL, checkInstalledExpr, ihd, ihb]
    all_goals rfl
  | letE _ _ _ _ _ _ => intro t; cases t <;> rfl
  | lit l =>
    intro t
    cases t
    case lit l' =>
      cases l <;> cases l' <;> rfl
    all_goals cases l <;> rfl
  | proj so si se ih =>
    intro t
    cases t
    case proj to ti te => simp only [checkInstalledExprL, checkInstalledExpr, ih]; rfl
    all_goals rfl

/-! ## The comparison on the DAG -/

section Pairs

variable (fS fT : Lookup) (names : Kernel.Name → Kernel.Name) (image : UniverseImage)

/-- A memo entry: a pair of nodes found equal, the addresses the walk saw them at, and the
proof. -/
structure PairEntry where
  s : Kernel.Expr
  t : Kernel.Expr
  pa : USize
  pb : USize
  ok : checkInstalledExprL fS fT names image s t = some true

abbrev PairMemo := Std.HashMap Nat (PairEntry fS fT names image)

/-- One pair's result, proved to be `checkInstalledExprL`'s, and the memo after it. -/
structure PairRes (s t : Kernel.Expr) where
  val : Option Bool
  eq : val = checkInstalledExprL fS fT names image s t
  memo : PairMemo fS fT names image

abbrev PairOut (s t : Kernel.Expr) := Squash (PairRes fS fT names image s t)

/-- The memo key of an address pair (as IxC's `beqKey`; collisions cost an entry, never an
answer: the probe verifies the stored pair). -/
@[inline] def pairKey (pa pb : USize) : Nat :=
  ((pa ^^^ (pb * 0x9E3779B97F4A7C15)) &&& 0x3FFFFFFFFFFFFFFF).toNat

/-- Does the entry under `key` identify `(s, t)`? The stored addresses filter, the stored
nodes tested by identity verify (as IxC's `probeHit`). -/
@[inline] def pairProbe (memo : PairMemo fS fT names image) (key : Nat) (pa pb : USize)
    (s t : Kernel.Expr) : { b : Bool // b = true → checkInstalledExprL fS fT names image s t = some true } :=
  match memo[key]? with
  | none => ⟨false, fun h => Bool.noConfusion h⟩
  | some q =>
    if q.pa == pa && q.pb == pb then
      match withPtrEqDecEq q.s s (fun _ => Kernel.instDecidableEqExpr q.s s),
          withPtrEqDecEq q.t t (fun _ => Kernel.instDecidableEqExpr q.t t) with
      | isTrue h₁, isTrue h₂ => ⟨true, fun _ => by subst h₁; subst h₂; exact q.ok⟩
      | _, _ => ⟨false, fun h => Bool.noConfusion h⟩
    else ⟨false, fun h => Bool.noConfusion h⟩

theorem bothChecks_some_true (x : Option Bool) : bothChecks (some true) x = x := rfl

theorem bothChecks_not_true {x : Option Bool} (h : ¬ x = some true) (y : Option Bool) :
    bothChecks x y = x := by
  cases x with
  | none => rfl
  | some b => cases b <;> simp_all [bothChecks]

/-- Is the node a pair the comparison descends into (the memo is written only for those)? -/
@[inline] def pairRecursive : Kernel.Expr → Bool
  | .app .. | .lam .. | .forallE .. | .proj .. => true
  | _ => false

/-- The memoised comparison: probe the pair; on a miss, the constructor cases of
`checkInstalledExprL` with the children through the walk; record a `some true`. -/
def pairGo (memo : PairMemo fS fT names image) (s t : @& Kernel.Expr) : PairOut fS fT names image s t :=
  withPtrAddr s (fun pa => withPtrAddr t (fun pb =>
    let key := pairKey pa pb
    let hit := pairProbe fS fT names image memo key pa pb s t
    if hh : hit.1 = true then Squash.mk ⟨some true, (hit.2 hh).symm, memo⟩
    else
      let node : PairOut fS fT names image s t := match s, t with
        | .app sf sa, .app tf ta =>
          Squash.lift (pairGo memo sf tf) fun r₁ =>
            if h₁ : r₁.val = some true then
              Squash.lift (pairGo r₁.memo sa ta) fun r₂ =>
                Squash.mk ⟨r₂.val, by
                  rw [r₂.eq]; simp only [checkInstalledExprL, ← r₁.eq, h₁, bothChecks_some_true], r₂.memo⟩
            else Squash.mk ⟨r₁.val, by
                  simp only [checkInstalledExprL, ← r₁.eq, bothChecks_not_true h₁], r₁.memo⟩
        | .lam sd sb sm, .lam td tb tm =>
          if hm : decide (tm.pw = image.datum sm.pw) = true then
            Squash.lift (pairGo memo sd td) fun r₁ =>
              if h₁ : r₁.val = some true then
                Squash.lift (pairGo r₁.memo sb tb) fun r₂ =>
                  Squash.mk ⟨r₂.val, by
                    rw [r₂.eq]
                    simp only [checkInstalledExprL, hm, ← r₁.eq, h₁, bothChecks_some_true], r₂.memo⟩
              else Squash.mk ⟨r₁.val, by
                    simp only [checkInstalledExprL, hm, ← r₁.eq, bothChecks_some_true,
                      bothChecks_not_true h₁], r₁.memo⟩
          else Squash.mk ⟨some false, by
                simp only [checkInstalledExprL, Bool.eq_false_iff.mpr hm]; rfl, memo⟩
        | .forallE sd sb sm, .forallE td tb tm =>
          if hm : decide (tm.pw = image.datum sm.pw) = true then
            Squash.lift (pairGo memo sd td) fun r₁ =>
              if h₁ : r₁.val = some true then
                Squash.lift (pairGo r₁.memo sb tb) fun r₂ =>
                  Squash.mk ⟨r₂.val, by
                    rw [r₂.eq]
                    simp only [checkInstalledExprL, hm, ← r₁.eq, h₁, bothChecks_some_true], r₂.memo⟩
              else Squash.mk ⟨r₁.val, by
                    simp only [checkInstalledExprL, hm, ← r₁.eq, bothChecks_some_true,
                      bothChecks_not_true h₁], r₁.memo⟩
          else Squash.mk ⟨some false, by
                simp only [checkInstalledExprL, Bool.eq_false_iff.mpr hm]; rfl, memo⟩
        | .proj so si se, .proj to ti te =>
          if hp : checkInstalledProjectionL fS fT names so to si ti = true then
            Squash.lift (pairGo memo se te) fun r =>
              Squash.mk ⟨r.val, by rw [r.eq]; simp only [checkInstalledExprL, hp, bothChecks_some_true], r.memo⟩
          else Squash.mk ⟨some false, by
                simp only [checkInstalledExprL, Bool.eq_false_iff.mpr hp]; rfl, memo⟩
        | s', t' => Squash.mk ⟨checkInstalledExprL fS fT names image s' t', rfl, memo⟩
      Squash.lift node fun r =>
        if hv : r.val = some true ∧ pairRecursive s = true then
          Squash.mk ⟨r.val, r.eq, r.memo.insert key ⟨s, t, pa, pb, r.eq.symm.trans hv.1⟩⟩
        else Squash.mk r)
    (fun _ _ => Subsingleton.elim _ _))
    (fun _ _ => Subsingleton.elim _ _)

/-- The walk's answer with its proof: a subsingleton. -/
def checkInstalledExprSharedVal (s t : Kernel.Expr) :
    { v : Option Bool // v = checkInstalledExprL fS fT names image s t } :=
  Squash.lift (pairGo fS fT names image {} s t) fun r => ⟨r.val, r.eq⟩

/-- **The comparison on the DAG.** -/
def checkInstalledExprShared (s t : Kernel.Expr) : Option Bool :=
  (checkInstalledExprSharedVal fS fT names image s t).val

theorem checkInstalledExprShared_eq (s t : Kernel.Expr) :
    checkInstalledExprShared fS fT names image s t = checkInstalledExprL fS fT names image s t :=
  (checkInstalledExprSharedVal fS fT names image s t).property

end Pairs

/-! ## Member comparisons with their lookups given (`…L`), and on the DAG (`…F`) -/

def checkInstalledMemberExprL (fS fT : Lookup) (names : Kernel.Name → Kernel.Name) (name : Kernel.Name)
    (source target : Kernel.Expr) : Option Bool :=
  match fS name, fT (names name) with
  | some sourceEntry, some targetEntry =>
    if source.allLevelParamsDefined sourceEntry.toConstantVal.levelParams then
      checkInstalledExprL fS fT names
        (UniverseImage.select sourceEntry.toConstantVal.levelParams
          (targetEntry.toConstantVal.levelParams.map Kernel.Level.param)) source target
    else some false
  | _, _ => some false

theorem checkInstalledMemberExprL_env (source target : Kernel.Env) :
    checkInstalledMemberExprL source.find? target.find? = checkInstalledMemberExpr source target := by
  funext names name s t
  simp only [checkInstalledMemberExprL, checkInstalledExprL_env]
  rfl

/-- The member comparison on the DAG. -/
def checkInstalledMemberExprF (fS fT : Lookup) (names : Kernel.Name → Kernel.Name) (name : Kernel.Name)
    (source target : Kernel.Expr) : Option Bool :=
  match fS name, fT (names name) with
  | some sourceEntry, some targetEntry =>
    if source.allLevelParamsDefined sourceEntry.toConstantVal.levelParams then
      checkInstalledExprShared fS fT names
        (UniverseImage.select sourceEntry.toConstantVal.levelParams
          (targetEntry.toConstantVal.levelParams.map Kernel.Level.param)) source target
    else some false
  | _, _ => some false

theorem checkInstalledMemberExprF_eq (fS fT : Lookup) :
    checkInstalledMemberExprF fS fT = checkInstalledMemberExprL fS fT := by
  funext names name s t
  simp only [checkInstalledMemberExprF, checkInstalledMemberExprL, checkInstalledExprShared_eq]

/-- The member comparison as the decisions call it: on the DAG, through the lookups. -/
theorem checkInstalledMemberExprF_env (source target : Kernel.Env) :
    checkInstalledMemberExprF source.find? target.find? = checkInstalledMemberExpr source target := by
  rw [checkInstalledMemberExprF_eq, checkInstalledMemberExprL_env]

def checkInstalledMemberExprsF (fS fT : Lookup) (names : Kernel.Name → Kernel.Name) (name : Kernel.Name) :
    List Kernel.Expr → List Kernel.Expr → Option Bool
  | [], [] => some true
  | sourceExpr :: sources, targetExpr :: targets => bothChecks
      (checkInstalledMemberExprF fS fT names name sourceExpr targetExpr)
      (checkInstalledMemberExprsF fS fT names name sources targets)
  | _, _ => some false

theorem checkInstalledMemberExprsF_env (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name)
    (name : Kernel.Name) : ∀ sources targets,
    checkInstalledMemberExprsF source.find? target.find? names name sources targets =
      checkInstalledMemberExprs source target names name sources targets
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | s :: ss, t :: ts => by
    simp only [checkInstalledMemberExprsF, checkInstalledMemberExprs, checkInstalledMemberExprF_env,
      checkInstalledMemberExprsF_env source target names name ss ts]

def checkInstalledFireF (fS fT : Lookup) (names : Kernel.Name → Kernel.Name)
    (name : Kernel.Name) : Kernel.RecRuleFire → Kernel.RecRuleFire → Option Bool
  | .inert, .inert | .plain, .plain => some true
  | .nested sourceUs sourcePins, .nested targetUs targetPins => bothChecks
      (checkInstalledMemberExprsF fS fT names name
        (sourceUs.map Kernel.Expr.sort) (targetUs.map Kernel.Expr.sort))
      (checkInstalledMemberExprsF fS fT names name sourcePins targetPins)
  | _, _ => some false

theorem checkInstalledFireF_env (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name)
    (name : Kernel.Name) (a b : Kernel.RecRuleFire) :
    checkInstalledFireF source.find? target.find? names name a b = checkInstalledFire source target names name a b := by
  cases a <;> cases b <;> simp only [checkInstalledFireF, checkInstalledFire, checkInstalledMemberExprsF_env]

def checkInstalledRulesF (fS fT : Lookup) (names : Kernel.Name → Kernel.Name)
    (name : Kernel.Name) : List Kernel.RecRule → List Kernel.RecRule → Option Bool
  | [], [] => some true
  | sourceRule :: sources, targetRule :: targets => bothChecks
      (some (decide (InstalledRuleHeader names sourceRule targetRule))) (bothChecks
        (checkInstalledFireF fS fT names name sourceRule.fire targetRule.fire) (bothChecks
          (checkInstalledMemberExprF fS fT names name sourceRule.rhs targetRule.rhs)
          (checkInstalledRulesF fS fT names name sources targets)))
  | _, _ => some false

theorem checkInstalledRulesF_env (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name)
    (name : Kernel.Name) : ∀ sources targets,
    checkInstalledRulesF source.find? target.find? names name sources targets =
      checkInstalledRules source target names name sources targets
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | s :: ss, t :: ts => by
    simp only [checkInstalledRulesF, checkInstalledRules, checkInstalledFireF_env,
      checkInstalledMemberExprF_env, checkInstalledRulesF_env source target names name ss ts]

/-! ## The row checks, on the lookups and the DAG -/

def checkTelescopesF (source : Kernel.Env) (fT : Lookup) (names : Kernel.Name → Kernel.Name) : Bool :=
  source.consts.all fun entry =>
    match fT (names entry.name) with
    | none => false
    | some targetEntry => decide (TelescopeEntry entry targetEntry)

theorem checkTelescopesF_env (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) :
    checkTelescopesF source target.find? names = checkTelescopes source target names := rfl

def checkInstalledTypesF (source : Kernel.Env) (fS fT : Lookup) (names : Kernel.Name → Kernel.Name) : Bool :=
  source.consts.all fun entry =>
    decide (fS entry.name = some entry) &&
    match fT (names entry.name) with
    | none => false
    | some targetEntry => decide (checkInstalledMemberExprF fS fT names entry.name
        entry.toConstantVal.type targetEntry.toConstantVal.type = some true)

theorem checkInstalledTypesF_env (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) :
    checkInstalledTypesF source source.find? target.find? names = checkInstalledTypes source target names := by
  simp only [checkInstalledTypesF, checkInstalledMemberExprF_env]
  rfl

def checkInstalledDefinitionsF (source : Kernel.Env) (fS fT : Lookup) (names : Kernel.Name → Kernel.Name) : Bool :=
  source.consts.all fun entry =>
    match entry with
    | .defnInfo header value _ =>
      decide (fS header.name = some entry) &&
      match fT (names header.name) with
      | some (.defnInfo _ targetValue _) =>
        decide (checkInstalledMemberExprF fS fT names header.name value targetValue = some true)
      | _ => false
    | _ => true

theorem checkInstalledDefinitionsF_env (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) :
    checkInstalledDefinitionsF source source.find? target.find? names =
      checkInstalledDefinitions source target names := by
  simp only [checkInstalledDefinitionsF, checkInstalledMemberExprF_env]
  rfl

def checkInstalledCapabilitiesF (source : Kernel.Env) (fS fT : Lookup) (names : Kernel.Name → Kernel.Name) : Bool :=
  source.consts.all fun entry => match entry with
    | .indInfo header caps =>
      decide (fS header.name = some entry) &&
      match fT (names header.name) with
      | some (.indInfo _ targetCaps) =>
        decide (InstalledCapsHeader names header.name caps targetCaps) &&
        decide (checkInstalledMemberExprF fS fT names header.name
          (capabilityDatumExpr caps) (capabilityDatumExpr targetCaps) = some true)
      | _ => false
    | _ => true

theorem checkInstalledCapabilitiesF_env (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) :
    checkInstalledCapabilitiesF source source.find? target.find? names =
      checkInstalledCapabilities source target names := by
  simp only [checkInstalledCapabilitiesF, checkInstalledMemberExprF_env]
  rfl

def checkInstalledRecursorsF (source : Kernel.Env) (fS fT : Lookup) (names : Kernel.Name → Kernel.Name) : Bool :=
  source.consts.all fun entry => match entry with
    | .recInfo header major rulePrefix rules =>
      decide (fS header.name = some entry) &&
      match fT (names header.name) with
      | some (.recInfo _ targetMajor targetPrefix targetRules) =>
        decide (major = targetMajor ∧ rulePrefix = targetPrefix) &&
          decide (checkInstalledRulesF fS fT names header.name rules targetRules = some true)
      | _ => false
    | _ => true

theorem checkInstalledRecursorsF_env (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) :
    checkInstalledRecursorsF source source.find? target.find? names =
      checkInstalledRecursors source target names := by
  simp only [checkInstalledRecursorsF, checkInstalledRulesF_env]
  rfl

def checkInstalledConstructorsF (source : Kernel.Env) (fS fT : Lookup) (names : Kernel.Name → Kernel.Name) : Bool :=
  source.consts.all fun entry => match entry with
    | .ctorInfo header params fields =>
      decide (fS header.name = some entry) &&
      match fT (names header.name) with
      | some (.ctorInfo _ targetParams targetFields) => decide (params = targetParams ∧ fields = targetFields)
      | _ => false
    | _ => true

theorem checkInstalledConstructorsF_env (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) :
    checkInstalledConstructorsF source source.find? target.find? names =
      checkInstalledConstructors source target names := rfl

/-! ## Eta associations and rule level links -/

def checkInstalledEtaFamilyL (find : Lookup) (name : Kernel.Name) (caps : Kernel.IndCaps) : Bool :=
  !Kernel.reservedBasisNames.contains caps.etaCtor &&
  (match find caps.etaCtor with | some (.ctorInfo ..) => true | _ => false) &&
  (List.range caps.etaFields).all fun index =>
    match find (Kernel.projFnName name index) with
    | some (.recInfo ..) => true
    | _ => false

def checkInstalledEtaAtL (find : Lookup) (name : Kernel.Name) : Bool :=
  match find name with
  | some (.indInfo _ caps) => Kernel.reservedBasisNames.contains name || checkInstalledEtaFamilyL find name caps
  | _ => false

def checkInstalledFamilyMemberF (fS fT : Lookup) (names : Kernel.Name → Kernel.Name)
    (owner member : Kernel.Name) : Option Bool :=
  match fS member, fT (names member), fT (names owner) with
  | some sourceMember, some targetMember, some targetOwner =>
    if targetMember.toConstantVal.levelParams.all
        (fun parameter => targetOwner.toConstantVal.levelParams.contains parameter) then
      checkInstalledMemberExprF fS fT names owner
        (.const member (sourceMember.toConstantVal.levelParams.map Kernel.Level.param))
        (.const (names member) (targetMember.toConstantVal.levelParams.map Kernel.Level.param))
    else some false
  | _, _, _ => some false

def checkInstalledEtaEntryF (fS fT : Lookup) (names : Kernel.Name → Kernel.Name)
    (entry : Kernel.ConstantInfo) : Option Bool :=
  match entry with
  | .indInfo header caps =>
    if caps.eta && (checkInstalledEtaFamilyL fS header.name caps ||
        Kernel.reservedBasisNames.contains header.name) then
      bothChecks (some (decide (fS header.name = some entry) && checkInstalledEtaAtL fT (names header.name)))
        (bothChecks (checkInstalledFamilyMemberF fS fT names header.name caps.etaCtor)
          ((List.range caps.etaFields).foldr (fun index rest => bothChecks
            (checkInstalledFamilyMemberF fS fT names header.name (Kernel.projFnName header.name index)) rest)
            (some true)))
    else some true
  | _ => some true

def checkInstalledEtaAssociationsF (source : Kernel.Env) (fS fT : Lookup) (names : Kernel.Name → Kernel.Name) :
    Option Bool :=
  source.consts.foldr (fun entry rest => bothChecks (checkInstalledEtaEntryF fS fT names entry) rest) (some true)

theorem checkInstalledEtaAssociationsF_env (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) :
    checkInstalledEtaAssociationsF source source.find? target.find? names =
      checkInstalledEtaAssociations source target names := by
  simp only [checkInstalledEtaAssociationsF, checkInstalledEtaEntryF, checkInstalledFamilyMemberF,
    checkInstalledMemberExprF_env]
  rfl

/-- What the rule level links read of an installed rule frame: the universe comparands and
the constructor's level parameters. -/
def readFrameL (find : Lookup) (name : Kernel.Name) (index : Nat) :
    Option (List Kernel.Level × List Kernel.Name) :=
  match find name with
  | some (.recInfo _ _ _ rules) =>
    match rules[index]? with
    | some rule =>
      if rule.fire = .inert then none else
      match find rule.ctor with
      | some (.ctorInfo constructor _ _) =>
        some ((match rule.fire with
          | .nested levels _ => levels
          | _ => constructor.levelParams.map Kernel.Level.param), constructor.levelParams)
      | _ => none
    | none => none
  | _ => none

theorem readFrameL_env (env : Kernel.Env) (name : Kernel.Name) (index : Nat) :
    readFrameL env.find? name index = (readInstalledRuleFrame env name index).map
      (fun frame => (frame.universeComparands, frame.constructor.levelParams)) := by
  unfold readFrameL readInstalledRuleFrame
  split
  · rename_i val major rp rules h1
    symm
    split
    · rename_i header major2 rp2 rules2 h2
      rw [h1] at h2
      cases h2
      split
      · rename_i rule h3
        simp only [h3]
        split
        · rfl
        · rename_i h4
          split
          · rename_i c p f h5
            simp only [h5]; rfl
          · rename_i h5
            split
            · rename_i c p f h6
              exact absurd h6 (h5 c p f)
            · rfl
      · rename_i h3
        simp only [h3]; rfl
    · rename_i h2
      exact absurd h1 (h2 val major rp rules)
  · rename_i h1
    symm
    split
    · rename_i header major rp rules h2
      exact absurd h2 (h1 header major rp rules)
    · rfl

def checkInstalledOwnerLevelsF (fS fT : Lookup) (names : Kernel.Name → Kernel.Name)
    (owner : Kernel.Name) (sourceLevels targetLevels : List Kernel.Level) : Option Bool :=
  match fT (names owner) with
  | none => some false
  | some targetOwner =>
    if targetLevels.all (fun level => level.allParamsDefined targetOwner.toConstantVal.levelParams) then
      checkInstalledMemberExprsF fS fT names owner (sourceLevels.map Kernel.Expr.sort) (targetLevels.map Kernel.Expr.sort)
    else some false

def checkInstalledRuleLevelLinkF (fS fT : Lookup) (names : Kernel.Name → Kernel.Name)
    (name : Kernel.Name) (index : Nat) : Option Bool :=
  match readFrameL fS name index, readFrameL fT (names name) index with
  | some (sourceComparands, sourceConstructor), some (targetComparands, targetConstructor) =>
    if sourceComparands.length = sourceConstructor.length ∧
        targetComparands.length = targetConstructor.length then
      checkInstalledOwnerLevelsF fS fT names name sourceComparands targetComparands
    else some false
  | _, _ => some false

theorem checkInstalledRuleLevelLinkF_env (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name)
    (name : Kernel.Name) (index : Nat) :
    checkInstalledRuleLevelLinkF source.find? target.find? names name index =
      checkInstalledRuleLevelLink source target names name index := by
  unfold checkInstalledRuleLevelLinkF checkInstalledRuleLevelLink
  rw [readFrameL_env, readFrameL_env]
  cases readInstalledRuleFrame source name index <;> cases readInstalledRuleFrame target (names name) index
  all_goals simp only [Option.map_some, Option.map_none]
  simp only [checkInstalledOwnerLevelsF, checkInstalledOwnerLevels, checkInstalledMemberExprsF_env]
  rfl

def checkInstalledRuleLevelEntryF (fS fT : Lookup) (names : Kernel.Name → Kernel.Name)
    (entry : Kernel.ConstantInfo) : Option Bool :=
  match entry with
  | .recInfo header _ _ rules =>
    bothChecks (some (decide (fS header.name = some entry)))
      ((List.range rules.length).foldr (fun index rest => bothChecks
        (match rules[index]? with
        | none => some false
        | some rule => if rule.fire = .inert then some true else
            checkInstalledRuleLevelLinkF fS fT names header.name index) rest) (some true))
  | _ => some true

def checkInstalledRuleLevelLinksF (source : Kernel.Env) (fS fT : Lookup) (names : Kernel.Name → Kernel.Name) :
    Option Bool :=
  source.consts.foldr (fun entry rest => bothChecks (checkInstalledRuleLevelEntryF fS fT names entry) rest) (some true)

theorem checkInstalledRuleLevelLinksF_env (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) :
    checkInstalledRuleLevelLinksF source source.find? target.find? names =
      checkInstalledRuleLevelLinks source target names := by
  simp only [checkInstalledRuleLevelLinksF, checkInstalledRuleLevelEntryF, checkInstalledRuleLevelLinkF_env]
  rfl

/-! ## Projection towers -/

def checkInstalledTowerEntryF (fS fT : Lookup) (names : Kernel.Name → Kernel.Name)
    (owner : Kernel.Name) (index : Nat) : Option Bool :=
  match lookupProj fS owner index, lookupProj fT (names owner) index with
  | some sourceEntry, some targetEntry =>
    bothChecks (some (decide (sourceEntry.numParams = targetEntry.numParams ∧
      sourceEntry.numFields = targetEntry.numFields ∧ sourceEntry.off = targetEntry.off ∧
      names sourceEntry.ctor = targetEntry.ctor)))
      (bothChecks (checkInstalledMemberExprF fS fT names owner
        (Kernel.projTele (sourceEntry.numParams + 1) sourceEntry.body)
        (Kernel.projTele (targetEntry.numParams + 1) targetEntry.body))
        (bothChecks (checkInstalledMemberExprF fS fT names owner
          (.sort sourceEntry.structSort) (.sort targetEntry.structSort))
          (checkInstalledMemberExprF fS fT names owner
            (.sort sourceEntry.fieldSort) (.sort targetEntry.fieldSort))))
  | _, _ => some false

def checkInstalledTowersF (source : Kernel.Env) (fS fT : Lookup) (names : Kernel.Name → Kernel.Name) :
    Option Bool :=
  source.consts.foldr (fun entry rest => bothChecks
    (match entry with
    | .projInfo table => (List.range table.numFields).foldr (fun index rest =>
        bothChecks (checkInstalledTowerEntryF fS fT names table.structName index) rest) (some true)
    | _ => some true) rest) (some true)

theorem checkInstalledTowersF_env (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) :
    checkInstalledTowersF source source.find? target.find? names = checkInstalledTowers source target names := by
  simp only [checkInstalledTowersF, checkInstalledTowerEntryF, checkInstalledMemberExprF_env]
  rfl

/-! ## The availability pass -/

def checkInstalledComparisonAvailabilityF (source : Kernel.Env) (fS fT : Lookup)
    (names : Kernel.Name → Kernel.Name) : Option Bool :=
  source.consts.foldr (fun entry rest => bothChecks (do
    let some targetEntry := fT (names entry.name) | return false
    let typeResult ← checkInstalledMemberExprF fS fT names entry.name
      entry.toConstantVal.type targetEntry.toConstantVal.type
    if !typeResult then return false
    match entry, targetEntry with
    | .defnInfo header value _, .defnInfo _ targetValue _ =>
      checkInstalledMemberExprF fS fT names header.name value targetValue
    | .recInfo header _ _ rules, .recInfo _ _ _ targetRules =>
      checkInstalledRulesF fS fT names header.name rules targetRules
    | .indInfo header caps, .indInfo _ targetCaps =>
      checkInstalledMemberExprF fS fT names header.name
        (capabilityDatumExpr caps) (capabilityDatumExpr targetCaps)
    | _, _ => return true) rest) (some true)

theorem checkInstalledComparisonAvailabilityF_env (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) :
    checkInstalledComparisonAvailabilityF source source.find? target.find? names =
      checkInstalledComparisonAvailability source target names := by
  simp only [checkInstalledComparisonAvailabilityF, checkInstalledMemberExprF_env, checkInstalledRulesF_env]
  rfl

/-- One row of the availability pass, as the Boolean checks see it. -/
theorem availability_row {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (types : checkInstalledTypes source target names = true)
    (definitions : checkInstalledDefinitions source target names = true)
    (capabilities : checkInstalledCapabilities source target names = true)
    (recursors : checkInstalledRecursors source target names = true)
    {entry : Kernel.ConstantInfo} (present : entry ∈ source.consts) :
    (do
      let some targetEntry := target.find? (names entry.name) | return false
      let typeResult ← checkInstalledMemberExpr source target names entry.name
        entry.toConstantVal.type targetEntry.toConstantVal.type
      if !typeResult then return false
      match entry, targetEntry with
      | .defnInfo header value _, .defnInfo _ targetValue _ =>
        checkInstalledMemberExpr source target names header.name value targetValue
      | .recInfo header _ _ rules, .recInfo _ _ _ targetRules =>
        checkInstalledRules source target names header.name rules targetRules
      | .indInfo header caps, .indInfo _ targetCaps =>
        checkInstalledMemberExpr source target names header.name
          (capabilityDatumExpr caps) (capabilityDatumExpr targetCaps)
      | _, _ => return true : Option Bool) = some true := by
  obtain ⟨_, targetEntry, targetLookup, typeCheck⟩ := checkInstalledTypes_member types present
  simp only [targetLookup, typeCheck, bind, Option.bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases entry
  case defnInfo header value hint =>
    obtain ⟨_, targetHeader, targetValue, targetHint, lookup, valueCheck⟩ :=
      checkInstalledDefinitions_member definitions present
    have same := Option.some.inj (targetLookup.symm.trans lookup)
    subst same
    exact valueCheck
  case recInfo header major rulePrefix rules =>
    obtain ⟨_, targetHeader, targetRules, lookup, rulesCheck⟩ :=
      checkInstalledRecursors_member recursors present
    have same := Option.some.inj (targetLookup.symm.trans lookup)
    subst same
    exact rulesCheck
  case indInfo header caps =>
    obtain ⟨_, targetHeader, targetCaps, lookup, _, capsCheck⟩ :=
      checkInstalledCapabilities_member capabilities present
    have same := Option.some.inj (targetLookup.symm.trans lookup)
    subst same
    exact capsCheck
  all_goals cases targetEntry <;> rfl

theorem bothChecks_foldr_true {α : Type} (check : α → Option Bool) :
    ∀ (entries : List α), (∀ e ∈ entries, check e = some true) →
      entries.foldr (fun e rest => bothChecks (check e) rest) (some true) = some true
  | [], _ => rfl
  | e :: es, h => by
    simp only [List.foldr_cons, h e List.mem_cons_self, bothChecks_some_true]
    exact bothChecks_foldr_true check es (fun x hx => h x (List.mem_cons_of_mem e hx))

/-- **The availability pass is implied by the Boolean checks.** -/
theorem availability_of_checks {source target : Kernel.Env} {names : Kernel.Name → Kernel.Name}
    (types : checkInstalledTypes source target names = true)
    (definitions : checkInstalledDefinitions source target names = true)
    (capabilities : checkInstalledCapabilities source target names = true)
    (recursors : checkInstalledRecursors source target names = true) :
    checkInstalledComparisonAvailability source target names = some true :=
  bothChecks_foldr_true _ source.consts fun _ present =>
    availability_row types definitions capabilities recursors present

/-! ## The installed association -/

/-- `checkInstalledAssociation` on the index and the DAG: the eight Boolean checks first;
when they accept, the availability pass is `some true` (`availability_of_checks`) and is
not run; otherwise it runs, indexed, to tell an unavailable comparison from a refusal. -/
def checkInstalledAssociationF (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Option Bool :=
  let fS := envFind source
  let fT := envFind target
  let structural := checkTelescopesF source fT names &&
    checkInstalledTypesF source fS fT names && checkInstalledDefinitionsF source fS fT names &&
    checkInstalledPin source names Kernel.falseName 0 && checkInstalledPin source names Kernel.eqName 1 &&
    checkInstalledCapabilitiesF source fS fT names && checkInstalledRecursorsF source fS fT names &&
    checkInstalledConstructorsF source fS fT names
  if structural then
    bothChecks (checkInstalledEtaAssociationsF source fS fT names)
      (checkInstalledRuleLevelLinksF source fS fT names)
  else
    match checkInstalledComparisonAvailabilityF source fS fT names with
    | none => none
    | some _ => some false

theorem checkInstalledAssociationF_eq (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) :
    checkInstalledAssociationF source target names = checkInstalledAssociation source target names := by
  simp only [checkInstalledAssociationF, envFind_eq, checkTelescopesF_env, checkInstalledTypesF_env,
    checkInstalledDefinitionsF_env, checkInstalledCapabilitiesF_env, checkInstalledRecursorsF_env,
    checkInstalledConstructorsF_env, checkInstalledEtaAssociationsF_env, checkInstalledRuleLevelLinksF_env,
    checkInstalledComparisonAvailabilityF_env]
  unfold checkInstalledAssociation
  split
  · rename_i h
    have h₀ := h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨_, types⟩, definitions⟩, _⟩, _⟩, capabilities⟩, recursors⟩, _⟩ := h
    rw [availability_of_checks types definitions capabilities recursors, bothChecks_some_true, h₀,
      bothChecks_some_true]
  · rename_i h
    have hf : (checkTelescopes source target names && checkInstalledTypes source target names &&
        checkInstalledDefinitions source target names && checkInstalledPin source names Kernel.falseName 0 &&
        checkInstalledPin source names Kernel.eqName 1 && checkInstalledCapabilities source target names &&
        checkInstalledRecursors source target names && checkInstalledConstructors source target names) = false :=
      Bool.eq_false_iff.mpr h
    rw [hf]
    cases checkInstalledComparisonAvailability source target names with
    | none => rfl
    | some b => cases b <;> rfl

/-! ## Literal support -/

theorem checkExprLiteralSupport_both {source target : Kernel.Env}
    (nat : Kernel.natLitSupported source = Kernel.natLitSupported target)
    (str : Kernel.strLitSupported source = Kernel.strLitSupported target) :
    ∀ e, checkExprLiteralSupport source target e = true
  | .lit (.natVal _) => by simp [checkExprLiteralSupport, nat]
  | .lit (.strVal _) => by simp [checkExprLiteralSupport, str]
  | .app f a => by simp [checkExprLiteralSupport, checkExprLiteralSupport_both nat str f,
      checkExprLiteralSupport_both nat str a]
  | .lam d b _ | .forallE d b _ => by simp [checkExprLiteralSupport, checkExprLiteralSupport_both nat str d,
      checkExprLiteralSupport_both nat str b]
  | .proj _ _ v => by simp [checkExprLiteralSupport, checkExprLiteralSupport_both nat str v]
  | .bvar _ | .fvar .. | .sort _ | .const .. | .letE .. => rfl

/-- Both literal checks: `true` at once when both environments support `Nat` and `String`
literals alike, the walks otherwise. -/
def checkLiteralSupportsF (source target : Kernel.Env) : Bool :=
  if decide (Kernel.natLitSupported source = Kernel.natLitSupported target) &&
      decide (Kernel.strLitSupported source = Kernel.strLitSupported target) then true
  else checkTypeLiteralSupport source target && checkDefinitionLiteralSupport source target

theorem checkLiteralSupportsF_eq (source target : Kernel.Env) :
    checkLiteralSupportsF source target =
      (checkTypeLiteralSupport source target && checkDefinitionLiteralSupport source target) := by
  unfold checkLiteralSupportsF
  split
  · rename_i h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have all := checkExprLiteralSupport_both h.1 h.2
    have ht : checkTypeLiteralSupport source target = true :=
      List.all_eq_true.mpr fun entry _ => all _
    have hd : checkDefinitionLiteralSupport source target = true :=
      List.all_eq_true.mpr fun entry _ => by cases entry <;> simp [all]
    rw [ht, hd]; rfl
  · rfl

/-! ## The annotated and the strong association -/

def checkAnnotatedAssociationF (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Option Bool :=
  bothChecks (checkInstalledAssociationF source target names)
    (some (checkReservedNameMap source names && checkLiteralSupportsF source target))

theorem checkAnnotatedAssociationF_eq (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) :
    checkAnnotatedAssociationF source target names = checkAnnotatedAssociation source target names := by
  simp only [checkAnnotatedAssociationF, checkAnnotatedAssociation, checkInstalledAssociationF_eq,
    checkLiteralSupportsF_eq, Bool.and_assoc]

def checkInstalledTowersFast (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Option Bool :=
  checkInstalledTowersF source (envFind source) (envFind target) names

theorem checkInstalledTowersFast_eq (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) :
    checkInstalledTowersFast source target names = checkInstalledTowers source target names := by
  simp only [checkInstalledTowersFast, envFind_eq, checkInstalledTowersF_env]

/-- **The strong check on the index and the DAG.** -/
def checkStrongAssociationF (source target : Kernel.Env)
    (names certificates operationCertificates elementCertificates : Kernel.Name → Kernel.Name)
    (levels : Kernel.Name → Kernel.Level) : Option Bool :=
  bothChecks (checkAnnotatedAssociationF source target names)
    (bothChecks (checkInstalledTowersFast source target names)
      (bothChecks (checkReduceOperationReceipts source target names operationCertificates elementCertificates)
        (bothChecks (checkNatOperationReceipts source target names certificates levels)
          (checkDivModReceipts source target names certificates levels))))

theorem checkStrongAssociationF_eq (source target : Kernel.Env)
    (names certificates operationCertificates elementCertificates : Kernel.Name → Kernel.Name)
    (levels : Kernel.Name → Kernel.Level) :
    checkStrongAssociationF source target names certificates operationCertificates elementCertificates levels =
      checkStrongAssociation source target names certificates operationCertificates elementCertificates levels := by
  simp only [checkStrongAssociationF, checkStrongAssociation, checkAnnotatedAssociationF_eq,
    checkInstalledTowersFast_eq]

/-! ## The name map against the accepted association, indexed -/

/-- The map's targets under their source names, the first entry of a name winning (as
`SourceMap.find`). -/
def mapIndex (m : SourceMap) : Std.HashMap Lean.Name (Kernel.ConstRef Address) :=
  m.foldr (fun e acc => acc.insert e.source e.target) {}

theorem mapIndex_get (m : SourceMap) (n : Lean.Name) : (mapIndex m)[n]? = m.find n := by
  unfold mapIndex SourceMap.find
  induction m with
  | nil => simp
  | cons e es ih =>
    rw [List.foldr_cons, Std.HashMap.getElem?_insert, ih, List.find?_cons]
    by_cases h : e.source = n
    · subst h; simp
    · simp [beq_eq_false_iff_ne.mpr h]

/-- `ExportContext.memberName` with the map lookup given. -/
def memberNameL (mapFind : Lean.Name → Option (Kernel.ConstRef Address)) (pins : Kernel.Reader.Pins)
    (n : Lean.Name) : ExportM Kernel.Name := do
  let some r := mapFind n | throw s!"missing source map entry: {n}"
  return pins.names.getD r (Kernel.Reader.keyName r)

/-- `ExportContext.name` with its lookups given: at `cx.source.find`, `cx.map.find` it is
`cx.name` by `rfl`. -/
def contextNameL (find : Lean.Name → Option Lean.ConstantInfo)
    (mapFind : Lean.Name → Option (Kernel.ConstRef Address)) (pins : Kernel.Reader.Pins)
    (images : Lean.Name → Bool) (n : Lean.Name) : ExportM Kernel.Name := do
  let some ci := find n | throw s!"missing source declaration: {n}"
  match ci with
  | .recInfo v =>
    if images n then memberNameL mapFind pins n else
    match n with
    | .str p "rec" =>
      unless v.all.contains p do throw s!"recursor owner mismatch: {n}"
      return (← memberNameL mapFind pins p).str "rec"
    | .str p suffix =>
      unless suffix.startsWith "rec_" && v.all.head? == some p do
        throw s!"unsupported recursor naming: {n}"
      return (← memberNameL mapFind pins p).str suffix
    | _ => throw s!"unsupported recursor naming: {n}"
  | _ => memberNameL mapFind pins n

theorem contextNameL_find (cx : ExportContext) :
    contextNameL cx.source.find cx.map.find cx.pins cx.images = cx.name := rfl

/-- `SemanticNamesAgree` decided with the source and the map indexed. -/
def semanticNamesFast {input : Input} (accepted : AcceptedAssociation input)
    (names : Kernel.Name → Kernel.Name) : Bool :=
  let sIdx := sourceIndex input.source
  let mIdx := mapIndex input.map
  input.source.declarations.all fun entry =>
    match contextNameL (fun n => sIdx[n]?) (fun n => mIdx[n]?) accepted.pins noImages entry.name with
    | .error _ => false
    | .ok actual => decide (actual = names (sourceName entry.name))

theorem semanticNamesFast_iff {input : Input} (accepted : AcceptedAssociation input)
    (names : Kernel.Name → Kernel.Name) :
    semanticNamesFast accepted names = true ↔ SemanticNamesAgree accepted names := by
  have hs : (fun n => (sourceIndex input.source)[n]?) = input.source.find := sourceIndex_find input.source
  have hm : (fun n => (mapIndex input.map)[n]?) = input.map.find := funext (mapIndex_get input.map)
  simp only [semanticNamesFast, hs, hm, List.all_eq_true]
  rw [show contextNameL input.source.find input.map.find accepted.pins noImages =
    (⟨input.source, input.map, accepted.pins, noImages⟩ : ExportContext).name from rfl]
  unfold SemanticNamesAgree NameAgrees
  constructor
  · intro h entry hentry
    have row := h entry hentry
    split at row
    · contradiction
    · rename_i actual hact
      rw [hact]
      exact of_decide_eq_true row
  · intro h entry hentry
    have row := h entry hentry
    split
    · rename_i e he
      rw [he] at row
      exact row.elim
    · rename_i actual hact
      rw [hact] at row
      exact decide_eq_true row

/-- `SemanticNamesAgree` decided through the indices. -/
def semanticNamesDecidable {input : Input} (accepted : AcceptedAssociation input)
    (names : Kernel.Name → Kernel.Name) : Decidable (SemanticNamesAgree accepted names) :=
  decidable_of_iff _ (semanticNamesFast_iff accepted names)

/-! ## Row preservation of the support, indexed -/

/-- `InstalledRowsPreserved` through the index of the extended environment and the pointer
test of `ciDecEqShared`. -/
def rowsPreservedFast (original extended : Kernel.Env) : Bool :=
  let fE := envFind extended
  original.consts.all fun entry => decide (fE entry.name = some entry)

theorem rowsPreservedFast_iff (original extended : Kernel.Env) :
    rowsPreservedFast original extended = true ↔ InstalledRowsPreserved original extended := by
  simp only [rowsPreservedFast, envFind_eq, List.all_eq_true, decide_eq_true_eq]
  rfl

def rowsPreservedDecidable (original extended : Kernel.Env) :
    Decidable (InstalledRowsPreserved original extended) :=
  decidable_of_iff _ (rowsPreservedFast_iff original extended)

/-- Compiled code decides row preservation through the index (in `admittedSupportEmpty`,
`StrongCone.lean`). -/
@[csimp] theorem instDecidableInstalledRowsPreserved_eq_fast :
    @instDecidableInstalledRowsPreserved = @rowsPreservedDecidable := by
  funext original extended
  exact Subsingleton.elim _ _

/-- Freshness of the support's names through the index of the original environment and a
hash set (M3's `nodupBy`). -/
def supportFreshFast (original : Kernel.Env) (support : Array Kernel.Declaration) : Bool :=
  let fO := envFind original
  let declared := support.toList.flatMap Kernel.Declaration.names
  nodupBy {} declared && declared.all fun name => (fO name).isNone

theorem supportFreshFast_sound {original : Kernel.Env} {support : Array Kernel.Declaration}
    (h : supportFreshFast original support = true) : SupportFresh original support := by
  simp only [supportFreshFast, envFind_eq, Bool.and_eq_true, List.all_eq_true, Option.isNone_iff_eq_none] at h
  exact ⟨nodup_of_nodupBy h.1, h.2⟩

/-- Freshness decided through the index; a refusal falls back to the list decision. -/
def supportFreshDecidable (original : Kernel.Env) (support : Array Kernel.Declaration) :
    Decidable (SupportFresh original support) :=
  if h : supportFreshFast original support = true then isTrue (supportFreshFast_sound h)
  else instDecidableSupportFresh original support

@[csimp] theorem instDecidableSupportFresh_eq_fast :
    @instDecidableSupportFresh = @supportFreshDecidable := by
  funext original support
  exact Subsingleton.elim _ _

/-- `checkAdmittedSupport`, verbatim: compiled after the two substitutions above, so it runs
the indexed decisions. It is `checkAdmittedSupport` by `rfl`. -/
def checkAdmittedSupportC {input : ArtifactInput} (artifact : AdmittedArtifact input)
    (support : Array Kernel.Declaration) : Except SupportError (AdmittedSupport artifact support) :=
  if fresh : SupportFresh artifact.env support then
    match pinsChecked : builtinNatOpPins with
    | .error reason => .error (.setup reason)
    | .ok pins =>
      match checked : Kernel.Cached.checkDecls .verified pins
          (Kernel.Frontend.preparePrelude artifact.prelude.ix artifact.declarations ++ support) with
      | .error (error, position) => .error (.checking error position)
      | .ok env =>
        if originalRows : InstalledRowsPreserved artifact.env env then
          .ok ⟨fresh, pins, pinsChecked, env, checked, originalRows⟩
        else .error .changedOriginal
  else .error .conflictingNames

/-- Compiled code admits support through the recompiled copy (in `admitSupport`,
`StrongCone.lean`). -/
@[csimp] theorem checkAdmittedSupport_eq_copy : @checkAdmittedSupport = @checkAdmittedSupportC := rfl

/-! ## The strong check as the decision calls it -/

/-- `checkNormalizedArtifactStrongAssociation` with the indexed name check and the fast
strong check. -/
def checkNormalizedArtifactStrongAssociationF {input : Input} (accepted : AcceptedAssociation input)
    {support : Array Kernel.Declaration} (bundle : AdmittedSupport accepted.toAdmittedArtifact support)
    (installed : SourceNormalizedInstallation input.source input.roots)
    (names certificates operationCertificates elementCertificates : Kernel.Name → Kernel.Name)
    (levels : Kernel.Name → Kernel.Level) : Option Bool :=
  bothChecks (some (semanticNamesFast accepted names))
    (checkStrongAssociationF installed.env bundle.env names certificates operationCertificates
      elementCertificates levels)

theorem checkNormalizedArtifactStrongAssociationF_eq {input : Input} (accepted : AcceptedAssociation input)
    {support : Array Kernel.Declaration} (bundle : AdmittedSupport accepted.toAdmittedArtifact support)
    (installed : SourceNormalizedInstallation input.source input.roots)
    (names certificates operationCertificates elementCertificates : Kernel.Name → Kernel.Name)
    (levels : Kernel.Name → Kernel.Level) :
    checkNormalizedArtifactStrongAssociationF accepted bundle installed names certificates
        operationCertificates elementCertificates levels =
      checkNormalizedArtifactStrongAssociation accepted bundle installed names certificates
        operationCertificates elementCertificates levels := by
  unfold checkNormalizedArtifactStrongAssociationF checkNormalizedArtifactStrongAssociation
  rw [checkStrongAssociationF_eq]
  congr 2
  by_cases h : SemanticNamesAgree accepted names
  · rw [decide_eq_true h]; exact (semanticNamesFast_iff accepted names).mpr h
  · rw [decide_eq_false h]; exact Bool.eq_false_iff.mpr (mt (semanticNamesFast_iff accepted names).mp h)

/-- Compiled code runs the fast strong check wherever it calls
`checkNormalizedArtifactStrongAssociation` (`decideStrongCone`, `StrongCone.lean`). -/
@[csimp] theorem checkNormalizedArtifactStrongAssociation_eq_fast :
    @checkNormalizedArtifactStrongAssociation = @checkNormalizedArtifactStrongAssociationF := by
  funext input accepted support bundle installed names certificates operationCertificates
    elementCertificates levels
  exact (checkNormalizedArtifactStrongAssociationF_eq accepted bundle installed names certificates
    operationCertificates elementCertificates levels).symm

/-! ## The individual checks, for the certifier's diagnostics and `--explain` -/

def checkInstalledTypesFast (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Bool :=
  checkInstalledTypesF source (envFind source) (envFind target) names

@[csimp] theorem checkInstalledTypes_eq_fast : @checkInstalledTypes = @checkInstalledTypesFast := by
  funext source target names
  simp only [checkInstalledTypesFast, envFind_eq, checkInstalledTypesF_env]

def checkInstalledDefinitionsFast (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Bool :=
  checkInstalledDefinitionsF source (envFind source) (envFind target) names

@[csimp] theorem checkInstalledDefinitions_eq_fast : @checkInstalledDefinitions = @checkInstalledDefinitionsFast := by
  funext source target names
  simp only [checkInstalledDefinitionsFast, envFind_eq, checkInstalledDefinitionsF_env]

def checkInstalledComparisonAvailabilityFast (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) :
    Option Bool :=
  checkInstalledComparisonAvailabilityF source (envFind source) (envFind target) names

@[csimp] theorem checkInstalledComparisonAvailability_eq_fast :
    @checkInstalledComparisonAvailability = @checkInstalledComparisonAvailabilityFast := by
  funext source target names
  simp only [checkInstalledComparisonAvailabilityFast, envFind_eq, checkInstalledComparisonAvailabilityF_env]

@[csimp] theorem checkInstalledTowers_eq_fast : @checkInstalledTowers = @checkInstalledTowersFast := by
  funext source target names
  exact (checkInstalledTowersFast_eq source target names).symm

@[csimp] theorem checkInstalledAssociation_eq_fast : @checkInstalledAssociation = @checkInstalledAssociationF := by
  funext source target names
  exact (checkInstalledAssociationF_eq source target names).symm

def checkTelescopesFast (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Bool :=
  checkTelescopesF source (envFind target) names

@[csimp] theorem checkTelescopes_eq_fast : @checkTelescopes = @checkTelescopesFast := by
  funext source target names
  simp only [checkTelescopesFast, envFind_eq, checkTelescopesF_env]

def checkInstalledCapabilitiesFast (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Bool :=
  checkInstalledCapabilitiesF source (envFind source) (envFind target) names

@[csimp] theorem checkInstalledCapabilities_eq_fast :
    @checkInstalledCapabilities = @checkInstalledCapabilitiesFast := by
  funext source target names
  simp only [checkInstalledCapabilitiesFast, envFind_eq, checkInstalledCapabilitiesF_env]

def checkInstalledRecursorsFast (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Bool :=
  checkInstalledRecursorsF source (envFind source) (envFind target) names

@[csimp] theorem checkInstalledRecursors_eq_fast : @checkInstalledRecursors = @checkInstalledRecursorsFast := by
  funext source target names
  simp only [checkInstalledRecursorsFast, envFind_eq, checkInstalledRecursorsF_env]

def checkInstalledConstructorsFast (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) : Bool :=
  checkInstalledConstructorsF source (envFind source) (envFind target) names

@[csimp] theorem checkInstalledConstructors_eq_fast :
    @checkInstalledConstructors = @checkInstalledConstructorsFast := by
  funext source target names
  simp only [checkInstalledConstructorsFast, envFind_eq, checkInstalledConstructorsF_env]

def checkInstalledEtaAssociationsFast (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) :
    Option Bool :=
  checkInstalledEtaAssociationsF source (envFind source) (envFind target) names

@[csimp] theorem checkInstalledEtaAssociations_eq_fast :
    @checkInstalledEtaAssociations = @checkInstalledEtaAssociationsFast := by
  funext source target names
  simp only [checkInstalledEtaAssociationsFast, envFind_eq, checkInstalledEtaAssociationsF_env]

def checkInstalledRuleLevelLinksFast (source target : Kernel.Env) (names : Kernel.Name → Kernel.Name) :
    Option Bool :=
  checkInstalledRuleLevelLinksF source (envFind source) (envFind target) names

@[csimp] theorem checkInstalledRuleLevelLinks_eq_fast :
    @checkInstalledRuleLevelLinks = @checkInstalledRuleLevelLinksFast := by
  funext source target names
  simp only [checkInstalledRuleLevelLinksFast, envFind_eq, checkInstalledRuleLevelLinksF_env]

/-- The type literal walk, skipped when both environments support literals alike. -/
def checkTypeLiteralSupportC (source target : Kernel.Env) : Bool :=
  source.consts.all fun entry => checkExprLiteralSupport source target entry.toConstantVal.type

def checkTypeLiteralSupportFast (source target : Kernel.Env) : Bool :=
  if decide (Kernel.natLitSupported source = Kernel.natLitSupported target) &&
      decide (Kernel.strLitSupported source = Kernel.strLitSupported target) then true
  else checkTypeLiteralSupportC source target

@[csimp] theorem checkTypeLiteralSupport_eq_fast : @checkTypeLiteralSupport = @checkTypeLiteralSupportFast := by
  funext source target
  unfold checkTypeLiteralSupportFast
  split
  · rename_i h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact List.all_eq_true.mpr fun entry _ => checkExprLiteralSupport_both h.1 h.2 _
  · rfl

/-- The definition literal walk, skipped when both environments support literals alike. -/
def checkDefinitionLiteralSupportC (source target : Kernel.Env) : Bool :=
  source.consts.all fun entry => match entry with
    | .defnInfo _ value _ => checkExprLiteralSupport source target value
    | _ => true

def checkDefinitionLiteralSupportFast (source target : Kernel.Env) : Bool :=
  if decide (Kernel.natLitSupported source = Kernel.natLitSupported target) &&
      decide (Kernel.strLitSupported source = Kernel.strLitSupported target) then true
  else checkDefinitionLiteralSupportC source target

@[csimp] theorem checkDefinitionLiteralSupport_eq_fast :
    @checkDefinitionLiteralSupport = @checkDefinitionLiteralSupportFast := by
  funext source target
  unfold checkDefinitionLiteralSupportFast
  split
  · rename_i h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact List.all_eq_true.mpr fun entry _ => by
      cases entry <;> simp [checkExprLiteralSupport_both h.1 h.2]
  · rfl

/-- `SemanticNamesAgree` decided through the indices wherever it is decided below. -/
@[csimp] theorem instDecidableSemanticNamesAgree_eq_fast :
    @instDecidableSemanticNamesAgree = @semanticNamesDecidable := by
  funext input accepted names
  exact Subsingleton.elim _ _

end Ix.CompileCert
