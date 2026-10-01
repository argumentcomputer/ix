module

public import ConLeche.Kernel.Inductives.NativeInstallF
public import ConLeche.Cached.CoreC

@[expose] public section

/-!
# The cached declaration driver

The declaration checker *above* `CheckerOps` is shared verbatim with
the generic one: only the core is replaced.  What lives here is the
thin per-declaration phase-driver layer at `CheckCM`, plus the
entry-point record over the cached core.

What the layer is *for*: the per-declaration phase driver that the
parsed-declaration driver (`ConLeche/Cached/ParsedC.lean`) and its bridges
consume — at a `CheckMode` (the trusted twin `ParsedT`/`CoreT` retired
2026-09-06, the configuration record that briefly stood in for the mode
retired at task #185; see `ParsedC.lean`'s header).  The `Expr`-typed
shared fold `checkDeclsShared` went at task #172 with the interned
checker it existed to compare against.
-/

namespace ConLeche.Cached

open ConLeche

/-! ### The direct installers' walkers (task #214) -/

/-- `Expr.instPisAtLift` at the memoised substitution. -/
def instPisAtLiftC : List Expr → Expr → Option Expr
  | [], e => some e
  | a :: as, .forallE _ body _ => instPisAtLiftC as (Expr.instantiate1LiftC body a)
  | _ :: _, _ => none

/-- `structProjBodiesGo` at the memoised substitution. -/
def structProjBodiesGoC (T : Name) : Nat → Nat → Expr → Option (List Expr)
  | 0, _, _ => some []
  | k + 1, i, .forallE fdom body _ =>
    (structProjBodiesGoC T k (i + 1) (Expr.instantiate1LiftC body (structProjArgP T i))).map
      (fdom :: ·)
  | _ + 1, _, _ => none

/-- `structProjBodies` at the memoised substitution
(`structProjBodiesC_eq`). -/
def structProjBodiesC (T : Name) (nP nF : Nat) (cty : Expr) : Option (Array Expr) :=
  match instPisAtLiftC (structProjPs nP) cty with
  | some r => (structProjBodiesGoC T nF 0 r).map List.toArray
  | none => none

/-- **The cached driver's walkers**: the memoised constant-resolution
gate (`constsResolveFC`, verified at `constsResolveFC_spec`) and the
memoised projection-body builder; equal to `StructWalkers.plain`
(`structWalkersC_eq_plain`). -/
def structWalkersC : StructWalkers := ⟨constsResolveFC, structProjBodiesC⟩

variable (mode : CheckMode)

/-! ## The entry-point record over the cached core

`opE`/`opB`/`opS` used to convert their `Expr` arguments in and their
results out.  Since task #172 B3a there is one expression type, so they
pass their arguments through — measured at −3.5 % / −3.8 % instructions
on `init-prelude` / `app-lam`, which is where that batch's win came
from. -/

/-- Shared-state unary entry point: run the cached knot. -/
def opE (fe : FEnv) (pick : CoreFnsI → Nat → Expr → CheckCM Expr)
    (d : Nat) (e : Expr) : CheckCM Expr := do
  pick (coreKnotI mode fe checkFuel) d e

/-- Shared-state definitional-equality entry point. -/
def opB (fe : FEnv) (d : Nat) (a b : Expr) : CheckCM Bool :=
  (coreKnotI mode fe checkFuel).defeq d a b

/-- Shared-state sort-ensuring entry point. -/
def opS (fe : FEnv) (d : Nat) (e : Expr) : CheckCM Level :=
  ensureSortI (coreKnotI mode fe checkFuel) d e

/-- The per-declaration shared operations at a fixed environment
index. -/
def sharedOpsC (fe : FEnv) : CheckerOps CheckCM where
  annotate _ d e := opE mode fe (·.annotate) d e
  inferType _ d e := opE mode fe (·.infer) d e
  isDefEq _ d a b := opB mode fe d a b
  ensureSort _ d e := opS mode fe d e
  whnf _ d e := opE mode fe (·.whnf) d e
  -- the executable's instantiation delivers the attempt's outcome to
  -- the continuation (the decline message names what each pin variant
  -- failed on); after an error the state is the PRE-attempt one — the
  -- memo entries the failed attempt wrote are discarded with it
  orElse x k := fun s => match x s with
    | .ok (true, s') => .ok ((), s')
    | .ok (false, s') => k none s'
    | .error e => k (some e) s

/-! ## Thin phase drivers (one `CState` per declaration)

Each mirrors its `ConLeche/Kernel/Checker.lean` counterpart clause by
clause; the differences are exactly: `flushC` at environment
transitions, `FEnv.push` maintaining the index, and *every*
environment lookup routed through the index (task #63). -/

/-- One non-recursor member (mirrors `checkIndMember`). -/
def checkIndMemberS (blockNames : List Name) (caps : IndCaps)
    (fe : FEnv) (ci : ConstantInfo) : CheckCM FEnv := do
  flushC
  let cvA ← checkMemberValF (sharedOpsC mode fe) blockNames fe ci.toConstantVal
  match ci with
  | .indInfo _ _ => pure (fe.push (.indInfo cvA caps))
  | .ctorInfo _ nP nF => pure (fe.push (.ctorInfo cvA nP nF))
  | _ => throw (.invalid s!"non-inductive member {cvA.name} in block")

/-- Phase 0 of the recursor group (mirrors `provisionRecs`). -/
def provisionRecsS (blockNames : List Name) :
    FEnv → List ConstantInfo →
    CheckCM (FEnv × List (ConstantVal × Nat × Nat × List RecRule))
  | feAcc, [] => pure (feAcc, [])
  | feAcc, ci :: rest =>
    match ci with
    | .recInfo _ mI rP rules => do
      flushC
      let cvA ← checkMemberValF (sharedOpsC mode feAcc) blockNames feAcc
        ci.toConstantVal
      let (feSelf, others) ← provisionRecsS blockNames
        (feAcc.push (.recInfo cvA mI rP [])) rest
      pure (feSelf, (cvA, mI, rP, rules) :: others)
    | _ => throw (.notImplemented "recursor before other block members")

/-- The recursor group (mirrors `checkIndRecs`).  All iota-rule checks
run at `envSelf` — one flush entering the phase, none inside the fold
(the fold's accumulator environments are never passed to the
operations).  The ruled recursors are installed on the `env₂` snapshot
of the index. -/
def checkIndRecsS (blockNames : List Name) (fe₂ : FEnv)
    (recs : List ConstantInfo) : CheckCM FEnv := do
  if recs.isEmpty then
    pure fe₂
  else do
    let f : Name → Name := fun n =>
      if blockNames.contains n then n.str "_model" else n
    unless fe₂.find? eqName = some eqA do
      throw (.notImplemented "modeled recursor requires the pinned Eq basis")
    let (feSelf, checked) ← provisionRecsS mode blockNames fe₂ recs
    flushC
    checked.foldlM (fun (acc : FEnv) c => do
        let rules' ← checkIotaRulesF mode (sharedOpsC mode feSelf) fe₂ feSelf
          f c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
        pure (acc.push (.recInfo c.1 c.2.1 c.2.2.1 rules')))
      fe₂

/-- The public projection function for field `i` (mirrors
`checkProjFn`; the single-environment stages are the generic ones). -/
def checkProjFnS (fe : FEnv) (T ctorName : Name) (lps : List Name)
    (nP nF i : Nat) : CheckCM FEnv := do
  let (cvj, mcv) ← checkProjLookupsF (m := CheckCM) fe T ctorName lps
    nP nF i
  let pty ← checkProjTyF (m := CheckCM) fe T ctorName lps mcv.type nP nF
  checkProjShape (m := CheckCM) pty cvj.type nP nF
  unless i < nF do
    throw (.invalid "projection index out of range")
  let rhsA ← checkProjRuleF (sharedOpsC mode fe) fe pty cvj lps nP nF i
  checkProjIotaF mode (sharedOpsC mode fe) fe T ctorName lps cvj nP nF i
  pure (fe.push (.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
    [projFnRule fe.find? T ctorName pty nP nF i rhsA]))

/-- One projection-function install step (mirrors `installProjFnStep`;
the artifact lookup goes through the index). -/
def installProjFnStepS (T ctorName : Name) (lps : List Name)
    (nP nF : Nat) (fe : FEnv) (i : Nat) : CheckCM FEnv := do
  if (fe.find? (projModelName T i)).isSome then do
    flushC
    checkProjFnS mode fe T ctorName lps nP nF i
  else pure fe

/-- `checkNativePass` through the index (task #268): one flush per
environment transition. -/
def checkNativePassS (fe : FEnv) (p₀ : NativeParts) (isRec : Bool) :
    CheckCM (NativePass FEnv × Bool) := do
  let (fe₁, cvTa, p₁) ← checkSumIndF (sharedOpsC mode fe) fe p₀.toInductiveShape
    (fun p₁ => nativeCapsAt p₁ isRec)
  let pC := p₀.complete p₁
  flushC
  let (ctorsA, sortss) ← checkSumCtorsF (sharedOpsC mode fe₁) fe₁ fe₁ pC.cvT.name
    pC.cvT.levelParams pC.nP pC.nIdx pC.resSort pC.isProp pC.large cvTa pC.ctors
  let kinds ← classifyFixKinds (m := CheckCM) pC.cvT.name pC.cvT.levelParams pC.nP pC.nIdx
    ctorsA
  let p := pC.withKinds kinds
  pure (⟨fe₁, cvTa, p, ctorsA, sortss⟩, nativeCaps p == nativeCapsAt p₁ isRec)

/-- `checkNativeTail` through the index: one flush entering the
recursor's environment. -/
def checkNativeTailS (fe : FEnv) (q : NativePass FEnv) : CheckCM FEnv := do
  let p := q.p
  if p.large && !p.resSort.isNeverZero && decide (2 ≤ p.ctors.length) then
    throw (.invalid "direct rec: large eliminator on a multi-constructor inductive \
      whose sort may be Prop")
  let tq ← unwrapOr (openPisAtFvars (p.nP + p.nIdx) q.cvTa.type 0)
    (.internal "direct rec: type former telescope")
  let _isorts ← checkStructFieldSortsIF (sharedOpsC mode q.env₁) q.env₁ true false p.resSort
    p.nP (tq.1.drop p.nP) [] p.nIdx
  unless nativeFieldsOkF structWalkersC fe p.cvT.name p.cvT.levelParams p.nP p.nIdx q.ctorsA
      p.kinds do
    throw (.internal "direct rec: field kinds")
  unless nativeRulesOk p.cvR.name (p.cvR.levelParams.map .param) .never p.nP p.ctors.length
      q.ctorsA p.kinds p.rhss p.cvR.type do
    throw (.invalid "direct rec: recursor rules are not the generated ones")
  let fe₂ := consSumCtorsF p.nP q.ctorsA q.env₁
  flushC
  let (cvRa, rhss) ← checkNativeRecF (sharedOpsC mode fe₂) structWalkersC fe₂ p q.cvTa q.ctorsA
  -- the projection table at a structure-like block (task #210 Part A)
  checkNativeTableF (m := CheckCM) structWalkersC p q.ctorsA q.sortss (fe₂.push (.recInfo cvRa
    p.majorIdx p.rulePrefix (sumRules fe₂.find? cvRa.name p.nP p.majorIdx p.rulePrefix
      cvRa.type q.ctorsA rhss)))

/-- `checkNative` through the index (task #188): the pass at the
syntactic `is_rec` reading, again at the classified verdict where the
reading overshot (task #268), and the install after it. -/
def checkNativeS (fe : FEnv) (p₀ : NativeParts) : CheckCM FEnv := do
  unless (p₀.ctors.map (·.1.name)).Nodup do
    throw (.invalid "direct rec: duplicate constructor")
  flushC
  let (q, settled) ← checkNativePassS mode fe p₀ (nativeRawRec p₀)
  if settled then checkNativeTailS mode fe q
  else do
    flushC
    let (q', settled') ← checkNativePassS mode fe p₀ (nativeIsRec q.p.kinds)
    unless settled' do
      throw (.internal "direct rec: the capability record did not settle")
    checkNativeTailS mode fe q'

/-- The modeled inductive block (mirrors `checkModeled`), returning
the extended index. -/
def checkIndDeclSF (fe : FEnv) (block : List ConstantInfo) :
    CheckCM FEnv := do
  let recs := block.filter (fun ci => match ci with
    | .recInfo _ _ _ _ => true | _ => false)
  let nonrecs := block.filter (fun ci => match ci with
    | .recInfo _ _ _ _ => false | _ => true)
  -- the tag pass, not the derived structural equality on the members'
  -- types (`ConLeche/Kernel/Env.lean`): the STATEMENT is unchanged, the
  -- decision is `recsFormSuffix`
  unless @decide _ (blockRecSuffixDec block) do
    throw (.notImplemented "recursor before other block members")
  let blockNames := block.map (·.name)
  match block.filter (fun ci => match ci with
      | .indInfo _ _ => true | _ => false),
    block.filter (fun ci => match ci with
      | .ctorInfo _ _ _ => true | _ => false) with
  | [.indInfo cvT _], [.ctorInfo cvC nP nF] =>
    let caps ← pure (indBlockCapsF mode fe cvT cvC nP nF)
    let fe₂ ← nonrecs.foldlM (checkIndMemberS mode blockNames caps) fe
    let fe₃ ← checkIndRecsS mode blockNames fe₂ recs
    unless ctorResidualOkF mode fe₃ cvT.name cvC.name cvT.levelParams nP nF
        caps.eta do
      throw (.notImplemented "modeled structure: eta constructor residual")
    unless (List.range nF).all
        (fun j => (fe₃.find? (projFnName cvT.name j)).isNone) do
      throw (.invalid "projection name family taken")
    if ctorTargetsFam cvC.type cvT.name cvT.levelParams nP nF then
      (List.range nF).foldlM
        (installProjFnStepS mode cvT.name cvC.name cvT.levelParams nP nF)
        fe₃
    else pure fe₃
  | _, _ => do
    let fe₂ ← nonrecs.foldlM (checkIndMemberS mode blockNames {}) fe
    checkIndRecsS mode blockNames fe₂ recs

end ConLeche.Cached
