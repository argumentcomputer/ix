module

public import ConLeche.Kernel.CheckerBase

@[expose] public section

/-!
# The modeled-inductive install

Everything the checker runs to install a **modeled** inductive block —
one whose `_model` family the frontend generated in-process at parse
time (`ConLeche/Frontend/InModel/*`; task #207 made that the only
source, and the install never knew the provenance either way): the
member checks against the `_model` artifacts under the **group-local**
renaming (only the current block's member names are identified with
their companions -- the model contract, ours to keep since #207: model
types match the renamed public types syntactically), the iota-rule
checks against the `_model.iota_j` theorems, the capability checks
(`checkEtaThm`/`checkUnitThm`), and the projection-function/template
installs.  The core checker (`ConLeche/Kernel/Core.lean`,
`TypeChecker*`) never imports this module; `ConLeche/Kernel/Checker.lean`
consumes it for `checkDecl`'s `indDecl` arm.  Verification:
`ConLeche/Verify/Extend/*` and `ConLeche/Model/Ind*P.lean`.
-/

namespace ConLeche

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]
variable (mode : CheckMode)

/-- Certify that both sides of a modeled iota equation inhabit the
equation's type (task #100 stage-3 finding: the collapse removed
value-driven domain pinning, so the fold derivation reads these
certificates), and that the equation's type slot itself inhabits the
sort the statement's own `Eq.{ℓA}` names (task #146: the `IndBottom*`
obligations fire the equality law, whose first β-step wants exactly
that membership; the slot is a motive application, so no syntactic pin
can serve it and inverting the theorem's derivation would need
Π-injectivity, which `propext` refutes). -/
def checkIotaSidesTy (ops : CheckerOps m) (envSelf : Env) (depth : Nat)
    (alphaS lhsS rhsS : Expr) (ℓA : Level) (cvName : Name) : m Unit := do
  let tl ← ops.inferType envSelf depth lhsS
  unless ← ops.isDefEq envSelf depth tl alphaS do
    throw (.notImplemented s!"iota statement lhs type for {cvName}")
  let tr ← ops.inferType envSelf depth rhsS
  unless ← ops.isDefEq envSelf depth tr alphaS do
    throw (.notImplemented s!"iota statement rhs type for {cvName}")
  -- TT-lane check (task #147): the slot-sort certification (task
  -- #146) is skipped unless `mode.ttChecks`.
  if mode.ttChecks then
    let tα ← ops.inferType envSelf depth alphaS
    unless ← ops.isDefEq envSelf depth tα (.sort ℓA) do
      throw (.notImplemented s!"iota statement type slot sort for {cvName}")

/-- Check a *canonical* recursor rule's `iota_j` theorem,
*semantically*: the stored theorem's telescope is opened at free
variables, its body must be an `Eq`, the equation's left side is
structurally the renamed recursor applied to the opened variables and
a canonical major (its index arguments definitionally the
constructor's canonical index tuple), and the right side is
definitionally the rule's applied right-hand side.  The opened
telescope's domains are definitionally the recursor's prefix and the
constructor's field domains (renamed), and the rule's own λ-domains
definitionally the public ones — the memberships the fold fact
quantifies over transfer along these equalities.  Definitional
comparison makes the checks insensitive to hygienic binder names and
reducible wrappers (`optParam` etc.) in the stored types. -/
def checkIotaThm (ops : CheckerOps m) (env' envSelf : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP j : Nat) (r : RecRule) (cvj : ConstantVal)
    (cnP cnF : Nat) (rhsA : Expr) : m Unit := do
    let cvt ← unwrapOr
        (env'.findCV? ((cvName.str "_model").str s!"iota_{j}"))
        (.notImplemented s!"missing iota theorem for {cvName}")
    unless cvt.levelParams = lps do
      throw (.notImplemented s!"iota theorem level mismatch for {cvName}")
    -- open the theorem's telescope: params, motives, minors, fields
    let depth := rP + cnF
    let (fvs, tbody) ← unwrapOr (openPisAtFvars depth cvt.type 0)
      (.notImplemented s!"iota statement shape mismatch for {cvName}")
    -- the body is an equation (at one level, like the pinned `Eq`)
    let targs := tbody.getAppArgs
    unless isEqHead tbody.getAppFn do
      throw (.notImplemented s!"iota statement not an equation for {cvName}")
    unless targs.length = 3 do
      throw (.notImplemented s!"iota statement not an equation for {cvName}")
    let lhsS := targs.getD 1 (.bvar 0)
    let rhsS := targs.getD 2 (.bvar 0)
    -- the equation's left side: structurally the renamed recursor
    -- applied to the opened prefix variables, `mI - rP` index arguments
    -- (checked below against the constructor's canonical tuple),
    -- and the constructor at its own level parameters applied to
    -- the leading parameter variables and the field variables
    let xFvs := fvs.drop rP
    let largs := lhsS.getAppArgs
    unless lhsS.getAppFn == Expr.const (f cvName) (lps.map .param) do
      throw (.notImplemented s!"iota statement head mismatch for {cvName}")
    unless largs.length = mI + 1 do
      throw (.notImplemented s!"iota statement arity mismatch for {cvName}")
    unless largs.take rP == fvs.take rP do
      throw (.notImplemented s!"iota statement prefix mismatch for {cvName}")
    let major := largs.getLastD (.bvar 0)
    unless major == Expr.mkAppN
        (.const (f r.ctor) (cvj.levelParams.map .param))
        (fvs.take cnP ++ xFvs) do
      throw (.notImplemented s!"iota statement major mismatch for {cvName}")
    -- the constructor's telescope (renamed), instantiated at the
    -- major's arguments: field domains and the canonical index tuple
    unless (cvj.type.stripPis (cnP + cnF)).isSome do
      throw (.notImplemented s!"iota constructor telescope for {cvName}")
    let (cdoms, cres) ← unwrapOr
        (Expr.instPisAt (fvs.take cnP ++ xFvs) (cvj.type.renameConsts f))
        (.notImplemented s!"iota constructor telescope for {cvName}")
    unless cres.getAppArgs.length = cnP + (mI - rP) do
      throw (.notImplemented s!"iota constructor indices for {cvName}")
    checkDefEqList ops envSelf depth ((largs.drop rP).take (mI - rP))
      (cres.getAppArgs.drop cnP)
    checkDefEqList ops envSelf depth (xFvs.map Expr.fvarTypeD)
      (cdoms.drop cnP)
    -- the statement's prefix domains are the recursor's (renamed)
    let (rdoms, _) ← unwrapOr
        (Expr.instPisAt (fvs.take rP) (tyA.renameConsts f))
        (.notImplemented s!"iota recursor telescope for {cvName}")
    checkDefEqList ops envSelf depth
      ((fvs.take rP).map Expr.fvarTypeD) rdoms
    -- the rule's λ-domains are the public recursor prefix and
    -- constructor field domains (the fold fact's value spines fit
    -- the public telescopes; these equalities let them fit the λs)
    let (fvsP, _) ← unwrapOr (openPisAtFvars rP tyA 0)
      (.notImplemented s!"iota recursor telescope for {cvName}")
    let (cdomsP, crestP) ← unwrapOr
      (Expr.instPisAt (fvsP.take cnP) cvj.type)
      (.notImplemented s!"iota constructor telescope for {cvName}")
    -- the constructor's parameter domains are the recursor's (the
    -- λ-tower's parameter values fit both telescopes)
    checkDefEqList ops envSelf depth
      ((fvsP.take cnP).map Expr.fvarTypeD) cdomsP
    let (xFvsP, _) ← unwrapOr (openPisAtFvars cnF crestP rP)
      (.notImplemented s!"iota constructor telescope for {cvName}")
    let (ldoms, _) ← unwrapOr (Expr.instLamsAt (fvsP ++ xFvsP) rhsA)
      (.notImplemented s!"rule shape mismatch for {cvName}")
    checkDefEqList ops envSelf depth ((fvsP ++ xFvsP).map Expr.fvarTypeD)
      ldoms
    -- the right side: definitionally the rule's applied rhs
    let rhsApplied := Expr.mkAppN (rhsA.renameConsts f) fvs
    unless ← ops.isDefEq envSelf depth rhsS rhsApplied do
      throw (.notImplemented s!"iota statement mismatch for {cvName}")
    checkIotaSidesTy mode ops envSelf depth (targs.getD 0 (.bvar 0)) lhsS
      rhsS (eqHeadLevel tbody.getAppFn) cvName

/-- The nested-shape data of a non-canonical rule: the constructor's
level and parameter instantiations, read off the recursor type's
major-premise domain
(`∀ …prefix… …indices…, ∀ (t : D.{lvls} p₁ … p_cnP i₁ … i_k), …`,
`k = mI - rP`).  The parameter instantiations are stored *lowered into
the rule-prefix context* (`rP` binders; `Expr.lowerBVars`) — the
lift-back roundtrip certifies that no index variable occurs in them —
and the domain's trailing arguments must be exactly the index
variables in order.  `none` — the rule stays inert, and a matched
major declines at fire time — when the model stores no `iota_j`
constant, the prefix exceeds the major's position, the major domain is
not a constant-headed application of exactly `cnP + k` arguments of
this split shape, or an instantiation fails the syntactic
well-formedness guards (closed, bounded by the prefix telescope,
constants resolving, levels declared — the facts `EnvWF` records for
the stored rule). -/
def nestedRuleShape (env' envSelf : Env) (cvName : Name)
    (lps : List Name) (tyA : Expr) (mI rP cnP j : Nat) :
    Option (List Level × List Expr) :=
  if (env'.findCV? ((cvName.str "_model").str s!"iota_{j}")).isSome ∧
      rP ≤ mI then
    match tyA.stripPis mI with
    | some (_, .forallE dom _ _) =>
      match dom.getAppFn with
      | .const _D lvls =>
        let args := dom.getAppArgs
        let k := mI - rP
        let pins := (args.take cnP).map (Expr.lowerBVars k 0)
        if args.length = cnP + k ∧
            args.take cnP == pins.map (Expr.liftLooseBVars k 0) ∧
            args.drop cnP ==
              (List.range k).map (fun i => Expr.bvar (k - 1 - i)) ∧
            pins.all (fun p => !p.hasFvar && p.looseBVarsBounded rP &&
              p.constsResolve envSelf && p.allLevelParamsDefined lps) ∧
            lvls.all (Level.allParamsDefined lps) then
          some (lvls, pins)
        else none
      | _ => none
    | _ => none
  else none

/-- Check a *nested-auxiliary* recursor rule's `iota_j` theorem — the
generalization of `checkIotaThm` to rules whose constructor parameters
and levels are fixed instantiations (`nestedRuleShape`): the theorem's
canonical major applies the constructor at the stored level
instantiations to the stored parameter instantiations (opened at the
statement's prefix variables) and the field variables, and the
constructor's telescope walks are taken at those instantiations.  The
major is pinned structurally (`==`; binder names are not part of an
`Expr` since task #205 — the `checkMemberVal` granularity): unlike the plain major, whose
arguments are all opened variables, the stored pins can contain
binders (dependent nested occurrences, `Impl α (fun _ => T ...)`), and
export arenas intern name-insensitively, so the theorem's pin spelling
can differ from the recursor type's in binder names only.  When
the rule has no certifiable shape the rule is stored inert (`.inert`;
a matched major positively declines at fire time); a shape whose
theorem then fails the pin is a positive decline here. -/
def checkIotaThmN (ops : CheckerOps m) (env' envSelf : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP j : Nat) (r : RecRule) (cvj : ConstantVal)
    (cnP cnF : Nat) (rhsA : Expr) : m RecRuleFire := do
    match nestedRuleShape env' envSelf cvName lps tyA mI rP cnP j with
    | none => pure .inert
    | some (lvls, pins) => do
    let cvt ← unwrapOr
        (env'.findCV? ((cvName.str "_model").str s!"iota_{j}"))
        (.notImplemented s!"missing iota theorem for {cvName}")
    unless cvt.levelParams = lps do
      throw (.notImplemented s!"iota theorem level mismatch for {cvName}")
    -- open the theorem's telescope: params, motives, minors, fields
    let depth := rP + cnF
    let (fvs, tbody) ← unwrapOr (openPisAtFvars depth cvt.type 0)
      (.notImplemented s!"iota statement shape mismatch for {cvName}")
    let targs := tbody.getAppArgs
    unless isEqHead tbody.getAppFn do
      throw (.notImplemented s!"iota statement not an equation for {cvName}")
    unless targs.length = 3 do
      throw (.notImplemented s!"iota statement not an equation for {cvName}")
    let lhsS := targs.getD 1 (.bvar 0)
    let rhsS := targs.getD 2 (.bvar 0)
    -- the equation's left side: structurally the renamed recursor
    -- applied to the opened prefix variables and the constructor at
    -- the stored level instantiations, applied to the stored parameter
    -- instantiations (renamed, opened at the prefix variables) and the
    -- field variables
    let xFvs := fvs.drop rP
    let pinsF := pins.map fun p =>
      Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f)
    let largs := lhsS.getAppArgs
    unless lhsS.getAppFn == Expr.const (f cvName) (lps.map .param) do
      throw (.notImplemented s!"iota statement head mismatch for {cvName}")
    unless largs.length = mI + 1 do
      throw (.notImplemented s!"iota statement arity mismatch for {cvName}")
    unless largs.take rP == fvs.take rP do
      throw (.notImplemented s!"iota statement prefix mismatch for {cvName}")
    let major := largs.getLastD (.bvar 0)
    -- structural up to display-only binder names: the stored pins may
    -- contain binders (dependent nested occurrences), and the artifact
    -- contract only fixes statements up to `Expr.eqv` — export arenas
    -- intern name-insensitively, so the theorem's pin spelling can
    -- differ from the recursor type's in binder names only
    unless major == (Expr.mkAppN (.const (f r.ctor) lvls)
        (pinsF ++ xFvs)) do
      throw (.notImplemented s!"iota statement major mismatch for {cvName}")
    -- the constructor's telescope at the stored level instantiations
    -- (renamed), instantiated at the major's arguments: field domains
    -- and the canonical index tuple.  The residual head must be a
    -- constant (the family former): the soundness layer decomposes
    -- both residual walks argument-wise over it, and a variable head
    -- could be captured by a pin instantiation.
    let (_, cbody0) ← unwrapOr (cvj.type.stripPis (cnP + cnF))
      (.notImplemented s!"iota constructor telescope for {cvName}")
    unless (match cbody0.getAppFn with
        | .const _ _ => true
        | _ => false) do
      throw (.notImplemented s!"iota constructor residual head for {cvName}")
    let (cdoms, cres) ← unwrapOr
        (Expr.instPisAt (pinsF ++ xFvs)
          ((cvj.type.instantiateLevelParams cvj.levelParams
            lvls).renameConsts f))
        (.notImplemented s!"iota constructor telescope for {cvName}")
    unless cres.getAppArgs.length = cnP + (mI - rP) do
      throw (.notImplemented s!"iota constructor indices for {cvName}")
    checkDefEqList ops envSelf depth ((largs.drop rP).take (mI - rP))
      (cres.getAppArgs.drop cnP)
    checkDefEqList ops envSelf depth (xFvs.map Expr.fvarTypeD)
      (cdoms.drop cnP)
    -- the statement's prefix domains are the recursor's (renamed)
    let (rdoms, _) ← unwrapOr
        (Expr.instPisAt (fvs.take rP) (tyA.renameConsts f))
        (.notImplemented s!"iota recursor telescope for {cvName}")
    checkDefEqList ops envSelf depth
      ((fvs.take rP).map Expr.fvarTypeD) rdoms
    -- the rule's λ-domains are the public recursor prefix and the
    -- constructor's field domains at the public instantiations
    let (fvsP, _) ← unwrapOr (openPisAtFvars rP tyA 0)
      (.notImplemented s!"iota recursor telescope for {cvName}")
    let pinsP := pins.map fun p =>
      Expr.instSpine (fvsP.take rP) (rP - 1) p
    -- the instantiated pins are fixed points of the annotation pass
    -- (their annotation truthfulness is read off this certificate at
    -- the canonical frame; with index premises it is not derivable
    -- from the recursor-type walk)
    checkAnnotList ops envSelf depth pinsP
    let (cdomsP, crestP) ← unwrapOr (Expr.instPisAt pinsP
        (cvj.type.instantiateLevelParams cvj.levelParams lvls))
      (.notImplemented s!"iota constructor telescope for {cvName}")
    -- the stored parameter instantiations inhabit the constructor's
    -- parameter domains (the λ-tower's parameter values fit them)
    checkTypedList ops envSelf depth pinsP cdomsP
    let (xFvsP, crest2P) ← unwrapOr (openPisAtFvars cnF crestP rP)
      (.notImplemented s!"iota constructor telescope for {cvName}")
    -- the auxiliary constructor's residual applies the family to its
    -- parameters and the canonical index tuple (empty at `mI = rP`)
    unless crest2P.getAppArgs.length == cnP + (mI - rP) do
      throw (.notImplemented s!"iota constructor arity for {cvName}")
    let (ldoms, _) ← unwrapOr (Expr.instLamsAt (fvsP ++ xFvsP) rhsA)
      (.notImplemented s!"rule shape mismatch for {cvName}")
    checkDefEqList ops envSelf depth ((fvsP ++ xFvsP).map Expr.fvarTypeD)
      ldoms
    -- the right side: definitionally the rule's applied rhs
    let rhsApplied := Expr.mkAppN (rhsA.renameConsts f) fvs
    unless ← ops.isDefEq envSelf depth rhsS rhsApplied do
      throw (.notImplemented s!"iota statement mismatch for {cvName}")
    checkIotaSidesTy mode ops envSelf depth (targs.getD 0 (.bvar 0)) lhsS
      rhsS (eqHeadLevel tbody.getAppFn) cvName
    pure (.nested lvls pins)

/-- Check one modeled recursor rule: generic well-formedness of the
right-hand side, then the model's `iota_j` theorem — for canonical
rules the plain statement pin (`checkIotaThm`), for nested-auxiliary
rules the generalized pin over the stored instantiations
(`checkIotaThmN`; rules without a certifiable shape are stored inert:
`iotaRec` never fires on them and a matched major declines). -/
def checkIotaRule (ops : CheckerOps m) (env' envSelf : Env)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP j : Nat) (r : RecRule) : m RecRule := do
    let some (.ctorInfo cvj cnP cnF) := env'.find? r.ctor
      | throw (.invalid s!"iota rule constructor {r.ctor} not stored")
    unless r.nfields = cnF do
      throw (.invalid "rule field count mismatch")
    unless r.rhs.looseBVarsBounded 0 do
      throw (.invalid s!"loose bound variable in rule of {cvName}")
    if r.rhs.hasFvar then
      throw (.invalid s!"free variable in rule of {cvName}")
    let rhsA ← ops.annotate envSelf 0 r.rhs
    unless rhsA.allLevelParamsDefined lps do
      throw (.invalid s!"undeclared universe parameter in rule of {cvName}")
    unless rhsA.constsResolve envSelf do
      throw (unresolvedConstsError s!"rule of {cvName}" rhsA)
    -- the rule's rhs must be a λ-telescope over the recursor prefix
    -- and the constructor fields (so it can be applied positionally)
    unless (rhsA.stripLams (rP + cnF)).isSome do
      throw (.notImplemented s!"rule shape mismatch for {cvName}")
    -- infer the rule's type: soundness interprets the (λ-tower)
    -- right-hand side through this inference
    let _rhsTy ← ops.inferType envSelf 0 rhsA
    -- the firing mode is computed once, here, and stored on the rule;
    -- `iotaRec` reads the flag instead of re-walking the recursor type
    -- on every fire
    let fire ← if Expr.recRulePlain tyA mI rP cnP then do
        checkIotaThm mode ops env' envSelf f cvName lps tyA mI rP j r
          cvj cnP cnF rhsA
        pure RecRuleFire.plain
      else
        checkIotaThmN mode ops env' envSelf f cvName lps tyA mI rP j r
          cvj cnP cnF rhsA
    pure (recRuleBits env'.find? cvName
      { r with rhs := rhsA, ctorParams := cnP, fire := fire,
               paramsBlind := false })

/-- The per-rule check, folded over a modeled recursor's rules. -/
def checkIotaRules (ops : CheckerOps m) (env' envSelf : Env) (f : Name → Name)
    (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP : Nat) : Nat → List RecRule → m (List RecRule)
  | _, [] => pure []
  | j, r :: rest => do
    let r' ← checkIotaRule mode ops env' envSelf f cvName lps tyA mI rP j r
    let rest' ← checkIotaRules ops env' envSelf f cvName lps tyA mI rP
      (j + 1) rest
    pure (r' :: rest')

/-- Check a block member's constant against its `_model` counterpart:
`checkConstantVal`, the member may not itself be model-shaped, and its
type is the model's under the block renaming — structurally (`==`;
binder names are not part of an `Expr` since task #205, so a
generator's re-spelling of a shared binder cannot make this miss).
On failure the
message dumps both sides, which identifies the offending subterm
immediately. -/
def checkMemberVal (ops : CheckerOps m) (blockNames : List Name)
    (env' : Env) (cv : ConstantVal) : m ConstantVal := do
  let f : Name → Name := fun n =>
    if blockNames.contains n then n.str "_model" else n
  let cvA ← checkConstantVal ops env' cv
  -- a member may not itself be shaped like a model companion, so the
  -- block renaming can never map onto a member
  if cvA.name.isModelSuffix then
    throw (.invalid s!"model-shaped member name {cvA.name}")
  -- the model counterpart
  let some (.defnInfo cvm _mval _) := env'.find? (cvA.name.str "_model")
    | throw (.notImplemented s!"no install route for inductive block \
        {blockNames.headD cvA.name}: no direct route recognises it and no \
        model for {cvA.name} was generated")
  unless cvm.levelParams = cvA.levelParams do
    throw (.notImplemented s!"model level parameters mismatch for {cvA.name}")
  unless cvA.type.renameConsts f == cvm.type do
    throw (.notImplemented
      s!"model type mismatch for {cvA.name}\n  member (renamed): \
        {reprStr (cvA.type.renameConsts f)}\n  model: {reprStr cvm.type}")
  pure cvA

/-- Check and install one non-recursor member of a modeled inductive
block against its `_model` counterpart (the step of `checkModeled`'s
fold, lifted for verification).  `caps` is the capability record the
block earned (recorded on the inductive type former).  Recursors are
handled by `checkIndRecs`. -/
def checkIndMember (ops : CheckerOps m) (blockNames : List Name)
    (caps : IndCaps) (env' : Env) (ci : ConstantInfo) : m Env := do
  let cvA ← checkMemberVal ops blockNames env' ci.toConstantVal
  match ci with
  | .indInfo _ _ => pure (⟨.indInfo cvA caps :: env'.consts⟩ : Env)
  | .ctorInfo _ nP nF => pure ⟨.ctorInfo cvA nP nF :: env'.consts⟩
  | _ => throw (.invalid s!"non-inductive member {cvA.name} in block")

/-- Phase 0 of the recursor group: check each recursor's constant and
provision it *rule-less* on top of the previous ones.  Returns the
fully provisioned environment together with the checked constants (in
order).  Rule right-hand sides may mention any recursor of the block
(mutual and nested blocks), so they are annotated only against the
fully provisioned environment. -/
def provisionRecs (ops : CheckerOps m) (blockNames : List Name) :
    Env → List ConstantInfo →
    m (Env × List (ConstantVal × Nat × Nat × List RecRule))
  | envAcc, [] => pure (envAcc, [])
  | envAcc, ci :: rest =>
    match ci with
    | .recInfo _ mI rP rules => do
      let cvA ← checkMemberVal ops blockNames envAcc ci.toConstantVal
      let (envSelf, others) ← provisionRecs ops blockNames
        ⟨.recInfo cvA mI rP [] :: envAcc.consts⟩ rest
      pure (envSelf, (cvA, mI, rP, rules) :: others)
    | _ => throw (.notImplemented "recursor before other block members")

/-- Check and install a block's recursors *as a group*: every rule
right-hand side may mention any of them, so all are provisioned
rule-less together (`envSelf`) and installed together — no
intermediate environment stores a recursor whose rules mention a
missing sibling. -/
def checkIndRecs (ops : CheckerOps m) (blockNames : List Name)
    (env₂ : Env) (recs : List ConstantInfo) : m Env := do
  if recs.isEmpty then
    pure env₂
  else do
    let f : Name → Name := fun n =>
      if blockNames.contains n then n.str "_model" else n
    -- iota statements are equations: pin the pinned equality former
    unless env₂.find? eqName = some eqA do
      throw (.notImplemented "modeled recursor requires the pinned Eq basis")
    let (envSelf, checked) ← provisionRecs ops blockNames env₂ recs
    checked.foldlM (fun (acc : Env) c => do
        let rules' ← checkIotaRules mode ops env₂ envSelf f c.1.name
          c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
        pure (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.consts⟩ : Env))
      env₂

/-- Rename a model-side projection type back to public names. -/
def projBack (T ctor : Name) (nF : Nat) : Name → Name := fun n =>
  if n = T.str "_model" then T
  else if n = ctor.str "_model" then ctor
  else
    match (List.range nF).find? (fun j => n == projModelName T j) with
    | some j => projFnName T j
    | none => n

/-- The forward (public → model) map on the projection family. -/
def projFwd (T ctor : Name) (nF : Nat) : Name → Name := fun n =>
  if n = T then T.str "_model"
  else if n = ctor then ctor.str "_model"
  else
    match (List.range nF).find? (fun j => n == projFnName T j) with
    | some j => projModelName T j
    | none => n

/-- Stage 1 of `checkProjFn`: the stored constants the projection
depends on — the single constructor (arity-matched), the model's
`proj_i` definition (level-matched), the parent type, and the pinned
equality former; the projection's own name must be free. -/
def checkProjLookups (env' : Env) (T ctorName : Name) (lps : List Name)
    (nP nF i : Nat) : m (ConstantVal × ConstantVal) := do
  let some (.ctorInfo cvj cnP cnF) := env'.find? ctorName
    | throw (.notImplemented "projection constructor not stored")
  unless cnP = nP ∧ cnF = nF do
    throw (.notImplemented "projection constructor arity mismatch")
  let some (.defnInfo mcv _ _) := env'.find? (projModelName T i)
    | throw (.notImplemented "missing projection model")
  unless mcv.levelParams = lps do
    throw (.notImplemented "projection model level mismatch")
  unless (env'.find? (projFnName T i)).isNone do
    throw (.invalid "projection name taken")
  unless (env'.find? T).isSome do
    throw (.notImplemented "projection parent not stored")
  unless env'.find? eqName = some eqA do
    throw (.notImplemented "projection iota requires the pinned Eq basis")
  pure (cvj, mcv)

/-- Stage 2: the public projection type — the model's, renamed back
(pinned by the renaming roundtrip), well-formed and parameter-led. -/
def checkProjTy (env' : Env) (T ctorName : Name) (lps : List Name)
    (mty : Expr) (nP nF : Nat) : m Expr := do
  let pty := mty.renameConsts (projBack T ctorName nF)
  unless (pty.renameConsts (projFwd T ctorName nF)) == mty do
    throw (.notImplemented "projection type roundtrip")
  unless pty.constsResolve env' do
    throw (.notImplemented "projection type resolution")
  unless pty.looseBVarsBounded 0 && !pty.hasFvar &&
      pty.allLevelParamsDefined lps do
    throw (.notImplemented "projection type wellformedness")
  unless (pty.stripPis (nP + 1)).isSome do
    throw (.notImplemented "projection type telescope")
  pure pty

/-- Stage 4: the model's `proj_i.iota` theorem pins the rule — the
statement's telescope domains are the constructor's (renamed to the
model side) and its body equates the projected constructor spine with
field `i`.  Both equation sides are certified against the equality's
type slot definitionally at the opened telescope, and the slot itself
against the sort the statement's `Eq.{ℓA}` names (task #100 stage-3:
the collapse removed value-driven domain pinning, and dependent field
types are emitted through the projections, so a syntactic pin on the
type slot would reject real streams; task #146 for the slot's sort). -/
def checkProjIota (ops : CheckerOps m) (env' envSelf : Env)
    (T ctorName : Name) (lps : List Name)
    (cvj : ConstantVal) (nP nF i : Nat) : m Unit := do
  let some (.thmInfo tcv _) := env'.find? ((projModelName T i).str "iota")
    | throw (.notImplemented "missing projection iota theorem")
  unless tcv.levelParams = lps do
    throw (.notImplemented "projection iota level mismatch")
  let some (sbinders, sbody) := tcv.type.stripPis (nP + nF)
    | throw (.notImplemented "projection iota telescope")
  let some (cbindersR, _) := cvj.type.stripPis (nP + nF)
    | throw (.notImplemented "projection constructor telescope")
  unless domsMatchAux
      (fun _ e => e.renameConsts (projFwd T ctorName nF))
      sbinders cbindersR 0 0 (nP + nF) do
    throw (.notImplemented "projection iota domain mismatch")
  let depth := nP + nF
  let pArgs := (List.range nP).map fun k => Expr.bvar (depth - 1 - k)
  let xArgs := (List.range nF).map fun k => Expr.bvar (nF - 1 - k)
  let mkSpine := Expr.mkAppN
    (.const (ctorName.str "_model") (cvj.levelParams.map .param))
    (pArgs ++ xArgs)
  let lhsS := Expr.mkAppN
    (.const (projModelName T i) (lps.map .param)) (pArgs ++ [mkSpine])
  match sbody with
  | .app (.app (.app (.const c [_ℓ]) _tySlot) lhsC) rhsC =>
    unless c = eqName do
      throw (.notImplemented "projection iota head")
    unless lhsC == lhsS do
      throw (.notImplemented "projection iota redex mismatch")
    unless rhsC == Expr.bvar (nF - 1 - i) do
      throw (.notImplemented "projection iota field mismatch")
  | _ => throw (.notImplemented "projection iota body shape")
  -- certify both equation sides against the statement's type slot,
  -- definitionally at the opened telescope (the fold derivation
  -- reads these certificates), and the slot itself against the sort
  -- the statement's `Eq.{ℓA}` names (task #146)
  let (_, sbodyO) ← unwrapOr (openPisAtFvars depth tcv.type 0)
    (.notImplemented "projection iota telescope")
  let targsO := sbodyO.getAppArgs
  checkIotaSidesTy mode ops envSelf depth (targsO.getD 0 (.bvar 0))
    (targsO.getD 1 (.bvar 0)) (targsO.getD 2 (.bvar 0))
    (eqHeadLevel sbody.getAppFn) (projModelName T i)

/-- Check and install the public projection function for field `i` of
a modeled single-constructor structure, against the model's
`T._model.proj_i` definition and its `iota` theorem.  The function is
stored as a degenerate recursor (no motive, no minors) carrying one
rule, so the generic iota machinery reduces it. -/
def checkProjFn (ops : CheckerOps m) (env' : Env) (T ctorName : Name) (lps : List Name)
    (nP nF i : Nat) : m Env := do
  let (cvj, mcv) ← checkProjLookups env' T ctorName lps nP nF i
  let pty ← checkProjTy env' T ctorName lps mcv.type nP nF
  checkProjShape pty cvj.type nP nF
  unless i < nF do
    throw (.invalid "projection index out of range")
  let rhsA ← checkProjRule ops env' pty cvj lps nP nF i
  checkProjIota mode ops env' env' T ctorName lps cvj nP nF i
  -- a degenerate recursor: no motive, no minors, no indices, so the
  -- major sits at position nP and the rule prefix is the parameters;
  -- the canonical flag is computed here, once, like `checkIotaRule`
  pure ⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
    [projFnRule env'.find? T ctorName pty nP nF i rhsA] ::
    env'.consts⟩

/-- Does the model document structural eta for this single-constructor
block — a `T._model.eta` theorem with the pinned statement
`∀ p⃗ (x : T._model p⃗), x = C._model p⃗ (T._model.proj_0 p⃗ x) …`?
Checked before install; a positive answer records the eta capability
on the stored inductive.  (`Bool`-valued: an absent or differently
shaped artifact just means no capability.)  The parameter telescope is
pinned against the constructor *model*'s (both live on the model side
and are annotated by the same pipeline); the equality's type slot is
pinned to the family application (task #100) and its sort to the
statement's own `Eq` level (task #135). -/
def checkEtaThm (env' : Env) (T ctorName : Name) (lps : List Name)
    (nP nF : Nat) : Bool :=
  match env'.find? ((T.str "_model").str "eta"),
      env'.find? (T.str "_model"),
      env'.find? (ctorName.str "_model"), env'.find? eqName with
  | some (.thmInfo tcv _), some (.defnInfo cvmT _ _),
      some (.defnInfo cvmC _ _), some eqStored =>
    eqStored == eqA && tcv.levelParams == lps &&
    cvmT.levelParams == lps && cvmC.levelParams == lps &&
    -- the projection models exist at the family's level parameters
    (List.range nF).all (fun j =>
      match env'.find? (projModelName T j) with
      | some (.defnInfo cvmj _ _) => cvmj.levelParams == lps
      | _ => false) &&
    (match tcv.type.stripPis (nP + 1), cvmT.type.stripPis nP with
     | some (sbinders, sbody), some (tbindersM, tbodyM) =>
       domsMatchAux (fun _ e => e) sbinders tbindersM 0 0 nP &&
       (match sbinders[nP]? with
        | some (xdom, _) =>
          xdom == Expr.mkAppN (.const (T.str "_model") (lps.map .param))
            ((List.range nP).map fun k => Expr.bvar (nP - 1 - k))
        | none => false) &&
       (match sbody with
        | .app (.app (.app (.const c [ℓA]) tySlot) lhsC) rhsC =>
          c == eqName && lhsC == Expr.bvar 0 &&
          -- the equation's type slot is the family application (task
          -- #100 stage-3: the fold derivation reads the statement's
          -- domain off this pin)
          tySlot == Expr.mkAppN (.const (T.str "_model") (lps.map .param))
            ((List.range nP).map fun k => Expr.bvar (nP - k)) &&
          rhsC == Expr.mkAppN
            (.const (ctorName.str "_model") (lps.map .param))
            (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
             (List.range nF).map fun j => Expr.mkAppN
               (.const (projModelName T j) (lps.map .param))
               (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
                [Expr.bvar 0])) &&
          -- the model former's telescope residual is the equation's own
          -- sort (task #135): the type slot above is `T._model p⃗`, so
          -- this says the slot lives at `Sort ℓA` for the very `ℓA` the
          -- statement's `Eq` carries — the premise `eqValT`'s first
          -- β-step needs and Π-injectivity cannot recover.  TT-lane
          -- check (task #147): skipped unless `mode.ttChecks`.
          (!mode.ttChecks || tbodyM == Expr.sort ℓA)
        | _ => false)
     | _, _ => false)
  | _, _, _, _ => false

/-- Does the model document unit-likeness for this block — a
`T._model.unitlike` theorem with the pinned statement
`∀ p⃗ (x y : T._model p⃗), x = y`?  Checked before install; a positive
answer records the unit-like capability on the stored inductive. -/
def checkUnitThm (env' : Env) (T : Name) (lps : List Name)
    (nP : Nat) : Bool :=
  match env'.find? ((T.str "_model").str "unitlike"),
      env'.find? (T.str "_model"), env'.find? eqName with
  | some (.thmInfo tcv _), some (.defnInfo cvmT _ _), some eqStored =>
    eqStored == eqA && tcv.levelParams == lps &&
    cvmT.levelParams == lps &&
    (match tcv.type.stripPis (nP + 2), cvmT.type.stripPis nP with
     | some (sbinders, sbody), some (tbindersM, tbodyM) =>
       domsMatchAux (fun _ e => e) sbinders tbindersM 0 0 nP &&
       (match sbinders[nP]? with
        | some (xdom, _) =>
          xdom == Expr.mkAppN (.const (T.str "_model") (lps.map .param))
            ((List.range nP).map fun k => Expr.bvar (nP - 1 - k))
        | none => false) &&
       (match sbinders[nP + 1]? with
        | some (ydom, _) =>
          ydom == Expr.mkAppN (.const (T.str "_model") (lps.map .param))
            ((List.range nP).map fun k => Expr.bvar (nP - k))
        | none => false) &&
       (match sbody with
        | .app (.app (.app (.const c [ℓA]) tySlot) lhsC) rhsC =>
          c == eqName && lhsC == Expr.bvar 1 && rhsC == Expr.bvar 0 &&
          -- type-slot pin, as in `checkEtaThm` (task #100 stage 3)
          tySlot == Expr.mkAppN (.const (T.str "_model") (lps.map .param))
            ((List.range nP).map fun k => Expr.bvar (nP + 1 - k)) &&
          -- and the slot's sort is the equation's own level (task
          -- #135; see `checkEtaThm`).  TT-lane check (task #147):
          -- skipped unless `mode.ttChecks`.
          (!mode.ttChecks || tbodyM == Expr.sort ℓA)
        | _ => false)
     | _, _ => false)
  | _, _, _ => false

/-- **Official's structure-likeness, read off the block's own
constructor** (`is_non_rec_structure`, `src/kernel/inductive.cpp`: one
constructor and *no indices*; the recursion half is decided by the
projection artifacts' own shape).  An index-free single-constructor
family's constructor targets the family at exactly its parameters,
`T p⃗` — the same conjunct `checkStructCtor` pins on the direct route —
while an indexed family's targets `T p⃗ i⃗`.

Task #175 SigmaHom (2026-09-06): the modeller also emits
`T._model.proj_i` artifacts for an *indexed* one-constructor family
(its indexed-fibre projection tranche; `CategoryTheory.Sigma.SigmaHom`
in Mathlib), and consuming them as projection functions declined at
`checkProjShape`'s residual pin, where the official kernel accepts the
block.  User ruling: indexed types are not structure-like — the model's
projections are **ignored** at install (the artifacts stay ordinary
definitions), and a `.proj` on such a type declines at its own site,
as it does for every type without a table (official rejects it).  So
the projection phase of `checkModeled` runs only when this holds.

The subject is the block's *incoming* constructor type, not the stored
one: the decision is then a function of the block, which is what the
parity↔P agreement floor's skeleton specification
(`indDeclSkelsModeled`) can compute.  It is a gate, not a pin — the
installs it admits are checked in full by `checkProjFn`. -/
def ctorTargetsFam (ctorTy : Expr) (T : Name) (lps : List Name)
    (nP nF : Nat) : Bool :=
  match ctorTy.stripPis (nP + nF) with
  | some (_, cbody) => cbody == structFam T lps nP nF
  | none => false

/-- One projection-function install step (skipped where the model's
projection artifact is absent — a family with such fields simply gets
no table, and a `.proj` on it declines at its own site; task #175
tower-flag retired the inert elimination-template table that used to
record the family).  The whole fold is skipped for a block that is not
structure-like (`ctorTargetsFam`). -/
def installProjFnStep (ops : CheckerOps m) (T ctorName : Name)
    (lps : List Name) (nP nF : Nat) (e : Env) (i : Nat) : m Env :=
  if (e.find? (projModelName T i)).isSome then
    checkProjFn mode ops e T ctorName lps nP nF i
  else pure e

/-- The capabilities recorded for a single-constructor modeled block. -/
def indBlockCaps (env : Env) (cvT cvC : ConstantVal) (nP nF : Nat) :
    IndCaps where
  eta := (cvC.levelParams = cvT.levelParams) &&
    checkEtaThm mode env cvT.name cvC.name cvT.levelParams nP nF
  etaCtor := cvC.name
  etaParams := nP
  etaFields := nF
  unitlike := checkUnitThm mode env cvT.name cvT.levelParams nP
  unitParams := nP
  ruleK := nF == 0 && piResultIsProp cvT.type
  sortZ := piResultZ cvT.type

/-- The modeled route stores the family's own result-sort datum, so
`capsNeverZero` at the stored record is `piResultNeverZero` at the
stored type (`capsNeverZero_eq`). -/
@[simp] theorem indBlockCaps_sortZ (env : Env) (cvT cvC : ConstantVal)
    (nP nF : Nat) :
    (indBlockCaps mode env cvT cvC nP nF).sortZ = piResultZ cvT.type := rfl

/-- **Task #136: an eta-capable family's constructor returns the family
applied to its parameters.**  Literally the conjunct `checkStructCtor`
(`ConLeche/Kernel/Checker.lean`) already makes on the direct path,
`cbody == structFam T lps nP nF`, here on the modeled path.

Two things about it are load-bearing and were measured, not argued.

*The subject is the **stored** constant.*  Not the block's incoming
`ConstantVal`: the environment contains only what `checkMemberVal`
stored — `checkConstantVal`'s **annotated** output — and that is what
every consumer reads back (`constTyAt`, and the fire-site certificate
through it).  A check on the raw type would be a different syntactic
object and would owe a bridge lemma "annotation preserves a
constructor's residual" that nothing else needs.  Hence the `find?`:
the check reads the constant exactly the way its consumers do.  (The
corpus says the two never disagree — 1356 blocks, 0 differences — but
that is evidence, not a licence to check the wrong object.)

*The capability guard is not cosmetic.*  Unguarded, this conjunct is
**refuted by the corpus** at the *indexed* families (`Acc`, `HEq`,
`Int.NonNeg`, `IndexedSingleton`, `IndexedUnit`, `SortElimProp`, …)
whose residual is `T p⃗ i⃗`; they earn no capability and must keep
installing untouched.  Guarded on `eta` it is corpus-clean: 975/975
eta-capable blocks satisfy it, and every one of the 91 failures is a
block with neither capability.  `unitlike` does not need it — its
right-hand side is a law premise, not a fabricated spine. -/
def ctorResidualOk (env' : Env) (T ctorName : Name) (lps : List Name)
    (nP nF : Nat) (eta : Bool) : Bool :=
  -- TT-lane check (task #147): trivially true unless `mode.ttChecks`.
  !mode.ttChecks || !eta ||
  (match env'.find? ctorName with
   | some (.ctorInfo cvCA _ _) =>
     (match cvCA.type.stripPis (nP + nF) with
      | some (_, cbody) => cbody == structFam T lps nP nF
      | none => false)
   | _ => false)

/-- Check and install a modeled inductive block: every member is
checked against its `_model` counterpart (type up to the public↔model
renaming, iota rules against the model's `iota_j` theorems), then
stored as a real inductive-kind constant.  Single-constructor blocks
determine their capability record first (recorded on the inductive)
and, when structure-like (`ctorTargetsFam`: the constructor targets
the family at exactly its parameters — no indices), additionally
install the projection functions the model documents (skipped where
the artifacts are absent).  The K flag is computed from
shape exactly as the official kernel does — an inductive proposition
with a single constructor taking only the parameters; the reduction
site carries the semantic load (proof irrelevance), so no model
theorem backs the flag. -/
def checkModeled (ops : CheckerOps m) (env : Env) (block : List ConstantInfo) : m Env := do
  -- the recursors must form a suffix of the block: their rules may
  -- mention each other, so they install as a group after everything
  -- else
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
    let caps ← pure (indBlockCaps mode env cvT cvC nP nF)
    let env₂ ← nonrecs.foldlM
      (checkIndMember ops blockNames caps) env
    let env₃ ← checkIndRecs mode ops blockNames env₂ recs
    -- the eta capability's constructor returns the family (task #136)
    unless ctorResidualOk mode env₃ cvT.name cvC.name cvT.levelParams nP nF
        caps.eta do
      throw (.notImplemented "modeled structure: eta constructor residual")
    -- the whole projection name family must be ours to install
    unless (List.range nF).all
        (fun j => (env₃.find? (projFnName cvT.name j)).isNone) do
      throw (.invalid "projection name family taken")
    -- the projection functions: structure-like blocks only (task #175
    -- SigmaHom; an indexed family's model projections are ignored)
    if ctorTargetsFam cvC.type cvT.name cvT.levelParams nP nF then
      (List.range nF).foldlM
        (installProjFnStep mode ops cvT.name cvC.name cvT.levelParams nP nF)
        env₃
    else pure env₃
  | _, _ => do
    let env₂ ← nonrecs.foldlM (checkIndMember ops blockNames {}) env
    checkIndRecs mode ops blockNames env₂ recs


end ConLeche
