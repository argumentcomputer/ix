module

public import ConLeche.Semantics.DeclRun

@[expose] public section

/-!
# `DeclIndRun` — the inductive kind's run/guard record family (task
#161 S11b, THE SEPARATION)

`DeclRun` (`SetBase/DeclRun.lean`) took the inductive kind's payload
as a **parameter** `Ind` — S4's slot, held open because the ind tier's
run projection was not yet designed.  This module supplies it.

**The shape, and why it is exactly this** (task #161 S10 ruling 1,
"payload ZERO"): the family below is `DeclIndRun`
(`SetBase/Decl.lean`) with every `∀ φ : Name → Nat, …` conjunct struck
out.  That is not a preference — it is a measurement.  The S10 seal
counted the derivation conjuncts the graded lane reads from the
ind-tier cone and found **three**, then rewired all three to
`acceptedReads_of` ("whatever `inferTypeCore` accepts, `denoteMeta`
reads", `Model/Steps/Accepted.lean`), which produces those readings
from the *runs*.  The count is now **zero**, so the run family owes no
derivation row at all.

**And therefore it carries no valuation.**  Each record below takes
`cval : TConstVal` in `DeclIndRun` for one reason only — to state its
own `∀ φ` rows — and the block folds thread `cvalModeled` /
`cvalWith` only to *feed* those rows at the next environment.  Strike
the rows and the whole valuation column dies with them: `MemberValRun`
has no `cval` because `ConstantValRun` has none, `IndMembersRun` has
no running valuation because there is nothing left to key on it, and
`DeclIndRun` binds no intermediate `cvalM`/`cvalR`/`cvalP`.  The
family is valuation-free outright, exactly like `DeclRun` — no
`denote`, no `Infer`, no `DefEq`, no `V`.

**Reused verbatim, not re-stated** (the S4 discipline):

* `IotaRuns` (`SetBase/Decl.lean`) — the walks' *recorded runs* were
  already valuation-free when H1 landed them, and both families point
  at the same definition;
* `DefEqListOk` / `TypedListOk` — the run halves of the two typed
  walks, likewise already there.

**What consumes it**: `checkDeclRun_ofEnvFactsE`'s `Ind` slot
(`SetBase/Bridge/Sound.lean`), fed by `declIndRun_of`
(`SetBase/Bridge/DeclIndRun.lean`), and the graded lane's ind tier
(`Model/DeclInd.lean` and the eight files below it).  The R lane keeps
proving `DeclIndRun`: nothing here replaces it, and the two families are
independent consumers of the same checker inversions.
-/

namespace ConLeche.Semantics

open ConLeche.Term ConLeche.Verify

/-! ## The block members -/

/-- `MemberValR`'s run/guard half: the member's front door
(`ConstantValRun`) and the model-counterpart pins, which were always
pure stored-data lookups. -/
def MemberValRun (μ : CheckMode) (F : Nat) (env' : Env)
    (blockNames : List Name) (cv : ConstantVal) (cvA : ConstantVal) :
    Prop :=
  ∃ type',
    ConstantValRun μ F env' cv type' ∧
    cvA = ⟨cv.name, cv.levelParams, type'⟩ ∧
    cvA.name.isModelSuffix = false ∧
    ∃ cvm mval hint,
      env'.find? (cvA.name.str "_model")
        = some (.defnInfo cvm mval hint) ∧
      cvm.levelParams = cvA.levelParams ∧
      ((cvA.type.renameConsts fun n =>
          if blockNames.contains n then n.str "_model" else n)
          == cvm.type) = true

/-- `IndMembersR`'s run/guard half.  **The running valuation is gone**:
`IndMembersR` threads `cvalModeled` from step to step so that member
`k`'s front door speaks at the valuation the members before it built,
and the front door is the only thing that reads it.  With the front
door's derivation struck, the fold is a plain walk over the running
*environment*. -/
def IndMembersRun (μ : CheckMode) (F : Nat)
    (blockNames : List Name) (caps : IndCaps) :
    Env → List ConstantInfo → Env → Prop
  | env', [], env₂ => env₂ = env'
  | env', ci :: rest, env₂ =>
    ∃ cvA, MemberValRun μ F env' blockNames ci.toConstantVal cvA ∧
      match ci with
      | .indInfo _ _ =>
        IndMembersRun μ F blockNames caps
          ⟨.indInfo cvA caps :: env'.consts⟩ rest env₂
      | .ctorInfo _ nP nF =>
        IndMembersRun μ F blockNames caps
          ⟨.ctorInfo cvA nP nF :: env'.consts⟩ rest env₂
      | _ => False

/-- `ProvisionRecsR`'s run/guard half. -/
def ProvisionRecsRun (μ : CheckMode) (F : Nat)
    (blockNames : List Name) :
    Env → List ConstantInfo →
    Env → List (ConstantVal × Nat × Nat × List RecRule) → Prop
  | envAcc, [], envSelf, checked =>
    envSelf = envAcc ∧ checked = []
  | envAcc, ci :: rest, envSelf, checked =>
    ∃ cvA mI rP rules rest',
      ci = .recInfo ci.toConstantVal mI rP rules ∧
      MemberValRun μ F envAcc blockNames ci.toConstantVal cvA ∧
      ProvisionRecsRun μ F blockNames
        ⟨.recInfo cvA mI rP [] :: envAcc.consts⟩ rest envSelf rest' ∧
      checked = (cvA, mI, rP, rules) :: rest'

/-! ## The rule packs -/

/-- `IotaThmR`'s run/guard half: the shape pins verbatim, the
parameter-domain comparison's recorded run (`DefEqListOk`), and
`IotaRuns` — the six walk rows' checker verdicts.  What is struck is
the `∀ φ` parameter-domain walk and `IotaWalksR` itself. -/
def IotaThmRun (μ : CheckMode) (F : Nat) (env' envSelf : Env)
    (f : Name → Name) (cvName : Name)
    (lps : List Name) (tyA : Expr) (mI rP j : Nat) (r : RecRule)
    (cvj : ConstantVal) (cnP cnF : Nat) (rhsA : Expr) : Prop :=
  ∃ cvt fvs tbody,
    env'.findCV? ((cvName.str "_model").str s!"iota_{j}") = some cvt ∧
    cvt.levelParams = lps ∧
    openPisAtFvars (rP + cnF) cvt.type 0 = some (fvs, tbody) ∧
    isEqHead tbody.getAppFn = true ∧
    tbody.getAppArgs.length = 3 ∧
    (let depth := rP + cnF
     let targs := tbody.getAppArgs
     let lhsS := targs.getD 1 (.bvar 0)
     let rhsS := targs.getD 2 (.bvar 0)
     let xFvs := fvs.drop rP
     let largs := lhsS.getAppArgs
     (lhsS.getAppFn == Expr.const (f cvName) (lps.map .param)) = true ∧
     largs.length = mI + 1 ∧
     (largs.take rP == fvs.take rP) = true ∧
     (largs.getLastD (.bvar 0) == Expr.mkAppN
        (.const (f r.ctor) (cvj.levelParams.map .param))
        (fvs.take cnP ++ xFvs)) = true ∧
     (cvj.type.stripPis (cnP + cnF)).isSome = true ∧
     ∃ cdoms cres rdoms fvsP cdomsP crestP xFvsP crest2 ldoms lrest,
       Expr.instPisAt (fvs.take cnP ++ xFvs) (cvj.type.renameConsts f)
         = some (cdoms, cres) ∧
       cres.getAppArgs.length = cnP + (mI - rP) ∧
       Expr.instPisAt (fvs.take rP) (tyA.renameConsts f)
         = some (rdoms, lrest) ∧
       openPisAtFvars rP tyA 0 = some (fvsP, crest2) ∧
       Expr.instPisAt (fvsP.take cnP) cvj.type = some (cdomsP, crestP) ∧
       openPisAtFvars cnF crestP rP = some (xFvsP, ldoms) ∧
       ∃ ldomsL lrest2,
         Expr.instLamsAt (fvsP ++ xFvsP) rhsA = some (ldomsL, lrest2) ∧
         DefEqListOk μ F envSelf depth
           ((fvsP.take cnP).map Expr.fvarTypeD) cdomsP ∧
         IotaRuns μ F envSelf depth
           ((largs.drop rP).take (mI - rP)) (cres.getAppArgs.drop cnP)
           (xFvs.map Expr.fvarTypeD) (cdoms.drop cnP)
           ((fvs.take rP).map Expr.fvarTypeD) rdoms
           ((fvsP ++ xFvsP).map Expr.fvarTypeD) ldomsL
           rhsS (Expr.mkAppN (rhsA.renameConsts f) fvs)
           (targs.getD 0 (.bvar 0)) lhsS)

/-- `IotaThmNR`'s run/guard half: the nested shape data verbatim (the
generalized major pin, the `checkAnnotList` fixed points, the arity
pin), the pins' recorded typing run (`TypedListOk`), and `IotaRuns`.
Struck: the `∀ φ` `TypedListW` walk and `IotaWalksR`. -/
def IotaThmNRun (μ : CheckMode) (F : Nat) (env' envSelf : Env)
    (f : Name → Name) (cvName : Name)
    (lps : List Name) (tyA : Expr) (mI rP j : Nat) (r : RecRule)
    (cvj : ConstantVal) (cnP cnF : Nat) (rhsA : Expr)
    (lvls : List Level) (pins : List Expr) : Prop :=
  nestedRuleShape env' envSelf cvName lps tyA mI rP cnP j
    = some (lvls, pins) ∧
  ∃ cvt fvs tbody,
    env'.findCV? ((cvName.str "_model").str s!"iota_{j}") = some cvt ∧
    cvt.levelParams = lps ∧
    openPisAtFvars (rP + cnF) cvt.type 0 = some (fvs, tbody) ∧
    isEqHead tbody.getAppFn = true ∧
    tbody.getAppArgs.length = 3 ∧
    (let depth := rP + cnF
     let targs := tbody.getAppArgs
     let lhsS := targs.getD 1 (.bvar 0)
     let rhsS := targs.getD 2 (.bvar 0)
     let xFvs := fvs.drop rP
     let pinsF := pins.map fun p =>
       Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f)
     let largs := lhsS.getAppArgs
     (lhsS.getAppFn == Expr.const (f cvName) (lps.map .param)) = true ∧
     largs.length = mI + 1 ∧
     (largs.take rP == fvs.take rP) = true ∧
     Expr.ErasedEq (largs.getLastD (.bvar 0))
       (Expr.mkAppN (.const (f r.ctor) lvls) (pinsF ++ xFvs)) ∧
     (∃ cbinders cbody0, cvj.type.stripPis (cnP + cnF)
        = some (cbinders, cbody0) ∧
       (match cbody0.getAppFn with
        | .const _ _ => true | _ => false) = true) ∧
     ∃ cdoms cres rdoms lrest fvsP crest2 cdomsP crestP xFvsP ldoms,
       Expr.instPisAt (pinsF ++ xFvs)
         ((cvj.type.instantiateLevelParams cvj.levelParams
           lvls).renameConsts f) = some (cdoms, cres) ∧
       cres.getAppArgs.length = cnP + (mI - rP) ∧
       Expr.instPisAt (fvs.take rP) (tyA.renameConsts f)
         = some (rdoms, lrest) ∧
       openPisAtFvars rP tyA 0 = some (fvsP, crest2) ∧
       (let pinsP := pins.map fun p =>
          Expr.instSpine (fvsP.take rP) (rP - 1) p
        (∀ p ∈ pinsP, annotateCore μ envSelf F depth p = .ok p) ∧
        Expr.instPisAt pinsP
          (cvj.type.instantiateLevelParams cvj.levelParams lvls)
          = some (cdomsP, crestP) ∧
        openPisAtFvars cnF crestP rP = some (xFvsP, ldoms) ∧
        (ldoms.getAppArgs.length == cnP + (mI - rP)) = true) ∧
       ∃ ldomsL lrest2,
         Expr.instLamsAt
           (fvsP ++ xFvsP) rhsA = some (ldomsL, lrest2) ∧
         TypedListOk μ F envSelf depth
           (pins.map fun p =>
             Expr.instSpine (fvsP.take rP) (rP - 1) p) cdomsP ∧
         IotaRuns μ F envSelf depth
           ((largs.drop rP).take (mI - rP)) (cres.getAppArgs.drop cnP)
           (xFvs.map Expr.fvarTypeD) (cdoms.drop cnP)
           ((fvs.take rP).map Expr.fvarTypeD) rdoms
           ((fvsP ++ xFvsP).map Expr.fvarTypeD) ldomsL
           rhsS (Expr.mkAppN (rhsA.renameConsts f) fvs)
           (targs.getD 0 (.bvar 0)) lhsS)

/-- `IotaRuleR`'s run/guard half: the rhs guards, the annotate output,
the λ-telescope shape and the fire-mode dispatch, with the rhs front
door's derivation struck and its recorded `inferTypeCore` run kept. -/
def IotaRuleRun (μ : CheckMode) (F : Nat) (env' envSelf : Env)
    (f : Name → Name) (cvName : Name)
    (lps : List Name) (tyA : Expr) (mI rP j : Nat) (r r' : RecRule) :
    Prop :=
  ∃ cvj cnP cnF rhsA,
    env'.find? r.ctor = some (.ctorInfo cvj cnP cnF) ∧
    r.nfields = cnF ∧
    r.rhs.looseBVarsBounded 0 = true ∧
    r.rhs.hasFvar = false ∧
    annotateCore μ envSelf F 0 r.rhs = .ok rhsA ∧
    rhsA.allLevelParamsDefined lps = true ∧
    rhsA.constsResolve envSelf = true ∧
    (rhsA.stripLams (rP + cnF)).isSome = true ∧
    (∃ t', inferTypeCore μ envSelf F 0 rhsA = .ok t') ∧
    ∃ fire,
      r' = recRuleBits env'.find? cvName
        { r with rhs := rhsA, ctorParams := cnP, fire := fire,
                 paramsBlind := false } ∧
      ((Expr.recRulePlain tyA mI rP cnP = true ∧ fire = .plain ∧
          IotaThmRun μ F env' envSelf f cvName lps tyA mI rP j r
            cvj cnP cnF rhsA) ∨
       (Expr.recRulePlain tyA mI rP cnP = false ∧
          ((fire = .inert ∧
            nestedRuleShape env' envSelf cvName lps tyA mI rP cnP j
              = none) ∨
           (∃ lvls pins, fire = .nested lvls pins ∧
             IotaThmNRun μ F env' envSelf f cvName lps tyA mI rP j r
               cvj cnP cnF rhsA lvls pins))))

/-- `IotaRulesR`'s run/guard half. -/
def IotaRulesRun (μ : CheckMode) (F : Nat) (env' envSelf : Env)
    (f : Name → Name) (cvName : Name)
    (lps : List Name) (tyA : Expr) (mI rP : Nat) :
    Nat → List RecRule → List RecRule → Prop
  | _, [], out => out = []
  | j, r :: rest, out =>
    ∃ r' rest',
      IotaRuleRun μ F env' envSelf f cvName lps tyA mI rP j r r' ∧
      IotaRulesRun μ F env' envSelf f cvName lps tyA mI rP
        (j + 1) rest rest' ∧
      out = r' :: rest'

/-- `IndRecsR`'s run/guard half. -/
def IndRecsRun (μ : CheckMode) (F : Nat)
    (blockNames : List Name) (env₂ : Env)
    (recs : List ConstantInfo) (env₃ : Env) : Prop :=
  (recs = [] ∧ env₃ = env₂) ∨
  (recs ≠ [] ∧
   env₂.find? eqName = some eqA ∧
   ∃ envSelf checked,
     ProvisionRecsRun μ F blockNames env₂ recs envSelf checked ∧
     IndRecsFoldRun μ F blockNames env₂ envSelf env₂ checked env₃)
where
  /-- The install fold over the provisioned group, run half. -/
  IndRecsFoldRun (μ : CheckMode) (F : Nat) (blockNames : List Name)
      (envBase envSelf : Env) :
      Env → List (ConstantVal × Nat × Nat × List RecRule) →
      Env → Prop
    | acc, [], out => out = acc
    | acc, c :: rest, out =>
      ∃ rules',
        IotaRulesRun μ F envBase envSelf
          (fun n => if blockNames.contains n then n.str "_model" else n)
          c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
          rules' ∧
        IndRecsFoldRun μ F blockNames envBase envSelf
          ⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.consts⟩ rest out

/-! ## The projection phase -/

/-- `ProjFnR`'s run/guard half: the five stage inversions verbatim,
with the rule's front-door derivation and the `proj_i.iota` sides
pack's `∀ φ` walk struck (their recorded runs — the `inferTypeCore`
verdict and `checkIotaSidesTy`'s literal pair — stay). -/
def ProjFnRun (μ : CheckMode) (F : Nat) (env' : Env)
    (T ctorName : Name) (lps : List Name) (nP nF i : Nat)
    (env'' : Env) : Prop :=
  ∃ cvj mcv mval mhint pty rhsA,
    env'.find? ctorName = some (.ctorInfo cvj nP nF) ∧
    env'.find? (projModelName T i) = some (.defnInfo mcv mval mhint) ∧
    mcv.levelParams = lps ∧
    (env'.find? (projFnName T i)).isNone = true ∧
    (env'.find? T).isSome = true ∧
    env'.find? eqName = some eqA ∧
    pty = mcv.type.renameConsts (projBack T ctorName nF) ∧
    (pty.renameConsts (projFwd T ctorName nF) == mcv.type) = true ∧
    pty.constsResolve env' = true ∧
    pty.looseBVarsBounded 0 = true ∧
    pty.hasFvar = false ∧
    pty.allLevelParamsDefined lps = true ∧
    (pty.stripPis (nP + 1)).isSome = true ∧
    i < nF ∧
    (pty.stripPis nP).isSome = true ∧
    (∃ cbinders cbody,
      cvj.type.stripPis (nP + nF) = some (cbinders, cbody) ∧
      cbody.getAppArgs.length = nP ∧
      (∃ c cus, cbody.getAppFn = Expr.const c cus) ∧
      rhsA.hasFvar = false ∧
      rhsA.looseBVarsBounded 0 = true ∧
      rhsA.allLevelParamsDefined lps = true ∧
      rhsA.constsResolve env' = true ∧
      (∃ rbinders,
        rhsA.stripLams (nP + nF) = some (rbinders, .bvar (nF - 1 - i)) ∧
        ∀ (i0 : Nat) (b b' : Expr × BinderMeta), i0 < nP + nF →
          rbinders[i0]? = some b → cbinders[i0]? = some b' →
          b.1 = b'.1) ∧
      (∃ t', inferTypeCore μ env' F 0 rhsA = .ok t') ∧
      (∃ tcv tval,
        env'.find? ((projModelName T i).str "iota")
          = some (.thmInfo tcv tval) ∧
        tcv.levelParams = lps ∧
        (∃ (sbinders : List (Expr × BinderMeta)) (ℓA : Level)
            (tySlot : Expr),
          tcv.type.stripPis (nP + nF) = some (sbinders,
            .app (.app (.app (.const eqName [ℓA]) tySlot)
              (Expr.mkAppN (.const (projModelName T i)
                  (lps.map .param))
                (((List.range nP).map fun k =>
                    Expr.bvar (nP + nF - 1 - k)) ++
                 [Expr.mkAppN
                   (.const (ctorName.str "_model")
                     (cvj.levelParams.map .param))
                   (((List.range nP).map fun k =>
                       Expr.bvar (nP + nF - 1 - k)) ++
                    ((List.range nF).map fun k =>
                      Expr.bvar (nF - 1 - k)))])))
              (.bvar (nF - 1 - i))) ∧
          ∀ (i0 : Nat) (b b' : Expr × BinderMeta), i0 < nP + nF →
            sbinders[i0]? = some b → cbinders[i0]? = some b' →
            b.1 = b'.1.renameConsts (projFwd T ctorName nF)) ∧
        ∃ fvsI sbodyO,
          openPisAtFvars (nP + nF) tcv.type 0 = some (fvsI, sbodyO) ∧
          (∃ tl, inferTypeCore μ env' F (nP + nF)
              (sbodyO.getAppArgs.getD 1 (.bvar 0)) = .ok tl ∧
            isDefEqCore μ env' F (nP + nF) tl
              (sbodyO.getAppArgs.getD 0 (.bvar 0)) = .ok true) ∧
          (∃ tr, inferTypeCore μ env' F (nP + nF)
              (sbodyO.getAppArgs.getD 2 (.bvar 0)) = .ok tr ∧
            isDefEqCore μ env' F (nP + nF) tr
              (sbodyO.getAppArgs.getD 0 (.bvar 0)) = .ok true))) ∧
    env'' = ⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
      [projFnRule env'.find? T ctorName pty nP nF i rhsA] :: env'.consts⟩

/-- `ProjInstallR`'s run/guard half.  The valuation the install picks
for the projection function (`cvalWith … (projModelName T i)`) was the
`ProjFnR` front door's, so it goes with it. -/
def ProjInstallRun (μ : CheckMode) (F : Nat)
    (T ctorName : Name) (lps : List Name) (nP nF : Nat) :
    Env → List Nat → Env → Prop
  | env', [], env₄ => env₄ = env'
  | env', i :: rest, env₄ =>
    ∃ env'',
      (ProjFnRun μ F env' T ctorName lps nP nF i env'' ∨
       ((env'.find? (projModelName T i)).isNone = true ∧
         env'' = env')) ∧
      ProjInstallRun μ F T ctorName lps nP nF env'' rest env₄

/-! ## The assembly -/

/-- **The inductive kind's run/guard record** — `DeclRun`'s `Ind`
parameter, at last (task #161 S11b).

`DeclIndRun` with every `∀ φ` conjunct struck and the valuation column
gone with them.  The block split pins, the member fold, the recursor
group, the constructor residual and projection-freshness guards and the
projection installs are carried
unchanged — they are stored-data guards and checker verdicts
throughout.

(Task #175 tower-flag: the elimination-template pass is gone — the
modeled route installs no projection table at all.) -/
def DeclIndRun (μ : CheckMode) (F : Nat) (env : Env)
    (block : List ConstantInfo) (env₂ : Env) : Prop :=
  let recs := block.filter (fun ci => match ci with
    | .recInfo _ _ _ _ => true | _ => false)
  let nonrecs := block.filter (fun ci => match ci with
    | .recInfo _ _ _ _ => false | _ => true)
  let blockNames := block.map (·.name)
  block = nonrecs ++ recs ∧
  ((∃ cvT capsT cvC nP nF,
      block.filter (fun ci => match ci with
        | .indInfo _ _ => true | _ => false) = [.indInfo cvT capsT] ∧
      block.filter (fun ci => match ci with
        | .ctorInfo _ _ _ => true | _ => false)
        = [.ctorInfo cvC nP nF] ∧
      (let caps := indBlockCaps μ env cvT cvC nP nF
       ∃ envM envR,
         IndMembersRun μ F blockNames caps env nonrecs envM ∧
         IndRecsRun μ F blockNames envM recs envR ∧
         ctorResidualOk μ envR cvT.name cvC.name cvT.levelParams nP nF
           caps.eta = true ∧
         (List.range nF).all
           (fun j => (envR.find? (projFnName cvT.name j)).isNone)
           = true ∧
         ProjInstallRun μ F cvT.name cvC.name cvT.levelParams nP nF
           envR
           (if ctorTargetsFam cvC.type cvT.name cvT.levelParams nP nF
            then List.range nF else []) env₂)) ∨
   (¬ (∃ cvT capsT cvC nP nF,
        block.filter (fun ci => match ci with
          | .indInfo _ _ => true | _ => false) = [.indInfo cvT capsT] ∧
        block.filter (fun ci => match ci with
          | .ctorInfo _ _ _ => true | _ => false)
          = [.ctorInfo cvC nP nF]) ∧
    ∃ envM,
      IndMembersRun μ F blockNames {} env nonrecs envM ∧
      IndRecsRun μ F blockNames envM recs env₂))

end ConLeche.Semantics
