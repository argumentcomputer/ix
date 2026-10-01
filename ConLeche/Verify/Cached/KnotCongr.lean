module

public import ConLeche.Cached.ParsedC

public section

/-!
# The knot reads the index only through `find?`

`FEnv` carries three fields, but the cached core only ever asks it
questions through `FEnv.find?`: every guard, every stored-constant
read and every rule lookup below goes through that one function.  This
file proves it, one congruence lemma per `fe`-taking function of
`ConLeche/Kernel/FEnv.lean` and `ConLeche/Cached/*` reachable from the
knot's bodies, bottom-up, landing on `coreKnotI_congr`.

The consumer is the re-check at a task-#108 prefix view:
`feFinal.restrictTo k` and `mkFEnv env` for the environment `env` of
the first `k` constants have the same `find?`, so `coreKnotI_congr`
says they run the *same* core — and the simulation stated at
`mkFEnv env` therefore covers a run at the prefix view.
`sharedOpsC_congr` and `opSIxC_congr` carry that to the two operation
records the drivers hand out.
-/

namespace ConLeche.Cached

variable {mode : CheckMode} {fe₁ fe₂ : FEnv}

/-! ## The environment-index guards (`ConLeche/Kernel/FEnv.lean`) -/

/-- `FEnv.findProj?` reads `fe` only through `find?`. -/
theorem findProj?_congr (hfe : fe₁.find? = fe₂.find?) :
    fe₁.findProj? = fe₂.findProj? := by
  funext T i; unfold FEnv.findProj?; simp only [hfe]

/-- `FEnv.towerSlotsAllF` reads `fe` only through `find?`. -/
theorem towerSlotsAllF_congr (hfe : fe₁.find? = fe₂.find?) :
    fe₁.towerSlotsAllF = fe₂.towerSlotsAllF := by
  funext T nF; unfold FEnv.towerSlotsAllF; simp only [findProj?_congr hfe]

/-- `FEnv.andRescueSlotsF` reads `fe` only through `find?`. -/
theorem andRescueSlotsF_congr (hfe : fe₁.find? = fe₂.find?) :
    fe₁.andRescueSlotsF = fe₂.andRescueSlotsF := by
  funext ctor nP ust; unfold FEnv.andRescueSlotsF
  simp only [findProj?_congr hfe]

/-- `FEnv.recSlotsAllF` reads `fe` only through `find?`. -/
theorem recSlotsAllF_congr (hfe : fe₁.find? = fe₂.find?) :
    fe₁.recSlotsAllF = fe₂.recSlotsAllF := by
  funext T nF; unfold FEnv.recSlotsAllF; simp only [hfe]

/-- `natLitSupportedF` reads `fe` only through `find?`. -/
theorem natLitSupportedF_congr (hfe : fe₁.find? = fe₂.find?) :
    natLitSupportedF fe₁ = natLitSupportedF fe₂ := by
  unfold natLitSupportedF; simp only [hfe]

/-- `strLitSupportedF` reads `fe` only through `find?`. -/
theorem strLitSupportedF_congr (hfe : fe₁.find? = fe₂.find?) :
    strLitSupportedF fe₁ = strLitSupportedF fe₂ := by
  unfold strLitSupportedF; simp only [hfe, natLitSupportedF_congr hfe]

/-- `natOpGuardF` reads `fe` only through `find?`. -/
theorem natOpGuardF_congr (hfe : fe₁.find? = fe₂.find?) :
    natOpGuardF fe₁ = natOpGuardF fe₂ := by
  funext c; unfold natOpGuardF; simp only [hfe, natLitSupportedF_congr hfe]

/-- `natOpStoredF` reads `fe` only through `find?`. -/
theorem natOpStoredF_congr (hfe : fe₁.find? = fe₂.find?) :
    natOpStoredF fe₁ = natOpStoredF fe₂ := by
  funext c; unfold natOpStoredF; simp only [hfe]

/-! ## The cached guards and stored-constant reads
(`ConLeche/Cached/StateC.lean`) -/

/-- `isUnitLikeTyC` reads `fe` only through `find?`. -/
theorem isUnitLikeTyC_congr (hfe : fe₁.find? = fe₂.find?) :
    isUnitLikeTyC fe₁ = isUnitLikeTyC fe₂ := by
  funext e; unfold isUnitLikeTyC; simp only [hfe]

/-- `isCtorAppC` reads `fe` only through `find?`. -/
theorem isCtorAppC_congr (hfe : fe₁.find? = fe₂.find?) :
    isCtorAppC fe₁ = isCtorAppC fe₂ := by
  funext e; unfold isCtorAppC; simp only [hfe]

/-- `headHintC` reads `fe` only through `find?`. -/
theorem headHintC_congr (hfe : fe₁.find? = fe₂.find?) :
    headHintC fe₁ = headHintC fe₂ := by
  funext e; unfold headHintC; simp only [hfe]

/-- `unfoldableHeadC` reads `fe` only through `find?`. -/
theorem unfoldableHeadC_congr (hfe : fe₁.find? = fe₂.find?) :
    unfoldableHeadC fe₁ = unfoldableHeadC fe₂ := by
  funext e; unfold unfoldableHeadC; simp only [hfe]

/-- `etaCtorShapeC` reads `fe` only through `find?`. -/
theorem etaCtorShapeC_congr (hfe : fe₁.find? = fe₂.find?) :
    etaCtorShapeC fe₁ = etaCtorShapeC fe₂ := by
  funext e; unfold etaCtorShapeC; simp only [hfe]

/-- `constTyAtM` reads `fe` only through `find?`. -/
theorem constTyAtM_congr (hfe : fe₁.find? = fe₂.find?) :
    constTyAtM fe₁ = constTyAtM fe₂ := by
  funext nI n us; unfold constTyAtM; simp only [hfe]

/-- `constValAtM` reads `fe` only through `find?`. -/
theorem constValAtM_congr (hfe : fe₁.find? = fe₂.find?) :
    constValAtM fe₁ = constValAtM fe₂ := by
  funext nI n us; unfold constValAtM; simp only [hfe]

/-- `ruleRhsAtM` reads `fe` only through `find?`. -/
theorem ruleRhsAtM_congr (hfe : fe₁.find? = fe₂.find?) :
    ruleRhsAtM fe₁ = ruleRhsAtM fe₂ := by
  funext cI jI c j us; unfold ruleRhsAtM; simp only [hfe]

/-- The walk's plain descent reads `fe` only through `find?`. -/
theorem constsResolveFP_congr (hfe : fe₁.find? = fe₂.find?) : ∀ e : Expr,
    constsResolveFP fe₁ e = constsResolveFP fe₂ e := by
  intro e
  induction e with
  | bvar i => rw [constsResolveFP, constsResolveFP]
  | sort u => rw [constsResolveFP, constsResolveFP]
  | lit l => cases l <;> simp only [constsResolveFP, hfe]
  | const n us => simp only [constsResolveFP, hfe]
  | fvar idx ty iht => simp only [constsResolveFP, iht]
  | app f a ihf iha => simp only [constsResolveFP, ihf, iha]
  | lam ty body m iht ihb => simp only [constsResolveFP, iht, ihb]
  | forallE ty body m iht ihb => simp only [constsResolveFP, iht, ihb]
  | letE ty val body iht ihv ihb => simp only [constsResolveFP, iht, ihv, ihb]
  | proj sn i sub ih => simp only [constsResolveFP, hfe, ih]

/-- `constsResolveFC` reads `fe` only through `find?`. -/
theorem constsResolveFC_congr (hfe : fe₁.find? = fe₂.find?) :
    constsResolveFC fe₁ = constsResolveFC fe₂ := by
  funext e
  unfold constsResolveFC
  rw [Expr.resBool_eq, Expr.resBool_eq]
  exact constsResolveFP_congr hfe e

/-! ## The core's readers (`ConLeche/Cached/CoreC.lean`)

Each lemma equates the two partial applications at everything up to
and including `fe`, so `simp only [f_congr hfe]` rewrites a call site
inside a larger body.  A few of these functions only *thread* `fe`;
their hypothesis is still taken, because it is what pins the two
indices when the lemma is used as a rewrite rule.
-/

/-- `unfoldDefinitionI` reads `fe` only through `find?`. -/
theorem unfoldDefinitionI_congr (hfe : fe₁.find? = fe₂.find?) :
    unfoldDefinitionI fe₁ = unfoldDefinitionI fe₂ := by
  funext e; unfold unfoldDefinitionI; simp only [hfe, constValAtM_congr hfe]

/-- `litToCtorIfNatI` reads `fe` only through `find?`. -/
theorem litToCtorIfNatI_congr (hfe : fe₁.find? = fe₂.find?) :
    litToCtorIfNatI fe₁ = litToCtorIfNatI fe₂ := by
  funext e; unfold litToCtorIfNatI; simp only [natLitSupportedF_congr hfe]

/-- `reduceNatI` reads `fe` only through `find?`. -/
theorem reduceNatI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    reduceNatI r fe₁ = reduceNatI r fe₂ := by
  funext depth e; unfold reduceNatI
  simp only [natLitSupportedF_congr hfe, natOpStoredF_congr hfe]

/-- `iotaCertsIAux` only threads `fe`. -/
theorem iotaCertsIAux_congr (_hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    iotaCertsIAux r fe₁ = iotaCertsIAux r fe₂ := by
  funext depth lic ty acc args
  induction ty, acc, args using iotaCertsIAux.induct (lic := lic) with
  | case1 ty acc => rw [iotaCertsIAux.eq_def, iotaCertsIAux.eq_def]
  | case2 acc arg rest dom body mb h ih =>
    rw [iotaCertsIAux.eq_def, iotaCertsIAux.eq_def]; simp only [h, ih]
  | case3 acc arg rest dom body mb h ih =>
    rw [iotaCertsIAux.eq_def, iotaCertsIAux.eq_def]; simp only [h, ih]
  | case4 arg rest i => rw [iotaCertsIAux.eq_def, iotaCertsIAux.eq_def]
  | case5 arg rest i head tail ih =>
    rw [iotaCertsIAux.eq_def, iotaCertsIAux.eq_def]; simp only [ih]
  | case6 ty acc arg rest h₁ h₂ =>
    rw [iotaCertsIAux.eq_def, iotaCertsIAux.eq_def]
    cases ty with
    | forallE d b m => exact (h₁ _ _ _ rfl).elim
    | bvar i => exact (h₂ _ rfl).elim
    | _ => rfl

/-- `iotaCertsI` only threads `fe`. -/
theorem iotaCertsI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    iotaCertsI r fe₁ = iotaCertsI r fe₂ := by
  funext depth lic ty args; unfold iotaCertsI
  simp only [iotaCertsIAux_congr hfe]

/-- `defEqListI` only threads `fe`. -/
theorem defEqListI_congr (_hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    defEqListI r fe₁ = defEqListI r fe₂ := by
  funext depth as bs
  induction as generalizing bs with
  | nil => cases bs <;> rfl
  | cons a as ih =>
    cases bs with
    | nil => rfl
    | cons b bs => simp only [defEqListI, ih]

/-- `iotaIndexOkI` only threads `fe`. -/
theorem iotaIndexOkI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    iotaIndexOkI r fe₁ = iotaIndexOkI r fe₂ := by
  funext depth mI rP cnP tyCtor margs idx; unfold iotaIndexOkI
  simp only [defEqListI_congr hfe]

/-- `defeqSpineI` only threads `fe`. -/
theorem defeqSpineI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    defeqSpineI r fe₁ = defeqSpineI r fe₂ := by
  funext depth a b; unfold defeqSpineI; simp only [defEqListI_congr hfe]

/-- `proofIrrelI` reads `fe` only through `find?`. -/
theorem proofIrrelI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    proofIrrelI r fe₁ = proofIrrelI r fe₂ := by
  funext depth a b; unfold proofIrrelI; simp only [isUnitLikeTyC_congr hfe]

/-- `propIrrelI` reads `fe` only through `find?`. -/
theorem propIrrelI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    propIrrelI r fe₁ = propIrrelI r fe₂ := by
  funext depth a b; unfold propIrrelI; simp only [hfe]

/-- `projAppsI` reads `fe` only through `find?`. -/
theorem projAppsI_congr (hfe : fe₁.find? = fe₂.find?) :
    projAppsI fe₁ = projAppsI fe₂ := by
  funext Tn T us' targs b nF; unfold projAppsI
  simp only [towerSlotsAllF_congr hfe]

/-- `structEtaProjCertsI` reads `fe` only through `find?`. -/
theorem structEtaProjCertsI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    structEtaProjCertsI r fe₁ = structEtaProjCertsI r fe₂ := by
  funext depth TI T us' targs b lpsT is
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [structEtaProjCertsI, hfe, constTyAtM_congr hfe,
      iotaCertsI_congr hfe, ih]

/-- `structEtaCertWithI` reads `fe` only through `find?`. -/
theorem structEtaCertWithI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    structEtaCertWithI mode r fe₁ = structEtaCertWithI mode r fe₂ := by
  funext depth a b wtb; unfold structEtaCertWithI
  simp only [hfe, towerSlotsAllF_congr hfe, recSlotsAllF_congr hfe,
    constTyAtM_congr hfe, iotaCertsI_congr hfe, structEtaProjCertsI_congr hfe,
    defEqListI_congr hfe, projAppsI_congr hfe]

/-- `structEtaCertI` reads `fe` only through `find?`. -/
theorem structEtaCertI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    structEtaCertI mode r fe₁ = structEtaCertI mode r fe₂ := by
  funext depth a b; unfold structEtaCertI
  simp only [etaCtorShapeC_congr hfe, structEtaCertWithI_congr hfe]

/-- `structUnitCertI` reads `fe` only through `find?`. -/
theorem structUnitCertI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    structUnitCertI mode r fe₁ = structUnitCertI mode r fe₂ := by
  funext depth a b; unfold structUnitCertI
  simp only [hfe, constTyAtM_congr hfe, iotaCertsI_congr hfe]

/-- `etaCertI` does not read `fe` at all. -/
theorem etaCertI_congr (_hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    etaCertI mode r fe₁ = etaCertI mode r fe₂ := rfl

/-- `stuckIrrelI` reads `fe` only through `find?`. -/
theorem stuckIrrelI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    stuckIrrelI mode r fe₁ = stuckIrrelI mode r fe₂ := by
  funext depth a b; unfold stuckIrrelI
  simp only [structEtaCertI_congr hfe, structUnitCertI_congr hfe,
    proofIrrelI_congr hfe]

/-- `majorToCtorI` reads `fe` only through `find?`. -/
theorem majorToCtorI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    majorToCtorI mode r fe₁ = majorToCtorI mode r fe₂ := by
  funext depth recName rules major; unfold majorToCtorI
  simp only [isCtorAppC_congr hfe, hfe, constTyAtM_congr hfe,
    iotaCertsI_congr hfe, proofIrrelI_congr hfe, projAppsI_congr hfe,
    structEtaCertWithI_congr hfe, andRescueSlotsF_congr hfe]

/-- `litMajorToCtorI` reads `fe` only through `find?`. -/
theorem litMajorToCtorI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    litMajorToCtorI r fe₁ = litMajorToCtorI r fe₂ := by
  funext depth e; unfold litMajorToCtorI
  simp only [strLitSupportedF_congr hfe, litToCtorIfNatI_congr hfe]

/-- `projLitToCtorI` reads `fe` only through `find?`. -/
theorem projLitToCtorI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    projLitToCtorI r fe₁ = projLitToCtorI r fe₂ := by
  funext depth e; unfold projLitToCtorI; simp only [strLitSupportedF_congr hfe]

/-- `prepareMajorI` reads `fe` only through `find?`. -/
theorem prepareMajorI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    prepareMajorI mode r fe₁ = prepareMajorI mode r fe₂ := by
  funext depth recName rules major; unfold prepareMajorI
  simp only [majorToCtorI_congr hfe, litMajorToCtorI_congr hfe]

/-- `iotaArityOk` reads `fe` only through `find?`. -/
theorem iotaArityOk_congr (hfe : fe₁.find? = fe₂.find?) :
    iotaArityOk fe₁ = iotaArityOk fe₂ := by
  funext e; unfold iotaArityOk; simp only [hfe]

/-- `iotaRecI` reads `fe` only through `find?`. -/
theorem iotaRecI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    iotaRecI mode r fe₁ = iotaRecI mode r fe₂ := by
  funext depth e; unfold iotaRecI
  simp only [hfe, prepareMajorI_congr hfe, defEqListI_congr hfe,
    constTyAtM_congr hfe, iotaCertsI_congr hfe, iotaIndexOkI_congr hfe,
    ruleRhsAtM_congr hfe]

/-- `projCertI` reads `fe` only through `find?`. -/
theorem projCertI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    projCertI r fe₁ = projCertI r fe₂ := by
  funext depth lic c us args; unfold projCertI
  simp only [hfe, constTyAtM_congr hfe, iotaCertsI_congr hfe]

/-- `projCertAtI` reads `fe` only through `find?`. -/
theorem projCertAtI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    projCertAtI r fe₁ = projCertAtI r fe₂ := by
  funext depth verified lic c us args; unfold projCertAtI
  simp only [projCertI_congr hfe]

/-- The bulk-beta spine loop and its peel loop read `fe` only through
`find?` (one mutual functional induction for the pair). -/
theorem whnfAppI_betaPeelI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI)
    (depth : Nat) (k : Expr → CheckCM Expr) :
    (∀ v args, whnfAppI mode r fe₁ depth k v args
        = whnfAppI mode r fe₂ depth k v args) ∧
      (∀ t acc args, betaPeelI mode r fe₁ depth k t acc args
        = betaPeelI mode r fe₂ depth k t acc args) := by
  refine whnfAppI.mutual_induct mode
    (fun v args => whnfAppI mode r fe₁ depth k v args
      = whnfAppI mode r fe₂ depth k v args)
    (fun t acc args => betaPeelI mode r fe₁ depth k t acc args
      = betaPeelI mode r fe₂ depth k t acc args)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro v; rw [whnfAppI.eq_def, whnfAppI.eq_def]
  · intro a rest ty body mb h ih
    rw [whnfAppI.eq_def, whnfAppI.eq_def]; simp only [h, ih]
  · intro a rest ty body mb h ih
    rw [whnfAppI.eq_def, whnfAppI.eq_def]; simp only [h, ih]
  · intro v a rest hnl ih
    rw [whnfAppI.eq_def, whnfAppI.eq_def]
    cases v with
    | lam ty body mb => exact (hnl _ _ _ rfl).elim
    | _ => simp only [iotaArityOk_congr hfe, iotaRecI_congr hfe, ih]
  · intro t acc; rw [betaPeelI.eq_def, betaPeelI.eq_def]
  · intro acc arg rest ty body mb h ih
    rw [betaPeelI.eq_def, betaPeelI.eq_def]; simp only [h, ih]
  · intro acc arg rest ty body mb h ih
    rw [betaPeelI.eq_def, betaPeelI.eq_def]; simp only [h, ih]
  · intro ty acc arg rest hnl ih
    rw [betaPeelI.eq_def, betaPeelI.eq_def]
    cases ty with
    | lam ty body mb => exact (hnl _ _ _ rfl).elim
    | _ => simp only [ih]

/-- `whnfAppI` reads `fe` only through `find?`. -/
theorem whnfAppI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI)
    (depth : Nat) (k : Expr → CheckCM Expr) :
    whnfAppI mode r fe₁ depth k = whnfAppI mode r fe₂ depth k := by
  funext v args; exact (whnfAppI_betaPeelI_congr hfe r depth k).1 v args

/-- `betaPeelI` reads `fe` only through `find?`. -/
theorem betaPeelI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI)
    (depth : Nat) (k : Expr → CheckCM Expr) :
    betaPeelI mode r fe₁ depth k = betaPeelI mode r fe₂ depth k := by
  funext t acc args; exact (whnfAppI_betaPeelI_congr hfe r depth k).2 t acc args

/-- `whnfCoreStepI` reads `fe` only through `find?`. -/
theorem whnfCoreStepI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    whnfCoreStepI mode r fe₁ = whnfCoreStepI mode r fe₂ := by
  funext depth k e; unfold whnfCoreStepI
  simp only [whnfAppI_congr hfe, projLitToCtorI_congr hfe,
    findProj?_congr hfe, projCertAtI_congr hfe]

/-- `whnfCoreLoopI` reads `fe` only through `find?`. -/
theorem whnfCoreLoopI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    whnfCoreLoopI mode r fe₁ = whnfCoreLoopI mode r fe₂ := by
  funext depth n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext e; unfold whnfCoreLoopI; rw [ih, whnfCoreStepI_congr hfe]

/-- `whnfCoreBodyI` reads `fe` only through `find?`. -/
theorem whnfCoreBodyI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    whnfCoreBodyI mode r fe₁ = whnfCoreBodyI mode r fe₂ := by
  funext depth e; unfold whnfCoreBodyI; rw [whnfCoreLoopI_congr hfe]

/-- `inferSpineI` only threads `fe`. -/
theorem inferSpineI_congr (_hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    inferSpineI r fe₁ = inferSpineI r fe₂ := by
  funext depth ty acc args
  induction args generalizing ty acc with
  | nil => rfl
  | cons a as ih => simp only [inferSpineI, ih]

/-- `inferSpineIOI` only threads `fe`. -/
theorem inferSpineIOI_congr (_hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    inferSpineIOI mode r fe₁ = inferSpineIOI mode r fe₂ := by
  funext depth ty acc args
  induction args generalizing ty acc with
  | nil => rfl
  | cons a as ih => simp only [inferSpineIOI, ih]

/-- `whnfStepI` reads `fe` only through `find?`. -/
theorem whnfStepI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    whnfStepI r fe₁ = whnfStepI r fe₂ := by
  funext depth k e; unfold whnfStepI
  simp only [reduceNatI_congr hfe, unfoldDefinitionI_congr hfe]

/-- `whnfLoopI` reads `fe` only through `find?`. -/
theorem whnfLoopI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    whnfLoopI r fe₁ = whnfLoopI r fe₂ := by
  funext depth n
  induction n with
  | zero => rfl
  | succ n ih => funext e; unfold whnfLoopI; rw [ih, whnfStepI_congr hfe]

/-- `whnfBodyI` reads `fe` only through `find?`. -/
theorem whnfBodyI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    whnfBodyI r fe₁ = whnfBodyI r fe₂ := by
  funext depth e; unfold whnfBodyI; rw [whnfLoopI_congr hfe]

/-- `inferBodyI` reads `fe` only through `find?`. -/
theorem inferBodyI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    inferBodyI mode r fe₁ = inferBodyI mode r fe₂ := by
  funext depth e; unfold inferBodyI
  simp only [hfe, natLitSupportedF_congr hfe, strLitSupportedF_congr hfe,
    constTyAtM_congr hfe, inferSpineI_congr hfe, findProj?_congr hfe]

/-- `inferBodyIOI` reads `fe` only through `find?`. -/
theorem inferBodyIOI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    inferBodyIOI mode r fe₁ = inferBodyIOI mode r fe₂ := by
  funext depth e; unfold inferBodyIOI
  simp only [inferSpineIOI_congr hfe, inferBodyI_congr hfe]

/-- `defeqStepI` reads `fe` only through `find?`. -/
theorem defeqStepI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    defeqStepI mode r fe₁ = defeqStepI mode r fe₂ := by
  funext depth k pi a b; unfold defeqStepI
  simp only [propIrrelI_congr hfe, reduceNatI_congr hfe,
    unfoldableHeadC_congr hfe, unfoldDefinitionI_congr hfe,
    headHintC_congr hfe, defeqSpineI_congr hfe, stuckIrrelI_congr hfe,
    strLitSupportedF_congr hfe, defEqListI_congr hfe, etaCertI_congr hfe]

/-- `defeqLoopI` reads `fe` only through `find?`. -/
theorem defeqLoopI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    defeqLoopI mode r fe₁ = defeqLoopI mode r fe₂ := by
  funext depth n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext pi a b; unfold defeqLoopI; rw [ih, defeqStepI_congr hfe]

/-- `defeqBodyI` reads `fe` only through `find?`. -/
theorem defeqBodyI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    defeqBodyI mode r fe₁ = defeqBodyI mode r fe₂ := by
  funext depth a b; unfold defeqBodyI; rw [defeqLoopI_congr hfe]

/-- `annotPwPiI` reads `fe` only through `find?`. -/
theorem annotPwPiI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    annotPwPiI r fe₁ = annotPwPiI r fe₂ := by
  funext depth body'; unfold annotPwPiI; simp only [hfe]

/-- `annotatePisPwI` reads `fe` only through `find?`. -/
theorem annotatePisPwI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    annotatePisPwI r fe₁ = annotatePisPwI r fe₂ := by
  funext d k leaf'; unfold annotatePisPwI; simp only [annotPwPiI_congr hfe]

/-- `annotatePisLeafI` reads `fe` only through `find?`. -/
theorem annotatePisLeafI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    annotatePisLeafI r fe₁ = annotatePisLeafI r fe₂ := by
  funext d t k fvs stk; unfold annotatePisLeafI
  simp only [annotatePisPwI_congr hfe]

/-- `annotatePisI` reads `fe` only through `find?`. -/
theorem annotatePisI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    annotatePisI r fe₁ = annotatePisI r fe₂ := by
  funext d fuel
  induction fuel with
  | zero =>
    funext t k fvs stk
    simp only [annotatePisI, annotatePisLeafI_congr hfe]
  | succ fuel ih =>
    funext t k fvs stk
    simp only [annotatePisI, ih, annotatePisLeafI_congr hfe]

/-- `annotPwLamI` reads `fe` only through `find?`. -/
theorem annotPwLamI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    annotPwLamI r fe₁ = annotPwLamI r fe₂ := by
  funext depth body'; unfold annotPwLamI; simp only [hfe]

/-- `annotateLamsPwI` reads `fe` only through `find?`. -/
theorem annotateLamsPwI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    annotateLamsPwI r fe₁ = annotateLamsPwI r fe₂ := by
  funext d k leaf'; unfold annotateLamsPwI; simp only [annotPwLamI_congr hfe]

/-- `annotateLamsLeafI` reads `fe` only through `find?`. -/
theorem annotateLamsLeafI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    annotateLamsLeafI r fe₁ = annotateLamsLeafI r fe₂ := by
  funext d t k fvs stk; unfold annotateLamsLeafI
  simp only [annotateLamsPwI_congr hfe]

/-- `annotateLamsI` reads `fe` only through `find?`. -/
theorem annotateLamsI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    annotateLamsI r fe₁ = annotateLamsI r fe₂ := by
  funext d fuel
  induction fuel with
  | zero =>
    funext t k fvs stk
    simp only [annotateLamsI, annotateLamsLeafI_congr hfe]
  | succ fuel ih =>
    funext t k fvs stk
    simp only [annotateLamsI, ih, annotateLamsLeafI_congr hfe]

/-- `annotateBodyI` reads `fe` only through `find?`. -/
theorem annotateBodyI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    annotateBodyI r fe₁ = annotateBodyI r fe₂ := by
  funext depth e; unfold annotateBodyI
  simp only [natLitSupportedF_congr hfe, strLitSupportedF_congr hfe,
    annotatePisI_congr hfe, annotateLamsI_congr hfe, annotPwLamI_congr hfe,
    findProj?_congr hfe]

/-! ## The knot, and the operation records built on it -/

/-- **The knot reads the index only through `find?`.**  `ensureSortI`
needs no lemma of its own: it takes the tied record, not the index. -/
theorem coreKnotI_congr (hfe : fe₁.find? = fe₂.find?) :
    ∀ F, coreKnotI mode fe₁ F = coreKnotI mode fe₂ F := by
  intro F
  induction F with
  | zero => rfl
  | succ F ih =>
    unfold coreKnotI
    simp only [ih, whnfCoreBodyI_congr hfe, whnfBodyI_congr hfe,
      inferBodyI_congr hfe, defeqBodyI_congr hfe, annotateBodyI_congr hfe,
      inferBodyIOI_congr hfe]

/-- `sharedOpsC` reads `fe` only through `find?`. -/
theorem sharedOpsC_congr (hfe : fe₁.find? = fe₂.find?) :
    sharedOpsC mode fe₁ = sharedOpsC mode fe₂ := by
  unfold sharedOpsC opE opB opS; simp only [coreKnotI_congr hfe]

/-- `opSIxC` reads `fe` only through `find?`. -/
theorem opSIxC_congr (hfe : fe₁.find? = fe₂.find?) :
    opSIxC mode fe₁ = opSIxC mode fe₂ := by
  funext d i; unfold opSIxC; rw [coreKnotI_congr hfe]

end ConLeche.Cached
