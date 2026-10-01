module

public import ConLeche.Semantics.DeclIndRun
import ConLeche.Semantics.Bridge.DeclRun
import ConLeche.Verify.Extend.Iota
public import ConLeche.Verify.Extend.Proj

@[expose] public section

/-!
# The **run-only** `indDecl` bridge (task #161 S11b, THE SEPARATION)

S11a cut the guard/derivation weld at the five non-`ind` declaration
kinds; this module cuts it at the sixth, and it is the last one.
`declIndRun_of` below produces `DeclIndRun` from `checkModeled`'s
verdict with **no derivation on the path**, which is what
`checkDeclRun_ofEnvFactsE`'s `Ind` slot has been waiting for since S4.

**Why this is not `declIndRR` re-typed.**  `Bridge/DeclInd.lean`'s
walk interleaves the bridge with an *install*: `IndMembersR` carries a
front-door derivation at each intermediate environment of the member
fold, so the fold has to build an `EnvFacts` there (finding 8, closed at
S7 by `memberInstallR`/`indRecsCoreR`/`projFnRR`).  Strike the
derivations and that obligation disappears with them: the run folds
below carry **no carrier, no `BlockInstalledTT`, no
`EtaFamiliesClosedO`, no `BlockEtaPinned`, no `RenameOkT`** — every
one of those premises existed to feed a `∀ φ` row.  What is left at
each step is the checker's own inversion.

**The route, decided by measurement** (the S11a seal's finding 2, the
import-layout question).  Two were priced from sources:

* *(a) duplicate the inversions on the run twins* — the S11a
  precedent, compile-time-coupled duplication as the known cost;
* *(b) a three-way split of `Bridge/DeclInd` with the derivation half
  re-proved on top of the run half* — single-sourced inversions, at
  the price of moving the module and stating the run→derivation
  lemmas.

(a) measured **cheaper**, and the reason is a fact about this tier that
neither S10 nor S11a had looked at: the ind kind's heavy inversions
are **already single-sourced**, in `Verify/Extend/Iota.lean`'s
`PlainChecked` / `NestedChecked` and in `Bridge/Decl.lean`'s
`checkIotaRule_inv` / `checkProjFn_inv` kits.  `iotaThmR_of` does not
invert the checker at all — it *converts* a `PlainChecked`, and so
does `iotaThmRun_of` below, from the same predicate.  What is left to
duplicate is four small scripts; route (b) would have had to state
four run→derivation lemmas to save them.  The seal carries both
prices.
-/

namespace ConLeche.Semantics

open ConLeche.Term ConLeche.Verify

/-! ## The block members -/

/-- **`checkMemberVal`, run half.**  `memberValR_of`'s script with
`constantValRun_of` in place of `constantValR_of`: the member's front
door and the model-counterpart lookups, no carrier. -/
theorem memberValRun_of {env' : Env} {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {cv cvA : ConstantVal}
    (h : checkMemberVal (m := CheckM) (fueledOps μ F) blockNames env' cv
      = .ok cvA) :
    MemberValRun μ F env' blockNames cv cvA := by
  simp only [checkMemberVal, Bind.bind, Except.bind] at h
  cases hccv : checkConstantVal (fueledOps μ F) env' cv with
  | error e => rw [hccv] at h; exact nomatch h
  | ok cv' =>
  rw [hccv] at h
  try dsimp only at h
  obtain ⟨type, rfl, -, -, hcv⟩ := constantValRun_of hccv
  by_cases hms : cv.name.isModelSuffix = true
  · rw [if_pos hms] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  rw [if_neg hms] at h
  have hmsF : cv.name.isModelSuffix = false := by
    revert hms; cases cv.name.isModelSuffix <;> simp
  revert h
  cases hfm : env'.find? (cv.name.str "_model") with
  | none => intro h; simp [throw, throwThe, MonadExceptOf.throw] at h
  | some ci =>
    match ci with
    | .defnInfo cvm mval hint =>
      intro h
      dsimp only at h
      by_cases hlp : cvm.levelParams = cv.levelParams
      · rw [if_pos hlp] at h
        by_cases het : ((type.renameConsts fun n =>
            if blockNames.contains n then n.str "_model" else n) == cvm.type)
            = true
        · rw [if_pos het] at h
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          exact ⟨type, hcv, rfl, hmsF, cvm, mval, hint, hfm, hlp, het⟩
        · rw [if_neg het] at h
          simp [throw, throwThe, MonadExceptOf.throw] at h
      · rw [if_neg hlp] at h
        simp [throw, throwThe, MonadExceptOf.throw] at h
    | .axiomInfo _ | .thmInfo _ _ | .indInfo _ _ | .ctorInfo _ _ _
    | .recInfo _ _ _ _ | .projInfo _ =>
      intro h
      dsimp only at h
      simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **The member fold, run half.**  `indMembersRS` with the install
gone: no `EnvFacts`, no invariants, no η bookkeeping — the fold is the
checker's `checkIndMember` step inverted at each member, and the
relation it builds is the same walk over the running environment. -/
theorem indMembersRunRS
    {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {caps : IndCaps} :
    ∀ (members : List ConstantInfo) {env env₂ : Env},
      members.foldlM (checkIndMember (m := CheckM) (fueledOps μ F)
        blockNames caps) env = .ok env₂ →
      IndMembersRun μ F blockNames caps env members env₂ := by
  intro members
  induction members with
  | nil =>
    intro env env₂ h
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h.symm
  | cons ci rest ih =>
    intro env env₂ h
    simp only [List.foldlM, Bind.bind, Except.bind, checkIndMember] at h
    revert h
    cases hmv0 : checkMemberVal (m := CheckM) (fueledOps μ F) blockNames
        env ci.toConstantVal with
    | error e => intro h; exact nomatch h
    | ok cvA =>
      intro h
      cases ci with
      | indInfo cv caps' =>
        simp only [pure, Except.pure] at h
        exact ⟨cvA, memberValRun_of hmv0, ih h⟩
      | ctorInfo cv nP nF =>
        simp only [pure, Except.pure] at h
        exact ⟨cvA, memberValRun_of hmv0, ih h⟩
      | axiomInfo cv | defnInfo cv v hint | thmInfo cv v
      | recInfo cv mI rP rules | projInfo e =>
        simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **The provisioning fold, run half.** -/
theorem provisionRecsRunRS
    {μ : CheckMode} {F : Nat} {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) {envAcc envSelf : Env}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      provisionRecs (m := CheckM) (fueledOps μ F) blockNames envAcc recs
        = .ok (envSelf, checked) →
      ProvisionRecsRun μ F blockNames envAcc recs envSelf checked := by
  intro recs
  induction recs with
  | nil =>
    intro envAcc envSelf checked h
    simp only [provisionRecs, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | cons ci rest ih =>
    intro envAcc envSelf checked h
    cases ci with
    | recInfo cv mI rP rules =>
      simp only [provisionRecs, Bind.bind, Except.bind] at h
      revert h
      cases hmv0 : checkMemberVal (m := CheckM) (fueledOps μ F)
          blockNames envAcc (ConstantInfo.recInfo cv mI rP
            rules).toConstantVal with
      | error e => intro h; exact nomatch h
      | ok cvA =>
        intro h
        dsimp only at h
        cases hrest : provisionRecs (m := CheckM) (fueledOps μ F)
            blockNames ⟨.recInfo cvA mI rP [] :: envAcc.consts⟩
            rest with
        | error e => rw [hrest] at h; exact nomatch h
        | ok p =>
          rw [hrest] at h
          simp only [pure, Except.pure, Except.ok.injEq,
            Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨cvA, mI, rP, rules, p.2, rfl,
            memberValRun_of hmv0, ih hrest, rfl⟩
    | axiomInfo cv | defnInfo cv v hint | thmInfo cv v
    | indInfo cv c | ctorInfo cv nP nF | projInfo e =>
      simp [provisionRecs, throw, throwThe, MonadExceptOf.throw] at h

/-! ## The rule packs

`iotaThmRun_of` and `iotaThmNRun_of` take the **same** hypothesis as
their derivation twins — `PlainChecked` / `NestedChecked`
(`Verify/Extend/Iota.lean`), the checker's inversion kits — so nothing
is inverted twice here.  What the twins do past that point is build
`IotaWalksR`; these stop at the shape pins and the recorded runs, which
the kit already carries. -/

/-- **A canonical rule's `iota_j` theorem, run half.**  `iotaThmR_of`'s
`refine` with the parameter-domain walk and `IotaWalksR` struck: the
remaining rows are `PlainChecked`'s own components. -/
theorem iotaThmRun_of {env' envSelf : Env}
    {μ : CheckMode} {F : Nat} {f : Name → Name} {cvA cvj : ConstantVal}
    {mI rP cnP cnF j : Nat} {r : RecRule} {rhsA : Expr}
    (h : PlainChecked μ F env' envSelf f cvA mI rP cnP cnF j
      { r with rhs := rhsA } cvj) :
    IotaThmRun μ F env' envSelf f cvA.name cvA.levelParams
      cvA.type mI rP j r cvj cnP cnF rhsA := by
  obtain ⟨thmName, cvt, ci, fvs, tbody, ℓA, αS, lhsS, rhsS, cdoms, cres,
    rdoms, rrest, fvsP, restP, cdomsP, crestP, xFvsP, crest2, ldoms,
    lrest, hfthm, hcvt, hpin, hlpt, hopen, hheadEq, hargs3, hlhead,
    hlarity, hlpre, hmaj, hcstrip, hcinst, hclen, hdeIdx, hdeFld,
    hrinst, hdePre, hopenP, hcinstP, hdeP, hopenX, hlinst, hdeLam,
    hdeRhs, hty1, hty2, hty3⟩ := h
  subst hpin
  refine ⟨cvt, fvs, tbody, ?_, hlpt, hopen, ?_, ?_, ?_⟩
  · rw [Env.findCV?, hfthm, Option.map_some, hcvt]
  · rw [hheadEq]; rfl
  · rw [hargs3]; rfl
  · rw [hargs3]
    dsimp only
    exact ⟨by simpa using hlhead, by simpa using hlarity,
      by simpa using hlpre, by simpa using hmaj,
      hcstrip, cdoms, cres, rdoms, fvsP, cdomsP, crestP, xFvsP, restP,
      crest2, rrest, hcinst, hclen, hrinst, hopenP, hcinstP, hopenX,
      ldoms, lrest, hlinst, hdeP,
      ⟨hdeIdx, hdeFld, hdePre, hdeLam, hdeRhs, hty1, hty2⟩⟩

/-- **A nested-auxiliary rule's `iota_j` theorem, run half.**  Same
move against `NestedChecked`; the generalized major pin, the
`checkAnnotList` fixed points and the arity pin are all stored-data
rows and carry over. -/
theorem iotaThmNRun_of {env' envSelf : Env}
    {μ : CheckMode} {F : Nat} {f : Name → Name} {cvA cvj : ConstantVal}
    {mI rP cnP cnF j : Nat} {r : RecRule} {rhsA : Expr}
    {lvls : List Level} {pins : List Expr}
    (hshape : nestedRuleShape env' envSelf cvA.name cvA.levelParams
      cvA.type mI rP cnP j = some (lvls, pins))
    (h : NestedChecked μ F env' envSelf f cvA mI rP cnP cnF j
      { r with rhs := rhsA } cvj lvls pins) :
    IotaThmNRun μ F env' envSelf f cvA.name cvA.levelParams
      cvA.type mI rP j r cvj cnP cnF rhsA lvls pins := by
  obtain ⟨thmName, cvt, ci, fvs, tbody, ℓA, αS, lhsS, rhsS, cdoms, cres,
    rdoms, rrest, fvsP, restP, cdomsP, crestP, xFvsP, crest2, ldoms,
    lrest, hfthm, hcvt, hpin, hlpt, hopen, hheadEq, hargs3, hlhead,
    hlarity, hlpre, hmaj, hcstrip, hcinst, hclen, hdeIdx, hdeFld,
    hrinst, hdePre, hopenP, hannP, hcinstP, htypedP, hopenX, hcrestLen,
    hlinst, hdeLam, hdeRhs, hty1, hty2, hty3⟩ := h
  subst hpin
  refine ⟨hshape, cvt, fvs, tbody, ?_, hlpt, hopen, ?_, ?_, ?_⟩
  · rw [Env.findCV?, hfthm, Option.map_some, hcvt]
  · rw [hheadEq]; rfl
  · rw [hargs3]; rfl
  · rw [hargs3]
    dsimp only
    refine ⟨by simpa using hlhead, by simpa using hlarity,
      by simpa using hlpre, hmaj, ?_,
      cdoms, cres, rdoms, rrest, fvsP, restP, cdomsP, crestP, xFvsP,
      crest2, hcinst, hclen, hrinst, hopenP,
      ⟨hannP, hcinstP, hopenX, by simpa using hcrestLen⟩,
      ldoms, lrest, hlinst, htypedP,
      ⟨hdeIdx, hdeFld, hdePre, hdeLam, hdeRhs, hty1, hty2⟩⟩
    obtain ⟨bsC0, cbody0, Dc, usc, hs1, hs2⟩ := hcstrip
    exact ⟨bsC0, cbody0, hs1, by rw [hs2]⟩

/-- **One modeled recursor rule, run half** (`checkIotaRule`).  The
kit is `checkIotaRule_inv`'s, shared with `iotaRuleR_of`; what does not
happen here is the rhs front door's conversion (`checkBridge` at the
empty context), whose *recorded run* — the fold's own `inferTypeCore`
verdict — is what the run record carries instead. -/
theorem iotaRuleRun_of {env' envSelf : Env}
    {μ : CheckMode} {F : Nat} {f : Name → Name} {cvA : ConstantVal}
    {mI rP j : Nat} {r r' : RecRule}
    (h : checkIotaRule μ (fueledOps μ F) env' envSelf f cvA.name
      cvA.levelParams cvA.type mI rP j r = .ok r') :
    IotaRuleRun μ F env' envSelf f cvA.name cvA.levelParams
      cvA.type mI rP j r r' := by
  obtain ⟨hkit, hrnf, hrb, cnP0, fire0, rhsA0, hann0, hr'eq,
    hinert, hnestShape⟩ := checkIotaRule_inv (cvA := cvA) h
  obtain ⟨cvj, cnP, cnF, raw, rhsTy, rbinders, rbody, hfc, hnf, hcp,
    hplainIff, hnested, hrawnf, hrawb, hrawann, hrhsnf, hrhsb, hrlp,
    hrres, hstripEq, hity, hplainKit⟩ := hkit
  subst hr'eq
  dsimp only [recRuleBits] at hfc hnf hcp hplainIff hnested hrhsnf hrhsb
  dsimp only [recRuleBits] at hplainKit hrlp hrres hstripEq hity
  subst hcp
  refine ⟨cvj, cnP0, cnF, rhsA0, hfc, hnf, hrb, hrnf,
    hann0, hrlp, hrres, (by rw [hstripEq]; rfl),
    ⟨rhsTy, hity⟩, fire0, rfl, ?_⟩
  by_cases hplain :
      Expr.recRulePlain cvA.type mI rP cnP0 = true
  · exact Or.inl ⟨hplain, hplainIff.mpr hplain,
      iotaThmRun_of (hplainKit hplain)⟩
  · have hplainF : Expr.recRulePlain cvA.type mI rP cnP0 = false := by
      revert hplain
      cases Expr.recRulePlain cvA.type mI rP cnP0 <;> simp
    refine Or.inr ⟨hplainF, ?_⟩
    cases hf : fire0 with
    | plain =>
      exact absurd (hplainIff.mp hf) (by rw [hplainF]; simp)
    | inert => exact Or.inl ⟨rfl, hinert hf⟩
    | nested lvls pins =>
      refine Or.inr ⟨lvls, pins, rfl, ?_⟩
      obtain ⟨-, -, -, -, -, hkitN⟩ := hnested lvls pins hf
      exact iotaThmNRun_of (hnestShape lvls pins hf) hkitN

/-- **The per-recursor rule fold, run half.** -/
theorem iotaRulesRun_of {env' envSelf : Env}
    {μ : CheckMode} {F : Nat} {f : Name → Name} {cvA : ConstantVal}
    {mI rP : Nat} :
    ∀ (j : Nat) (rules rules' : List RecRule),
      checkIotaRules μ (fueledOps μ F) env' envSelf f cvA.name
        cvA.levelParams cvA.type mI rP j rules = .ok rules' →
      IotaRulesRun μ F env' envSelf f cvA.name cvA.levelParams
        cvA.type mI rP j rules rules' := by
  intro j rules
  induction rules generalizing j with
  | nil =>
    intro rules' h
    simp only [checkIotaRules, pure, Except.pure,
      Except.ok.injEq] at h
    exact h.symm
  | cons r rest ih =>
    intro rules' h
    simp only [checkIotaRules, Bind.bind, Except.bind] at h
    revert h
    cases hr1 : checkIotaRule μ (fueledOps μ F) env' envSelf f
        cvA.name cvA.levelParams cvA.type mI rP j r with
    | error e => intro h; exact nomatch h
    | ok r₁ => ?_
    intro h
    try dsimp only at h
    revert h
    cases hrest : checkIotaRules μ (fueledOps μ F) env' envSelf f
        cvA.name cvA.levelParams cvA.type mI rP (j + 1) rest with
    | error e => intro h; exact nomatch h
    | ok rest' => ?_
    intro h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨r₁, rest', iotaRuleRun_of hr1, ih (j + 1) rest' hrest, rfl⟩

/-- **The recursor-group phase, run half** (`checkIndRecs`).

`indRecsRS` needed six premises — the block-name coverage, the
`BlockInstalledTT`/`EtaFamiliesClosedO`/`BlockEtaPinned` invariants and
the two provisioning monotonicity facts — for one purpose: to build the
`RenameOkT` the rules' *denotation* rows are stated at
(`blockRenameOkT`).  The run rows are `isDefEqCore` verdicts at the
self environment, so the fold takes the checker's verdict and nothing
else. -/
theorem indRecsRunRS
    {μ : CheckMode} {F : Nat} {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) {env₂ env₃ : Env},
      checkIndRecs (m := CheckM) μ (fueledOps μ F) blockNames env₂ recs
        = .ok env₃ →
      IndRecsRun μ F blockNames env₂ recs env₃ := by
  intro recs env₂ env₃ h
  simp only [checkIndRecs] at h
  by_cases hemp : recs.isEmpty = true
  · rw [if_pos hemp] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl ⟨List.isEmpty_iff.mp hemp, h.symm⟩
  rw [if_neg hemp] at h
  simp only [Bind.bind, Except.bind] at h
  revert h
  by_cases heqf : env₂.find? eqName = some eqA
  case neg =>
    rw [if_neg heqf]
    intro h
    exact nomatch h
  rw [if_pos heqf]
  intro h
  try dsimp only at h
  revert h
  cases hprovE : provisionRecs (m := CheckM) (fueledOps μ F)
      blockNames env₂ recs with
  | error e => intro h; exact nomatch h
  | ok p => ?_
  obtain ⟨envSelf, checked⟩ := p
  intro h
  try dsimp only at h
  exact Or.inr ⟨fun hc => hemp (by rw [hc]; rfl), heqf,
    envSelf, checked, provisionRecsRunRS recs hprovE,
    indRecsFoldRunRS checked h⟩
where
  /-- The rules fold, run half — at the fixed self environment, as the
  derivation fold already was (`IndRecsFoldR`'s own note: the rules are
  checked at the *base* environment, the accumulator only collects). -/
  indRecsFoldRunRS {μ : CheckMode} {F : Nat} {blockNames : List Name}
      {envBase envSelf : Env} :
      ∀ (checked : List (ConstantVal × Nat × Nat × List RecRule))
        {acc env₃ : Env},
        checked.foldlM (fun (acc : Env) c => do
          let rules' ← checkIotaRules (m := CheckM) μ (fueledOps μ F)
            envBase envSelf
            (fun n => if blockNames.contains n then n.str "_model" else n)
            c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
          pure (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.consts⟩ : Env))
          acc = .ok env₃ →
        IndRecsRun.IndRecsFoldRun μ F blockNames envBase envSelf acc
          checked env₃ := by
    intro checked
    induction checked with
    | nil =>
      intro acc env₃ h
      simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
      exact h.symm
    | cons c rest ih =>
      intro acc env₃ h
      simp only [List.foldlM, Bind.bind, Except.bind] at h
      revert h
      cases hr : checkIotaRules (m := CheckM) μ (fueledOps μ F) envBase
          envSelf
          (fun n => if blockNames.contains n then n.str "_model" else n)
          c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2 with
      | error e => intro h; exact nomatch h
      | ok rules' => ?_
      intro h
      try dsimp only at h
      exact ⟨rules', iotaRulesRun_of 0 c.2.2.2 rules' hr, ih h⟩

/-! ## The projection phase -/

/-- **One projection-function install, run half** (`checkProjFn`).
The five stage inversions are `projFn_of`'s own — one `_inv` call
each, all relation-free — and what does not happen here is the rule's
front-door conversion and the `proj_i.iota` sides pack's `∀ φ` walk. -/
theorem projFnRun_of {env' env₁ : Env} {μ : CheckMode}
    {F : Nat} {T ctorName : Name} {lps : List Name} {nP nF i : Nat}
    (h : checkProjFn μ (fueledOps μ F) env' T ctorName lps nP nF i
      = .ok env₁) :
    ProjFnRun μ F env' T ctorName lps nP nF i env₁ := by
  obtain ⟨cvj, mcv, hlk, pty, hty, ⟨u0, hshape⟩, hilt, rhsA, hrule,
    ⟨u, hio⟩, henv⟩ := checkProjFn_inv h
  obtain ⟨mval, mhint, hctor, hfm, hmlps, hpnone, hTf, heqf⟩ :=
    checkProjLookups_inv hlk
  obtain ⟨hptyB, hround, hptyres, hptyb, hptyf, hptylp, hstrip1⟩ :=
    checkProjTy_inv hty
  obtain ⟨abinders, arest, cbindersR, cbody, hstripP, hCstrip,
    hcbodyHead, hcbodyArity⟩ := checkProjShape_inv hshape
  obtain ⟨raw, rbinders, cbindersR2, cbody2, hraw, hrawnf, hrawb,
    hrawann, hrlp, hrres, hrhsb, hrhsnf, hrhsAstrip, hCstrip2,
    hdomsR, fvsP, rest0, cdomsP, crestP, xFvs, crest2X, ldoms, lrestL,
    hopenP, hcinstP, hdeP, hopenX, hlinst, hdeLam, rhsTy, hity⟩ :=
    checkProjRule_inv hrule
  obtain ⟨tcv, tval, sbinders, cbindersR3, cbody3, tySlot, ℓA,
    hthmE, htlps, hCstrip3, hdomsS, hSstrip, fvsO, sbodyO, hopenO,
    hsty1, hsty2, hsty3⟩ := checkProjIota_inv hio
  have hcb2 : cbindersR2 = cbindersR :=
    (Prod.mk.inj (Option.some.inj (hCstrip2.symm.trans hCstrip))).1
  have hcb3 : cbindersR3 = cbindersR :=
    (Prod.mk.inj (Option.some.inj (hCstrip3.symm.trans hCstrip))).1
  rw [hcb2] at hdomsR
  rw [hcb3] at hdomsS
  refine ⟨cvj, mcv, mval, mhint, pty, rhsA, hctor, hfm, hmlps,
    (by rw [hpnone]; rfl), hTf, heqf, hptyB, (by rw [hround]; simp),
    hptyres, hptyb, hptyf, hptylp, hstrip1, hilt,
    (by rw [hstripP]; rfl),
    ⟨cbindersR, cbody, hCstrip, hcbodyArity, hcbodyHead, hrhsnf,
      hrhsb, hrlp, hrres, ⟨rbinders, hrhsAstrip, ?_⟩,
      ⟨rhsTy, hity⟩,
      tcv, tval, hthmE, htlps,
      ⟨sbinders, ℓA, tySlot, hSstrip, ?_⟩, fvsO, sbodyO, hopenO,
      hsty1, hsty2⟩,
    henv⟩
  · -- the rule's domains are the constructor's
    intro i0 b b' hlt hb hb'
    exact domsMatchAux_inv hdomsR hlt (o₁ := 0) (o₂ := 0)
      (by simpa using hb) (by simpa using hb')
  · -- the statement's domains are the constructor's, renamed
    intro i0 b b' hlt hb hb'
    exact domsMatchAux_inv hdomsS hlt (o₁ := 0) (o₂ := 0)
      (by simpa using hb) (by simpa using hb')

/-- **The projection-function fold, run half.**  `projInstallRS`
without the install: `ProjPhaseInvS` and `BlockInstalledTT` were
`projFnRR`'s inputs, and `projFnRR` existed to carry the `EnvFacts` across
the cons — which the run record does not need. -/
theorem projInstallRunRS {μ : CheckMode} {F : Nat} {T ctorName : Name}
    {lps : List Name} {nP nF : Nat} :
    ∀ (fields : List Nat) {env' env₄ : Env},
      fields.foldlM (installProjFnStep (m := CheckM) μ (fueledOps μ F)
        T ctorName lps nP nF) env' = .ok env₄ →
      ProjInstallRun μ F T ctorName lps nP nF env' fields env₄ := by
  intro fields
  induction fields with
  | nil =>
    intro env' env₄ h
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h.symm
  | cons i rest ih =>
    intro env' env₄ h
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    revert h
    cases hstep : installProjFnStep (m := CheckM) μ (fueledOps μ F) T
        ctorName lps nP nF env' i with
    | error e => intro h; exact nomatch h
    | ok env'' => ?_
    intro h
    by_cases hm : (env'.find? (projModelName T i)).isSome = true
    case neg =>
      -- the skip branch: the step is the identity
      have henv : env'' = env' := by
        simp only [installProjFnStep, if_neg hm, pure, Except.pure,
          Except.ok.injEq] at hstep
        exact hstep.symm
      subst henv
      refine ⟨env'', Or.inr ⟨?_, rfl⟩, ih h⟩
      revert hm
      cases (env''.find? (projModelName T i)) <;> simp
    -- the install branch
    have hchk : checkProjFn μ (fueledOps μ F) env' T ctorName lps nP
        nF i = .ok env'' := by
      simp only [installProjFnStep, if_pos hm] at hstep
      exact hstep
    exact ⟨env'', Or.inl (projFnRun_of hchk), ih h⟩

/-! ## The assembly -/

/-- **The `indDecl` branch, run half** (`checkModeled`) — the batch's
deliverable and the campaign's last door.

`declIndRR`'s five folds, each replaced by its run twin, and **the
whole block-bookkeeping half deleted**: `hI0`/`hEC0`/`hBP0` (the base
invariants pulled back through the checker folds), `hpMem` (the η pins
at the single inductive member), `hall`/`hbshape`/`hTnres`/`hinvR` (the
recursor group's and projection phase's carrier inputs) and the
`indRecsCoreR` swap all existed to feed a `∀ φ` row somewhere below.

(Task #175 tower-flag: the elimination-template install is gone, and
with it the run record's last conjunct.) -/
theorem declIndRun_of
    {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo}
    (h : checkModeled (m := CheckM) μ (fueledOps μ F) env block
      = .ok env₂) :
    DeclIndRun μ F env block env₂ := by
  simp only [checkModeled, Bind.bind, Except.bind, pure,
    Except.pure] at h
  split at h
  case isFalse => simp [throw, throwThe, MonadExceptOf.throw] at h
  next hsplit =>
  -- the guard now decides the SAME statement through `recsFormSuffix`
  -- (`ConLeche/Kernel/Env.lean`), so it arrives as a `decide`
  have hsplit := of_decide_eq_true hsplit
  split at h
  case h_2 =>
    next hnone =>
    split at h
    case h_1 => exact nomatch h
    next envM hmemFold =>
    refine ⟨hsplit, Or.inr ⟨?_, envM,
      indMembersRunRS _ hmemFold, indRecsRunRS _ h⟩⟩
    rintro ⟨cvT, capsT, cvC, nP, nF, hI, hC⟩
    exact hnone cvT capsT cvC nP nF hI hC
  next cvT capsT cvC nP nF hIfilt hCfilt =>
  split at h
  case h_1 => exact nomatch h
  next envM hmemFold =>
  split at h
  case h_1 => exact nomatch h
  next envR hrecsFold =>
  split at h
  case isFalse => exact nomatch h
  next hres =>
  split at h
  case isFalse => exact nomatch h
  next hprojFresh =>
  -- the projection phase: structure-like blocks only (task #175 SigmaHom)
  by_cases hsl : ctorTargetsFam cvC.type cvT.name cvT.levelParams nP nF = true
  case neg =>
    rw [if_neg hsl] at h
    obtain rfl : envR = env₂ := Except.ok.inj h
    exact ⟨hsplit, Or.inl ⟨cvT, capsT, cvC, nP, nF, hIfilt, hCfilt,
      envM, envR, indMembersRunRS _ hmemFold, indRecsRunRS _ hrecsFold,
      hres, hprojFresh, (by rw [if_neg hsl]; rfl)⟩⟩
  rw [if_pos hsl] at h
  exact ⟨hsplit, Or.inl ⟨cvT, capsT, cvC, nP, nF, hIfilt, hCfilt,
    envM, envR, indMembersRunRS _ hmemFold, indRecsRunRS _ hrecsFold,
    hres, hprojFresh,
    (by rw [if_pos hsl]; exact projInstallRunRS (List.range nF) h)⟩⟩

end ConLeche.Semantics
