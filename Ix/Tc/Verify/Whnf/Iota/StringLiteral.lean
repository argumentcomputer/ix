import Ix.Tc.Verify.Whnf.Iota.NatLiteral

/-!
# String-literal iota preprocessing

NatLiteral closes the Nat-literal variant of production's post-WHNF iota path.
This slice closes the neighboring String variant: the second Nat-offset
cleanup must miss, `strLitToConstructor` builds the constructor spine through
the intern table, the callback selected by `cheapRec` normalizes that spine,
and ordinary constructor dispatch resumes with `transient = false`.

The callback's invariant and intern-only frame are explicit at the headline
boundary.  Proving those facts uniformly for arbitrary generated String
spines is a separate helper-closure obligation; this file does not disguise
it as a consequence of the operational callback equation.
-/

namespace Ix.Tc

open Lean4Lean (VDefEq VExpr)

namespace RecM

/-- Direct expression interning is total and changes only the intern table.
This operational fact does not require semantic collision freedom: a hash hit
may return an existing canonical node, but it cannot throw or mutate any
other checker component. -/
theorem intern_success_frame (e : KExpr .anon) (s : TcState .anon) :
    ∃ result s',
      TcM.intern e s = .ok result s' ∧ InternUpdateFrame s s' := by
  unfold TcM.intern TcM.runIntern
  generalize hpair : internExprM e s.env.intern = pair
  rcases pair with ⟨result, intern⟩
  refine ⟨result, { s with env := { s.env with intern } }, ?_, rfl⟩
  rfl

/-- The extracted character fold has a definitional empty case. -/
theorem strLitListToConstructor_empty
    (methods : Methods .anon) (s : TcState .anon)
    (charOfNat cons nil : KExpr .anon) :
    (strLitListToConstructor charOfNat cons [] nil).run methods s =
      .ok nil s := by
  rfl

/-- Every character-fold step is total and changes only the intern table.
The result remains abstract because collision freedom is what identifies an
intern request with the requested expression; totality and framing do not
need that stronger assumption. -/
theorem strLitListToConstructor_success_frame
    (methods : Methods .anon) (chars : List Char)
    (charOfNat cons list : KExpr .anon) (s : TcState .anon) :
    ∃ result s',
      (strLitListToConstructor charOfNat cons chars list).run methods s =
          .ok result s' ∧
        InternUpdateFrame s s' := by
  induction chars generalizing list s with
  | nil =>
      exact ⟨list, s, rfl, InternUpdateFrame.refl s⟩
  | cons c chars ih =>
      obtain ⟨natLit, s₁, hnatLit, hframe₁⟩ := intern_success_frame
        (natExprFromValue c.toNat) s
      obtain ⟨charVal, s₂, hcharVal, hframe₂⟩ := intern_success_frame
        (KExpr.mkApp charOfNat natLit) s₁
      obtain ⟨partialApp, s₃, hpartial, hframe₃⟩ := intern_success_frame
        (KExpr.mkApp cons charVal) s₂
      obtain ⟨nextList, s₄, hnextList, hframe₄⟩ := intern_success_frame
        (KExpr.mkApp partialApp list) s₃
      obtain ⟨result, s₅, htail, htailFrame⟩ := ih nextList s₄
      refine ⟨result, s₅, ?_,
        (((hframe₁.trans hframe₂).trans hframe₃).trans hframe₄).trans
          htailFrame⟩
      unfold strLitListToConstructor
      rw [ReaderT.run_bind, ReaderT.run_monadLift]
      change EStateM.bind (TcM.intern (natExprFromValue c.toNat)) _ s = _
      unfold EStateM.bind
      rw [hnatLit]
      simp only
      rw [ReaderT.run_bind, ReaderT.run_monadLift]
      change EStateM.bind (TcM.intern (KExpr.mkApp charOfNat natLit)) _ s₁ = _
      unfold EStateM.bind
      rw [hcharVal]
      simp only
      rw [ReaderT.run_bind, ReaderT.run_monadLift]
      change EStateM.bind (TcM.intern (KExpr.mkApp cons charVal)) _ s₂ = _
      unfold EStateM.bind
      rw [hpartial]
      simp only
      rw [ReaderT.run_bind, ReaderT.run_monadLift]
      change EStateM.bind (TcM.intern (KExpr.mkApp partialApp list)) _ s₃ = _
      unfold EStateM.bind
      rw [hnextList]
      exact htail

/-- Full String constructor expansion is total and intern-framed for every
literal.  Canonical-result identity remains deliberately separate: it needs
run-scoped collision freedom and support for every generated node. -/
theorem strLitToConstructor_success_frame
    (methods : Methods .anon) (value : String) (s : TcState .anon) :
    ∃ result s',
      (strLitToConstructor value).run methods s = .ok result s' ∧
        InternUpdateFrame s s' := by
  let p := s.prims
  obtain ⟨charConst, s₁, hcharConst, hframe₁⟩ := intern_success_frame
    (KExpr.mkConst p.charType #[]) s
  obtain ⟨charOfNat, s₂, hcharOfNat, hframe₂⟩ := intern_success_frame
    (KExpr.mkConst p.charOfNat #[]) s₁
  obtain ⟨stringMk, s₃, hstringMk, hframe₃⟩ := intern_success_frame
    (KExpr.mkConst p.stringOfList #[]) s₂
  obtain ⟨listNilZ, s₄, hlistNilZ, hframe₄⟩ := intern_success_frame
    (KExpr.mkConst p.listNil #[KUniv.mkZero]) s₃
  obtain ⟨nil, s₅, hnil, hframe₅⟩ := intern_success_frame
    (KExpr.mkApp listNilZ charConst) s₄
  obtain ⟨listConsZ, s₆, hlistConsZ, hframe₆⟩ := intern_success_frame
    (KExpr.mkConst p.listCons #[KUniv.mkZero]) s₅
  obtain ⟨cons, s₇, hcons, hframe₇⟩ := intern_success_frame
    (KExpr.mkApp listConsZ charConst) s₆
  obtain ⟨list, s₈, hlist, hlistFrame⟩ :=
    strLitListToConstructor_success_frame methods value.toList.reverse
      charOfNat cons nil s₇
  obtain ⟨result, s₉, hresult, hframe₉⟩ := intern_success_frame
    (KExpr.mkApp stringMk list) s₈
  refine ⟨result, s₉, ?_,
    (((((((hframe₁.trans hframe₂).trans hframe₃).trans hframe₄).trans
      hframe₅).trans hframe₆).trans hframe₇).trans hlistFrame).trans
        hframe₉⟩
  unfold strLitToConstructor
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run prims methods) _ s = _
  unfold EStateM.bind
  rw [show ReaderT.run prims methods s = .ok p s from rfl]
  simp only
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.intern (KExpr.mkConst p.charType #[])) _ s = _
  unfold EStateM.bind
  rw [hcharConst]
  simp only
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.intern (KExpr.mkConst p.charOfNat #[])) _ s₁ = _
  unfold EStateM.bind
  rw [hcharOfNat]
  simp only
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.intern (KExpr.mkConst p.stringOfList #[])) _ s₂ = _
  unfold EStateM.bind
  rw [hstringMk]
  simp only
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind
    (TcM.intern (KExpr.mkConst p.listNil #[KUniv.mkZero])) _ s₃ = _
  unfold EStateM.bind
  rw [hlistNilZ]
  simp only
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.intern (KExpr.mkApp listNilZ charConst)) _ s₄ = _
  unfold EStateM.bind
  rw [hnil]
  simp only
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind
    (TcM.intern (KExpr.mkConst p.listCons #[KUniv.mkZero])) _ s₅ = _
  unfold EStateM.bind
  rw [hlistConsZ]
  simp only
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.intern (KExpr.mkApp listConsZ charConst)) _ s₆ = _
  unfold EStateM.bind
  rw [hcons]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run
      (strLitListToConstructor charOfNat cons value.toList.reverse nil)
      methods) _ s₇ = _
  unfold EStateM.bind
  rw [hlist]
  simp only
  rw [ReaderT.run_monadLift]
  exact hresult

theorem evalNatOffsetLiteral_str
    (methods : Methods .anon) (s : TcState .anon)
    (value : String) (blob : Address) (info : ExprInfo .anon) :
    (evalNatOffsetLiteral (.str value blob info) 0).run methods s =
      .ok none s := by
  unfold evalNatOffsetLiteral evalNatOffsetLiteralFuel
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run prims methods) _ s = _
  unfold EStateM.bind
  rw [show ReaderT.run prims methods s = .ok s.prims s from rfl]
  rfl

theorem natOffset_str
    (methods : Methods .anon) (s : TcState .anon)
    (value : String) (blob : Address) (info : ExprInfo .anon) :
    (natOffset (.str value blob info) 0).run methods s = .ok none s := by
  unfold natOffset natOffsetFuel
  rfl

/-- The Nat-offset cleanup preceding String expansion is an exact,
state-preserving miss for every literal. -/
theorem cleanupNatOffsetMajor_str
    (methods : Methods .anon) (s : TcState .anon)
    (value : String) (blob : Address) (info : ExprInfo .anon) :
    (cleanupNatOffsetMajor (.str value blob info)).run methods s =
      .ok none s := by
  unfold cleanupNatOffsetMajor
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (evalNatOffsetLiteral (.str value blob info) 0) methods) _
      s = _
  unfold EStateM.bind
  rw [evalNatOffsetLiteral_str]
  simp only [Option.isSome, Bool.false_eq_true, if_false, pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (natOffset (.str value blob info) 0) methods) _ s = _
  unfold EStateM.bind
  rw [natOffset_str]
  rfl

/-- Exact String-literal path through post-WHNF preprocessing.  Unlike Nat
literals, String expansion runs a policy-selected recursive WHNF callback and
does not enable transient rule application. -/
theorem tryIotaAfterMajorWhnf_str
    {methods : Methods .anon} {flags : WhnfFlags}
    {s sCleanup sStr sWhnf sf : TcState .anon}
    {recId : KId .anon} {recr : IotaInfo .anon}
    {recUs : Array (KUniv .anon)} {spine : Array (KExpr .anon)}
    {value : String} {blob : Address} {info : ExprInfo .anon}
    {strCtor ctorMajor result : KExpr .anon}
    (hcleanup : (cleanupNatOffsetMajor (.str value blob info)).run methods s =
      .ok none sCleanup)
    (hstr : (strLitToConstructor value).run methods sCleanup =
      .ok strCtor sStr)
    (hwhnf :
      (if flags.cheapRec then
          (whnfCoreFlagsRec strCtor flags).run methods sStr
        else (whnfRec strCtor).run methods sStr) =
        .ok ctorMajor sWhnf)
    (hdispatch :
      (tryIotaCtorOrStructEta recId recr recUs spine ctorMajor false).run
        methods sWhnf = .ok (some result) sf) :
    (tryIotaAfterMajorWhnf flags recId recr recUs spine
      (.str value blob info)).run methods s = .ok (some result) sf := by
  unfold tryIotaAfterMajorWhnf
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (cleanupNatOffsetMajor (.str value blob info)) methods) _ s = _
  unfold EStateM.bind
  rw [hcleanup]
  simp only
  unfold tryIotaAfterCleanup
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (strLitToConstructor value) methods) _
    sCleanup = _
  unfold EStateM.bind
  rw [hstr]
  cases hcheap : flags.cheapRec
  · simp only [hcheap, Bool.false_eq_true, ↓reduceIte] at hwhnf ⊢
    change EStateM.bind _ _ sStr = _
    unfold EStateM.bind
    change whnfRec strCtor methods sStr = .ok ctorMajor sWhnf at hwhnf
    rw [hwhnf]
    exact hdispatch
  · simp only [hcheap, ↓reduceIte] at hwhnf ⊢
    change EStateM.bind _ _ sStr = _
    unfold EStateM.bind
    change whnfCoreFlagsRec strCtor flags methods sStr =
      .ok ctorMajor sWhnf at hwhnf
    rw [hwhnf]
    exact hdispatch

/-- Complete non-K String-literal branch of `tryIotaWithFlags`. -/
theorem tryIotaWithFlags_strCtor
    {methods : Methods .anon} {source : KExpr .anon} {flags : WhnfFlags}
    {s sLookup sCleanup sWhnf sCleanupWhnf sStr sStrWhnf sCtor sf :
      TcState .anon}
    {recId : KId .anon} {recUs : Array (KUniv .anon)}
    {headInfo : ExprInfo .anon} {spine : Array (KExpr .anon)}
    {recursor : KConst .anon} {recr : IotaInfo .anon}
    {major : KExpr .anon} {value : String} {blob : Address}
    {strInfo : ExprInfo .anon} {strCtor ctorMajor : KExpr .anon}
    {ctorId : KId .anon} {ctorUs : Array (KUniv .anon)}
    {ctorHeadInfo : ExprInfo .anon} {ctorArgs : Array (KExpr .anon)}
    {ctor : KConst .anon} {cidx ctorFields : Nat}
    {result : KExpr .anon}
    (hsource : source.collectSpine = (.const recId recUs headInfo, spine))
    (hlookup : TcM.tryGetConst recId s = .ok (some recursor) sLookup)
    (hinfo : recursor.iotaInfo? = some recr)
    (hmajorBound : recr.majorIdx < spine.size)
    (hmajor : spine[recr.majorIdx]! = major)
    (hk : recr.k = false)
    (hcleanup : (cleanupNatOffsetMajor major).run methods sLookup =
      .ok none sCleanup)
    (hmajorWhnf :
      (if flags.cheapRec then
          (whnfCoreFlagsRec major flags).run methods sCleanup
        else (whnfRec major).run methods sCleanup) =
        .ok (.str value blob strInfo) sWhnf)
    (hcleanupWhnf :
      (cleanupNatOffsetMajor (.str value blob strInfo)).run methods sWhnf =
        .ok none sCleanupWhnf)
    (hstr : (strLitToConstructor value).run methods sCleanupWhnf =
      .ok strCtor sStr)
    (hstrWhnf :
      (if flags.cheapRec then
          (whnfCoreFlagsRec strCtor flags).run methods sStr
        else (whnfRec strCtor).run methods sStr) =
        .ok ctorMajor sStrWhnf)
    (hctorSpine : ctorMajor.collectSpine =
      (.const ctorId ctorUs ctorHeadInfo, ctorArgs))
    (hctorLookup : TcM.tryGetConst ctorId sStrWhnf =
      .ok (some ctor) sCtor)
    (hctorInfo : ctor.iotaCtorInfo? = some (cidx, ctorFields))
    (hdispatch :
      (tryApplyIotaCtor recr recUs spine ctorArgs cidx ctorFields false).run
        methods sCtor = .ok (some result) sf) :
    (tryIotaWithFlags source flags).run methods s = .ok (some result) sf := by
  have hctor := tryIotaCtorOrStructEta_regular (recId := recId)
    (transient := false) hctorSpine hctorLookup hctorInfo hdispatch
  have hafter := tryIotaAfterMajorWhnf_str (flags := flags)
    hcleanupWhnf hstr hstrWhnf hctor
  exact tryIotaWithFlags_nonKPrefix hsource hlookup hinfo hmajorBound hmajor
    hk hcleanup hmajorWhnf hafter

/-- Headline StringLiteral contract: an actual String-literal recursor run executes the
checked ordinary-constructor rule selected after constructor expansion and
recursive normalization. -/
theorem tryIotaWithFlags_strCtor_checkedAcceptance_empty
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {methods : Methods .anon} {source : KExpr .anon} {flags : WhnfFlags}
    {s sLookup sCleanup sWhnf sCleanupWhnf sStr sStrWhnf sCtor sf :
      TcState .anon}
    {recId : KId .anon} {recUs : Array (KUniv .anon)}
    {headInfo : ExprInfo .anon} {spine : Array (KExpr .anon)}
    {recursor : KConst .anon} {recr : IotaInfo .anon}
    {major : KExpr .anon} {value : String} {blob : Address}
    {strInfo : ExprInfo .anon} {strCtor ctorMajor : KExpr .anon}
    {ctorId : KId .anon} {ctorUs : Array (KUniv .anon)}
    {ctorHeadInfo : ExprInfo .anon} {ctorArgs : Array (KExpr .anon)}
    {ctor : KConst .anon} {cidx ctorFields : Nat}
    {rule : RecRule .anon} {defeq : VDefEq} {startV : VExpr}
    {final : KExpr .anon} {finalV : VExpr}
    (h : ApplyIotaCtorTrace layer semantics trProj world support 0 []
      methods recr recUs spine ctorArgs cidx ctorFields false rule startV
      sCtor final finalV sf)
    (hcollect : source.collectSpine = (.const recId recUs headInfo, spine))
    (hlookup : TcM.tryGetConst recId s = .ok (some recursor) sLookup)
    (hinfo : recursor.iotaInfo? = some recr)
    (hmajorBound : recr.majorIdx < spine.size)
    (hmajor : spine[recr.majorIdx]! = major)
    (hk : recr.k = false)
    (hcleanup : (cleanupNatOffsetMajor major).run methods sLookup =
      .ok none sCleanup)
    (hmajorWhnf :
      (if flags.cheapRec then
          (whnfCoreFlagsRec major flags).run methods sCleanup
        else (whnfRec major).run methods sCleanup) =
        .ok (.str value blob strInfo) sWhnf)
    (hcleanupWhnf :
      (cleanupNatOffsetMajor (.str value blob strInfo)).run methods sWhnf =
        .ok none sCleanupWhnf)
    (hstr : (strLitToConstructor value).run methods sCleanupWhnf =
      .ok strCtor sStr)
    (hstrWhnf :
      (if flags.cheapRec then
          (whnfCoreFlagsRec strCtor flags).run methods sStr
        else (whnfRec strCtor).run methods sStr) =
        .ok ctorMajor sStrWhnf)
    (hctorSpine : ctorMajor.collectSpine =
      (.const ctorId ctorUs ctorHeadInfo, ctorArgs))
    (hctorLookup : TcM.tryGetConst ctorId sStrWhnf =
      .ok (some ctor) sCtor)
    (hctorInfo : ctor.iotaCtorInfo? = some (cidx, ctorFields))
    (hprefixFrame : InternUpdateFrame s sCtor)
    (hdispatchI : WhnfStateInv layer semantics trProj world support 0 []
      sCtor)
    (hregistered : RegisteredRecursorRuleRhsRel world.venv world.nameOf
      trProj recId recursor rule defeq)
    (theory : WhnfTheory trProj world 0)
    (hempty : recUs.isEmpty = true)
    (harity : defeq.uvars = 0)
    (hruleSupport : support rule.rhs)
    (hstartV : startV = defeq.rhs)
    {pattern : RecursorRulePattern}
    (hpattern : RawRecursorRulePatternRel world.venv world.catalog
      world.nameOf recId recursor rule pattern)
    (hdispatchAligned : IotaCtorDispatchAligned cidx ctorFields pattern)
    {sourceV sourceType : VExpr}
    (hsourceTr : TrKExprS world.venv 0 world.nameOf trProj [] source
      sourceV)
    (hsourceType : world.venv.HasType 0 [] sourceV sourceType)
    {levels : List Lean4Lean.VLevel}
    {captures : (RecursorIotaPattern pattern.recursorName pattern.majorIdx
      pattern.constructorName
      (pattern.constructorParams.toNat +
        pattern.constructorFields.toNat)).Path → VExpr}
    (hmatch : Lean4Lean.Pattern.Matches
      (RecursorIotaPattern pattern.recursorName pattern.majorIdx
        pattern.constructorName
        (pattern.constructorParams.toNat +
          pattern.constructorFields.toNat))
      sourceV levels captures)
    (hchecks : pattern.checks.OK
      (world.venv.IsDefEqU 0 []) levels captures)
    (hrhsAligned : IotaRhsApplicationAligned pattern levels captures
      finalV) :
    (tryIotaWithFlags source flags).run methods s = .ok (some final) sf ∧
      WhnfStateInv layer semantics trProj world support 0 [] sf ∧
      InternUpdateFrame s sf ∧
      support final ∧
      WhnfMeaning trProj world 0 [] source final := by
  have hpatternDispatch :
      ApplyIotaCtorTrace layer semantics trProj world support 0 [] methods
        recr recUs spine ctorArgs pattern.ruleIndex
          pattern.constructorFields.toNat false rule startV sCtor final finalV
          sf := by
    simpa only [hdispatchAligned.ruleIndex, hdispatchAligned.fields] using h
  have hchecked := hpatternDispatch.checkedAcceptance_empty hregistered
    theory hempty harity hdispatchI hruleSupport hstartV hpattern hsourceTr
    hsourceType hmatch hchecks hrhsAligned
  obtain ⟨_, hfinalI, hdispatchFrame, hfinalSupport, hmeaning⟩ := hchecked
  have hrun := tryIotaWithFlags_strCtor hcollect hlookup hinfo
    hmajorBound hmajor hk hcleanup hmajorWhnf hcleanupWhnf hstr hstrWhnf
    hctorSpine hctorLookup hctorInfo h.eval
  exact ⟨hrun, hfinalI, hprefixFrame.trans hdispatchFrame,
    hfinalSupport, hmeaning⟩

end RecM

end Ix.Tc
