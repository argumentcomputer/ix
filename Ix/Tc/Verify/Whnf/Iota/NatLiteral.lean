import Ix.Tc.Verify.Whnf.Iota.ConstructorDispatch

/-!
# Nat-literal iota preprocessing

ConstructorDispatch verifies the ordinary-constructor path once the normalized major is
already a constructor spine.  This slice closes the adjacent Nat-literal
branch: production expands exactly one constructor layer, marks the ensuing
iota application transient, performs the second Nat-offset cleanup, and then
uses the same constructor-indexed dispatcher.

String-literal expansion remains separate because it invokes a recursive
WHNF callback after constructing the String spine.  K synthesis and struct
eta likewise retain their own inference and recursive-WHNF obligations.
-/

namespace Ix.Tc

open Lean4Lean (VDefEq VExpr)

namespace RecM

/-- Production's zero-literal expansion reads the active primitive table and
does not mutate checker state. -/
theorem natToConstructor_zero
    (methods : Methods .anon) (s : TcState .anon) :
    (natToConstructor 0).run methods s =
      .ok (KExpr.mkConst s.prims.natZero #[]) s := by
  unfold natToConstructor
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run prims methods) _ s = _
  unfold EStateM.bind
  rw [show ReaderT.run prims methods s = .ok s.prims s from rfl]
  rfl

/-- Production exposes exactly one successor layer and retains the
predecessor as a literal.  In particular, this is not recursive unary
expansion. -/
theorem natToConstructor_succ
    (methods : Methods .anon) (s : TcState .anon) (predecessor : Nat) :
    (natToConstructor (predecessor + 1)).run methods s =
      .ok (KExpr.mkApp (KExpr.mkConst s.prims.natSucc #[])
        (natExprFromValue predecessor)) s := by
  unfold natToConstructor
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run prims methods) _ s = _
  unfold EStateM.bind
  rw [show ReaderT.run prims methods s = .ok s.prims s from rfl]
  rfl

/-- Exact Nat-literal path through post-WHNF preprocessing.  The dispatch
receives `transient = true`, matching production's protection against
interning work proportional to a literal's value. -/
theorem tryIotaAfterMajorWhnf_nat
    {methods : Methods .anon} {flags : WhnfFlags}
    {s sNat sCleanup sf : TcState .anon}
    {recId : KId .anon} {recr : IotaInfo .anon}
    {recUs : Array (KUniv .anon)} {spine : Array (KExpr .anon)}
    {value : Nat} {blob : Address} {info : ExprInfo .anon}
    {ctorMajor result : KExpr .anon}
    (hnat : (natToConstructor value).run methods s = .ok ctorMajor sNat)
    (hctorShape : IotaCtorMajor ctorMajor)
    (hcleanup : (cleanupNatOffsetMajor ctorMajor).run methods sNat =
      .ok none sCleanup)
    (hdispatch :
      (tryIotaCtorOrStructEta recId recr recUs spine ctorMajor true).run
        methods sCleanup = .ok (some result) sf) :
    (tryIotaAfterMajorWhnf flags recId recr recUs spine
      (.nat value blob info)).run methods s = .ok (some result) sf := by
  unfold tryIotaAfterMajorWhnf
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run (natToConstructor value) methods) _ s = _
  unfold EStateM.bind
  rw [hnat]
  cases hctorShape <;> simp only [pure_bind]
  all_goals
    rw [ReaderT.run_bind]
    change EStateM.bind _ _ sNat = _
    unfold EStateM.bind
    rw [hcleanup]
    exact hdispatch

/-- Complete non-K Nat-literal branch of `tryIotaWithFlags`.  Constructor
lookup and rule selection are the same production operations as ConstructorDispatch, but
the selected rule now runs transiently after one-layer literal expansion. -/
theorem tryIotaWithFlags_natCtor
    {methods : Methods .anon} {source : KExpr .anon} {flags : WhnfFlags}
    {s sLookup sCleanup sWhnf sNat sCleanupWhnf sCtor sf : TcState .anon}
    {recId : KId .anon} {recUs : Array (KUniv .anon)}
    {headInfo : ExprInfo .anon} {spine : Array (KExpr .anon)}
    {recursor : KConst .anon} {recr : IotaInfo .anon}
    {major : KExpr .anon} {value : Nat} {blob : Address}
    {natInfo : ExprInfo .anon} {ctorMajor : KExpr .anon}
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
    (hwhnf :
      (if flags.cheapRec then
          (whnfCoreFlagsRec major flags).run methods sCleanup
        else (whnfRec major).run methods sCleanup) =
        .ok (.nat value blob natInfo) sWhnf)
    (hnat : (natToConstructor value).run methods sWhnf =
      .ok ctorMajor sNat)
    (hctorShape : IotaCtorMajor ctorMajor)
    (hcleanupWhnf : (cleanupNatOffsetMajor ctorMajor).run methods sNat =
      .ok none sCleanupWhnf)
    (hctorSpine : ctorMajor.collectSpine =
      (.const ctorId ctorUs ctorHeadInfo, ctorArgs))
    (hctorLookup : TcM.tryGetConst ctorId sCleanupWhnf =
      .ok (some ctor) sCtor)
    (hctorInfo : ctor.iotaCtorInfo? = some (cidx, ctorFields))
    (hdispatch :
      (tryApplyIotaCtor recr recUs spine ctorArgs cidx ctorFields true).run
        methods sCtor = .ok (some result) sf) :
    (tryIotaWithFlags source flags).run methods s = .ok (some result) sf := by
  have hctor := tryIotaCtorOrStructEta_regular (recId := recId)
    (transient := true) hctorSpine hctorLookup hctorInfo hdispatch
  have hafter := tryIotaAfterMajorWhnf_nat (flags := flags)
    (blob := blob) (info := natInfo) hnat hctorShape hcleanupWhnf hctor
  exact tryIotaWithFlags_nonKPrefix hsource hlookup hinfo hmajorBound hmajor
    hk hcleanup hwhnf hafter

/-- Headline NatLiteral contract: an actual Nat-literal recursor run executes the
checked constructor rule selected after literal expansion.  As in ConstructorDispatch, the
mutable prefix frame and dispatch-ingress invariant remain explicit until
the cleanup, callback, and lazy lookup helpers receive their own semantic
preservation theorems. -/
theorem tryIotaWithFlags_natCtor_checkedAcceptance_empty
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {methods : Methods .anon} {source : KExpr .anon} {flags : WhnfFlags}
    {s sLookup sCleanup sWhnf sNat sCleanupWhnf sCtor sf : TcState .anon}
    {recId : KId .anon} {recUs : Array (KUniv .anon)}
    {headInfo : ExprInfo .anon} {spine : Array (KExpr .anon)}
    {recursor : KConst .anon} {recr : IotaInfo .anon}
    {major : KExpr .anon} {value : Nat} {blob : Address}
    {natInfo : ExprInfo .anon} {ctorMajor : KExpr .anon}
    {ctorId : KId .anon} {ctorUs : Array (KUniv .anon)}
    {ctorHeadInfo : ExprInfo .anon} {ctorArgs : Array (KExpr .anon)}
    {ctor : KConst .anon} {cidx ctorFields : Nat}
    {rule : RecRule .anon} {defeq : VDefEq} {startV : VExpr}
    {final : KExpr .anon} {finalV : VExpr}
    (h : ApplyIotaCtorTrace layer semantics trProj world support 0 []
      methods recr recUs spine ctorArgs cidx ctorFields true rule startV
      sCtor final finalV sf)
    (hcollect : source.collectSpine = (.const recId recUs headInfo, spine))
    (hlookup : TcM.tryGetConst recId s = .ok (some recursor) sLookup)
    (hinfo : recursor.iotaInfo? = some recr)
    (hmajorBound : recr.majorIdx < spine.size)
    (hmajor : spine[recr.majorIdx]! = major)
    (hk : recr.k = false)
    (hcleanup : (cleanupNatOffsetMajor major).run methods sLookup =
      .ok none sCleanup)
    (hwhnf :
      (if flags.cheapRec then
          (whnfCoreFlagsRec major flags).run methods sCleanup
        else (whnfRec major).run methods sCleanup) =
        .ok (.nat value blob natInfo) sWhnf)
    (hnat : (natToConstructor value).run methods sWhnf =
      .ok ctorMajor sNat)
    (hctorShape : IotaCtorMajor ctorMajor)
    (hcleanupWhnf : (cleanupNatOffsetMajor ctorMajor).run methods sNat =
      .ok none sCleanupWhnf)
    (hctorSpine : ctorMajor.collectSpine =
      (.const ctorId ctorUs ctorHeadInfo, ctorArgs))
    (hctorLookup : TcM.tryGetConst ctorId sCleanupWhnf =
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
          pattern.constructorFields.toNat true rule startV sCtor final finalV
          sf := by
    simpa only [hdispatchAligned.ruleIndex, hdispatchAligned.fields] using h
  have hchecked := hpatternDispatch.checkedAcceptance_empty hregistered
    theory hempty harity hdispatchI hruleSupport hstartV hpattern hsourceTr
    hsourceType hmatch hchecks hrhsAligned
  obtain ⟨_, hfinalI, hdispatchFrame, hfinalSupport, hmeaning⟩ := hchecked
  have hrun := tryIotaWithFlags_natCtor hcollect hlookup hinfo
    hmajorBound hmajor hk hcleanup hwhnf hnat hctorShape hcleanupWhnf
    hctorSpine hctorLookup hctorInfo h.eval
  exact ⟨hrun, hfinalI, hprefixFrame.trans hdispatchFrame,
    hfinalSupport, hmeaning⟩

end RecM

end Ix.Tc
