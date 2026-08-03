import Ix.Tc.Verify.Whnf.Iota.SelectedRule

/-!
# Ordinary-constructor iota dispatch

SelectedRule verifies execution after one concrete recursor rule has already been
selected.  This slice moves the boundary outward through production's rule
array lookup, universe-arity guard, and constructor-field guard.  It also
records the exact regular-constructor path through `tryIotaWithFlags`:
recursor lookup, major cleanup/WHNF, constructor lookup, and dispatch.

The trace deliberately excludes the three preprocessing variants that alter
the major before constructor dispatch: K synthesis, Nat-literal expansion,
and String-literal expansion.  Those remain separate exhaustive branches;
the regular theorem cannot silently justify any of them.
-/

namespace Ix.Tc

open Lean4Lean (VDefEq VExpr)

namespace KConst

/-- The pure iota snapshot retains production's exact wrapping major index. -/
theorem recursorMajorIdx_of_iotaInfo
    {c : KConst .anon} {recr : IotaInfo .anon}
    (hinfo : c.iotaInfo? = some recr) :
    c.RecursorMajorIdx = some recr.majorIdx := by
  cases c <;> simp [KConst.iotaInfo?] at hinfo
  case recr =>
    cases hinfo
    simp [KConst.RecursorMajorIdx]

/-- A rule selected from the decoded snapshot is at the same position in the
loaded recursor declaration.  This prevents a semantic certificate for one
array slot from being reused for another. -/
theorem recursorRuleAt_of_iotaInfo
    {c : KConst .anon} {recr : IotaInfo .anon}
    (hinfo : c.iotaInfo? = some recr)
    {index : Nat} {rule : RecRule .anon}
    (hrule : recr.rules[index]? = some rule) :
    c.RecursorRuleAt index rule := by
  cases c <;> simp [KConst.iotaInfo?] at hinfo
  case recr =>
    cases hinfo
    exact hrule

end KConst

namespace RecM

/-- Exact successful execution data for the constructor-dispatch helper.
The selected rule is an index, rather than existential data hidden inside the
record, so this remains a proof-irrelevant operational certificate. -/
structure TryApplyIotaCtorSuccessTrace
    (methods : Methods .anon) (recr : IotaInfo .anon)
    (recUs : Array (KUniv .anon))
    (spine ctorArgs : Array (KExpr .anon)) (cidx ctorFields : Nat)
    (transient : Bool) (rule : RecRule .anon)
    (s : TcState .anon) (final : KExpr .anon) (sf : TcState .anon) : Prop where
  selected : recr.rules[cidx]? = some rule
  levelArity : recUs.size.toUInt64 = recr.lvls
  fieldBound : ctorFields ≤ ctorArgs.size
  apply : (applyIotaRule rule recUs recr spine ctorArgs ctorFields
    transient).run methods s = .ok final sf

namespace TryApplyIotaCtorSuccessTrace

/-- Erase the dispatch certificate to the exact extracted production run. -/
theorem eval
    {methods : Methods .anon} {recr : IotaInfo .anon}
    {recUs : Array (KUniv .anon)}
    {spine ctorArgs : Array (KExpr .anon)} {cidx ctorFields : Nat}
    {transient : Bool} {rule : RecRule .anon}
    {s : TcState .anon} {final : KExpr .anon} {sf : TcState .anon}
    (h : TryApplyIotaCtorSuccessTrace methods recr recUs spine ctorArgs
      cidx ctorFields transient rule s final sf) :
    (tryApplyIotaCtor recr recUs spine ctorArgs cidx ctorFields transient).run
      methods s = .ok (some final) sf := by
  unfold tryApplyIotaCtor
  rw [h.selected]
  simp only
  have hlevels : (recUs.size.toUInt64 != recr.lvls) = false := by
    simp [h.levelArity]
  rw [hlevels]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [if_neg (Nat.not_lt.mpr h.fieldBound)]
  simp only [pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run
      (applyIotaRule rule recUs recr spine ctorArgs ctorFields transient)
      methods) _ s = _
  unfold EStateM.bind
  rw [h.apply]
  rfl

end TryApplyIotaCtorSuccessTrace

/-- Semantic dispatch certificate: the guard facts are tied to SelectedRule's exact
selected-rule trace, so the operational rule and the semantically interpreted
rule cannot drift apart. -/
structure ApplyIotaCtorTrace
    (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (Delta : KVLCtx) (methods : Methods .anon)
    (recr : IotaInfo .anon) (recUs : Array (KUniv .anon))
    (spine ctorArgs : Array (KExpr .anon)) (cidx ctorFields : Nat)
    (transient : Bool) (rule : RecRule .anon) (startV : VExpr)
    (s : TcState .anon) (final : KExpr .anon) (finalV : VExpr)
    (sf : TcState .anon) : Type where
  selected : recr.rules[cidx]? = some rule
  levelArity : recUs.size.toUInt64 = recr.lvls
  fieldBound : ctorFields ≤ ctorArgs.size
  ruleTrace : ApplyIotaRuleTrace layer semantics trProj world support uvars
    Delta methods rule recUs recr spine ctorArgs ctorFields transient startV
    s final finalV sf

namespace ApplyIotaCtorTrace

theorem operational
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {recr : IotaInfo .anon} {recUs : Array (KUniv .anon)}
    {spine ctorArgs : Array (KExpr .anon)} {cidx ctorFields : Nat}
    {transient : Bool} {rule : RecRule .anon} {startV : VExpr}
    {s : TcState .anon} {final : KExpr .anon} {finalV : VExpr}
    {sf : TcState .anon}
    (h : ApplyIotaCtorTrace layer semantics trProj world support uvars Delta
      methods recr recUs spine ctorArgs cidx ctorFields transient rule startV
      s final finalV sf) :
    TryApplyIotaCtorSuccessTrace methods recr recUs spine ctorArgs cidx
      ctorFields transient rule s final sf :=
  ⟨h.selected, h.levelArity, h.fieldBound, h.ruleTrace.eval⟩

/-- Exact execution of the constructor dispatch seam. -/
theorem eval
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {recr : IotaInfo .anon} {recUs : Array (KUniv .anon)}
    {spine ctorArgs : Array (KExpr .anon)} {cidx ctorFields : Nat}
    {transient : Bool} {rule : RecRule .anon} {startV : VExpr}
    {s : TcState .anon} {final : KExpr .anon} {finalV : VExpr}
    {sf : TcState .anon}
    (h : ApplyIotaCtorTrace layer semantics trProj world support uvars Delta
      methods recr recUs spine ctorArgs cidx ctorFields transient rule startV
      s final finalV sf) :
    (tryApplyIotaCtor recr recUs spine ctorArgs cidx ctorFields transient).run
      methods s = .ok (some final) sf :=
  h.operational.eval

/-- The exact decoded rule position is also a position in the loaded
recursor that produced the snapshot. -/
theorem recursorRuleAt
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {recr : IotaInfo .anon} {recUs : Array (KUniv .anon)}
    {spine ctorArgs : Array (KExpr .anon)} {cidx ctorFields : Nat}
    {transient : Bool} {rule : RecRule .anon} {startV : VExpr}
    {s : TcState .anon} {final : KExpr .anon} {finalV : VExpr}
    {sf : TcState .anon}
    (h : ApplyIotaCtorTrace layer semantics trProj world support uvars Delta
      methods recr recUs spine ctorArgs cidx ctorFields transient rule startV
      s final finalV sf)
    {recursor : KConst .anon}
    (hinfo : recursor.iotaInfo? = some recr) :
    recursor.RecursorRuleAt cidx rule :=
  KConst.recursorRuleAt_of_iotaInfo hinfo h.selected

/-- Parameter-free semantic acceptance before relating the registered rule
back to an original recursor application. -/
theorem acceptance_empty
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {recr : IotaInfo .anon} {recUs : Array (KUniv .anon)}
    {spine ctorArgs : Array (KExpr .anon)} {cidx ctorFields : Nat}
    {transient : Bool} {rule : RecRule .anon} {startV : VExpr}
    {s : TcState .anon} {final : KExpr .anon} {finalV : VExpr}
    {sf : TcState .anon}
    (h : ApplyIotaCtorTrace layer semantics trProj world support uvars Delta
      methods recr recUs spine ctorArgs cidx ctorFields transient rule startV
      s final finalV sf)
    (hempty : recUs.isEmpty = true)
    (theory : WhnfTheory trProj world uvars)
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (hruleSupport : support rule.rhs)
    (hruleTr : TrKExpr world.venv uvars world.nameOf trProj Delta rule.rhs
      startV) :
    (tryApplyIotaCtor recr recUs spine ctorArgs cidx ctorFields transient).run
        methods s = .ok (some final) sf ∧
      WhnfStateInv layer semantics trProj world support uvars Delta sf ∧
      InternUpdateFrame s sf ∧
      support final ∧
      TrKExpr world.venv uvars world.nameOf trProj Delta final finalV ∧
      WhnfMeaning trProj world uvars Delta
        ((((iotaPrefixArgs recr spine).toList ++
          (iotaFieldArgs ctorArgs ctorFields).toList) ++
          (iotaTrailingArgs recr spine).toList).foldl
            KExpr.mkApp h.ruleTrace.rhs) final := by
  have hacc := h.ruleTrace.acceptance_empty hempty theory hDelta hI
    hruleSupport hruleTr
  exact ⟨h.eval, hacc.2⟩

/-- Parameter-free checked acceptance lifted through the exact rule-selection
and guard helper.  Runtime/pattern alignment is added by the outer regular
branch theorem below, where the constructor lookup is still visible. -/
theorem checkedAcceptance_empty
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {methods : Methods .anon}
    {id : KId .anon} {recursor : KConst .anon}
    {recr : IotaInfo .anon} {recUs : Array (KUniv .anon)}
    {spine ctorArgs : Array (KExpr .anon)} {cidx ctorFields : Nat}
    {transient : Bool} {rule : RecRule .anon} {defeq : VDefEq}
    {startV : VExpr} {s : TcState .anon}
    {final : KExpr .anon} {finalV : VExpr} {sf : TcState .anon}
    (h : ApplyIotaCtorTrace layer semantics trProj world support 0 []
      methods recr recUs spine ctorArgs cidx ctorFields transient rule startV
      s final finalV sf)
    (hregistered : RegisteredRecursorRuleRhsRel world.venv world.nameOf
      trProj id recursor rule defeq)
    (theory : WhnfTheory trProj world 0)
    (hempty : recUs.isEmpty = true)
    (harity : defeq.uvars = 0)
    (hI : WhnfStateInv layer semantics trProj world support 0 [] s)
    (hruleSupport : support rule.rhs)
    (hstartV : startV = defeq.rhs)
    {pattern : RecursorRulePattern}
    (hpattern : RawRecursorRulePatternRel world.venv world.catalog
      world.nameOf id recursor rule pattern)
    {source : KExpr .anon} {sourceV sourceType : VExpr}
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
    (haligned : IotaRhsApplicationAligned pattern levels captures finalV) :
    (tryApplyIotaCtor recr recUs spine ctorArgs cidx ctorFields transient).run
        methods s = .ok (some final) sf ∧
      WhnfStateInv layer semantics trProj world support 0 [] sf ∧
      InternUpdateFrame s sf ∧
      support final ∧
      WhnfMeaning trProj world 0 [] source final := by
  have hacc := h.ruleTrace.checkedAcceptance_empty hregistered theory hempty
    harity hI hruleSupport hstartV hpattern hsourceTr hsourceType hmatch
    hchecks haligned
  exact ⟨h.eval, hacc.2⟩

/-- Universe-instantiated checked acceptance lifted through the same exact
constructor dispatch. -/
theorem checkedAcceptance_nonempty
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {methods : Methods .anon}
    {id : KId .anon} {recursor : KConst .anon}
    {recr : IotaInfo .anon} {recUs : Array (KUniv .anon)}
    {spine ctorArgs : Array (KExpr .anon)} {cidx ctorFields : Nat}
    {transient : Bool} {rule : RecRule .anon} {defeq : VDefEq}
    {startV : VExpr} {s : TcState .anon}
    {final : KExpr .anon} {finalV : VExpr} {sf : TcState .anon}
    (h : ApplyIotaCtorTrace layer semantics trProj world support uvars []
      methods recr recUs spine ctorArgs cidx ctorFields transient rule startV
      s final finalV sf)
    (hregistered : RegisteredRecursorRuleRhsRel world.venv world.nameOf
      trProj id recursor rule defeq)
    (theory : WhnfTheory trProj world uvars)
    (hnonempty : recUs.isEmpty = false)
    (hus : ∀ level ∈ recUs, (KUniv.toVLevel level).WF uvars)
    (harity : defeq.uvars = recUs.size)
    (hcollision : support.CollisionFree)
    (hreach : ∀ x, KExpr.InstUnivReach recUs rule.rhs x → support x)
    (hI : WhnfStateInv layer semantics trProj world support uvars [] s)
    (hfaithful : ∀ left right,
      KExpr.LevelReach recUs rule.rhs left →
      KExpr.LevelReach recUs rule.rhs right → left.AddrFaithful right)
    (hsize : ∀ level, KExpr.LevelReach recUs rule.rhs level →
      level.size < UInt64.size)
    (hstartV : startV =
      defeq.rhs.instL (recUs.toList.map KUniv.toVLevel))
    {pattern : RecursorRulePattern}
    (hpattern : RawRecursorRulePatternRel world.venv world.catalog
      world.nameOf id recursor rule pattern)
    {source : KExpr .anon} {sourceV sourceType : VExpr}
    (hsourceTr : TrKExprS world.venv uvars world.nameOf trProj [] source
      sourceV)
    (hsourceType : world.venv.HasType uvars [] sourceV sourceType)
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
      (world.venv.IsDefEqU uvars []) levels captures)
    (haligned : IotaRhsApplicationAligned pattern levels captures finalV) :
    (tryApplyIotaCtor recr recUs spine ctorArgs cidx ctorFields transient).run
        methods s = .ok (some final) sf ∧
      WhnfStateInv layer semantics trProj world support uvars [] sf ∧
      InternUpdateFrame s sf ∧
      support final ∧
      WhnfMeaning trProj world uvars [] source final := by
  have hacc := h.ruleTrace.checkedAcceptance_nonempty hregistered theory
    hnonempty hus harity hcollision hreach hI hfaithful hsize hstartV
    hpattern hsourceTr hsourceType hmatch hchecks haligned
  exact ⟨h.eval, hacc.2⟩

end ApplyIotaCtorTrace

/-- Explicit bridge between the constructor metadata selected by execution
and the pattern metadata supplied by inductive admission.  Duplicate rule
bodies make the index equality non-derivable from rule equality alone. -/
structure IotaCtorDispatchAligned (cidx ctorFields : Nat)
    (pattern : RecursorRulePattern) : Prop where
  ruleIndex : pattern.ruleIndex = cidx
  fields : pattern.constructorFields.toNat = ctorFields

/-- Shapes that can enter the regular constructor-spine path without Nat or
String literal conversion.  A constant is the nullary case; an application
retains an arbitrary nonempty constructor spine. -/
inductive IotaCtorMajor : KExpr .anon → Prop
  | const {id us info} : IotaCtorMajor (.const id us info)
  | app {fn arg info} : IotaCtorMajor (.app fn arg info)

/-- Exact constructor-hit branch of the final dispatch seam. -/
theorem tryIotaCtorOrStructEta_regular
    {methods : Methods .anon}
    {s sCtor sf : TcState .anon}
    {recId : KId .anon} {recr : IotaInfo .anon}
    {recUs : Array (KUniv .anon)} {spine : Array (KExpr .anon)}
    {majorWhnf : KExpr .anon} {transient : Bool}
    {ctorId : KId .anon} {ctorUs : Array (KUniv .anon)}
    {ctorHeadInfo : ExprInfo .anon} {ctorArgs : Array (KExpr .anon)}
    {ctor : KConst .anon} {cidx ctorFields : Nat}
    {result : KExpr .anon}
    (hctorSpine : majorWhnf.collectSpine =
      (.const ctorId ctorUs ctorHeadInfo, ctorArgs))
    (hctorLookup : TcM.tryGetConst ctorId s = .ok (some ctor) sCtor)
    (hctorInfo : ctor.iotaCtorInfo? = some (cidx, ctorFields))
    (hdispatch :
      (tryApplyIotaCtor recr recUs spine ctorArgs cidx ctorFields transient).run
        methods sCtor = .ok (some result) sf) :
    (tryIotaCtorOrStructEta recId recr recUs spine majorWhnf transient).run
      methods s = .ok (some result) sf := by
  unfold tryIotaCtorOrStructEta
  rw [hctorSpine, ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.tryGetConst ctorId) _ s = _
  unfold EStateM.bind
  rw [hctorLookup]
  simp only [hctorInfo, pure_bind]
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run
      (tryApplyIotaCtor recr recUs spine ctorArgs cidx ctorFields transient)
      methods) _ sCtor = _
  unfold EStateM.bind
  rw [hdispatch]
  rfl

/-- Exact regular, non-literal path through post-WHNF preprocessing. -/
theorem tryIotaAfterMajorWhnf_regular
    {methods : Methods .anon} {flags : WhnfFlags}
    {s sCleanup sf : TcState .anon}
    {recId : KId .anon} {recr : IotaInfo .anon}
    {recUs : Array (KUniv .anon)} {spine : Array (KExpr .anon)}
    {majorWhnf : KExpr .anon} {result : KExpr .anon}
    (hmajorShape : IotaCtorMajor majorWhnf)
    (hcleanup : (cleanupNatOffsetMajor majorWhnf).run methods s =
      .ok none sCleanup)
    (hdispatch :
      (tryIotaCtorOrStructEta recId recr recUs spine majorWhnf false).run
        methods sCleanup = .ok (some result) sf) :
    (tryIotaAfterMajorWhnf flags recId recr recUs spine majorWhnf).run
      methods s = .ok (some result) sf := by
  unfold tryIotaAfterMajorWhnf
  cases hmajorShape <;>
    simp only [pure_bind]
  all_goals
    rw [ReaderT.run_bind]
    change EStateM.bind _ _ s = _
    unfold EStateM.bind
    rw [hcleanup]
    exact hdispatch

/-- Exact non-K prefix through recursor lookup, initial cleanup, and the
major callback.  Post-WHNF variants remain indexed by `hafter`. -/
theorem tryIotaWithFlags_nonKPrefix
    {methods : Methods .anon} {source : KExpr .anon} {flags : WhnfFlags}
    {s sLookup sCleanup sWhnf sf : TcState .anon}
    {recId : KId .anon} {recUs : Array (KUniv .anon)}
    {headInfo : ExprInfo .anon} {spine : Array (KExpr .anon)}
    {recursor : KConst .anon} {recr : IotaInfo .anon}
    {major majorWhnf result : KExpr .anon}
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
        .ok majorWhnf sWhnf)
    (hafter :
      (tryIotaAfterMajorWhnf flags recId recr recUs spine majorWhnf).run
        methods sWhnf = .ok (some result) sf) :
    (tryIotaWithFlags source flags).run methods s = .ok (some result) sf := by
  unfold tryIotaWithFlags
  rw [hsource, ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.tryGetConst recId) _ s = _
  unfold EStateM.bind
  rw [hlookup]
  simp only
  rw [hinfo]
  simp only
  rw [if_neg (Nat.not_le.mpr hmajorBound)]
  rw [hmajor, hk]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (cleanupNatOffsetMajor major) methods) _ sLookup = _
  unfold EStateM.bind
  rw [hcleanup]
  simp only [Option.getD]
  cases hcheap : flags.cheapRec
  · simp only [hcheap, Bool.false_eq_true, ↓reduceIte] at hwhnf ⊢
    change EStateM.bind _ _ sCleanup = _
    unfold EStateM.bind
    change whnfRec major methods sCleanup = .ok majorWhnf sWhnf at hwhnf
    rw [hwhnf]
    exact hafter
  · simp only [hcheap, ↓reduceIte] at hwhnf ⊢
    change EStateM.bind _ _ sCleanup = _
    unfold EStateM.bind
    change whnfCoreFlagsRec major flags methods sCleanup =
      .ok majorWhnf sWhnf at hwhnf
    rw [hwhnf]
    exact hafter

/-- Complete regular-constructor branch of `tryIotaWithFlags`.  Every
mutable prefix state is explicit, and the three extracted production seams
are composed without unfolding into another preprocessing variant. -/
theorem tryIotaWithFlags_regularCtor
    {methods : Methods .anon} {source : KExpr .anon} {flags : WhnfFlags}
    {s sLookup sCleanup sWhnf sCleanupWhnf sCtor sf : TcState .anon}
    {recId : KId .anon} {recUs : Array (KUniv .anon)}
    {headInfo : ExprInfo .anon} {spine : Array (KExpr .anon)}
    {recursor : KConst .anon} {recr : IotaInfo .anon}
    {major majorWhnf : KExpr .anon}
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
        .ok majorWhnf sWhnf)
    (hmajorShape : IotaCtorMajor majorWhnf)
    (hcleanupWhnf : (cleanupNatOffsetMajor majorWhnf).run methods sWhnf =
      .ok none sCleanupWhnf)
    (hctorSpine : majorWhnf.collectSpine =
      (.const ctorId ctorUs ctorHeadInfo, ctorArgs))
    (hctorLookup : TcM.tryGetConst ctorId sCleanupWhnf =
      .ok (some ctor) sCtor)
    (hctorInfo : ctor.iotaCtorInfo? = some (cidx, ctorFields))
    (hdispatch :
      (tryApplyIotaCtor recr recUs spine ctorArgs cidx ctorFields false).run
        methods sCtor = .ok (some result) sf) :
    (tryIotaWithFlags source flags).run methods s = .ok (some result) sf := by
  have hctor := tryIotaCtorOrStructEta_regular (recId := recId)
    hctorSpine hctorLookup hctorInfo hdispatch
  have hafter := tryIotaAfterMajorWhnf_regular (flags := flags)
    hmajorShape hcleanupWhnf hctor
  exact tryIotaWithFlags_nonKPrefix hsource hlookup hinfo hmajorBound hmajor
    hk hcleanup hwhnf hafter

/-- Headline ConstructorDispatch contract: the actual parameter-free regular-constructor
branch executes the checked rule selected at the runtime constructor index.
The mutable preprocessing prefix must supply its intern-only frame and the
invariant at dispatch ingress; later K1 slices discharge those facts for the
cleanup, callback, and lazy-lookup helpers themselves. -/
theorem tryIotaWithFlags_regularCtor_checkedAcceptance_empty
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {methods : Methods .anon} {source : KExpr .anon} {flags : WhnfFlags}
    {s sLookup sCleanup sWhnf sCleanupWhnf sCtor sf : TcState .anon}
    {recId : KId .anon} {recUs : Array (KUniv .anon)}
    {headInfo : ExprInfo .anon} {spine : Array (KExpr .anon)}
    {recursor : KConst .anon} {recr : IotaInfo .anon}
    {major majorWhnf : KExpr .anon}
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
    (hwhnf :
      (if flags.cheapRec then
          (whnfCoreFlagsRec major flags).run methods sCleanup
        else (whnfRec major).run methods sCleanup) =
        .ok majorWhnf sWhnf)
    (hmajorShape : IotaCtorMajor majorWhnf)
    (hcleanupWhnf : (cleanupNatOffsetMajor majorWhnf).run methods sWhnf =
      .ok none sCleanupWhnf)
    (hctorSpine : majorWhnf.collectSpine =
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
          pattern.constructorFields.toNat false rule startV sCtor final finalV
          sf := by
    simpa only [hdispatchAligned.ruleIndex, hdispatchAligned.fields] using h
  have hchecked := hpatternDispatch.checkedAcceptance_empty hregistered
    theory hempty harity hdispatchI hruleSupport hstartV hpattern hsourceTr
    hsourceType hmatch hchecks hrhsAligned
  obtain ⟨_, hfinalI, hdispatchFrame, hfinalSupport, hmeaning⟩ := hchecked
  have hrun := tryIotaWithFlags_regularCtor hcollect hlookup hinfo
    hmajorBound hmajor hk hcleanup hwhnf hmajorShape hcleanupWhnf
    hctorSpine hctorLookup hctorInfo h.eval
  exact ⟨hrun, hfinalI, hprefixFrame.trans hdispatchFrame,
    hfinalSupport, hmeaning⟩

end RecM

end Ix.Tc
