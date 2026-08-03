import Ix.Tc.Verify.DefEq.StringLiteral
import Ix.Tc.Verify.Whnf.NoDelta.Reducer

/-!
# Cheap DefEq reduction prefix

DefEq performs two cheap-projection normalization passes before lazy delta:
structural core reduction and then no-delta WHNF.  This module verifies the
cheap-depth scope itself and composes both passes with address collision
freedom and the already verified structural comparison.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace RecM

/-- Common semantic contract for a direct production reducer used by DefEq. -/
def DefEqReduction.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat)
    (reduce : KExpr .anon → RecM .anon (KExpr .anon)) : Prop :=
  ∀ {Delta state source sourceV},
    support source →
    TrKExprS world.venv uvars world.nameOf trProj Delta source sourceV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (reduce source)
      (fun result _ => support result ∧
        WhnfPost trProj world uvars Delta sourceV result)

/-- Incrementing the cheap-recursion counter changes only operational
bookkeeping and preserves the complete verification invariant. -/
theorem cheapRecursionDepth_enter_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon} :
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) state
      (modify (fun s : TcState .anon =>
        {s with cheapRecursionDepth := s.cheapRecursionDepth + 1}))
      (fun _ _ => True) := by
  unfold modify
  exact TcM.WF.modifyGet
    (fun hI => hI.of_semantic_fields_eq rfl rfl rfl rfl rfl rfl rfl rfl)
    (fun _ => trivial)

/-- Decrementing the cheap-recursion counter is the matching invariant-safe
finalizer operation. -/
theorem cheapRecursionDepth_exit_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon} :
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) state
      (modify (fun s : TcState .anon =>
        {s with cheapRecursionDepth := s.cheapRecursionDepth - 1}))
      (fun _ _ => True) := by
  unfold modify
  exact TcM.WF.modifyGet
    (fun hI => hI.of_semantic_fields_eq rfl rfl rfl rfl rfl rfl rfl rfl)
    (fun _ => trivial)

/-- Any state-independent semantic result survives the production cheap-depth
scope.  The finalizer runs after both successful and failed body executions. -/
theorem withCheapRecursionDepth_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {x : RecM .anon α} {P : α → Prop}
    (hbody : ∀ {bodyState},
      RecM.WF layer semantics trProj world support uvars Delta bodyState x
        (fun result _ => P result)) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (withCheapRecursionDepth x) (fun result _ => P result) := by
  intro methods hmethods
  unfold withCheapRecursionDepth
  rw [ReaderT.run_bind]
  change TcM.WF
    (WhnfStateInv layer semantics trProj world support uvars Delta) state
    (do
      (modify (fun s : TcState .anon =>
        {s with cheapRecursionDepth := s.cheapRecursionDepth + 1}) :
          TcM .anon Unit)
      tryFinally (x.run methods)
        (modify (fun s : TcState .anon =>
          {s with cheapRecursionDepth := s.cheapRecursionDepth - 1})))
    (fun result _ => P result)
  apply TcM.WF.bind cheapRecursionDepth_enter_wf
  intro _ afterEnter _
  change TcM.WF
    (WhnfStateInv layer semantics trProj world support uvars Delta)
    afterEnter
    (tryFinally (x.run methods)
      (modify (fun s : TcState .anon =>
        {s with cheapRecursionDepth := s.cheapRecursionDepth - 1})))
    (fun result _ => P result)
  apply TcM.WF.tryFinally_const
  · exact hbody methods hmethods
  · intro afterBody
    exact cheapRecursionDepth_exit_wf

/-- Lift a verified `.DEF_EQ_CORE` structural reducer through the concrete
cheap-depth wrapper. -/
theorem whnfCoreForDefEq_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (hbody : DefEqReduction.WFAt layer semantics trProj world support uvars
      (fun source => whnfCoreWithFlags source .DEF_EQ_CORE)) :
    DefEqReduction.WFAt layer semantics trProj world support uvars
      whnfCoreForDefEq := by
  intro Delta state source sourceV hsourceSupport hsource
  unfold whnfCoreForDefEq
  apply withCheapRecursionDepth_wf
  intro bodyState
  exact hbody hsourceSupport hsource

/-- Lift a verified cheap no-delta reducer through the concrete cheap-depth
wrapper. -/
theorem whnfNoDeltaForDefEq_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (hbody : DefEqReduction.WFAt layer semantics trProj world support uvars
      (fun source => whnfNoDeltaImpl source .DEF_EQ_CORE .collapse)) :
    DefEqReduction.WFAt layer semantics trProj world support uvars
      whnfNoDeltaForDefEq := by
  intro Delta state source sourceV hsourceSupport hsource
  unfold whnfNoDeltaForDefEq
  apply withCheapRecursionDepth_wf
  intro bodyState
  exact hbody hsourceSupport hsource

/-- The two direct cheap reducers used by the pre-delta DefEq prefix. -/
structure DefEqCheapReductionContext
    (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) : Prop where
  core : DefEqReduction.WFAt layer semantics trProj world support uvars
    whnfCoreForDefEq
  noDelta : DefEqReduction.WFAt layer semantics trProj world support uvars
    whnfNoDeltaForDefEq

namespace DefEqCheapReductionContext

/-- Construct the public cheap reducers from their unwrapped K1/K2 body
contracts. -/
theorem ofBodies
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (hcore : DefEqReduction.WFAt layer semantics trProj world support uvars
      (fun source => whnfCoreWithFlags source .DEF_EQ_CORE))
    (hnoDelta : DefEqReduction.WFAt layer semantics trProj world support uvars
      (fun source => whnfNoDeltaImpl source .DEF_EQ_CORE .collapse)) :
    DefEqCheapReductionContext layer semantics trProj world support uvars :=
  ⟨whnfCoreForDefEq_wf hcore, whnfNoDeltaForDefEq_wf hnoDelta⟩

end DefEqCheapReductionContext

namespace DefEqAfterCorePass

/-- Semantic contract for the tiers following the cheap structural-core
comparison. -/
def WF (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) : Prop :=
  ∀ {Delta state a b aV bV},
    support a → support b →
    TrKExprS world.venv uvars world.nameOf trProj Delta a aV →
    TrKExprS world.venv uvars world.nameOf trProj Delta b bV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (isDefEqInnerAfterCorePass a b)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx aV bV)

/-- Close the first cheap normalization pass.  Address equality is interpreted
only through finite-run expression collision freedom; equal digests alone are
never treated as semantic equality. -/
theorem closesAfterStringExpansion
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    (hcollision : support.CollisionFree)
    (hsorts : SortComponentResources support)
    (hstructural : QuickDefEqResources support)
    (hreduction : DefEqCheapReductionContext layer semantics trProj world
      support uvars)
    (htail : WF layer semantics trProj world support uvars) :
    DefEqAfterStringExpansion.WF layer semantics trProj world support
      uvars := by
  intro Delta state a b aV bV haSupport hbSupport ha hb
  unfold isDefEqInnerAfterStringExpansion
  apply RecM.WF.bind (RecM.WF.withInv <|
    hreduction.core haSupport ha)
  intro ca afterA hca
  rcases hca with ⟨hIA, hcaSupport, caV, hcaTr, haCa⟩
  apply RecM.WF.bind (RecM.WF.withInv <|
    hreduction.core hbSupport hb)
  intro cb afterB hcb
  rcases hcb with ⟨hIB, hcbSupport, cbV, hcbTr, hbCb⟩
  cases haddr : ca.addr == cb.addr with
  | true =>
      simp only [if_true]
      exact RecM.WF.pure fun _ _ => by
        have herase :=
          hcollision.expr hcaSupport hcbSupport (eq_of_beq haddr)
        have hsame : ca = cb := by
          simpa only [KExpr.eraseMeta_anon] using herase
        subst cb
        have hmiddle := hcaTr.uniq world.venvWF theory.literalWF
          theory.projections
          (KVLCtx.IsDefEq.refl world.venvWF hIB.2.1.wf) hcbTr
        exact haCa.trans world.venvWF hIB.2.1.wf <|
          hmiddle.trans world.venvWF hIB.2.1.wf hbCb.symm
  | false =>
      simp only [Bool.false_eq_true, if_false]
      apply RecM.WF.bind
        (quickDefEq_wf theory hcollision hsorts hstructural
          hcaSupport hcbSupport hcaTr hcbTr)
      intro accepted afterQuick haccepted
      cases accepted with
      | true =>
          simp only [if_true]
          exact RecM.WF.pure fun hI _ =>
            haCa.trans world.venvWF hI.2.1.wf <|
              (haccepted rfl).trans world.venvWF hI.2.1.wf hbCb.symm
      | false =>
          simp only [Bool.false_eq_true, if_false]
          exact htail haSupport hbSupport ha hb

end DefEqAfterCorePass

namespace DefEqAfterNoDeltaPass

/-- Semantic contract for lazy-delta and final-WHNF tiers after the cheap
no-delta pair has failed its immediate comparisons. -/
def WF (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) : Prop :=
  ∀ {Delta state a b aV bV},
    support a → support b →
    TrKExprS world.venv uvars world.nameOf trProj Delta a aV →
    TrKExprS world.venv uvars world.nameOf trProj Delta b bV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (isDefEqInnerAfterNoDeltaPass a b)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx aV bV)

/-- Close the second cheap normalization pass and transport a later verdict
back across both no-delta reductions. -/
theorem closesAfterCorePass
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    (hcollision : support.CollisionFree)
    (hsorts : SortComponentResources support)
    (hstructural : QuickDefEqResources support)
    (hreduction : DefEqCheapReductionContext layer semantics trProj world
      support uvars)
    (htail : WF layer semantics trProj world support uvars) :
    DefEqAfterCorePass.WF layer semantics trProj world support uvars := by
  intro Delta state a b aV bV haSupport hbSupport ha hb
  unfold isDefEqInnerAfterCorePass
  apply RecM.WF.bind (RecM.WF.withInv <|
    hreduction.noDelta haSupport ha)
  intro wa afterA hwa
  rcases hwa with ⟨hIA, hwaSupport, waV, hwaTr, haWa⟩
  apply RecM.WF.bind (RecM.WF.withInv <|
    hreduction.noDelta hbSupport hb)
  intro wb afterB hwb
  rcases hwb with ⟨hIB, hwbSupport, wbV, hwbTr, hbWb⟩
  cases haddr : wa.addr == wb.addr with
  | true =>
      simp only [if_true]
      exact RecM.WF.pure fun _ _ => by
        have herase :=
          hcollision.expr hwaSupport hwbSupport (eq_of_beq haddr)
        have hsame : wa = wb := by
          simpa only [KExpr.eraseMeta_anon] using herase
        subst wb
        have hmiddle := hwaTr.uniq world.venvWF theory.literalWF
          theory.projections
          (KVLCtx.IsDefEq.refl world.venvWF hIB.2.1.wf) hwbTr
        exact haWa.trans world.venvWF hIB.2.1.wf <|
          hmiddle.trans world.venvWF hIB.2.1.wf hbWb.symm
  | false =>
      simp only [Bool.false_eq_true, if_false]
      apply RecM.WF.bind
        (quickDefEq_wf theory hcollision hsorts hstructural
          hwaSupport hwbSupport hwaTr hwbTr)
      intro accepted afterQuick haccepted
      cases accepted with
      | true =>
          simp only [if_true]
          exact RecM.WF.pure fun hI _ =>
            haWa.trans world.venvWF hI.2.1.wf <|
              (haccepted rfl).trans world.venvWF hI.2.1.wf hbWb.symm
      | false =>
          simp only [Bool.false_eq_true, if_false]
          apply RecM.WF.mono (RecM.WF.withInv <|
            htail hwaSupport hwbSupport hwaTr hwbTr)
          · intro answer final hpost htrue
            exact haWa.trans world.venvWF hpost.1.2.1.wf <|
              (hpost.2 htrue).trans world.venvWF hpost.1.2.1.wf hbWb.symm
          · intro _ _ _
            trivial

/-- Compose both cheap passes behind the post-String seam. -/
theorem closesAfterStringExpansion
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    (hcollision : support.CollisionFree)
    (hsorts : SortComponentResources support)
    (hstructural : QuickDefEqResources support)
    (hreduction : DefEqCheapReductionContext layer semantics trProj world
      support uvars)
    (htail : WF layer semantics trProj world support uvars) :
    DefEqAfterStringExpansion.WF layer semantics trProj world support
      uvars :=
  DefEqAfterCorePass.closesAfterStringExpansion theory hcollision hsorts
    hstructural hreduction
    (closesAfterCorePass theory hcollision hsorts hstructural hreduction
      htail)

end DefEqAfterNoDeltaPass

end RecM

end Ix.Tc
