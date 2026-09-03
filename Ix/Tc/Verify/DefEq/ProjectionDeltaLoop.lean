import Ix.Tc.Verify.DefEq.StructuralCongruence

/-!
# Projection-directed lazy-delta loop

The structural projection branch runs a second bounded lazy-delta loop over
the two projected values.  A delta step may prove the values equal, expose a
new pair, or stop and try the projection reducer on both sides before one
final recursive comparison.  This module proves the bounded driver from
exact contracts for those two lower helpers.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

/-- A supported projection node exposes its value to the projection-directed
loop. -/
structure ProjectionValueResources (support : RunSupport) : Prop where
  value : ∀ {id : KId .anon} {field : UInt64} {source : KExpr .anon}
      {info : ExprInfo .anon},
    support (.prj id field source info) → support source

namespace RecM

/-- Semantic interpretation of one `lazyDeltaReductionStep` result. -/
def LazyDeltaReductionStepPost (trProj : RawProjRel) (world : VerifyWorld)
    (support : RunSupport) (uvars : Nat) (Delta : KVLCtx)
    (leftSource rightSource : VExpr)
    (result : LazyDeltaStep × KExpr .anon × KExpr .anon) : Prop :=
  match result.1 with
  | .equal =>
      world.venv.IsDefEqU uvars Delta.toCtx leftSource rightSource
  | .continue' | .unknown =>
      DefEqPairInvariant trProj world support uvars Delta
        leftSource rightSource (result.2.1, result.2.2)

/-- Exact one-step contract for the projection-directed legacy delta
machine.  This lower helper remains executable and branch-specific. -/
def LazyDeltaReductionStep.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state leftSource rightSource left right},
    DefEqPairInvariant trProj world support uvars Delta
      leftSource rightSource (left, right) →
    RecM.WF layer semantics trProj world support uvars Delta state
      (lazyDeltaReductionStep left right)
      (fun result _ => LazyDeltaReductionStepPost trProj world support uvars
        Delta leftSource rightSource result)

/-- Exact semantic contract for a direct projection-reducer attempt.  On a
hit, the returned raw expression is a sound reduction of the supplied Theory
projection.  A miss carries no semantic claim. -/
def TryProjReduce.WFAt (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) : Prop :=
  ∀ {Delta state id field source sourceV structName projectedV},
    support source →
    TrKExprS world.venv uvars world.nameOf trProj Delta source sourceV →
    world.nameOf id.addr = some structName →
    trProj uvars Delta.toCtx structName field.toNat sourceV projectedV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryProjReduce id field source)
      (fun result _ => match result with
        | none => True
        | some reduced => support reduced ∧
            WhnfPost trProj world uvars Delta projectedV reduced)

/-- Lower helper contracts and finite child coverage for the complete
projection-directed loop. -/
structure ProjectionDeltaLoopResources (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop where
  values : ProjectionValueResources support
  step : LazyDeltaReductionStep.WFAt layer semantics trProj world support
    uvars
  projection : TryProjReduce.WFAt layer semantics trProj world support uvars

/-- Complete bounded execution proof for `lazyDeltaProjReduction`. -/
theorem lazyDeltaProjReduction_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {id : KId .anon} {field : UInt64} {left right : KExpr .anon}
    {leftInfo rightInfo : ExprInfo .anon} {leftV rightV : VExpr}
    (theory : WhnfTheory trProj world uvars)
    (resources : ProjectionDeltaLoopResources layer semantics trProj world
      support uvars)
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    (hleftSupport : support (.prj id field left leftInfo))
    (hrightSupport : support (.prj id field right rightInfo))
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.prj id field left leftInfo) leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.prj id field right rightInfo) rightV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (lazyDeltaProjReduction id field left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) := by
  cases hleft with
  | prj hname hleftValue hleftProjection =>
    cases hright with
    | prj hrightName hrightValue hrightProjection =>
      rename_i structName leftValueV rightStructName rightValueV
      have hstructName : structName = rightStructName :=
        Option.some.inj (hname.symm.trans hrightName)
      subst rightStructName
      have hinitial : DefEqPairInvariant trProj world support uvars Delta
          leftValueV rightValueV (left, right) :=
        DefEqPairInvariant.refl theory hDelta
          (resources.values.value hleftSupport)
          (resources.values.value hrightSupport) hleftValue hrightValue
      unfold lazyDeltaProjReduction
      apply runBounded_wf
        (P := fun pair => DefEqPairInvariant trProj world support uvars Delta
          leftValueV rightValueV pair)
        (Q := fun answer _ => answer = true →
          world.venv.IsDefEqU uvars Delta.toCtx leftV rightV)
      · intro pair current hpair
        rcases pair with ⟨currentLeft, currentRight⟩
        apply RecM.WF.bind (resources.step hpair)
        intro stepResult afterStep hstep
        rcases stepResult with ⟨outcome, nextLeft, nextRight⟩
        cases outcome with
        | equal =>
            exact RecM.WF.pure fun _ _ =>
              theory.projections.uniq
                (KVLCtx.IsDefEq.refl world.venvWF.ordered hDelta).defeqCtx
                hleftProjection hrightProjection hstep
        | continue' =>
            exact RecM.WF.pure fun _ => hstep
        | unknown =>
            obtain ⟨nextLeftV, hnextLeft, hleftNext⟩ := hstep.left
            obtain ⟨nextRightV, hnextRight, hrightNext⟩ := hstep.right
            have hctx :=
              (KVLCtx.IsDefEq.refl world.venvWF.ordered hDelta).defeqCtx
            obtain ⟨nextLeftProjectionV, hnextLeftProjection⟩ :=
              theory.projections.defeqDFC hctx hleftNext hleftProjection
            obtain ⟨nextRightProjectionV, hnextRightProjection⟩ :=
              theory.projections.defeqDFC hctx hrightNext hrightProjection
            have hleftProjectionEq := theory.projections.uniq hctx
              hleftProjection hnextLeftProjection hleftNext
            have hrightProjectionEq := theory.projections.uniq hctx
              hrightProjection hnextRightProjection hrightNext
            apply RecM.WF.bind (RecM.WF.withInv <|
              resources.projection hstep.leftSupport hnextLeft hname
                hnextLeftProjection)
            intro leftReduced afterLeftReduced hleftReduced
            rcases hleftReduced with ⟨hILeftReduced, hleftReduced⟩
            apply RecM.WF.bind (RecM.WF.withInv <|
              resources.projection hstep.rightSupport hnextRight hname
                hnextRightProjection)
            intro rightReduced afterRightReduced hrightReduced
            rcases hrightReduced with ⟨hIRightReduced, hrightReduced⟩
            cases leftReduced with
            | none =>
                apply RecM.WF.bind (RecM.WF.withInv <|
                  RecM.isDefEqCall_wf hstep.leftSupport hstep.rightSupport
                    hnextLeft hnextRight)
                intro answer final hanswer
                rcases hanswer with ⟨hI, hanswer⟩
                exact RecM.WF.pure fun _ htrue =>
                  theory.projections.uniq
                    (KVLCtx.IsDefEq.refl world.venvWF.ordered
                      hI.2.1.wf).defeqCtx
                    hleftProjection hrightProjection <|
                    hleftNext.trans world.venvWF hI.2.1.wf <|
                      (hanswer htrue).trans world.venvWF hI.2.1.wf
                        hrightNext.symm
            | some reducedLeft =>
                cases rightReduced with
                | none =>
                    apply RecM.WF.bind (RecM.WF.withInv <|
                      RecM.isDefEqCall_wf hstep.leftSupport
                        hstep.rightSupport hnextLeft hnextRight)
                    intro answer final hanswer
                    rcases hanswer with ⟨hI, hanswer⟩
                    exact RecM.WF.pure fun _ htrue =>
                      theory.projections.uniq
                        (KVLCtx.IsDefEq.refl world.venvWF.ordered
                          hI.2.1.wf).defeqCtx
                        hleftProjection hrightProjection <|
                        hleftNext.trans world.venvWF hI.2.1.wf <|
                          (hanswer htrue).trans world.venvWF hI.2.1.wf
                            hrightNext.symm
                | some reducedRight =>
                    rcases hleftReduced with
                      ⟨hleftReducedSupport, reducedLeftV, hleftReducedTr,
                        hleftReducedEq⟩
                    rcases hrightReduced with
                      ⟨hrightReducedSupport, reducedRightV, hrightReducedTr,
                        hrightReducedEq⟩
                    apply RecM.WF.bind (RecM.WF.withInv <|
                      RecM.isDefEqCall_wf hleftReducedSupport
                        hrightReducedSupport hleftReducedTr hrightReducedTr)
                    intro answer final hanswer
                    rcases hanswer with ⟨hI, hanswer⟩
                    exact RecM.WF.pure fun _ htrue =>
                      hleftProjectionEq.trans world.venvWF hI.2.1.wf <|
                        hleftReducedEq.trans world.venvWF hI.2.1.wf <|
                          (hanswer htrue).trans world.venvWF hI.2.1.wf <|
                            hrightReducedEq.symm.trans world.venvWF
                              hI.2.1.wf hrightProjectionEq.symm
      · intro _ _
        trivial
      · exact hinitial

namespace LazyDeltaProjReduction

/-- Construct the exact structural-congruence projection contract from the
bounded loop's lower helper contracts. -/
theorem ofResources
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    (resources : ProjectionDeltaLoopResources layer semantics trProj world
      support uvars) :
    LazyDeltaProjReduction.WFAt layer semantics trProj world support
      uvars := by
  intro Delta state id field left right leftInfo rightInfo leftV rightV
    hleftSupport hrightSupport hleft hright
  intro methods hmethods hI
  exact (lazyDeltaProjReduction_wf theory resources hI.2.1.wf
    hleftSupport hrightSupport hleft hright) methods hmethods hI

end LazyDeltaProjReduction

end RecM

end Ix.Tc
