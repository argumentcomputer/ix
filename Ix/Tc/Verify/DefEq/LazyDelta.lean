import Ix.Tc.Verify.DefEq.ProofIrrelevance

/-!
# Bounded lazy-delta DefEq closure

The production lazy-delta tier is a bounded state machine over expression
pairs.  This module fixes its semantic loop invariant and proves the bounded
driver and its post-loop continuation correct from exact contracts for one
step and the stopped tail.  Individual reduction branches discharge those
contracts in subsequent modules.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace RecM

/-- A current lazy-delta pair remains supported and each component is a
sound reduction of the corresponding original operand. -/
structure DefEqPairInvariant (trProj : RawProjRel) (world : VerifyWorld)
    (support : RunSupport) (uvars : Nat) (Delta : KVLCtx)
    (leftSource rightSource : VExpr)
    (pair : KExpr .anon × KExpr .anon) : Prop where
  leftSupport : support pair.1
  rightSupport : support pair.2
  left : WhnfPost trProj world uvars Delta leftSource pair.1
  right : WhnfPost trProj world uvars Delta rightSource pair.2

namespace DefEqPairInvariant

/-- The input pair establishes the lazy-delta invariant reflexively. -/
theorem refl {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {uvars : Nat} {Delta : KVLCtx}
    {left right : KExpr .anon} {leftV rightV : VExpr}
    (theory : WhnfTheory trProj world uvars)
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    (hleftSupport : support left) (hrightSupport : support right)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right rightV) :
    DefEqPairInvariant trProj world support uvars Delta leftV rightV
      (left, right) := by
  refine ⟨hleftSupport, hrightSupport, ?_, ?_⟩
  · exact WhnfPost.refl hleft <|
      hleft.wf world.venvWF.ordered theory.literalWF theory.projections.wf
        hDelta
  · exact WhnfPost.refl hright <|
      hright.wf world.venvWF.ordered theory.literalWF theory.projections.wf
        hDelta

/-- Transport a successful comparison of the current pair back across both
components of the loop invariant. -/
theorem conclude {trProj : RawProjRel} {world : VerifyWorld}
    {support : RunSupport} {uvars : Nat} {Delta : KVLCtx}
    {leftSource rightSource : VExpr}
    {pair : KExpr .anon × KExpr .anon}
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    (hpair : DefEqPairInvariant trProj world support uvars Delta
      leftSource rightSource pair)
    (hcurrent : ∀ {leftV rightV},
      TrKExprS world.venv uvars world.nameOf trProj Delta pair.1 leftV →
      TrKExprS world.venv uvars world.nameOf trProj Delta pair.2 rightV →
      world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) :
    world.venv.IsDefEqU uvars Delta.toCtx leftSource rightSource := by
  obtain ⟨leftV, hleft, hleftEq⟩ := hpair.left
  obtain ⟨rightV, hright, hrightEq⟩ := hpair.right
  exact hleftEq.trans world.venvWF hDelta <|
    (hcurrent hleft hright).trans world.venvWF hDelta hrightEq.symm

end DefEqPairInvariant

/-- Semantic interpretation of one lazy-delta step action. -/
def DefEqLazyDeltaActionPost (trProj : RawProjRel) (world : VerifyWorld)
    (support : RunSupport) (uvars : Nat) (Delta : KVLCtx)
    (leftSource rightSource : VExpr) :
    BoundedStep (KExpr .anon × KExpr .anon)
      (LazyDeltaLoopResult .anon) → Prop
  | .next pair =>
      DefEqPairInvariant trProj world support uvars Delta
        leftSource rightSource pair
  | .done (.answer result) =>
      result = true →
        world.venv.IsDefEqU uvars Delta.toCtx leftSource rightSource
  | .done (.stopped left right) =>
      DefEqPairInvariant trProj world support uvars Delta
        leftSource rightSource (left, right)

/-- Exact semantic contract for one production lazy-delta iteration. -/
def DefEqLazyDeltaStep.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state leftSource rightSource pair},
    DefEqPairInvariant trProj world support uvars Delta
      leftSource rightSource pair →
    RecM.WF layer semantics trProj world support uvars Delta state
      (defEqLazyDeltaStep pair)
      (fun action _ => DefEqLazyDeltaActionPost trProj world support uvars
        Delta leftSource rightSource action)

/-- A Nat-offset hit may be negative, but every positive hit proves equality
of the exact current operands.  A miss carries no completeness claim. -/
def TryDefEqOffset.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state left right leftV rightV},
    support left → support right →
    TrKExprS world.venv uvars world.nameOf trProj Delta left leftV →
    TrKExprS world.venv uvars world.nameOf trProj Delta right rightV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryDefEqOffset left right)
      (fun result _ => match result with
        | none => True
        | some answer => answer = true →
            world.venv.IsDefEqU uvars Delta.toCtx leftV rightV)

/-- Exact remaining one-step contract once Nat-offset comparison misses. -/
def DefEqLazyDeltaAfterOffsetMiss.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state leftSource rightSource pair},
    DefEqPairInvariant trProj world support uvars Delta
      leftSource rightSource pair →
    RecM.WF layer semantics trProj world support uvars Delta state
      (defEqLazyDeltaStepAfterOffsetMiss pair)
      (fun action _ => DefEqLazyDeltaActionPost trProj world support uvars
        Delta leftSource rightSource action)

/-- Close the production step's Nat-offset prefix.  This theorem does not
assume shared-offset injectivity itself: that obligation is exactly the
`TryDefEqOffset.WFAt` premise. -/
theorem defEqLazyDeltaStep_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {leftSource rightSource : VExpr}
    {pair : KExpr .anon × KExpr .anon}
    (hoffset : TryDefEqOffset.WFAt layer semantics trProj world support
      uvars)
    (hafter : DefEqLazyDeltaAfterOffsetMiss.WFAt layer semantics trProj
      world support uvars)
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    (hpair : DefEqPairInvariant trProj world support uvars Delta
      leftSource rightSource pair) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (defEqLazyDeltaStep pair)
      (fun action _ => DefEqLazyDeltaActionPost trProj world support uvars
        Delta leftSource rightSource action) := by
  obtain ⟨leftV, hleft, hleftEq⟩ := hpair.left
  obtain ⟨rightV, hright, hrightEq⟩ := hpair.right
  unfold defEqLazyDeltaStep
  apply RecM.WF.bind <|
    hoffset hpair.leftSupport hpair.rightSupport hleft hright
  intro result after hresult
  cases result with
  | none =>
      exact hafter hpair
  | some answer =>
      exact RecM.WF.pure fun _ htrue =>
        hleftEq.trans world.venvWF hDelta <|
          (hresult htrue).trans world.venvWF hDelta hrightEq.symm

namespace DefEqLazyDeltaStep

/-- Package the offset prefix theorem as the complete one-step contract. -/
theorem ofOffset
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (hoffset : TryDefEqOffset.WFAt layer semantics trProj world support
      uvars)
    (hafter : DefEqLazyDeltaAfterOffsetMiss.WFAt layer semantics trProj
      world support uvars) :
    DefEqLazyDeltaStep.WFAt layer semantics trProj world support uvars := by
  intro Delta state leftSource rightSource pair hpair
  intro methods hmethods hI
  exact (defEqLazyDeltaStep_wf hoffset hafter hI.2.1.wf hpair)
    methods hmethods hI

end DefEqLazyDeltaStep

/-- The bounded driver preserves the pair invariant until it either returns
a sound answer or exposes a stopped pair carrying the same invariant. -/
theorem runDefEqLazyDelta_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {left right : KExpr .anon} {leftV rightV : VExpr}
    (theory : WhnfTheory trProj world uvars)
    (hstep : DefEqLazyDeltaStep.WFAt layer semantics trProj world support
      uvars)
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    (hleftSupport : support left) (hrightSupport : support right)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right rightV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (runDefEqLazyDelta left right)
      (fun result _ => DefEqLazyDeltaActionPost trProj world support uvars
        Delta leftV rightV (.done result)) := by
  unfold runDefEqLazyDelta
  apply runBounded_wf
    (P := fun pair => DefEqPairInvariant trProj world support uvars Delta
      leftV rightV pair)
    (Q := fun result _ => DefEqLazyDeltaActionPost trProj world support
      uvars Delta leftV rightV (.done result))
  · intro pair current hpair
    apply RecM.WF.mono (hstep (state := current) hpair)
    · intro action _ haction
      cases action <;> exact haction
    · intro _ _ _
      trivial
  · intro _ _
    trivial
  · exact DefEqPairInvariant.refl theory hDelta hleftSupport hrightSupport
      hleft hright

/-- Semantic contract for the tiers entered from a stopped lazy-delta pair. -/
def DefEqAfterLazyDeltaStopped.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state leftSource rightSource left right},
    DefEqPairInvariant trProj world support uvars Delta
      leftSource rightSource (left, right) →
    RecM.WF layer semantics trProj world support uvars Delta state
      (isDefEqAfterLazyDeltaStopped left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx leftSource rightSource)

/-- The two exact contracts needed to close the production lazy-delta tier. -/
structure DefEqLazyDeltaContext (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop where
  step : DefEqLazyDeltaStep.WFAt layer semantics trProj world support uvars
  stopped : DefEqAfterLazyDeltaStopped.WFAt layer semantics trProj world
    support uvars

/-- Compose the bounded driver with its post-loop continuation. -/
theorem isDefEqInnerAfterProofIrrelevance_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {left right : KExpr .anon} {leftV rightV : VExpr}
    (theory : WhnfTheory trProj world uvars)
    (context : DefEqLazyDeltaContext layer semantics trProj world support
      uvars)
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    (hleftSupport : support left) (hrightSupport : support right)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right rightV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (isDefEqInnerAfterProofIrrelevance left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) := by
  unfold isDefEqInnerAfterProofIrrelevance
  apply RecM.WF.bind <|
    runDefEqLazyDelta_wf theory context.step hDelta hleftSupport
      hrightSupport hleft hright
  intro result after hresult
  cases result with
  | answer answer =>
      exact RecM.WF.pure fun _ htrue => hresult htrue
  | stopped currentLeft currentRight =>
      exact context.stopped hresult

/-- A verified lazy-delta context discharges the abstract tail contract used
by the already-verified pre-delta proof-irrelevance tier. -/
theorem DefEqAfterProofIrrelevance.ofLazyDelta
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    (context : DefEqLazyDeltaContext layer semantics trProj world support
      uvars) :
    DefEqAfterProofIrrelevance.WF layer semantics trProj world support
      uvars := by
  intro Delta state left right leftV rightV hleftSupport hrightSupport
    hleft hright
  intro methods hmethods hI
  exact (isDefEqInnerAfterProofIrrelevance_wf theory context
    hI.2.1.wf hleftSupport hrightSupport hleft hright) methods hmethods hI

end RecM

end Ix.Tc
