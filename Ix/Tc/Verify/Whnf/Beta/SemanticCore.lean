import Ix.Tc.Verify.Whnf.Beta.ConsumptionBoundary

/-!
# Isolate the semantic core of general multi-beta

The original `BetaManyMeaningOracle` bundled four independent concerns:
changed-head congruence, splitting the consumed application prefix, semantic
multi-beta, and rebuilding the unconsumed suffix.  ConsumptionBoundary proves the exact typed
split.  This slice discharges every concern except the actual simultaneous
substitution theorem, leaving `BetaPrefixMeaning` as the minimal semantic
statement that must be proved structurally.
-/

namespace Ix.Tc
namespace RecM

/-- Semantic core of production multi-beta.  Starting from a translated
lambda chain and exactly the arguments peeled by `consumeBetaLams`, the direct
simultaneous-substitution result translates and is definitionally equal to
the fully applied prefix. -/
def BetaPrefixMeaning (trProj : RawProjRel) (world : VerifyWorld) : Prop :=
  forall {uvars : Nat}, WhnfTheory trProj world uvars ->
    forall {Delta : KVLCtx} {start body : KExpr .anon}
      {consumed : Array (KExpr .anon)}
      {startV consumedV : Lean4Lean.VExpr},
    KVLCtx.WF world.venv uvars Delta ->
    TrKExprS world.venv uvars world.nameOf trProj Delta start startV ->
    BetaPeel start consumed.toList body ->
    TrAppSuffix world.venv uvars world.nameOf trProj Delta startV
      consumed.toList consumedV ->
    (WalkerRequest.simulSubst body consumed.reverse 0).Bounds ->
    exists resultV,
      TrKExprS world.venv uvars world.nameOf trProj Delta
          (KExpr.simulSubstSpec body consumed.reverse 0) resultV /\
        world.venv.IsDefEqU uvars Delta.toCtx consumedV resultV

namespace BetaManyMeaningOracle

/-- The minimal consumed-prefix theorem implies the original complete
multi-beta branch contract.  Changed-head equality is transported through
the consumed prefix, the beta result is transported through the untouched
suffix, and `FinishAppRequests` identifies the exact rebuilt concrete term. -/
theorem of_prefix {trProj : RawProjRel} {world : VerifyWorld}
    (hprefix : BetaPrefixMeaning trProj world) :
    BetaManyMeaningOracle trProj world := by
  intro uvars theory Delta requests f arg info args name bi ty body body0
    lamInfo consumed result sourceV headV hDelta hsource hsuffix hheadPost
    hconsume hbounds hfinish
  obtain ⟨lambdaV, hlambdaTr, hheadEq⟩ := hheadPost
  obtain ⟨middleV, hpeel, hconsumed, hremaining⟩ :=
    hsuffix.splitConsume hconsume
  obtain ⟨appliedV, happliedSuffix, hmiddleApplied⟩ :=
    hconsumed.rebaseStart world.venvWF hDelta hheadEq
  obtain ⟨reducedV, hreducedTr, happliedReduced⟩ :=
    hprefix theory hDelta hlambdaTr hpeel happliedSuffix hbounds
  have hmiddleReduced :
      world.venv.IsDefEqU uvars Delta.toCtx middleV reducedV :=
    hmiddleApplied.trans world.venvWF hDelta.toCtx happliedReduced
  obtain ⟨finalV, hfinalTr, hsourceFinal⟩ :=
    hremaining.rebase world.venvWF hDelta hreducedTr hmiddleReduced
  rw [hfinish.result_eq_foldl]
  exact ⟨sourceV, finalV, hsource, hfinalTr, hsourceFinal⟩

end BetaManyMeaningOracle
end RecM
end Ix.Tc
