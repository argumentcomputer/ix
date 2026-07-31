import Ix.Tc.Verify.Whnf.Beta.Translation

/-!
# Constructive multi-beta meaning

The preceding slices recover the translated lambda telescope, its dependent
context-instantiation chain, the exact Theory argument values, and a one-pass
translation theorem for production's simultaneous-substitution walker.  This
file assembles those pieces into `BetaPrefixMeaning`, eliminating the last
semantic oracle specific to general multi-beta.
-/

namespace Ix.Tc

open Lean4Lean

namespace RecM

/-- Production's consumed beta prefix has the exact structural translation
and Theory meaning required by `BetaPrefixMeaning`. -/
theorem betaPrefixMeaning (trProj : RawProjRel) (world : VerifyWorld) :
    BetaPrefixMeaning trProj world := by
  intro uvars theory Delta start body consumed startV consumedV hDelta
    hstart hpeel hsuffix hbounds
  obtain ⟨argValues, hvalues⟩ := TrAppSuffix.Values.ofSuffix hsuffix
  obtain ⟨bodyDelta, bodyV, htrace⟩ := hpeel.translate hstart
  have hinsts := htrace.contextInsts theory hDelta hvalues
  have harguments :
      SimulArgs world.venv uvars world.nameOf trProj Delta
        consumed.reverse argValues := by
    simpa using SimulArgs.ofValues hvalues
  have hresult := TrKExprS.simulSubstBeta
    world.venvWF.ordered theory.projections.weakN theory.projections.instN
    harguments htrace.result hinsts KVLCtx.KBVLift.refl hbounds rfl
  have hmeaning := htrace.theoryMeaning theory hDelta hvalues
  exact ⟨VExpr.instBetaArgs bodyV argValues 0, hresult, hmeaning⟩

/-- The old complete application-branch interface is now a theorem rather
than an independent semantic assumption. -/
theorem betaManyMeaning (trProj : RawProjRel) (world : VerifyWorld) :
    BetaManyMeaningOracle trProj world :=
  BetaManyMeaningOracle.of_prefix (betaPrefixMeaning trProj world)

end RecM
end Ix.Tc
