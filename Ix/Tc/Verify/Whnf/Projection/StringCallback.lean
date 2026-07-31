import Ix.Tc.Verify.Whnf.Projection.NoAccelTail

/-!
# Projection String callback closure

NoAccelTail proves every projection-helper operation after preprocessing.  This
slice discharges the recursive callback inside String preprocessing from the
predecessor method table.  The remaining String premise now owns only the
interned constructor expansion itself: finite support and structural
translation of the exact generated term.
-/

namespace Ix.Tc
namespace RecM

attribute [local irreducible] whnfRec strLitToConstructor

namespace ProjectionStringExpansion

/-- Exact state/support/translation contract for production's generated
String constructor term, before the recursive WHNF callback. -/
structure WF (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) : Prop where
  run : ∀ {uvars Delta s value blob info},
    support (.str value blob info) →
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (strLitToConstructor value)
      (fun expanded _ =>
        support expanded ∧
          ∃ expandedV,
            TrKExprS world.venv uvars world.nameOf trProj Delta expanded
              expandedV)

end ProjectionStringExpansion

namespace ProjectionStringPrelude

/-- String expansion followed by the actual recursive full-WHNF callback
satisfies NoAccelTail's complete preprocessing contract. -/
theorem ofExpansion
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (hexpansion : ProjectionStringExpansion.WF semantics trProj world
      support) :
    ProjectionStringPrelude.WF semantics trProj world support where
  run := by
    intro uvars Delta s value blob info hvalue
    rw [tryProjPrepare_eq]
    apply RecM.WF.bind
      (Q₁ := fun expanded _ =>
        support expanded ∧
          ∃ expandedV,
            TrKExprS world.venv uvars world.nameOf trProj Delta expanded
              expandedV)
      (hexpansion.run hvalue)
    intro expanded after hExpanded
    obtain ⟨hSupport, expandedV, hTr⟩ := hExpanded
    exact RecM.WF.mono
      (whnfRec_wf (s := after) hSupport hTr)
      (fun _ _ hPost => hPost.1)
      (fun _ _ _ => trivial)

end ProjectionStringPrelude

namespace ProjectionHelper

/-- Concrete `.noAccel` projection helper with only the exact String
constructor expansion and lazy-ingress refinements left as premises. -/
theorem noAccelOfExpansion
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (hinputs : WhnfCoreInputSupport support)
    (hfault : ∀ uvars Delta,
      TcM.LazyFaultPreserves
        (WhnfStateInv .noAccel semantics trProj world support uvars Delta))
    (hexpansion : ProjectionStringExpansion.WF semantics trProj world
      support) :
    ProjectionHelper.WF .noAccel semantics trProj world support :=
  ProjectionHelper.noAccel hinputs hfault
    (ProjectionStringPrelude.ofExpansion hexpansion)

end ProjectionHelper

end RecM
end Ix.Tc
