import Ix.Tc.Verify.DefEq.FinalWhnf.NatBridge
import Ix.Tc.Verify.DefEq.FinalWhnf.EtaExpansion
import Ix.Tc.Verify.DefEq.FinalWhnf.StringExpansion
import Ix.Tc.Verify.DefEq.FinalWhnf.StructuralPrefix
import Ix.Tc.Verify.DefEq.FinalWhnf.StructureEta
import Ix.Tc.Verify.DefEq.FinalWhnf.UnitLike
import Ix.Tc.Verify.DefEq.PropositionClassifier

/-!
# Complete final-WHNF comparison

The final comparator consists of an exhaustive structural prefix followed by
the ordered Nat, lambda-eta, String, structure-eta, unit-like, and proof-
irrelevance fallbacks.  This module assembles those independently verified
phases under one canonical K2 suffix model.
-/

namespace Ix.Tc
namespace RecM

/-- Concrete resources for every production phase of `isDefEqWhnf`.  The
proposition-classifier context fixes the canonical K2 suffix model used by
all cache-aware fields. -/
structure FinalWhnfClosureResources
    {trProj : RawProjRel} {world : VerifyWorld} (support : RunSupport)
    (proposition : PropositionClassifierContext trProj world support)
    (eligible : KId .anon → Prop) where
  structural : FinalWhnfStructuralResources .noAccel
    (kernelCacheSemantics proposition.model.keys trProj) trProj world support
    proposition.model.keys.uvars
  nat : FinalWhnfNatResources world support
  lambdaEta : FinalWhnfEtaResources support
  directWhnf : DefEqDirectWhnf.WFAt .noAccel
    (kernelCacheSemantics proposition.model.keys trProj) trProj world support
    proposition.model.keys.uvars
  string : DefEqStringContext trProj world support
  canonical : CanonicalPrimitiveStates .noAccel
    (kernelCacheSemantics proposition.model.keys trProj) trProj world support
    proposition.model.keys.uvars
  structureEta : FinalWhnfStructEtaResources .noAccel
    (kernelCacheSemantics proposition.model.keys trProj) trProj world support
    proposition.model.keys.uvars eligible
  unit : FinalWhnfUnitResources .noAccel
    (kernelCacheSemantics proposition.model.keys trProj) trProj world support
    proposition.model.keys.uvars

namespace FinalWhnfClosureResources

/-- Assemble the complete post-structure fallback in its exact production
order. -/
theorem afterStructural
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {proposition : PropositionClassifierContext trProj world support}
    {eligible : KId .anon → Prop}
    (resources : FinalWhnfClosureResources support proposition eligible) :
    IsDefEqWhnfAfterStructural.WFAt .noAccel
      (kernelCacheSemantics proposition.model.keys trProj) trProj world
      support proposition.model.keys.uvars := by
  have hafterStructEta : IsDefEqWhnfAfterStructEta.WFAt .noAccel
      (kernelCacheSemantics proposition.model.keys trProj) trProj world
      support proposition.model.keys.uvars :=
    IsDefEqWhnfAfterStructEta.ofUnitAndProof
      (TryDefEqUnit.ofResources resources.unit)
      (isPropType_wf proposition)
  have hafterString : IsDefEqWhnfAfterString.WFAt .noAccel
      (kernelCacheSemantics proposition.model.keys trProj) trProj world
      support proposition.model.keys.uvars :=
    IsDefEqWhnfAfterString.ofStructEta
      (TryDefEqWhnfStructEta.ofResources resources.structureEta)
      hafterStructEta
  have hafterEta : IsDefEqWhnfAfterEta.WFAt .noAccel
      (kernelCacheSemantics proposition.model.keys trProj) trProj world
      support proposition.model.keys.uvars :=
    IsDefEqWhnfAfterEta.ofString
      (TryDefEqWhnfString.ofContext resources.string resources.canonical)
      hafterString
  have hafterNat : IsDefEqWhnfAfterNat.WFAt .noAccel
      (kernelCacheSemantics proposition.model.keys trProj) trProj world
      support proposition.model.keys.uvars :=
    IsDefEqWhnfAfterNat.ofEta resources.structural.theory
      resources.lambdaEta resources.structural.collision resources.directWhnf
      hafterEta
  intro Delta state left right leftV rightV hleftSupport hrightSupport hleft
    hright
  exact isDefEqWhnfAfterStructural_wf
    (TryDefEqWhnfNat.ofResources resources.structural.theory resources.nat)
    hafterNat hleftSupport hrightSupport hleft hright

/-- Close the complete concrete final-WHNF comparator. -/
theorem finalWhnf
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {proposition : PropositionClassifierContext trProj world support}
    {eligible : KId .anon → Prop}
    (resources : FinalWhnfClosureResources support proposition eligible) :
    IsDefEqWhnf.WFAt .noAccel
      (kernelCacheSemantics proposition.model.keys trProj) trProj world
      support proposition.model.keys.uvars :=
  IsDefEqWhnf.ofPhases
    (TryDefEqWhnfStructural.ofResources resources.structural)
    resources.afterStructural

end FinalWhnfClosureResources

end RecM
end Ix.Tc
