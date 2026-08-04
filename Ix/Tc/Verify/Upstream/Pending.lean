import Ix.Tc.Verify.Inductive.BlockPatternSoundness
import Lean4Lean.Verify.Environment.MutualInductiveFixtures

/-!
# Quarantined pending-upstream witnesses

Nothing in this module may state an Ix ingress, address, ownership, checker,
cache, collision, or workset fact.  Conditional consumers import it directly;
unconditional completed roots must not depend on it.
-/

namespace Ix.Tc.Upstream.Pending

open Lean4Lean
open Lean4Lean.MutualInductiveFixtures

/-! ## Physical mutual-family permutation

Ix's canonical mutual SCC order for this fixture is `TreeList, Tree`, while
the retained Lean declaration order is `Tree, TreeList`.  Lean4Lean can
compute the exact reversed generation descriptor today; the missing upstream
piece is a theorem transporting block-generation WF across that family
permutation. -/

def mutualTreePhysicalDecl : VInductDecl :=
  ⟨1, 1, [treeListType, treeType]⟩

def mutualTreePhysicalGeneration :
    mutualTreePhysicalDecl.BlockGenerationChecked :=
  mutualTreePhysicalDecl.identityBlockGeneration?.get (by decide)

def mutualTreePhysicalBlockEnv : VEnv :=
  (VEnv.empty.stageInductiveTypes mutualTreePhysicalDecl.types).get
    (by decide)

/-- Fixture-specific stand-in for the future Lean4Lean permutation theorem
`VInductDecl.BlockGenerationChecked.permuteFamiliesWF`.

This is a Theory-only statement: it certifies the computed `TreeList, Tree`
generation descriptor and says nothing about Ix addresses, compilation,
ingress, checker execution, or ownership. -/
axiom mutualTreePhysicalGenerationWF :
  mutualTreePhysicalGeneration.WF VEnv.empty mutualTreePhysicalBlockEnv

def mutualTreePhysicalSemantic :
    mutualTreePhysicalDecl.BlockGenerationCertificate VEnv.empty where
  generation := mutualTreePhysicalGeneration
  blockEnv := mutualTreePhysicalBlockEnv
  wf := mutualTreePhysicalGenerationWF

def mutualTreePhysicalFinalEnv : VEnv :=
  (VEnv.empty.addInductBlockCertified mutualTreePhysicalSemantic).get
    (by decide)

theorem mutualTreePhysicalSuccess :
    VEnv.empty.addInductBlockCertified mutualTreePhysicalSemantic =
      some mutualTreePhysicalFinalEnv := rfl

def mutualTreePhysicalCertificate :
    mutualTreePhysicalDecl.BlockCertificate VEnv.empty
      mutualTreePhysicalFinalEnv where
  semantic := mutualTreePhysicalSemantic
  success := mutualTreePhysicalSuccess
  beforeWF := ⟨[], .empty⟩

/-- Fixture-specific stand-in for the future Lean4Lean consumer theorem
`VInductDecl.BlockCertificate.recursorPatternSound` (the constructive wrapper
around `BlockGenerationChecked.pat_wf`).

The current pin exposes the exact pattern payload and its registered rule but
does not yet publish this environment-parametric consumer conclusion without
the upstream metatheory gap.  Delete this declaration, and replace its sole
use with that theorem, when the upstream result lands. -/
axiom mutualTreePhysicalRulePatternSound :
  CertifiedBlockRulePatternSound mutualTreePhysicalCertificate

end Ix.Tc.Upstream.Pending
