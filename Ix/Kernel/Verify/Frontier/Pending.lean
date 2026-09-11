import Ix.Kernel.Verify.Inductive.BlockPatternSoundness
import Ix.Theory.Named.Verify.Environment.MutualInductiveFixtures

/-!
# Quarantined pending metatheory witnesses

Nothing in this module may state an Ix ingress, address, ownership, checker,
cache, collision, or workset fact.  Conditional consumers import it directly;
unconditional completed roots must not depend on it.
-/

namespace Ix.Kernel.Frontier.Pending

open Ix.Theory.Named
open Ix.Theory.Named.MutualInductiveFixtures

/-! ## Physical mutual-family permutation

Ix's canonical mutual SCC order for this fixture is `TreeList, Tree`, while
the retained Lean declaration order is `Tree, TreeList`. The named specification
computes the exact reversed generation descriptor; the missing local
proof transports block-generation WF across that family
permutation. -/

def mutualTreePhysicalDecl : VInductDecl :=
  ⟨1, 1, [treeListType, treeType]⟩

def mutualTreePhysicalGeneration :
    mutualTreePhysicalDecl.BlockGenerationChecked :=
  mutualTreePhysicalDecl.identityBlockGeneration?.get (by decide)

def mutualTreePhysicalBlockEnv : VEnv :=
  (VEnv.empty.stageInductiveTypes mutualTreePhysicalDecl.types).get
    (by decide)

/-- Fixture-specific stand-in for the missing named-specification permutation theorem
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

/-- Fixture-specific stand-in for the missing named-specification consumer theorem
`VInductDecl.BlockCertificate.recursorPatternSound` (the constructive wrapper
around `BlockGenerationChecked.pat_wf`).

The local specification exposes the exact pattern payload and its registered
rule. This conclusion still requires a metatheory proof. Completing that proof
must replace this axiom and its sole conditional use. -/
axiom mutualTreePhysicalRulePatternSound :
  CertifiedBlockRulePatternSound mutualTreePhysicalCertificate

end Ix.Kernel.Frontier.Pending
