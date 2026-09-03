import Ix.Tc.Verify.Inductive.BlockCertificate
import Lean4Lean.Verify.Environment.MutualInductiveFixtures

/-!
# Genuine mutual-block certificate fixture

`Tree`/`TreeList` is the first E2c witness that cannot be represented honestly
by a singleton transaction.  It has two mutually visible families, five
globally flattened constructors, one generated recursor per family, and five
globally flattened iota rules.  Recursive fields target both the sibling
family and their own family, including one recursive occurrence below a Pi.

This module consumes Lean4Lean's retained L4L-08 certificate through Ix's
Theory-only block adapter.  Physical Ix ingress, checker execution, catalog
linkage, and recursor admission remain separate obligations.
-/

namespace Ix.Tc.MutualTreeCertificateFixture

open Lean4Lean
open Lean4Lean.MutualInductiveFixtures
open Lean4Lean.MutualInductiveReplayFixtures

/-- One atomic two-family Theory transaction. -/
def transaction :
    CertifiedBlockGenerationTransaction treeDecl VEnv.empty treeFinalEnv where
  certificate := treeGenerationCertificate
  success := tree_addInductBlockCertified
  beforeWF := ⟨[], .empty⟩

/-- The same completed transaction exposed through Lean4Lean's latest
consumer API.  In particular, its derived rule-closure and iota-pattern
theorems are available to the physical recursor link without an Ix axiom. -/
def lean4leanCertificate :
    treeDecl.BlockCertificate VEnv.empty treeFinalEnv :=
  transaction.toBlockCertificate

/-- Exact block inventory and cross-family recursion facts.  These keep the
fixture from degenerating into a singleton or a family-local prefix while the
generic transaction interface remains fully quantified. -/
structure BreadthFacts : Prop where
  oneUniverse : treeDecl.uvars = 1
  oneParameter : treeDecl.nparams = 1
  twoFamilies : treeDecl.types.length = 2
  familyNames : treeGeneration.families.map (·.raw.name) =
    [``Tree, ``TreeList]
  fiveConstructors : treeGeneration.flatCtors.length = 5
  twoMotives : treeGeneration.motiveTypes.length = 2
  fiveMinors : treeGeneration.minorTypes.length = 5
  twoRecursors : treeGeneration.recursors.length = 2
  recursorNames : treeGeneration.recursors.map (·.name) =
    [``Tree.rec, ``TreeList.rec]
  fiveRules : treeGeneration.generatedRules.length = 5
  treeTargetsTreeList :
    treeChecked.families.constructors[0][1].recursive[0].targetType = 1
  functionTargetsTreeList :
    treeChecked.families.constructors[0][2].recursive[0].targetType = 1
  functionBinderRetained :
    treeChecked.families.constructors[0][2].recursive[0].binders.length = 1
  treeListTargetsTree :
    treeChecked.families.constructors[1][1].recursive[0].targetType = 0
  treeListTargetsItself :
    treeChecked.families.constructors[1][1].recursive[1].targetType = 1

theorem breadth : BreadthFacts where
  oneUniverse := rfl
  oneParameter := rfl
  twoFamilies := rfl
  familyNames := rfl
  fiveConstructors := rfl
  twoMotives := rfl
  fiveMinors := rfl
  twoRecursors := rfl
  recursorNames := rfl
  fiveRules := rfl
  treeTargetsTreeList := rfl
  functionTargetsTreeList := rfl
  functionBinderRetained := rfl
  treeListTargetsTree := rfl
  treeListTargetsItself := rfl

/-- Complete block-wide family/constructor/recursor/rule consequences from
the exact retained L4L-08 transaction. -/
theorem certifiedFacts :
    CertifiedBlockGenerationFacts VEnv.empty treeFinalEnv
      transaction.certificate :=
  transaction.facts

/-- The post-environment has a genuine one-entry mutual-inductive Theory
history, rather than two sequential singleton history entries. -/
theorem finalEnvWF : treeFinalEnv.WF :=
  transaction.afterWF

end Ix.Tc.MutualTreeCertificateFixture
