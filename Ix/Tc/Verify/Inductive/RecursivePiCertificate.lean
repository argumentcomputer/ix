import Ix.Tc.Verify.Inductive.Certificate
import Lean4Lean.Theory.InductiveFixtures

/-!
# Certified recursive-Pi generation fixture

`Acc.intro` contains a recursive occurrence beneath a two-binder function
telescope. This is the next one-family E2c breadth case after `IndexedVec`:
the recursive argument is not a direct family application, and its induction
hypothesis is itself a function.

This module stays on the Theory-only side of the boundary. It constructs the
public proof-carrying Lean4Lean transaction directly from `accDecl_wf`; it
does not import the reflected Lean-environment replay or assert any Ix catalog
correspondence. Production ingress, constructor traversal, and generated
recursor comparison remain separate obligations.
-/

namespace Ix.Tc.RecursivePiCertificateFixture

open Lean4Lean
open Lean4Lean.InductiveFixtures

/-- The public Lean4Lean certificate for the actual `Acc` declaration. -/
def certificate : accDecl.GenerationCertificate VEnv.empty where
  generation := accChecked.identityGeneration
  wf := (accChecked.wf_of_decl accDecl_wf).identityGeneration .empty

/-- The exact Theory environment produced by the certificate. -/
def finalEnv : VEnv :=
  (VEnv.empty.addInductCertified certificate).get (by decide)

theorem success :
    VEnv.empty.addInductCertified certificate = some finalEnv := rfl

/-- The complete proof-carrying transaction for recursive-Pi generation. -/
def transaction : CertifiedGenerationTransaction accDecl VEnv.empty finalEnv where
  certificate := certificate
  success := success
  beforeWF := ⟨[], .empty⟩

/-- The transaction uses the analyzer-selected identity generation rather
than a separately chosen artifact. -/
@[simp] theorem transaction_generation :
    transaction.certificate.generation =
      accChecked.identityGeneration := rfl

/-- Exact computed facts which distinguish `Acc` from direct recursive
families such as `IndexedVec`.

The only recursive field is constructor field one. Its target family remains
the sole source family, but the occurrence is reached only after opening two
binders. The generated rule therefore exercises the recursive-Pi artifact
path rather than direct application recursion. -/
structure BreadthFacts : Prop where
  oneUniverse : accDecl.uvars = 1
  twoParameters : accDecl.nparams = 2
  singletonFamily : accDecl.types.length = 1
  oneIndex :
    transaction.certificate.generation.block.checked.indices.length = 1
  largeElimination :
    transaction.certificate.generation.block.checked.elimination = .large
  oneConstructor :
    transaction.certificate.generation.block.checked.constructors.length = 1
  twoConstructorFields :
    transaction.certificate.generation.block.checked.constructors[0].fields.length = 2
  oneRecursiveArgument :
    transaction.certificate.generation.block.checked.constructors[0].recursive.length = 1
  recursiveFieldIndex :
    transaction.certificate.generation.block.checked.constructors[0].recursive[0].fieldIndex = 1
  recursiveBinderCount :
    transaction.certificate.generation.block.checked.constructors[0].recursive[0].binders.length = 2
  recursiveTargetFamily :
    transaction.certificate.generation.block.checked.constructors[0].recursive[0].targetType = 0
  recursiveTargetIndex :
    transaction.certificate.generation.block.checked.constructors[0].recursive[0].indices =
      [.bvar 1]
  oneGeneratedRule :
    transaction.certificate.generation.generatedRules.length = 1

theorem breadth : BreadthFacts := by
  constructor <;> rfl

/-- Stable semantic consequences obtained through the same generic E2a
adapter used by the IndexedVec transaction. -/
theorem certifiedFacts :
    CertifiedGenerationFacts VEnv.empty finalEnv transaction.certificate :=
  transaction.facts

end Ix.Tc.RecursivePiCertificateFixture
