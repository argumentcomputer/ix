import Ix.Tc.Verify.Inductive.Certificate
import Lean4Lean.Verify.Environment.InductiveFixtures

/-!
# Certified parameterized, indexed, recursive generation fixture

Lean4Lean's `IndexedVec` fixture is the first certificate in the dependency
whose source is simultaneously parameterized, indexed, and recursive.  This
module reconstructs it through the Theory-only proof-carrying transaction
boundary and records the exact breadth facts that distinguish it from E2b's
Boolean enumeration.

The ambient `Nat` environment is reconstructed through its own certified
transaction instead of importing the implementation-reflection replay proof.
This is important for the trust manifest: the resulting certificate depends
only on the accepted Lean axioms, not on persistent-map or reflected-expression
equations from the `Lean4Lean.Verify` layer.

Nothing here asserts an Ix catalog correspondence.  That separate link must
be constructed from production anonymous ingress and checking, so the
certificate cannot silently choose the concrete declarations it certifies.
-/

namespace Ix.Tc.IndexedRecursiveCertificateFixture

open Lean4Lean
open Lean4Lean.InductiveFixtures
open Lean4Lean.InductiveReplayFixtures

/-- The exact proof-carrying transaction that constructs the ambient `Nat`
environment needed by `IndexedVec`. -/
def natCertificate : natDecl.GenerationCertificate VEnv.empty where
  generation := natChecked.identityGeneration
  wf := (natChecked.wf_of_decl natDecl_wf).identityGeneration .empty

theorem natSuccess :
    VEnv.empty.addInductCertified natCertificate = some natFinalEnv := rfl

def natTransaction : CertifiedGenerationTransaction natDecl VEnv.empty
    natFinalEnv where
  certificate := natCertificate
  success := natSuccess
  beforeWF := ⟨[], .empty⟩

/-- A trust-minimal proof of the ambient Theory environment's well-formedness.
It is derived from the certified transaction rather than the reflected kernel
environment replay. -/
theorem natWF : natFinalEnv.WF := natTransaction.afterWF

/-- The identity generation selected by the executable checker is semantically
well formed in the certified ambient environment. -/
theorem generationWF :
    indexedVecChecked.identityGeneration.WF natFinalEnv := by
  exact (indexedVecChecked.wf_of_decl indexedVecDecl_wf).identityGeneration
    natWF.ordered

def certificate : indexedVecDecl.GenerationCertificate natFinalEnv where
  generation := indexedVecChecked.identityGeneration
  wf := generationWF

theorem success :
    natFinalEnv.addInductCertified certificate = some indexedVecFinalEnv := rfl

/-- The exact successful proof-carrying transaction for the real Theory
`IndexedVec` declaration. -/
def transaction : CertifiedGenerationTransaction indexedVecDecl natFinalEnv
    indexedVecFinalEnv where
  certificate := certificate
  success := success
  beforeWF := natWF

/-- The certificate retains the same generation selected by the executable
normalization candidate; it is not an independently regenerated artifact. -/
@[simp] theorem transaction_generation :
    transaction.certificate.generation =
      indexedVecChecked.identityGeneration := rfl

/-- Auditable shape of the first non-enumeration E2c certificate.

The recursive argument is the third constructor field and targets the sole
family at the predecessor index.  The constructor result advances that index
through `Nat.succ`, so this witness exercises changing indices rather than a
syntactically constant recursive occurrence. -/
structure BreadthFacts : Prop where
  oneUniverse : indexedVecDecl.uvars = 1
  oneParameter : indexedVecDecl.nparams = 1
  singletonFamily : indexedVecDecl.types.length = 1
  oneIndex : transaction.certificate.generation.block.checked.indices.length = 1
  largeElimination :
    transaction.certificate.generation.block.checked.elimination = .large
  twoConstructors :
    transaction.certificate.generation.block.checked.constructors.length = 2
  consHasThreeFields :
    transaction.certificate.generation.block.checked.constructors[1].fields.length = 3
  consHasOneRecursiveArgument :
    transaction.certificate.generation.block.checked.constructors[1].recursive.length = 1
  recursiveFieldIndex :
    transaction.certificate.generation.block.checked.constructors[1].recursive[0].fieldIndex = 2
  recursiveTargetFamily :
    transaction.certificate.generation.block.checked.constructors[1].recursive[0].targetType = 0
  recursiveTargetIndex :
    transaction.certificate.generation.block.checked.constructors[1].recursive[0].indices =
      [.bvar 1]
  resultIndexChanges :
    transaction.certificate.generation.block.checked.constructors[1].resultIndices =
      [VExpr.app (VExpr.const ``Nat.succ []) (VExpr.bvar 2)]
  generatedRuleCount :
    transaction.certificate.generation.generatedRules.length = 2

/-- Exact computed breadth facts for the certified transaction. -/
theorem breadth : BreadthFacts := by
  constructor <;> rfl

/-- Stable semantic consequences obtained only from the Ix E2a adapter. -/
theorem certifiedFacts :
    CertifiedGenerationFacts natFinalEnv indexedVecFinalEnv
      transaction.certificate :=
  transaction.facts

end Ix.Tc.IndexedRecursiveCertificateFixture
