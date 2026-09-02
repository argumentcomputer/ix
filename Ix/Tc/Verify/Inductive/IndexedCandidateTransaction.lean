import Ix.Tc.Verify.Inductive.IndexedRecursiveCertificate
import Ix.Tc.Verify.Inductive.ProducedGenerationTransaction
import Lean4Lean.Verify.Environment.IndexedVecSemanticReplay

/-!
# Producer-linked IndexedVec generation transaction

The existing `IndexedVec` certificate is deliberately reconstructed through
the Theory-only API so its semantic roots keep a minimal trust footprint.
Lean4Lean also exposes the exact ordinary metadata producer and dependent
semantic package for that same generation.  This module proves those two
paths meet, without making the producer replay a dependency of the clean
Theory-only transaction.
-/

namespace Ix.Tc.IndexedRecursiveCertificateFixture

open Lean4Lean
open Lean4Lean.InductiveFixtures
open Lean4Lean.InductiveReplayFixtures

/-- The L4L-01E package retains the exact source declaration and checked
generation selected by the ordinary metadata producer. -/
noncomputable def exactPackage :
    VInductDecl.ExactProducedGenerationCandidatePackage natFinalEnv [`u]
      indexedVecSemanticProducedGenerationShapeCandidate
      indexedVecChecked.identityGeneration :=
  Classical.choice
    indexedVecSemanticExactProducedGenerationCandidatePackage_exists

/-- The exact outer producer package, its projected certificate insertion,
and the already-certified ambient Nat environment in one transaction.  The
source and generation indices have not yet been erased at this boundary. -/
noncomputable def exactProducedTransaction :
    ExactProducedGenerationTransaction natFinalEnv indexedVecFinalEnv [`u]
      indexedVecSemanticProducedGenerationShapeCandidate
      indexedVecChecked.identityGeneration where
  exactPackage := exactPackage
  success := by
    have certificate_eq :
        exactPackage.package.package.certificate =
          indexedVecSemanticGenerationCertificate := by
      congr
    rw [certificate_eq]
    exact indexedVecSemantic_addInductCertified
  beforeWF := natWF

/-- Intentional operational erasure of the exact L4L-01E indices. -/
noncomputable def producedTransaction :
    ProducedGenerationTransaction natFinalEnv indexedVecFinalEnv [`u] :=
  exactProducedTransaction.toProduced

/-- The producer-selected package erases to the same generation certificate
as the independently audited Theory-only construction. -/
theorem producedCertificate_eq :
    producedTransaction.certificate = certificate := rfl

/-- Consequently the producer-linked and trust-minimal transactions are the
same data after Verify-side provenance is erased.  Proof irrelevance handles
the distinct derivations of generation well-formedness. -/
theorem producedToCertified_eq :
    producedTransaction.toCertified = transaction := rfl

/-- The executable producer equation and semantic transaction remain coupled
before erasure. -/
theorem producerLinkedFacts : producedTransaction.Facts :=
  producedTransaction.facts

end Ix.Tc.IndexedRecursiveCertificateFixture
