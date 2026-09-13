import Ix.Kernel.Verify.Inductive.GeneratedRecursorAdmission
import Ix.Kernel.Verify.Inductive.IndexedCandidateTransaction

/-!
# Producer-linked IndexedVec one-family closure

The trust-minimal `IndexedVec` Theory transaction and the executable
Ix.Theory.Named candidate replay are intentionally audited separately.  This module
joins them only at a stronger inductive verification root: the exact producer-selected package
erases to the same certificate transaction consumed by the Ix family and
generated-recursor admission, while all three anonymous ingress calls and both
production block checks remain explicit.
-/

namespace Ix.Kernel.IndexedRecursiveFixture

open IndexedRecursiveCertificateFixture

/-- Complete producer-linked vertical closure for `IndexedVec`.

No oracle-selected future world appears in this statement.  The semantic
field ends in the explicit `OneFamilyRecursorCertificate` closure carried by
`CanonicalRecursorAtomicClosure`; the operational fields record the concrete
Ix ingress and block-check executions which precede it. -/
structure ProducerLinkedOneFamilyClosure : Prop where
  producer : producedTransaction.Facts
  erasedTransaction : producedTransaction.toCertified = transaction
  natIngress : natIngressOutcome = .ok natIngressResult natIngressAfter
  familyIngress :
    familyIngressOutcome = .ok familyIngressResult familyIngressAfter
  recursorIngress :
    recursorIngressOutcome = .ok recursorIngressResult recursorIngressAfter
  familyChecked :
    (RecM.checkInductiveBlock familyBlockId familyMembers).run checkerMethods
      natKernelAfter = .ok () familyKernelAfter
  recursorChecked :
    (RecM.checkRecursorBlock recursorBlockId recursorMembers).run
      checkerMethods familyKernelAfter = .ok () recursorKernelAfter
  semantic : CanonicalRecursorAtomicClosure

/-- The exact outer Ix.Theory.Named producer, production Ix executions, and
oracle-free one-family semantic closure for the concrete indexed-recursive
fixture. -/
theorem producerLinkedOneFamilyClosure : ProducerLinkedOneFamilyClosure where
  producer := producerLinkedFacts
  erasedTransaction := producedToCertified_eq
  natIngress := natIngressRun
  familyIngress := familyIngressRun
  recursorIngress := recursorIngressRun
  familyChecked := familyKernelRun
  recursorChecked := recursorKernelRun
  semantic := familyRecursorAtomicClosure

end Ix.Kernel.IndexedRecursiveFixture
