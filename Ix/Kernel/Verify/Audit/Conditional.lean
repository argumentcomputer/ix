import Ix.Kernel.Verify.Audit.Completed
import Ix.Kernel.Verify.Inductive.MutualRecursorAdmission

/-!
# Trust manifest for conditional `Ix.Kernel.Verify` roots

This manifest is deliberately separate from `Audit.Completed`.  Its roots
may use only individually named witnesses from `Ix.Kernel.Frontier.Pending`, and
the exact axiom audit fails as soon as either the pending or native footprint
changes.  Moving a theorem from here to `Completed` therefore requires
removing every dependency on the quarantine namespace.
-/

namespace Ix.Kernel.Verify.Audit.Conditional

open Ix.Kernel.Verify.Audit

private def standard : Array Lean.Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

private def mutualRecursorPending : Array Lean.Name := #[
  ``Ix.Kernel.Frontier.Pending.mutualTreePhysicalGenerationWF,
  ``Ix.Kernel.Frontier.Pending.mutualTreePhysicalRulePatternSound
]

private def roots : Array RootAllowance := #[
  { root := ``Ix.Kernel.MutualTreeFixture.mutualRecursorConditionalClosure,
    standardAxioms := standard,
    pendingAxioms := mutualRecursorPending,
    nativeAxioms := Completed.mutualRecursorConditionalNative }
]

run_cmd Ix.Kernel.Verify.Audit.check roots

end Ix.Kernel.Verify.Audit.Conditional
