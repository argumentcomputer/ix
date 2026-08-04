import Ix.Tc.Verify.Audit.Completed
import Ix.Tc.Verify.Inductive.MutualRecursorAdmission

/-!
# Trust manifest for conditional `Ix.Tc.Verify` roots

This manifest is deliberately separate from `Audit.Completed`.  Its roots
may use only individually named witnesses from `Ix.Tc.Upstream.Pending`, and
the exact axiom audit fails as soon as either the pending or native footprint
changes.  Moving a theorem from here to `Completed` therefore requires
removing every dependency on the quarantine namespace.
-/

namespace Ix.Tc.Verify.Audit.Conditional

open Ix.Tc.Verify.Audit

private def standard : Array Lean.Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

private def mutualRecursorPending : Array Lean.Name := #[
  ``Ix.Tc.Upstream.Pending.mutualTreePhysicalGenerationWF,
  ``Ix.Tc.Upstream.Pending.mutualTreePhysicalRulePatternSound
]

private def roots : Array RootAllowance := #[
  { root := ``Ix.Tc.MutualTreeFixture.mutualRecursorConditionalClosure,
    standardAxioms := standard,
    pendingAxioms := mutualRecursorPending,
    nativeAxioms := Completed.mutualRecursorConditionalNative }
]

run_cmd Ix.Tc.Verify.Audit.check roots

end Ix.Tc.Verify.Audit.Conditional
