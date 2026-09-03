import Ix.Tc.Verify.Inductive.ConstructorPositivityTraversal
import Ix.Tc.Verify.Inductive.IndexedPositivityTransport

/-!
# IndexedVec enclosing constructor-positivity execution

The field transports in `IndexedPositivityTransport` start at the exact states
reached after production's field-loop WHNF calls.  This module closes the
remaining outer execution boundary: it retains one complete successful
`checkPositivity` run for `IndexedVec.cons` and classifies that same run with
`ConstructorPositivityTrace`.

This is stronger than three independent successful domain checks.  The trace
also records the shared-parameter opening, source-ordered bounded field loop,
and public local-context restoration performed by production.
-/

namespace Ix.Tc.IndexedRecursiveFixture

/-- Exact result of running production strict positivity on the ingressed
`IndexedVec.cons` declaration. -/
def ixConsPositivityOutcome :=
  (RecM.checkPositivity consConcrete.ty 1 #[familyId.addr]).run checkerMethods
    checkerInitial

/-- Successful post-state projected from `ixConsPositivityOutcome`. -/
def ixConsPositivityAfter : TcState .anon :=
  match ixConsPositivityOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private def ixConsPositivitySucceeded : Bool :=
  match ixConsPositivityOutcome with
  | .ok _ _ => true
  | .error _ _ => false

private theorem ixConsPositivitySucceededNative :
    ixConsPositivitySucceeded = true := by
  native_decide

/-- The complete public positivity call succeeds with the projected exact
post-state. -/
theorem ixConsPositivityRun :
    (RecM.checkPositivity consConcrete.ty 1 #[familyId.addr]).run checkerMethods
      checkerInitial = .ok () ixConsPositivityAfter := by
  have success := ixConsPositivitySucceededNative
  unfold ixConsPositivitySucceeded at success
  unfold ixConsPositivityAfter
  generalize houtcome : ixConsPositivityOutcome = outcome at success ⊢
  cases outcome <;> simp_all [ixConsPositivityOutcome]

/-- Exhaustive execution trace for the same complete production call.  In
particular, each retained `PositivityDomainTrace` is reached through the
enclosing parameter and field traversal rather than assumed independently. -/
theorem indexedVecConsIxPositivityTrace :
    ConstructorPositivityTrace consConcrete.ty 1 #[familyId.addr]
      checkerMethods checkerInitial ixConsPositivityAfter :=
  RecM.checkPositivity_success checkerMethods ixConsPositivityRun

end Ix.Tc.IndexedRecursiveFixture
