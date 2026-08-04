import Ix.Tc.Inductive
import Ix.Tc.Verify.Whnf.StructEta.ExactMajorTelescope

/-!
# Exact result-sort telescope restoration

`getResultSortLevel` temporarily retains peeled forall binders in the legacy
context so recursive normalization sees the correct de Bruijn scope.  This
module proves that the direct syntactic path—already-forall inputs followed by
an already-sort result—restores the caller's complete checker state exactly.

The theorem is deliberately operational.  It grants no authority to a WHNF
callback and makes no scoped suffix model admit the temporary telescope.
-/

namespace Ix.Tc
namespace RecM

/-- Pure syntax certificate for a fixed forall prefix ending in a sort. -/
def directResultSortAfterForalls : Nat → KExpr .anon → Option (KUniv .anon)
  | 0, .sort level _ => some level
  | fuel + 1, .all _ _ _ body _ =>
      directResultSortAfterForalls fuel body
  | _, _ => none

/-- The named production peeling helper performs exactly one local push per
certified forall and leaves the certified sort as its result. -/
theorem peelResultSortForalls_direct_exact
    {expected : Nat} {methods : Methods .anon} :
    ∀ (fuel found : Nat) {source : KExpr .anon} {level : KUniv .anon}
        {base current : TcState .anon} {n : Nat},
      ExactLocalExtension base n current →
      directResultSortAfterForalls fuel source = some level →
      ∃ result after,
        (peelResultSortForalls expected fuel found source).run methods current =
            .ok result after ∧
          ExactLocalExtension base (n + fuel) after ∧
          directResultSortAfterForalls 0 result = some level
  | 0, _, source, _, _, current, _, extension, shape =>
      ⟨source, current, rfl, by simpa using extension, shape⟩
  | fuel + 1, found, source, level, base, current, n, extension, shape => by
      cases source <;> try simp [directResultSortAfterForalls] at shape
      case all name bi dom body info =>
        obtain ⟨afterPush, pushRun⟩ := scratch_pushLocal_ok dom current
        obtain ⟨result, after, recursiveRun, recursiveExtension,
            resultShape⟩ :=
          peelResultSortForalls_direct_exact fuel (found + 1)
            (.succ extension pushRun) shape
        refine ⟨result, after, ?_, ?_, resultShape⟩
        · rw [peelResultSortForalls]
          rw [ReaderT.run_bind]
          change EStateM.bind
            ((whnf (.all name bi dom body info)).run methods) _ current = _
          unfold EStateM.bind
          rw [show (whnf (.all name bi dom body info)).run methods current =
            .ok (.all name bi dom body info) current from rfl]
          simp only
          rw [ReaderT.run_bind, ReaderT.run_monadLift, monadLift_self]
          change EStateM.bind (TcM.pushLocal dom) _ current = _
          unfold EStateM.bind
          rw [pushRun]
          exact recursiveRun
        · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            recursiveExtension

/-- Expose the `try/finally` state boundary of result-sort discovery. -/
theorem resultSort_tryFinally_run
    (source : KExpr .anon) (arity : Nat) (methods : Methods .anon)
    (state : TcState .anon) :
    (getResultSortLevel source arity).run methods state =
      tryFinally
        ((getResultSortLevelBody source arity).run methods)
        (TcM.restoreDepth state.ctx.size) state := by
  rfl

/-- On a direct forall-to-sort telescope, production result-sort discovery
returns the certified level and reconstructs every field of the caller state.
-/
theorem getResultSortLevel_direct_exact
    {methods : Methods .anon} {source : KExpr .anon} {arity : Nat}
    {level : KUniv .anon} {state : TcState .anon}
    (shape : directResultSortAfterForalls arity source = some level) :
    (getResultSortLevel source arity).run methods state =
      .ok level state := by
  obtain ⟨result, after, peelRun, extension, resultShape⟩ :=
    peelResultSortForalls_direct_exact (expected := arity) arity 0
      (ExactLocalExtension.zero (base := state)) shape
  cases result <;> try simp [directResultSortAfterForalls] at resultShape
  case sort actual info =>
    have levelEq : actual = level := resultShape
    subst actual
    have bodyRun :
        (getResultSortLevelBody source arity).run methods state =
              .ok level after := by
      unfold getResultSortLevelBody
      rw [ReaderT.run_bind, scratch_bind_ok peelRun]
      rfl
    have cleanup := ExactLocalExtension.restoreDepth_exact extension
    rw [resultSort_tryFinally_run]
    exact scratch_tryFinally_ok bodyRun cleanup

end RecM
end Ix.Tc
