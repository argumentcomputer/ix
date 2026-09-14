import Ix.Kernel.Verify.Check.InferencePolicy
import Ix.Kernel.Verify.UniverseInternOnly

/-!
# Inference-policy frame for universe instantiation

`TcM.instantiateUnivParams` is a memoized `StateT` walk over an expression
DAG.  Its semantic verification needs collision and reachability resources,
but its operational noninterference fact does not: the walk can throw while
substituting a universe, and otherwise changes only its private memo table and
the kernel intern table.

The shared exact intern-table frame proves this operational fact for memo
hits, every expression constructor, the constant-universe array loop,
recursive child failures, interning, and memo writes on both outcomes.
-/

namespace Ix.Kernel

namespace TcM.PreservesInferOnly

theorem ofExcept (value : Except (TcError .anon) alpha) :
    (TcM.ofExcept value).PreservesInferOnly := by
  cases value with
  | ok value => exact pure value
  | error err => exact throw err

theorem map {x : TcM .anon alpha} (hx : x.PreservesInferOnly)
    (f : alpha → beta) : (f <$> x).PreservesInferOnly := by
  rw [← bind_pure_comp]
  exact bind hx fun value => pure (f value)

/-- The exact intern-only frame supplies policy preservation on both
outcomes, without collision or semantic premises. -/
theorem instantiateUnivParams (e : KExpr .anon) (us : Array (KUniv .anon)) :
    (TcM.instantiateUnivParams e us).PreservesInferOnly := by
  intro before
  have changed := TcM.InternOnly.instantiateUnivParams e us before
  cases run : TcM.instantiateUnivParams e us before <;> rw [run] at changed <;>
    obtain ⟨table, exactState⟩ := changed <;> rw [exactState]

end TcM.PreservesInferOnly
end Ix.Kernel
