import Aiur.Scalar.Correctness
import Aiur.Scalar.Circuit.MemoAcyclic

namespace Aiur.Scalar

/-- Every acyclic graph for a compiled system has a finite source evaluation. -/
theorem memo_acyclic_sound [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system) {message : Circuit.Message F}
    (graph : Circuit.MemoDerivation system message) (acyclic : graph.Acyclic) :
    EvalCall program message.channel message.args message.result := by
  obtain ⟨tree⟩ := graph.derives_of_acyclic acyclic
  exact derivation_sound compiled tree

end Aiur.Scalar
