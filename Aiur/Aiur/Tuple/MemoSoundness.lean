import Aiur.Tuple.Correctness
import Aiur.Tuple.Circuit.MemoAcyclic

namespace Aiur.Tuple

/-- An acyclic memoized graph for the tuple compiler recovers source evaluation. -/
theorem memo_acyclic_sound [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system) {message : Circuit.Message F}
    (graph : Circuit.MemoDerivation system message) (acyclic : graph.Acyclic) :
    EvalCall program message.channel message.args message.result := by
  obtain ⟨tree⟩ := graph.derives_of_acyclic acyclic
  exact derivation_sound compiled tree

end Aiur.Tuple
