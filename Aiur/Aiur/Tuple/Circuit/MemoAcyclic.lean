import Aiur.Tuple.Circuit.MemoDerivation
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Logic.Relation
import Mathlib.Order.WellFounded

namespace Aiur.Tuple.Circuit.MemoDerivation

variable [Field F] [DecidableEq F] {system : System F} {message : Message F}

/-- An enabled premise of `parent` is supplied by `child`, oriented for induction. -/
def Dependency (graph : MemoDerivation system message) (child parent : Fin graph.size) : Prop :=
  ∃ j : Fin (graph.node parent).premises.length, graph.target parent j = child

/-- No node lies on a nonempty directed path back to itself. Sharing is allowed. -/
def Acyclic (graph : MemoDerivation system message) : Prop :=
  ∀ i, ¬ Relation.TransGen graph.Dependency i i

/-- On the finite node set, the absence of directed cycles permits dependency induction. -/
theorem Acyclic.wellFounded {graph : MemoDerivation system message}
    (acyclic : graph.Acyclic) : WellFounded graph.Dependency := by
  letI : Std.Irrefl (Relation.TransGen graph.Dependency) := ⟨acyclic⟩
  exact (Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen graph.Dependency)).mono
    (fun _ _ edge => .single edge)

/-- Unfold the dependencies of any node into a finite, closed derivation tree. -/
theorem node_derives_of_acyclic (graph : MemoDerivation system message)
    (acyclic : graph.Acyclic) (i : Fin graph.size) :
    Derives system (graph.node i).conclusion := by
  induction i using acyclic.wellFounded.induction with
  | h i ih =>
      have premises : ∀ premise ∈ (graph.node i).premises, Derives system premise := by
        intro premise member
        obtain ⟨j, bounded, same⟩ := List.mem_iff_getElem.mp member
        have child := ih (graph.target i ⟨j, bounded⟩) ⟨⟨j, bounded⟩, rfl⟩
        rwa [(graph.target_claim i ⟨j, bounded⟩).trans same] at child
      obtain ⟨children⟩ := derivations_nonempty_iff.mpr premises
      exact ⟨.node (graph.node i).chip (graph.node i).row
        (graph.node i).lookup (graph.node i).valid children⟩

/-- An acyclic memoized graph supplies an ordinary derivation of its root claim. -/
theorem derives_of_acyclic (graph : MemoDerivation system message)
    (acyclic : graph.Acyclic) : Derives system message := by
  rw [← graph.root_claim]
  exact graph.node_derives_of_acyclic acyclic graph.root

end Aiur.Tuple.Circuit.MemoDerivation
