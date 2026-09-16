import Compilatrix.Aiur.AIR.Rank.Check
import Compilatrix.Aiur.AIR.Rank.Balance
import Compilatrix.Aiur.Static.Assignment

/-! Extract natural ranked-edge facts while retaining the physical rank
binding. Erasing the rank before matching messages is not sufficient. -/

namespace Compilatrix.Aiur.AIR.Rank

open _root_.Aiur (G)

theorem functionMessage_rank {leftFunction rightFunction : G}
    {leftInputs leftOutputs rightInputs rightOutputs : List G} {leftRank rightRank : G}
    (binding : functionMessage leftFunction leftInputs leftOutputs leftRank =
      functionMessage rightFunction rightInputs rightOutputs rightRank) : leftRank = rightRank := by
  have last := congrArg List.getLast? binding
  simpa only [functionMessage, List.getLast?_concat, Option.some.injEq] using last

theorem ordered_message_increases {parent gap child : Limbs}
    (parentRanges : parent.RangeProvided) (gapRanges : gap.RangeProvided)
    (childRanges : child.RangeProvided)
    {callerFunction providerFunction : G} {callInputs callOutputs providerInputs providerOutputs : List G}
    (binding : functionMessage callerFunction callInputs callOutputs (ordered parent gap) =
      functionMessage providerFunction providerInputs providerOutputs child.packed) :
    parent.value < child.value :=
  (ordered_from_range parentRanges gapRanges childRanges (functionMessage_rank binding)).2

theorem root_rank_zero {rank : Limbs} (bounded : rank.Bounded) (binding : rank.packed = 0) :
    rank.value = 0 := by
  have values := congrArg G.n binding
  simpa only [rank.packed_n bounded, Field.zero_value] using values

theorem bound_message_rank {child : Limbs} (bounded : child.Bounded)
    {callerFunction providerFunction boundary : G}
    {callInputs callOutputs providerInputs providerOutputs : List G}
    (binding : functionMessage callerFunction callInputs callOutputs boundary =
      functionMessage providerFunction providerInputs providerOutputs child.packed) :
    boundary.n = child.value ∧ boundary.n < rankBound := by
  have equal := functionMessage_rank binding
  rw [equal, child.packed_n bounded]
  exact ⟨rfl, child.value_lt bounded⟩

theorem ordered_message_of_balance {demands : List (List G)} {providers : List RangeRow}
    (balanced : RangeBalanced demands providers) (budget : demands.length < _root_.Aiur.gSize.toNat)
    {parent gap child : Limbs}
    (requested : ∀ message ∈ parent.requests ++ gap.requests ++ child.requests, message ∈ demands)
    {callerFunction providerFunction : G} {callInputs callOutputs providerInputs providerOutputs : List G}
    (binding : functionMessage callerFunction callInputs callOutputs (ordered parent gap) =
      functionMessage providerFunction providerInputs providerOutputs child.packed) :
    parent.value < child.value :=
  (ordered_of_balance balanced budget requested (functionMessage_rank binding)).2

theorem Checked.facts {edge : Edge} (checked : Checked edge) :
    edge.parent.Bounded ∧ edge.gap.Bounded ∧ edge.child.Bounded ∧
      ordered edge.parent edge.gap = edge.child.packed := by
  have facts := checked.checked
  simp only [Edge.check, Bool.and_eq_true, decide_eq_true_eq] at facts
  exact ⟨facts.1.1.1, facts.1.1.2, facts.1.2, facts.2⟩

theorem Checked.equation {edge : Edge} (checked : Checked edge) :
    edge.child.value = edge.parent.value + 1 + edge.gap.value :=
  ordered_eq checked.facts.1 checked.facts.2.1 checked.facts.2.2.1 checked.facts.2.2.2

theorem Checked.increases {edge : Edge} (checked : Checked edge) : edge.parent.value < edge.child.value :=
  ordered_increases checked.facts.1 checked.facts.2.1 checked.facts.2.2.1 checked.facts.2.2.2

theorem Checked.child_bound {edge : Edge} (checked : Checked edge) : edge.child.value < rankBound :=
  edge.child.value_lt checked.facts.2.2.1

/-- This discharges one ranked static edge after its physical message has
been matched. It does not turn equality of erased logical messages into
the physical rank equality. -/
theorem Checked.advances {edge : Edge} (checked : Checked edge) (order : Nat)
    (ranked : Static.rankedOrder order = true) (parentCounter childCounter : G) :
    Static.Advances ⟨order, parentCounter, edge.parent.value⟩
      ⟨order, childCounter, edge.child.value⟩ := by
  exact Or.inr ⟨rfl, by simpa only [ranked, ↓reduceIte] using checked.increases⟩

theorem checked_no_self (parent gap : Limbs) : ¬ Nonempty (Checked ⟨parent, gap, parent⟩) := by
  rintro ⟨checked⟩
  have := checked.increases
  exact Nat.lt_irrefl _ this

end Compilatrix.Aiur.AIR.Rank
