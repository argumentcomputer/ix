import Aiur.Circuit.CycleLength
import Aiur.Circuit.CheckerSoundness

/-!
# Memo graphs with one row node per accepted row

`memoDerives_of_balance` builds a memo graph from balanced weighted rule
instances. Row bounds need its size: the graph built here has one row node per
rule instance, so a checker's row count bounds `MemoDerivation.rows`.
-/

namespace Aiur.Circuit

variable {F : Type} [Field F] [DecidableEq F] {rom : WireROM F}

/-- A balanced ledger of weighted rule instances yields a memo graph whose row
nodes are at most the instances. Fixed claims become table nodes. -/
theorem MemoDerivation.exists_of_balance {system : System F} {root : Message F}
    (rules : List (RuleInstance system rom × Int))
    (zero : (Balance.accumulator (fun c => decide (system.MapClaim c)) root
      (rules.map fun rule => (rule.1.claims, rule.2))).isZero = true) :
    ∃ graph : MemoDerivation system rom root, graph.rows.card ≤ rules.length := by
  let tables : List (RuleInstance system rom) :=
    system.mapClaims.attach.map fun claim => .table claim.val claim.property
  let nodes := rules.map Prod.fst ++ tables
  have locate (claim : Message F)
      (used : claim = root ∨ ∃ rule ∈ rules, claim ∈ rule.1.premises) :
      ∃ node ∈ nodes, node.conclusion = claim := by
    by_cases static : system.MapClaim claim
    · exact ⟨.table claim static, List.mem_append_right _
        (List.mem_map.mpr ⟨⟨claim, static⟩, List.mem_attach _ _, rfl⟩), rfl⟩
    · have needed : claim ∈ Balance.required (fun c => decide (system.MapClaim c)) root
          ((rules.map fun rule => (rule.1.claims, rule.2)).map Prod.fst) := by
        apply List.mem_filter.mpr
        refine ⟨?_, by simp [static]⟩
        rcases used with rfl | ⟨rule, member, premise⟩
        · exact List.mem_cons_self
        · apply List.mem_cons_of_mem
          exact List.mem_flatMap.mpr ⟨rule.1.claims,
            List.mem_map.mpr ⟨(rule.1.claims, rule.2), List.mem_map.mpr ⟨rule, member, rfl⟩, rfl⟩,
            premise⟩
      obtain ⟨provider, member, same⟩ := Balance.provider_of_zero zero needed
      obtain ⟨rule, belongs, rfl⟩ := List.mem_map.mp member
      exact ⟨rule.1, List.mem_append_left _ (List.mem_map.mpr ⟨rule, belongs, rfl⟩), same⟩
  let graph := MemoDerivation.ofClosed nodes (locate root (Or.inl rfl)) (by
    intro rule member premise needed
    rcases List.mem_append.mp member with dynamic | static
    · obtain ⟨weighted, belongs, rfl⟩ := List.mem_map.mp dynamic
      exact locate premise (Or.inr ⟨weighted, belongs, needed⟩)
    · obtain ⟨claim, _, rfl⟩ := List.mem_map.mp static
      simp [RuleInstance.premises] at needed)
  refine ⟨graph, ?_⟩
  have rowIndex : ∀ (k : Nat) (h : k < nodes.length), (nodes[k]'h).isNode = true →
      k < rules.length := by
    intro k h isRow
    by_contra outside
    have later : (rules.map Prod.fst).length ≤ k := by simpa using outside
    simp only [nodes] at isRow
    rw [List.getElem_append_right later] at isRow
    simp [tables, RuleInstance.isNode] at isRow
  have bound : ∀ i ∈ graph.rows, i.val < rules.length := by
    intro i member
    simp only [MemoDerivation.rows, Finset.mem_filter, Finset.mem_univ, true_and] at member
    exact rowIndex i.val i.isLt member
  calc graph.rows.card ≤ (Finset.range rules.length).card :=
        Finset.card_le_card_of_injOn Fin.val
          (by intro i member; simpa using bound i (by simpa using member))
          (by intro x _ y _ same; exact Fin.ext same)
    _ = rules.length := by simp

/-- Memo-checker acceptance gives a memo graph with at most one row node per row. -/
theorem System.checkMemo_graph {system : System F} {root : Message F} {rows : List (WeightedRow F)}
    (checked : system.checkMemo rom root rows = .ok ()) :
    ∃ graph : MemoDerivation system rom root, graph.rows.card ≤ rows.length := by
  obtain ⟨_, claims, inspected, zero⟩ := System.checkMemo_iff.mp checked
  have count := (mapM_ok_iff.mp inspected).length_eq
  obtain ⟨rules, rfl⟩ := system.inspectWeightedRows_rules inspected
  simp only [List.length_map] at count
  obtain ⟨graph, card⟩ := MemoDerivation.exists_of_balance rules zero
  exact ⟨graph, card.trans count.symm.le⟩

end Aiur.Circuit
