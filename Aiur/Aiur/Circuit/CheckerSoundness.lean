import Aiur.Circuit.CheckerFacts

namespace Aiur.Circuit

variable {F : Type} [Field F] [DecidableEq F] {system : System F} {rom : WireROM F}

def RuleInstance.claims (rule : RuleInstance system rom) : RuleClaims (Message F) :=
  (rule.conclusion, rule.premises)

theorem RuleInstance.derives (rule : RuleInstance system rom)
    (premises : ∀ claim ∈ rule.premises, Derives system rom claim) : Derives system rom rule.conclusion := by
  obtain ⟨children⟩ := derivations_nonempty_iff.mpr premises
  cases rule with
  | node chip row lookup valid => exact ⟨.node chip row lookup valid children⟩
  | table claim member => exact ⟨.table member⟩

theorem System.inspectRows_rules {rows : List (Row F)} {claims : List (RuleClaims (Message F))}
    (inspected : system.inspectRows rom rows = .ok claims) :
    ∃ rules : List (RuleInstance system rom), claims = rules.map RuleInstance.claims := by
  have related := mapM_ok_iff.mp inspected
  clear inspected
  induction related with
  | nil => exact ⟨[], rfl⟩
  | cons head _ ih =>
      obtain ⟨rules, rfl⟩ := ih
      obtain ⟨chip, lookup, valid, rfl⟩ := System.inspectRow_iff.mp head
      exact ⟨.node chip _ lookup valid :: rules, rfl⟩

theorem System.inspectWeightedRows_rules {rows : List (WeightedRow F)}
    {claims : List (RuleClaims (Message F) × Int)}
    (inspected : system.inspectWeightedRows rom rows = .ok claims) :
    ∃ rules : List (RuleInstance system rom × Int),
      claims = rules.map (fun rule => (rule.1.claims, rule.2)) := by
  have related := mapM_ok_iff.mp inspected
  clear inspected
  induction related with
  | nil => exact ⟨[], rfl⟩
  | @cons row claim rows claims head _ ih =>
      obtain ⟨rules, rfl⟩ := ih
      obtain ⟨info, checked, same⟩ := except_bind_ok.mp head
      have same : (info, row.multiplicity) = claim := by simpa using same
      subst claim
      obtain ⟨chip, lookup, valid, rfl⟩ := System.inspectRow_iff.mp checked
      exact ⟨(.node chip row.row lookup valid, row.multiplicity) :: rules, rfl⟩

/-- Soundness of the unit-multiplicity trace checker, independently of compilation.
Unreachable balanced components need not be part of the resulting finite tree. -/
theorem System.check_sound {root : Message F} {rows : List (Row F)}
    (checked : system.check rom root rows = .ok ()) : Derives system rom root := by
  obtain ⟨_, claims, inspected, balanced⟩ := System.check_iff.mp checked
  obtain ⟨rules, rfl⟩ := system.inspectRows_rules inspected
  apply Balance.property_of_unit_balance (property := Derives system rom) ?_ ?_ balanced
  · intro claim member
    exact ⟨.table (of_decide_eq_true member)⟩
  · intro claim member premises
    obtain ⟨rule, _, rfl⟩ := List.mem_map.mp member
    exact rule.derives premises

/-- Signed provide weights force the support condition of a closed memoized graph.
There is no acyclicity condition in this theorem. -/
theorem memoDerives_of_balance {root : Message F} {rules : List (RuleInstance system rom × Int)}
    (zero : (Balance.accumulator (fun c => decide (system.MapClaim c)) root
      (rules.map fun rule => (rule.1.claims, rule.2))).isZero = true) : MemoDerives system rom root := by
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
  refine ⟨MemoDerivation.ofClosed nodes (locate root (Or.inl rfl)) ?_⟩
  intro rule member premise needed
  rcases List.mem_append.mp member with dynamic | static
  · obtain ⟨weighted, belongs, rfl⟩ := List.mem_map.mp dynamic
    exact locate premise (Or.inr ⟨weighted, belongs, needed⟩)
  · obtain ⟨claim, _, rfl⟩ := List.mem_map.mp static
    simp [RuleInstance.premises] at needed

theorem System.checkMemo_sound {root : Message F} {rows : List (WeightedRow F)}
    (checked : system.checkMemo rom root rows = .ok ()) : MemoDerives system rom root := by
  obtain ⟨_, claims, inspected, zero⟩ := System.checkMemo_iff.mp checked
  obtain ⟨rules, rfl⟩ := system.inspectWeightedRows_rules inspected
  exact memoDerives_of_balance zero

end Aiur.Circuit
