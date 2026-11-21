import Aiur.Circuit.Accumulator

namespace Aiur.Circuit

/-- A rule's conclusion and its active premise occurrences. -/
abbrev RuleClaims (α : Type) := α × List α

namespace Balance

def required (static : α → Bool) (root : α) (rules : List (RuleClaims α)) : List α :=
  (root :: rules.flatMap Prod.snd).filter (fun claim => !static claim)

def accumulator (static : α → Bool) (root : α) (rules : List (RuleClaims α × Int)) : Accumulator α :=
  Accumulator.requires (required static root (rules.map Prod.fst)) ++
    Accumulator.provides (rules.map fun rule => (rule.1.1, rule.2))

/-- A balanced integer ledger must provide every dynamically required claim,
even when provide weights are zero or negative. -/
theorem provider_of_zero [DecidableEq α] {static : α → Bool} {root claim : α}
    {rules : List (RuleClaims α × Int)}
    (zero : (accumulator static root rules).isZero = true)
    (needed : claim ∈ required static root (rules.map Prod.fst)) :
    ∃ rule ∈ rules, rule.1.1 = claim := by
  have balance := (Accumulator.isZero_iff _).mp zero claim
  simp only [accumulator, Accumulator.value_append, Accumulator.value_requires,
    Accumulator.value_provides] at balance
  by_contra absent
  have empty : Accumulator.value (rules.map fun rule => (rule.1.1, rule.2)) claim = 0 := by
    apply Accumulator.value_of_absent
    intro entry member same
    obtain ⟨rule, belongs, rfl⟩ := List.mem_map.mp member
    exact absent ⟨rule, belongs, same⟩
  have positive := List.count_pos_iff.mpr needed
  rw [empty] at balance
  omega

/-- Exact unit balance establishes every property closed under the supplied rules
and the static leaves. In particular, take the property to be finite derivability. -/
theorem property_of_unit_balance {static : α → Bool} {root : α} {rules : List (RuleClaims α)}
    {property : α → Prop}
    (leaves : ∀ claim, static claim = true → property claim)
    (closed : ∀ rule ∈ rules, (∀ premise ∈ rule.2, property premise) → property rule.1)
    (balanced : (required static root rules).Perm (rules.map Prod.fst)) : property root := by
  classical
  let bad : α → Bool := fun claim => decide (¬property claim)
  have step (rule : RuleClaims α) (member : rule ∈ rules) :
      (if bad rule.1 then 1 else 0) ≤ rule.2.countP bad := by
    by_cases good : property rule.1
    · simp [bad, good]
    · have existsBad : ∃ premise ∈ rule.2, bad premise = true := by
        by_contra noBad
        apply good
        apply closed rule member
        intro premise present
        by_contra notGood
        exact noBad ⟨premise, present, by simp [bad, notGood]⟩
      have positive := List.countP_pos_iff.mpr existsBad
      simpa [bad, good] using positive
  have total : (rules.map Prod.fst).countP bad ≤ (rules.flatMap Prod.snd).countP bad := by
    clear closed balanced
    induction rules with
    | nil => simp
    | cons rule rules ih =>
        have one := step rule (by simp)
        have tail := ih (fun r h => step r (by simp [h]))
        simp only [List.map_cons, List.countP_cons, List.flatMap_cons, List.countP_append]
        omega
  have filtered (claims : List α) :
      (claims.filter (fun claim => !static claim)).countP bad = claims.countP bad := by
    rw [List.countP_filter]
    congr 1
    funext claim
    by_cases s : static claim = true
    · simp [s, bad, leaves claim s]
    · simp [Bool.eq_false_iff.mpr s]
  have counts := balanced.countP_eq bad
  rw [required, filtered, List.countP_cons] at counts
  by_contra notRoot
  have badRoot : bad root = true := by simp [bad, notRoot]
  rw [badRoot] at counts
  simp only [Bool.true_eq, ite_true] at counts
  omega

/-- Allocate all demand for a conclusion to its first providing row. Repeated
providers get weight zero, while their premises remain ordinary requirements. -/
def weigh [DecidableEq α] (demands : List α) : List (RuleClaims α) → List (RuleClaims α × Int)
  | [] => []
  | rule :: rules => (rule, (demands.count rule.1 : Int)) ::
      weigh (demands.filter (fun claim => decide (claim ≠ rule.1))) rules

@[simp] theorem weigh_rules [DecidableEq α] (demands : List α) (rules : List (RuleClaims α)) :
    (weigh demands rules).map Prod.fst = rules := by
  induction rules generalizing demands with
  | nil => rfl
  | cons rule rules ih => simp [weigh, ih]

private theorem count_filter_ne [DecidableEq α] (claims : List α) (removed claim : α) :
    (claims.filter (fun x => decide (x ≠ removed))).count claim =
      if claim = removed then 0 else claims.count claim := by
  induction claims with
  | nil => simp
  | cons head tail ih =>
      by_cases a : head = removed <;> by_cases b : head = claim <;>
        by_cases c : claim = removed <;> simp_all

theorem weigh_value [DecidableEq α] {demands : List α} {rules : List (RuleClaims α)}
    (covered : ∀ claim ∈ demands, ∃ rule ∈ rules, rule.1 = claim) (claim : α) :
    Accumulator.value ((weigh demands rules).map fun rule => (rule.1.1, rule.2)) claim =
      (demands.count claim : Int) := by
  induction rules generalizing demands with
  | nil =>
      have absent : claim ∉ demands := by intro h; simpa using covered claim h
      simp [weigh, List.count_eq_zero.mpr absent]
  | cons rule rules ih =>
      have rest : ∀ next ∈ demands.filter (fun x => decide (x ≠ rule.1)),
          ∃ provider ∈ rules, provider.1 = next := by
        intro next member
        obtain ⟨present, different⟩ := List.mem_filter.mp member
        obtain ⟨provider, member, same⟩ := covered next present
        rcases List.mem_cons.mp member with rfl | member
        · simp [same] at different
        · exact ⟨provider, member, same⟩
      simp only [weigh, List.map_cons, Accumulator.value_cons]
      rw [ih rest, count_filter_ne]
      by_cases same : rule.1 = claim
      · simp [same]
      · simp [same, Ne.symm same]

theorem weigh_balanced [DecidableEq α] {static : α → Bool} {root : α}
    {rules : List (RuleClaims α)}
    (covered : ∀ claim ∈ required static root rules, ∃ rule ∈ rules, rule.1 = claim) :
    (accumulator static root (weigh (required static root rules) rules)).isZero = true := by
  apply (Accumulator.isZero_iff _).mpr
  intro claim
  simp only [accumulator, weigh_rules, Accumulator.value_append, Accumulator.value_requires,
    Accumulator.value_provides, weigh_value covered]
  omega

end Balance
end Aiur.Circuit
