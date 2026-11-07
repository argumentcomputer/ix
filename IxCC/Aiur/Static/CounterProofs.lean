import IxCC.Aiur.Static.Counter
import IxCC.Aiur.Field

/-! Normalize both input/output unit-counter directions using the exact
pinned field representation. No abstract field-law or primality axiom is used. -/

namespace IxCC.Aiur.Static

open _root_.IxCC.Vendor.Aiur (G gSize)
open _root_.IxCC.Vendor.Aiur.Bytecode

theorem neg_add_one (value : G) : (0 - (value + 1)) + 1 = 0 - value := by
  apply Field.ext
  rw [G.add_one_n, G.sub_n, G.sub_n, G.add_one_n]
  have zero : (0 : G).n = 0 := rfl
  simp only [zero, Nat.zero_add]
  have bound := Field.value_lt value
  have positive : 1 < gSize.toNat := by decide
  by_cases small : value.n + 1 < gSize.toNat
  · rw [Nat.mod_eq_of_lt small]
    have subBound : gSize.toNat - (value.n + 1) < gSize.toNat := by omega
    rw [Nat.mod_eq_of_lt subBound]
    congr 1
    omega
  · have full : value.n + 1 = gSize.toNat := by omega
    rw [full, Nat.mod_self]
    simp only [Nat.sub_zero, Nat.mod_self, Nat.zero_add]
    have remaining : gSize.toNat - value.n = 1 := by omega
    rw [remaining]

theorem neg_sub_one (value : G) : 0 - (value - 1) = (0 - value) + 1 := by
  have opposite := neg_add_one (value - 1)
  rw [G.sub_one_add_one] at opposite
  exact opposite.symm

theorem normalizeCounter_step (candidate : UnitCounter.Certificate) (parent child : G)
    (unit : candidate.step = 1 ∨ candidate.step = (0 : G) - 1)
    (step : CounterStep candidate parent child) :
    normalizeCounter candidate child = normalizeCounter candidate parent + 1 := by
  rcases candidate with ⟨mode, column, direction⟩
  cases mode <;> rcases unit with rfl | rfl
  · simpa [normalizeCounter, CounterStep] using step
  · have raw : child = parent - 1 := by
      simpa [CounterStep, G.add_neg_one_eq_sub] using step
    have different : ((0 : G) - 1 != (1 : G)) = true := by decide
    simp only [normalizeCounter, different, ↓reduceIte]
    rw [raw, neg_sub_one]
  · have raw : parent = child + 1 := step
    simpa [normalizeCounter, raw] using (neg_add_one child).symm
  · have raw : parent = child - 1 := by
      simpa [CounterStep, G.add_neg_one_eq_sub] using step
    have different : ((0 : G) - 1 == (1 : G)) = false := by decide
    simp only [normalizeCounter, different, Bool.false_eq_true, ↓reduceIte]
    rw [raw, G.sub_one_add_one]

theorem normalizedCounter_step (candidate : UnitCounter.Certificate)
    (parentInputs parentOutputs childInputs childOutputs : List G) (parent child : G)
    (observedParent : counterObservation candidate parentInputs parentOutputs = some parent)
    (observedChild : counterObservation candidate childInputs childOutputs = some child)
    (unit : candidate.step = 1 ∨ candidate.step = (0 : G) - 1)
    (step : CounterStep candidate parent child) :
    normalizedCounter candidate childInputs childOutputs =
      normalizedCounter candidate parentInputs parentOutputs + 1 := by
  simpa [normalizedCounter, observedParent, observedChild] using
    normalizeCounter_step candidate parent child unit step

end IxCC.Aiur.Static
