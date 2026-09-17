import Compilatrix.Ixby.Runtime.Native.Values
import Compilatrix.Ixby.Runtime.ConversionLaws

namespace Compilatrix.Ixby.Runtime.Native

open Ix.Ixby

def ElementsValid (limits : Limits) (values : Array Value) : Prop :=
  ∀ value ∈ values, ArgumentValid limits value ∧ ResultValid limits value

theorem natValid_array_index (limits : Limits) (capacity : 32 ≤ limits.natBits)
    (n : Nat) (bound : n < 2 ^ 32) : NatValid limits n :=
  Conversion.validate_nat_of_bits bound capacity

/-- Consuming the next source element preserves the remaining sequence. -/
theorem extract_cons {α : Type} (values : Array α) (index stop : Nat)
    (inside : index < stop) (bound : stop ≤ values.size) :
    #[values[index]'(by omega)] ++ values.extract (index + 1) stop = values.extract index stop := by
  have singleton : values.extract index (index + 1) = #[values[index]'(by omega)] := by
    apply Array.ext
    · simp [Array.size_extract_of_le (show index + 1 ≤ values.size by omega)]
    · intro i left right
      have zero : i = 0 := by simpa using right
      subst i
      simp
  rw [← singleton, Array.extract_append_extract]
  simp [Nat.min_eq_left (by omega : index ≤ index + 1), Nat.max_eq_right (by omega : index + 1 ≤ stop)]

theorem extract_accumulator {α : Type} (values accumulator : Array α) (index stop : Nat)
    (inside : index < stop) (bound : stop ≤ values.size) :
    accumulator.push values[index] ++ values.extract (index + 1) stop =
      accumulator ++ values.extract index stop := by
  rw [← Array.append_singleton, Array.append_assoc, extract_cons values index stop inside bound]

end Compilatrix.Ixby.Runtime.Native
