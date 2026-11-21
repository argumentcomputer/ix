import Aiur.AST
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Nat.Cast.Basic

namespace Aiur.Library.Carry

/-- The shared input domain and its low digit. Keeping one row generator
ensures the two precommitted traces use exactly the same ordering. -/
def rows (base count : Nat) : List (Nat × Nat) :=
  (List.range count).map fun n => (n, n % base)

/-- The original two-output relation, after conversion to the chosen field. -/
def fullRows (F : Type) [NatCast F] (base count : Nat) : List (F × F × F) :=
  (List.range count).map fun (n : Nat) =>
    ((n : F), ((n % base : Nat) : F), ((n / base : Nat) : F))

/-- The slimmer relation used by the actual generated tables. -/
def fieldRows (F : Type) [NatCast F] (base count : Nat) : List (F × F) :=
  (rows base count).map fun (n, byte) => ((n : F), (byte : F))

variable {F : Type} [Field F]

/-- The omitted carry is determined by the input and low digit. No natural
division is performed by the circuit; it multiplies by the field inverse. -/
theorem recover (base n : Nat) (nonzero : (base : F) ≠ 0) :
    ((n : F) - ((n % base : Nat) : F)) / (base : F) = ((n / base : Nat) : F) := by
  apply (div_eq_iff nonzero).2
  have equation := congrArg (fun n : Nat => (n : F)) (Nat.mod_add_div n base)
  rw [Nat.cast_add, Nat.cast_mul] at equation
  exact (sub_eq_iff_eq_add).2 (by simpa only [add_comm, mul_comm] using equation.symm)

/-- Exact before/after lookup equivalence, including the input domain. The
statement remains true over any field in which the base is nonzero; table
input uniqueness is checked separately during ordinary program checking. -/
theorem fullRows_iff (base count : Nat) (nonzero : (base : F) ≠ 0) (input byte carry : F) :
    (input, byte, carry) ∈ fullRows F base count ↔
      (input, byte) ∈ fieldRows F base count ∧ carry = (input - byte) / (base : F) := by
  simp only [fullRows, fieldRows, rows, List.map_map, List.mem_map]
  constructor
  · rintro ⟨n, member, equal⟩
    obtain ⟨rfl, tailEq⟩ := Prod.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj tailEq
    exact ⟨⟨n, member, rfl⟩, (recover base n nonzero).symm⟩
  · rintro ⟨⟨n, member, equal⟩, rfl⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
    exact ⟨n, member, by dsimp only [Function.comp_apply]; rw [recover base n nonzero]⟩

/-- A map returning both coordinates is interchangeable with a byte-only map
followed by carry reconstruction. This uses the same `MapEntry` shape as the
static-map leaves of the circuit derivation model. -/
theorem mapEntries_iff (base count : Nat) (nonzero : (base : F) ≠ 0) (input byte carry : F) :
    (⟨[.field input], .tuple [.field byte, .field carry]⟩ : MapEntry F) ∈
        (fullRows F base count).map (fun (x, lo, hi) => ⟨[.field x], .tuple [.field lo, .field hi]⟩) ↔
      (⟨[.field input], .field byte⟩ : MapEntry F) ∈
        (fieldRows F base count).map (fun (x, lo) => ⟨[.field x], .field lo⟩) ∧
      carry = (input - byte) / (base : F) := by
  simpa [List.mem_map, MapEntry.mk.injEq, Prod.exists, exists_and_left, and_assoc] using
    fullRows_iff base count nonzero input byte carry

end Aiur.Library.Carry
