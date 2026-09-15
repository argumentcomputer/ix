module
public import Ix.MultiStark.Verify.Protocol.Arithmetic
public import Ix.MultiStark.Verify.Proofs.Basic

public section

namespace MultiStark.Verify.Proofs

theorem extension_beq_iff_eq (left right : Ext) : (left == right) = true ↔ left = right := by
  cases left with
  | mk l0 l1 =>
    cases right with
    | mk r0 r1 =>
      change ((l0 == r0) && (l1 == r1)) = true ↔ _
      simp only [Bool.and_eq_true, beq_iff_eq, Ix.Ixby.ExtGoldilocks.mk.injEq]

theorem inverseBase_refines (value result : Field) :
    Arithmetic.inverseBase value = .ok result ↔ Protocol.BaseInverse value result := by
  by_cases zero : value.val = 0 <;> simp [Arithmetic.inverseBase, Protocol.BaseInverse, zero]

theorem inverse_refines (value result : Ext) :
    Arithmetic.inverse value = .ok result ↔ Protocol.ExtensionInverse value result := by
  simp only [Arithmetic.inverse, bind_ok_iff, pure_ok_iff, inverseBase_refines,
    Protocol.BaseInverse, Protocol.ExtensionInverse, Ix.Ixby.ExtGoldilocks.inverse,
    and_assoc, exists_and_left, exists_eq_left']

theorem divide_refines (left right result : Ext) :
    Arithmetic.divide left right = .ok result ↔ Protocol.Division left right result := by
  simp only [Arithmetic.divide, bind_ok_iff, pure_ok_iff, inverse_refines, Protocol.Division]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- A finite kernel proof, not a native-evaluation axiom or an imported
runtime table assertion. The specification computes powers of one root;
the executable verifier uses a separately written 33-entry table. -/
theorem generator_table : ∀ bits : Fin 33,
    (Arithmetic.twoAdicGenerator bits.val).toOption = some (Protocol.generator bits.val) := by decide

theorem twoAdicGenerator_refines (bits : Nat) (value : Field) :
    Arithmetic.twoAdicGenerator bits = .ok value ↔ Protocol.TwoAdicGenerator bits value := by
  by_cases bounded : bits ≤ 32
  · have table := generator_table ⟨bits, by omega⟩
    cases computed : Arithmetic.twoAdicGenerator bits with
    | error error => simp [computed, Except.toOption] at table
    | ok result =>
      have equal : result = Protocol.generator bits := by simpa [computed, Except.toOption] using table
      simp only [equal, Except.ok.injEq, Protocol.TwoAdicGenerator, bounded, true_and]
  · have outside : 33 ≤ bits := by omega
    unfold Arithmetic.twoAdicGenerator
    rw [Array.getElem?_eq_none (by simpa using outside)]
    simp [Protocol.TwoAdicGenerator, bounded]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem generator_order : ∀ bits : Fin 33,
    (Protocol.generator bits.val).pow (2 ^ bits.val) = 1 ∧
      (0 < bits.val → (Protocol.generator bits.val).pow (2 ^ (bits.val - 1)) ≠ 1) := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem generator_normalization_nonzero : ∀ bits : Fin 33,
    ((Ix.Ixby.Goldilocks.reduce (2 ^ bits.val)).mul (Protocol.generator bits.val)).val ≠ 0 := by decide

end MultiStark.Verify.Proofs
