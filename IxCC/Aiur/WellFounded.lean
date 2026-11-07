import IxCC.Aiur.Finite
import IxCC.Aiur.Trace
import Ix.Aiur.Compiler.UnitCounter

/-! A mixed static-order / unit-counter / ranked trace argument. The
certificate records properties of extracted rows. Proving that a bytecode
certificate and the keyed AIR establish those properties is separate work.
-/

namespace IxCC.Aiur

open _root_.Aiur (G gSize)

structure RowFacts where
  order : Nat
  counter : G
  rank : Nat

structure StaticCertificate (Row : Type) (requiresRel : Row → Row → Prop) where
  facts : Row → RowFacts
  /-- One choice per static component, never a witness choice per edge. -/
  ranked : Nat → Bool
  edge : ∀ child parent, requiresRel child parent →
    (facts parent).order < (facts child).order ∨
    ((facts parent).order = (facts child).order ∧
      if ranked (facts parent).order then (facts parent).rank < (facts child).rank
      else (facts child).counter = (facts parent).counter + 1)

namespace StaticCertificate

variable {Row : Type} {requiresRel : Row → Row → Prop} (certificate : StaticCertificate Row requiresRel)

def ClosedWalk (_certificate : StaticCertificate Row requiresRel) (walk : Nat → Row) (length : Nat) : Prop :=
  (∀ i, i < length → requiresRel (walk (i + 1)) (walk i)) ∧ walk length = walk 0

theorem order_mono (walk : Nat → Row) (length : Nat)
    (edges : ∀ i, i < length → requiresRel (walk (i + 1)) (walk i)) :
    ∀ i, i ≤ length → (certificate.facts (walk 0)).order ≤ (certificate.facts (walk i)).order := by
  intro i
  induction i with
  | zero => intro _; exact Nat.le_refl _
  | succ i ih =>
    intro bounded
    have edge := certificate.edge _ _ (edges i (by omega))
    have := ih (by omega)
    rcases edge with edge | ⟨edge, _⟩ <;> omega

theorem closed_order (walk : Nat → Row) (length : Nat)
    (closed : certificate.ClosedWalk walk length) :
    ∀ i, i ≤ length → (certificate.facts (walk i)).order = (certificate.facts (walk 0)).order := by
  intro i bounded
  have lower := certificate.order_mono walk length closed.1 i bounded
  have upper := certificate.order_mono (fun k => walk (i + k)) (length - i)
    (fun k hk => by simpa [Nat.add_assoc] using closed.1 (i + k) (by omega))
    (length - i) (Nat.le_refl _)
  have finish : i + (length - i) = length := by omega
  simp only [Nat.add_zero, finish, closed.2] at upper
  omega

/-- Every short cycle remains in one component. There it either strictly
increases a natural rank or advances a field counter by one on every edge. -/
theorem noShortCycle (walk : Nat → Row) (length : Nat)
    (positive : 0 < length) (short : length < gSize.toNat)
    (closed : certificate.ClosedWalk walk length) : False := by
  have same := certificate.closed_order walk length closed
  have steps : ∀ i, i < length →
      if certificate.ranked (certificate.facts (walk 0)).order then
        (certificate.facts (walk i)).rank < (certificate.facts (walk (i + 1))).rank
      else (certificate.facts (walk (i + 1))).counter = (certificate.facts (walk i)).counter + 1 := by
    intro i bounded
    have left := same i (by omega)
    have right := same (i + 1) (by omega)
    rcases certificate.edge _ _ (closed.1 i bounded) with order | ⟨_, step⟩
    · omega
    · simpa only [left] using step
  by_cases ranked : certificate.ranked (certificate.facts (walk 0)).order = true
  · have increasing : ∀ i, i ≤ length →
        (certificate.facts (walk 0)).rank + i ≤ (certificate.facts (walk i)).rank := by
      intro i
      induction i with
      | zero => intro _; omega
      | succ i ih =>
        intro bounded
        have previous := ih (by omega)
        have step := steps i (by omega)
        simp only [ranked, ↓reduceIte] at step
        omega
    have impossible := increasing length (Nat.le_refl _)
    rw [closed.2] at impossible
    omega
  · have counter := _root_.Aiur.Bytecode.UnitCounter.Proofs.no_short_field_cycle
      (fun i => (certificate.facts (walk i)).counter) positive short
      (fun i hi => by simpa [ranked] using steps i hi)
    exact counter (by rw [closed.2])

theorem wellFounded {n : Nat} {requiresRel : Fin n → Fin n → Prop}
    (certificate : StaticCertificate (Fin n) requiresRel) (bound : n < gSize.toNat) :
    WellFounded requiresRel := by
  apply Finite.wellFounded_of_noShortCycle
  intro walk length positive bounded edges closed
  exact certificate.noShortCycle walk length positive (by omega) ⟨edges, closed⟩

end StaticCertificate

theorem Trace.static_wellFounded (trace : Trace) (bound : trace.WithinCharacteristic)
    (certificate : StaticCertificate trace.RowId trace.Requires) : WellFounded trace.Requires :=
  certificate.wellFounded (trace.rows_lt bound)

end IxCC.Aiur
