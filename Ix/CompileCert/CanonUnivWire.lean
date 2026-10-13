import Ix.CompileCert.CanonUnivEmit
import IxC.Ixon.Wire

/-! Wire bounds for the production universe canonicalizer. Its emitted imax
gates have a variable on the right, so evaluating every variable at one
bounds every successor chain in the output, including inside gates. -/

namespace Ix.CompileCert.CanonUnivWire

open Ixon Ixon.CanonUniv Ix.CompileCert.CanonUnivMeaning
open Ix.CompileCert.CanonUnivEmit

/-- The output grammar of the production linearizer. -/
def Shape : Univ → Prop
  | .zero | .var _ => True
  | .succ child => Shape child
  | .max left right => Shape left ∧ Shape right
  | .imax left right => Shape left ∧ ∃ parameter, right = .var parameter

theorem succCount_le_eval (value : Univ) (valuation : UInt64 → Nat) :
    value.succCountNat ≤ univEval valuation value := by
  induction value <;> simp_all [Univ.succCountNat, univEval]
  omega

theorem Shape.wire {value : Univ} (shape : Shape value)
    (bounded : univEval (fun _ => 1) value < UInt64.size) : value.wireWF := by
  induction value with
  | zero => trivial
  | var _ => trivial
  | succ child ih =>
    refine ⟨Nat.lt_of_le_of_lt (succCount_le_eval _ _) bounded, ih shape ?_⟩
    change univEval (fun _ => 1) child + 1 < UInt64.size at bounded
    omega
  | max left right ihLeft ihRight =>
    change max (univEval (fun _ => 1) left) (univEval (fun _ => 1) right) < UInt64.size at bounded
    exact ⟨ihLeft shape.1 (by omega), ihRight shape.2 (by omega)⟩
  | imax left right ihLeft _ =>
    obtain ⟨leftShape, parameter, rfl⟩ := shape
    simp only [univEval, Nat.one_ne_zero, ↓reduceIte] at bounded
    exact ⟨ihLeft leftShape (by omega), trivial⟩

theorem Shape.addSuccs {value : Univ} (shape : Shape value) (count : Nat) :
    Shape (Univ.addSuccs value count) := by
  induction count with
  | zero => exact shape
  | succ count ih => exact ih

theorem maxFold_shape (terms : List Univ) (seed : Univ) (start : Shape seed)
    (each : ∀ term ∈ terms, Shape term) :
    Shape (terms.foldl (fun acc term => Univ.max term acc) seed) := by
  induction terms generalizing seed with
  | nil => exact start
  | cons term rest ih =>
    exact ih (.max term seed) ⟨each term (by simp), start⟩ (fun value member => each value (by simp [member]))

theorem maxChain_shape (terms : List Univ) (each : ∀ term ∈ terms, Shape term) : Shape (maxChain terms) := by
  unfold maxChain
  have reversed : ∀ term ∈ terms.reverse, Shape term := by simpa using each
  cases same : terms.reverse with
  | nil => trivial
  | cons last rest =>
    rw [same] at reversed
    exact maxFold_shape rest last (reversed last (by simp)) (fun term member => reversed term (by simp [member]))

theorem emitGated_shape (order : List UInt64) (body : Univ) (shape : Shape body) :
    Shape (emitGated order body) := by
  induction order with
  | nil => exact shape
  | cons parameter rest ih =>
    rw [emitGated_cons]
    exact ⟨ih, parameter, rfl⟩

theorem atomTerm_shape (consumed : Markers) (context : CPath) (entry : UInt64 × Nat)
    (value : Univ) (emitted : atomTerm consumed context entry = some value) : Shape value := by
  unfold atomTerm at emitted
  split at emitted
  · cases emitted
  · cases Option.some.inj emitted
    exact Shape.addSuccs (value := .var entry.1) trivial entry.2

theorem retainedTerms_shape (consumed : Markers) (context : CPath) (group : CGroup) :
    ∀ value ∈ retainedTerms consumed context group, Shape value := by
  intro value member
  rw [retainedTerms, List.mem_append] at member
  rcases member with atom | constant
  · obtain ⟨entry, _, emitted⟩ := List.mem_filterMap.mp atom
    exact atomTerm_shape consumed context entry value emitted
  · split at constant
    · obtain rfl := List.mem_singleton.mp constant
      exact Shape.addSuccs (value := .zero) trivial group.constant
    · cases constant

theorem groupOutput_shape (norm : CNorm) (consumed : Markers) (context : CPath) (group : CGroup)
    (value : Univ) (emitted : groupOutput norm consumed context group = some value) : Shape value := by
  unfold groupOutput at emitted
  split at emitted
  · cases emitted
  · split at emitted
    · cases emitted
    · cases Option.some.inj emitted
      exact emitGated_shape _ _ (maxChain_shape _ (retainedTerms_shape consumed context group))

theorem rootPass_shape (norm : CNorm) (groups : Groups) (consumed : Markers) :
    ∀ value ∈ (rootPass norm groups consumed).1, Shape value := by
  unfold rootPass
  cases groups.find? [] with
  | none => simp
  | some group =>
    dsimp only
    rw [rootLoop_eq]
    intro value member
    obtain ⟨entry, _, emitted⟩ := List.mem_filterMap.mp member
    exact atomTerm_shape consumed [] entry value emitted

theorem finishEmission_shape (root : Nat) (absorbed : Bool) (terms : List Univ)
    (each : ∀ value ∈ terms, Shape value) : Shape (finishEmission root absorbed terms) := by
  unfold finishEmission
  split
  · apply maxChain_shape
    intro value member
    rcases List.mem_append.mp member with old | constant
    · exact each value old
    · obtain rfl := List.mem_singleton.mp constant
      exact Shape.addSuccs (value := .zero) trivial root
  · exact maxChain_shape terms each

theorem emitGroups_shape (norm : CNorm) (groups : Groups) (consumed : Markers) :
    Shape (emitGroups norm groups consumed) := by
  rw [emitGroups_terms]
  apply finishEmission_shape
  intro value member
  rcases List.mem_append.mp member with root | group
  · exact rootPass_shape norm groups consumed value root
  · obtain ⟨entry, _, emitted⟩ := List.mem_filterMap.mp group
    exact groupOutput_shape norm consumed entry.1 entry.2 value emitted

theorem linearize_shape (norm : CNorm) : Shape (linearize norm) := by
  rw [linearize_phases]
  exact emitGroups_shape _ _ _

theorem canonUniv_wire (source : Univ)
    (bounded : univEval (fun _ => 1) source < UInt64.size) : (canonUniv source).wireWF := by
  apply (linearize_shape (normalize source)).wire
  change univEval (fun _ => 1) (canonUniv source) < UInt64.size
  rw [canonUniv_eval]
  exact bounded

end Ix.CompileCert.CanonUnivWire
