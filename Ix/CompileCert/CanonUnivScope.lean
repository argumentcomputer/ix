import Ix.CompileCert.CanonUnivEmit
import IxC.Kernel.Ixon.Reader
import IxC.Kernel.Verify.Level

/-! Parameter-scope preservation for production canonical universes and their
certified reader interpretation. Canonicalization introduces no parameters
(`canonUniv_occurs`), so a bound on the raw universe's variables bounds the
canonical one's; the certified reader's reading of a canonical universe has
the raw universe's value (`convCanon_eval`) and mentions only the member's
level parameters (`convCanon_defined`, `convCanon_defined_id`). Level
parameters are positions (`Kernel.LevelParam := Nat`). -/

namespace Ix.CompileCert.CanonUnivScope

open Ixon Ixon.CanonUniv Ix.CompileCert.CanonUnivMeaning Ix.CompileCert.CanonUnivEmit

def Occurs (parameter : UInt64) : Univ → Prop
  | .zero => False
  | .var other => parameter = other
  | .succ body => Occurs parameter body
  | .max left right | .imax left right => Occurs parameter left ∨ Occurs parameter right

/-- The emitter's imax nodes always have a variable on their right. Thus a
syntactic parameter cannot be hidden beneath an always-zero imax branch. -/
inductive Shape : Univ → Prop where
  | zero : Shape .zero
  | var (parameter : UInt64) : Shape (.var parameter)
  | succ {body} : Shape body → Shape (.succ body)
  | max {left right} : Shape left → Shape right → Shape (.max left right)
  | gate {body} (parameter : UInt64) : Shape body → Shape (.imax body (.var parameter))

theorem Shape.addSuccs {body : Univ} (shape : Shape body) (count : Nat) : Shape (Univ.addSuccs body count) := by
  induction count with
  | zero => exact shape
  | succ count ih => exact Shape.succ ih

theorem Shape.gated {body : Univ} (shape : Shape body) (order : List UInt64) : Shape (emitGated order body) := by
  induction order with
  | nil => exact shape
  | cons parameter rest ih => rw [emitGated_cons]; exact Shape.gate parameter ih

theorem shape_maxFold (terms : List Univ) (seed : Univ) (start : Shape seed)
    (each : ∀ term ∈ terms, Shape term) : Shape (terms.foldl (fun acc term => Univ.max term acc) seed) := by
  induction terms generalizing seed with
  | nil => exact start
  | cons term rest ih =>
    rw [List.foldl_cons]
    exact ih _ (Shape.max (each term (by simp)) start) (fun term member => each term (by simp [member]))

theorem shape_maxChain (terms : List Univ) (each : ∀ term ∈ terms, Shape term) : Shape (maxChain terms) := by
  unfold maxChain
  cases reversed : terms.reverse with
  | nil => exact Shape.zero
  | cons last rest =>
    have reversedEach : ∀ term ∈ last :: rest, Shape term := by
      intro term member
      apply each term
      have : term ∈ terms.reverse := by rwa [reversed]
      simpa using this
    exact shape_maxFold rest last (reversedEach last (by simp))
      (fun term member => reversedEach term (by simp [member]))

theorem atomTerm_shape (consumed : Markers) (context : CPath) (entry : UInt64 × Nat) {term : Univ}
    (present : atomTerm consumed context entry = some term) : Shape term := by
  unfold atomTerm at present
  split at present
  · cases present
  · cases Option.some.inj present
    exact (Shape.var _).addSuccs _

theorem retainedTerms_shape (consumed : Markers) (context : CPath) (group : CGroup) :
    ∀ term ∈ retainedTerms consumed context group, Shape term := by
  intro term member
  unfold retainedTerms at member
  rcases List.mem_append.mp member with atom | constant
  · obtain ⟨entry, _, present⟩ := List.mem_filterMap.mp atom
    exact atomTerm_shape consumed context entry present
  · split at constant
    · have same : term = Univ.addSuccs .zero group.constant := by simpa using constant
      subst term
      exact Shape.zero.addSuccs _
    · cases constant

theorem groupOutput_shape (norm : CNorm) (consumed : Markers) (context : CPath) (group : CGroup)
    {term : Univ} (present : groupOutput norm consumed context group = some term) : Shape term := by
  unfold groupOutput at present
  split at present
  · cases present
  · split at present
    · cases present
    · cases Option.some.inj present
      exact (shape_maxChain _ (retainedTerms_shape consumed context group)).gated _

theorem rootPass_shape (norm : CNorm) (groups : Groups) (consumed : Markers) :
    ∀ term ∈ (rootPass norm groups consumed).1, Shape term := by
  intro term member
  cases found : groups.find? [] with
  | none => simp [rootPass, found] at member
  | some group =>
    rw [rootPass_terms norm groups consumed found] at member
    obtain ⟨entry, _, present⟩ := List.mem_filterMap.mp member
    exact atomTerm_shape consumed [] entry present

theorem finishEmission_shape (root : Nat) (absorbed : Bool) (terms : List Univ)
    (each : ∀ term ∈ terms, Shape term) : Shape (finishEmission root absorbed terms) := by
  unfold finishEmission
  split
  · apply shape_maxChain
    intro term member
    rcases List.mem_append.mp member with old | added
    · exact each term old
    · have same : term = Univ.addSuccs .zero root := by simpa using added
      subst term
      exact Shape.zero.addSuccs _
  · exact shape_maxChain terms each

theorem emitGroups_shape (norm : CNorm) (groups : Groups) (consumed : Markers) :
    Shape (emitGroups norm groups consumed) := by
  rw [emitGroups_terms]
  apply finishEmission_shape
  intro term member
  rcases List.mem_append.mp member with root | group
  · exact rootPass_shape norm groups consumed term root
  · obtain ⟨⟨context, value⟩, _, present⟩ := List.mem_filterMap.mp group
    exact groupOutput_shape norm consumed context value present

theorem canonUniv_shape (source : Univ) : Shape (canonUniv source) := by
  unfold canonUniv
  rw [linearize_phases]
  exact emitGroups_shape _ _ _

theorem Shape.parameter_le {source : Univ} (shape : Shape source) (ρ : UInt64 → Nat)
    (positive : ∀ parameter, 0 < ρ parameter) {parameter : UInt64} (occurs : Occurs parameter source) :
    ρ parameter ≤ univEval ρ source := by
  induction shape with
  | zero => cases occurs
  | var other => cases occurs; exact Nat.le_refl _
  | succ shape ih =>
    have bound := ih occurs
    simp only [univEval]
    omega
  | max left right leftIH rightIH =>
    rcases occurs with first | second
    · exact Nat.le_trans (leftIH first) (Nat.le_max_left _ _)
    · exact Nat.le_trans (rightIH second) (Nat.le_max_right _ _)
  | gate gate shape ih =>
    simp only [univEval, Nat.ne_of_gt (positive gate), ↓reduceIte]
    rcases occurs with left | same
    · exact Nat.le_trans (ih left) (Nat.le_max_left _ _)
    · cases same; exact Nat.le_max_right _ _

theorem univEval_ext (source : Univ) (first second : UInt64 → Nat)
    (agree : ∀ parameter, Occurs parameter source → first parameter = second parameter) :
    univEval first source = univEval second source := by
  induction source with
  | zero => rfl
  | var parameter => exact agree parameter rfl
  | succ body ih => simp only [univEval, ih agree]
  | max left right leftIH rightIH =>
    simp only [univEval, leftIH (fun parameter occurs => agree parameter (Or.inl occurs)),
      rightIH (fun parameter occurs => agree parameter (Or.inr occurs))]
  | imax left right leftIH rightIH =>
    simp only [univEval, leftIH (fun parameter occurs => agree parameter (Or.inl occurs)),
      rightIH (fun parameter occurs => agree parameter (Or.inr occurs))]

/-- Canonicalization introduces no syntactic parameters. A fresh parameter
would dominate the output under a positive separating valuation, contradicting
the established value equality and the input's independence from that parameter. -/
theorem canonUniv_occurs (source : Univ) (parameter : UInt64)
    (present : Occurs parameter (canonUniv source)) : Occurs parameter source := by
  by_contra absent
  let baseline := univEval (fun _ => 1) source
  let ρ : UInt64 → Nat := fun query => if query = parameter then baseline + 1 else 1
  have positive : ∀ query, 0 < ρ query := by intro query; simp only [ρ]; split <;> omega
  have same : univEval ρ source = baseline := by
    apply univEval_ext source ρ (fun _ => 1)
    intro query occurs
    have different : query ≠ parameter := by intro equal; subst query; exact absent occurs
    simp [ρ, different]
  have bound := (canonUniv_shape source).parameter_le ρ positive present
  rw [canonUniv_eval, same] at bound
  have selected : ρ parameter = baseline + 1 := by simp [ρ]
  rw [selected] at bound
  omega


theorem canonUniv_bounded (source : Univ) (count : Nat)
    (bounded : ∀ parameter, Occurs parameter source → parameter.toNat < count) :
    ∀ parameter, Occurs parameter (canonUniv source) → parameter.toNat < count :=
  fun parameter occurs => bounded parameter (canonUniv_occurs source parameter occurs)

/-! ## The certified reader's reading

The reader reads a universe-table entry with `Kernel.Reader.convUniv param`,
where variable `i` is the level parameter `param i`: `id` for every member
but a recursor, whose variable `i` is its `i`-th level parameter
(`Kernel.Reader.recParam`). Level parameters are positions
(`Kernel.LevelParam := Nat`), so a valuation of the reader's level is a
valuation of positions, and the reading of a canonical entry has the value of
the raw compiled universe. -/

theorem convUniv_eval (param : Nat → Kernel.LevelParam) (φ : Kernel.LevelParam → Nat)
    (source : Univ) :
    Kernel.Level.eval φ (Kernel.Reader.convUniv param source) =
      univEval (fun index => φ (param index.toNat)) source := by
  induction source <;> simp_all [Kernel.Reader.convUniv, Kernel.Level.eval, univEval]

/-- **The universe bridge.** The certified reader's reading of the
canonical form of a compiled universe has, under every valuation of the
reader's level parameters, the value of the compiled universe itself. -/
theorem convCanon_eval (param : Nat → Kernel.LevelParam) (φ : Kernel.LevelParam → Nat)
    (source : Univ) :
    Kernel.Level.eval φ (Kernel.Reader.convUniv param (canonUniv source)) =
      univEval (fun index => φ (param index.toNat)) source := by
  rw [convUniv_eval, canonUniv_eval]

theorem convUniv_defined (source : Univ) (param : Nat → Kernel.LevelParam)
    (params : List Kernel.LevelParam)
    (allowed : ∀ parameter, Occurs parameter source → param parameter.toNat ∈ params) :
    Kernel.Level.allParamsDefined params (Kernel.Reader.convUniv param source) = true := by
  induction source with
  | zero => rfl
  | var parameter =>
    simpa [Kernel.Reader.convUniv, Kernel.Level.allParamsDefined] using allowed parameter rfl
  | succ body ih => exact ih allowed
  | max left right leftIH rightIH =>
    exact Bool.and_eq_true_iff.mpr ⟨leftIH (fun parameter occurs => allowed parameter (Or.inl occurs)),
      rightIH (fun parameter occurs => allowed parameter (Or.inr occurs))⟩
  | imax left right leftIH rightIH =>
    exact Bool.and_eq_true_iff.mpr ⟨leftIH (fun parameter occurs => allowed parameter (Or.inl occurs)),
      rightIH (fun parameter occurs => allowed parameter (Or.inr occurs))⟩

theorem recParam_mem (params : List Kernel.LevelParam) (index : Nat) (inside : index < params.length) :
    Kernel.Reader.recParam params index ∈ params := by
  unfold Kernel.Reader.recParam
  rw [List.getD_eq_getElem?_getD, getElem?_pos params index inside, Option.getD_some]
  exact List.getElem_mem inside

/-- A recursor's reading of a canonical universe whose raw form uses only
its first `params.length` variables mentions only its level parameters. -/
theorem convCanon_defined (source : Univ) (params : List Kernel.LevelParam)
    (bounded : ∀ parameter, Occurs parameter source → parameter.toNat < params.length) :
    Kernel.Level.allParamsDefined params
      (Kernel.Reader.convUniv (Kernel.Reader.recParam params) (canonUniv source)) = true :=
  convUniv_defined (canonUniv source) (Kernel.Reader.recParam params) params
    (fun parameter occurs => recParam_mem params parameter.toNat
      (canonUniv_bounded source params.length bounded parameter occurs))

/-- Every other member's reading (`param := id`, level parameters
`[0, …, count - 1]`) of a canonical universe whose raw form uses only its
first `count` variables mentions only its level parameters. -/
theorem convCanon_defined_id (source : Univ) (count : Nat)
    (bounded : ∀ parameter, Occurs parameter source → parameter.toNat < count) :
    Kernel.Level.allParamsDefined (List.range count)
      (Kernel.Reader.convUniv id (canonUniv source)) = true :=
  convUniv_defined (canonUniv source) id (List.range count)
    (fun parameter occurs => List.mem_range.mpr (canonUniv_bounded source count bounded parameter occurs))

end Ix.CompileCert.CanonUnivScope
