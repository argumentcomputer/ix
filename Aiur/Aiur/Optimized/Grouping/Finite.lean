import Aiur.Optimized.Grouping.Payload

namespace Aiur.Optimized.Grouping
open Circuit
variable {F : Type} [Field F] [DecidableEq F]

def restrict (width v : Nat) : Polynomial F :=
  if v < width then .var v else .const 0

omit [DecidableEq F] in
@[simp] theorem restrict_denote (width v : Nat) (a : Nat → F) (name : String) :
    (restrict width v).denote a = (Row.ofAssignment name width a).assignment v := by
  by_cases inside : v < width
  · simp [restrict, inside, Scalar.Circuit.ArithExpr.denote,
      Row.ofAssignment_agree _ _ _ _ inside]
  · simp [restrict, inside, Scalar.Circuit.ArithExpr.denote, Row.assignment,
      Scalar.Circuit.Row.assignment, Row.ofAssignment]

/-- Truncating the assignment to the actual exported row width must preserve
every equation and decoded payload. This prevents completeness from relying
on an infinite assignment with values outside the allocated columns. -/
def Layout.FiniteCertificate (g : Layout F) : Prop :=
  (∀ p ∈ g.constraints, (p.subst (restrict g.width)).Identical p) ∧
  (g.activation.subst (restrict g.width)).Identical g.activation ∧
  ∀ m ∈ g.members, m.selector < g.width ∧
    ((g.view m).subst (restrict g.width)).Identical (g.view m)

instance (g : Layout F) : Decidable g.FiniteCertificate := by
  unfold Layout.FiniteCertificate
  infer_instance

theorem Layout.finiteAssignment (g : Layout F) (checked : g.FiniteCertificate)
    (a : Nat → F) (valid : g.ValidRow rom a) :
    let row := Row.ofAssignment g.name g.width a
    g.ValidRow rom row.assignment ∧
      ∀ m ∈ g.members, (g.view m).denote row.assignment = (g.view m).denote a := by
  have payload (m : Member F) (hm : m ∈ g.members) :
      (g.view m).denote (Row.ofAssignment g.name g.width a).assignment = (g.view m).denote a := by
    simpa only [Payload.denote_subst, restrict_denote g.width _ a g.name] using
      (checked.2.2 m hm).2.denote a
  refine ⟨⟨?_, ?_, ?_⟩, payload⟩
  · intro p hp
    have same := (checked.1 p hp).denote a
    simpa only [Polynomial.denote_subst, restrict_denote g.width _ a g.name, valid.1 p hp] using same
  · have same := checked.2.1.denote a
    simpa only [Polynomial.denote_subst, restrict_denote g.width _ a g.name, valid.2.1] using same
  · intro m hm on
    rw [payload m hm]
    apply valid.2.2 m hm
    simpa only [Row.ofAssignment_agree _ _ _ _ (checked.2.2 m hm).1] using on

/-- The physical rule uses a finite row with exactly the exported width. -/
def Layout.RowRule (g : Layout F) (rom : WireROM F) (root : Message F)
    (premises : List (Message F)) : Prop :=
  ∃ (row : Row F) (m : Member F), row.chip = g.name ∧ row.values.length = g.width ∧ m ∈ g.members ∧
    g.ValidRow rom row.assignment ∧ row.assignment m.selector = 1 ∧
    ((g.view m).denote row.assignment).root = root ∧
    ((g.view m).denote row.assignment).requirements = premises

theorem Layout.rowRule_iff (g : Layout F) (checked : g.FiniteCertificate)
    (rom : WireROM F) (root : Message F) (premises : List (Message F)) :
    g.RowRule rom root premises ↔ g.LocalRule rom root premises := by
  constructor
  · rintro ⟨row, m, _, _, hm, valid, active, rootEq, callsEq⟩
    exact ⟨row.assignment, m, hm, valid, active, rootEq, callsEq⟩
  · rintro ⟨a, m, hm, valid, active, rootEq, callsEq⟩
    have finite := g.finiteAssignment checked a valid
    refine ⟨Row.ofAssignment g.name g.width a, m, rfl, Row.ofAssignment_length _ _ _,
      hm, finite.1, ?_, ?_, ?_⟩
    · simpa only [Row.ofAssignment_agree _ _ _ _ (checked.2.2 m hm).1] using active
    · simpa only [finite.2 m hm] using rootEq
    · simpa only [finite.2 m hm] using callsEq

end Aiur.Optimized.Grouping
