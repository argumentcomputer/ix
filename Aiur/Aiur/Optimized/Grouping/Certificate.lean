import Aiur.Optimized.Grouping.Payload

namespace Aiur.Optimized.Grouping
open Circuit
variable {F : Type} [Field F] [DecidableEq F]

deriving instance DecidableEq for Lookup
deriving instance DecidableEq for Member

def Member.project (m : Member F) (v : Nat) : Polynomial F := .var (m.columns[v]?.getD 0)

def Implied (constraints : List (Polynomial F)) (p : Polynomial F) : Prop :=
  p.Identical (.const 0) ∨ ∃ q ∈ constraints, p.Identical q

instance (constraints : List (Polynomial F)) (p : Polynomial F) : Decidable (Implied constraints p) := by
  unfold Implied
  infer_instance

theorem Implied.sound {cs : List (Polynomial F)} {p : Polynomial F} (h : Implied cs p)
    (a : Nat → F) (valid : Satisfies cs a) : p.denote a = 0 := by
  rcases h with h | ⟨q, hq, same⟩
  · exact h.denote a
  · exact (same.denote a).trans (valid q hq)

/-- Finite checks over actual output expressions and actual constraints.
All conditions are decidable polynomial/structural comparisons. -/
structure Certificate (sources : List (Chip F)) (g : Layout F) : Prop where
  sources_eq : g.members.map Member.origin = sources
  shapes : ∀ m ∈ g.members, m.Shape
  names : ∀ m ∈ g.members, m.name = m.origin.name
  formed : ∀ m ∈ g.members, m.origin.wellFormed = true
  unique : ∀ m ∈ g.members, ∀ n ∈ g.members, m.selector = n.selector → m = n
  project_payload : ∀ m ∈ g.members,
    ((g.view m).subst (g.back (some m.selector))).Identical ((ofChip m.origin).subst m.project)
  extend_payload : ∀ m ∈ g.members,
    ((g.view m).subst m.embedding).Identical (ofChip m.origin)
  extend_constraints : ∀ m ∈ g.members, ∀ p ∈ g.constraints,
    Implied m.origin.constraints (p.subst m.embedding)
  extend_selectors : ∀ m ∈ g.members, ∀ n ∈ g.members,
    (m.embedding n.selector).Identical (.const (selected (some m.selector) n))
  extend_activation : ∀ m ∈ g.members,
    (g.activation.subst m.embedding).Identical (.const 1)
  zero_constraints : Satisfies g.constraints (fun _ => 0)

instance (sources : List (Chip F)) (g : Layout F) : Decidable (Certificate sources g) := by
  letI : Decidable (Satisfies g.constraints (fun _ => (0 : F))) := by
    unfold Satisfies Scalar.Circuit.Satisfies
    infer_instance
  apply decidable_of_iff ((g.members.map Member.origin = sources) ∧
    (∀ m ∈ g.members, m.Shape) ∧
    (∀ m ∈ g.members, m.name = m.origin.name) ∧
    (∀ m ∈ g.members, m.origin.wellFormed = true) ∧
    (∀ m ∈ g.members, ∀ n ∈ g.members, m.selector = n.selector → m = n) ∧
    (∀ m ∈ g.members,
    ((g.view m).subst (g.back (some m.selector))).Identical ((ofChip m.origin).subst m.project)) ∧
    (∀ m ∈ g.members,
    ((g.view m).subst m.embedding).Identical (ofChip m.origin)) ∧
    (∀ m ∈ g.members, ∀ p ∈ g.constraints,
    Implied m.origin.constraints (p.subst m.embedding)) ∧
    (∀ m ∈ g.members, ∀ n ∈ g.members,
    (m.embedding n.selector).Identical (.const (selected (some m.selector) n))) ∧
    (∀ m ∈ g.members,
    (g.activation.subst m.embedding).Identical (.const 1)) ∧
    (Satisfies g.constraints (fun _ => 0)))
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  · intro h
    exact ⟨h.sources_eq, h.shapes, h.names, h.formed, h.unique, h.project_payload, h.extend_payload, h.extend_constraints, h.extend_selectors, h.extend_activation, h.zero_constraints⟩

namespace Certificate
variable {sources : List (Chip F)} {g : Layout F}

theorem payload_project (checked : Certificate sources g) (m : Member F) (hm : m ∈ g.members)
    (a : Nat → F) (valid : Satisfies g.constraints a)
    (selectors : ∀ n ∈ g.members, a n.selector = selected (some m.selector) n) :
    (g.view m).denote a = (ofChip m.origin).denote (fun v => a (m.columns[v]?.getD 0)) := by
  have same := (checked.project_payload m hm).denote a
  have back := g.back_sound checked.shapes a valid (some m.selector) selectors
  simpa only [Payload.denote_subst, back, Member.project, Scalar.Circuit.ArithExpr.denote] using same

theorem payload_extend (checked : Certificate sources g) (m : Member F) (hm : m ∈ g.members)
    (a : Nat → F) :
    (g.view m).denote (fun v => (m.embedding v).denote a) = (ofChip m.origin).denote a := by
  simpa only [Payload.denote_subst] using (checked.extend_payload m hm).denote a

theorem project_valid (checked : Certificate sources g) (m : Member F) (hm : m ∈ g.members)
    (a : Nat → F) (valid : g.ValidRow rom a) (active : a m.selector = 1) :
    m.origin.ValidAssignment rom (fun v => a (m.columns[v]?.getD 0)) ∧
      (g.view m).denote a = (ofChip m.origin).denote (fun v => a (m.columns[v]?.getD 0)) := by
  obtain ⟨n, hn, _, selectors⟩ := g.select checked.shapes a valid.1 valid.2.1
  have sameSelector : n.selector = m.selector := by
    have h := selectors m hm
    by_contra hne
    simp [selected, hne, active] at h
  have same := checked.unique n hn m hm sameSelector
  subst n
  have payload := checked.payload_project m hm a valid.1 selectors
  have memory := valid.2.2 m hm active
  rw [payload, ofChip_memory] at memory
  let b := fun v : Nat => a (m.columns[v]?.getD 0)
  have on : b m.sourceSelector = 1 := by simpa [b, ← (checked.shapes m hm).1] using active
  have activatedMemory : ∀ lookup ∈ m.source.memory, lookup.Valid rom b := by
    intro lookup present
    obtain ⟨original, ho, rfl⟩ := List.mem_map.mp present
    have originalValid := memory original ho
    have on' : b m.origin.numVars = 1 := on
    simpa only [Activation.memory, MemoryLookup.Valid,
      Activation.polynomial_active m.origin.numVars original.enable b on', b] using originalValid
  have original := (Activation.valid_active_iff m.origin b on).mp
    (g.selected_member_sound m hm a valid.1 on activatedMemory)
  exact ⟨original, payload⟩

theorem extend_valid (checked : Certificate sources g) (m : Member F) (hm : m ∈ g.members)
    (a : Nat → F) (valid : m.origin.ValidAssignment rom a) :
    g.ValidRow rom (fun v => (m.embedding v).denote a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    have h := (checked.extend_constraints m hm p hp).sound a valid.1
    simpa only [Polynomial.denote_subst] using h
  · simpa only [Polynomial.denote_subst, Scalar.Circuit.ArithExpr.denote] using
      (checked.extend_activation m hm).denote a
  · intro n hn on
    have sel := (checked.extend_selectors m hm n hn).denote a
    have sameSelector : m.selector = n.selector := by
      by_contra different
      simp [selected, different, Scalar.Circuit.ArithExpr.denote, on] at sel
    have same := checked.unique m hm n hn sameSelector
    subst n
    rw [checked.payload_extend m hm a, ofChip_memory]
    exact valid.2

/-- The complete emitted row rule is equivalent to the disjunction of the
original source row rules. Selection and source-memory validity are derived,
not premises supplied to this theorem. -/
theorem localRule_iff (checked : Certificate sources g) (rom : WireROM F)
    (root : Message F) (premises : List (Message F)) :
    g.LocalRule rom root premises ↔ ∃ c ∈ sources, c.LocalRule rom root premises := by
  constructor
  · rintro ⟨a, m, hm, valid, active, rootEq, callsEq⟩
    have h := checked.project_valid m hm a valid active
    have finite := m.origin.finiteAssignment (checked.formed m hm)
      (fun v => a (m.columns[v]?.getD 0)) rom
    refine ⟨m.origin, ?_, Row.ofAssignment m.origin.name m.origin.numVars
      (fun v => a (m.columns[v]?.getD 0)), rfl,
      ⟨checked.formed m hm, Row.ofAssignment_length _ _ _, finite.1.mp h.1⟩, ?_, ?_⟩
    · rw [← checked.sources_eq]
      exact List.mem_map.mpr ⟨m, hm, rfl⟩
    · rw [h.2, ofChip_root] at rootEq
      exact finite.2.1.symm.trans rootEq
    · rw [h.2, ofChip_requirements] at callsEq
      exact finite.2.2.symm.trans callsEq
  · rintro ⟨c, hc, row, _, valid, rootEq, callsEq⟩
    rw [← checked.sources_eq] at hc
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hc
    refine ⟨fun v => (m.embedding v).denote row.assignment, m, hm,
      checked.extend_valid m hm row.assignment valid.2.2, ?_, ?_, ?_⟩
    · simpa [selected, Scalar.Circuit.ArithExpr.denote] using
        (checked.extend_selectors m hm m hm).denote row.assignment
    · rw [checked.payload_extend m hm row.assignment, ofChip_root]
      exact rootEq
    · rw [checked.payload_extend m hm row.assignment, ofChip_requirements]
      exact callsEq

end Certificate
end Aiur.Optimized.Grouping
