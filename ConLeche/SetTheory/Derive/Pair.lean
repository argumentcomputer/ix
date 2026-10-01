module

public import ConLeche.SetTheory.Derive.Sep

@[expose] public section

/-!
# Singletons, binary unions, and Kuratowski ordered pairs

Singleton and ordered pair are derived from the unordered pair — the
Kuratowski pair `⟨a, b⟩ := {{a}, {a, b}}` (Kuratowski, Fund. Math. 2
(1921)); binary union is the union of an unordered pair.  The payoff
lemmas are the
injectivity of the Kuratowski pair and the fact that an ordered pair is
never `{∅}` — the tag that keeps the proof point `pt` apart from
function graphs (`Derive/Pt.lean`, `Derive/Graphs.lean`).
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- The singleton `{a}`. -/
noncomputable def sing (a : V) : V := upair a a

theorem mem_sing {z a : V} : z ∈ˢ sing a ↔ z = a := by
  rw [sing, mem_upair]; exact ⟨fun h => h.elim id id, Or.inl⟩

theorem sing_inj {a b : V} (h : sing a = sing b) : a = b :=
  mem_sing.mp (h ▸ mem_sing.mpr rfl)

theorem sUnion_sing (a : V) : sUnion (sing a) = a :=
  ext fun z => by
    rw [mem_sUnion]
    constructor
    · rintro ⟨y, hy, hz⟩; rwa [mem_sing.mp hy] at hz
    · exact fun hz => ⟨a, mem_sing.mpr rfl, hz⟩

/-- Binary union `a ∪ b := ⋃ {a, b}`. -/
noncomputable def binUnion (a b : V) : V := sUnion (upair a b)

theorem mem_binUnion {z a b : V} : z ∈ˢ binUnion a b ↔ z ∈ˢ a ∨ z ∈ˢ b := by
  rw [binUnion, mem_sUnion]
  constructor
  · rintro ⟨y, hy, hz⟩
    rcases mem_upair.mp hy with h | h <;> subst h
    · exact Or.inl hz
    · exact Or.inr hz
  · rintro (hz | hz)
    · exact ⟨a, mem_upair.mpr (Or.inl rfl), hz⟩
    · exact ⟨b, mem_upair.mpr (Or.inr rfl), hz⟩

/-- The Kuratowski ordered pair `⟨a, b⟩ = {{a}, {a, b}}`. -/
noncomputable def kpair (a b : V) : V := upair (sing a) (upair a b)

theorem upair_eq_sing {a b c : V} (h : upair a b = sing c) : a = c ∧ b = c := by
  constructor
  · exact mem_sing.mp (h ▸ mem_upair.mpr (Or.inl rfl))
  · exact mem_sing.mp (h ▸ mem_upair.mpr (Or.inr rfl))

theorem mem_upair_left (a b : V) : a ∈ˢ upair a b := mem_upair.mpr (Or.inl rfl)
theorem mem_upair_right (a b : V) : b ∈ˢ upair a b := mem_upair.mpr (Or.inr rfl)

theorem upair_comm (a b : V) : upair a b = upair b a :=
  ext fun z => by rw [mem_upair, mem_upair]; exact Or.comm

/-- First-component injectivity of the Kuratowski pair. -/
theorem kpair_inj_left {a b c d : V} (h : kpair a b = kpair c d) : a = c := by
  have hac : sing a ∈ˢ kpair c d := h ▸ mem_upair_left (sing a) (upair a b)
  rcases mem_upair.mp hac with h1 | h1
  · exact sing_inj h1
  · -- `{a} = {c, d}`, so `c = a` (and `d = a`).
    obtain ⟨hc, -⟩ := upair_eq_sing (h1.symm)
    exact hc.symm

theorem kpair_inj {a b c d : V} (h : kpair a b = kpair c d) : a = c ∧ b = d := by
  obtain rfl : a = c := kpair_inj_left h
  refine ⟨rfl, ?_⟩
  -- `{a, b} ∈ {{a}, {a, d}}` and `{a, d} ∈ {{a}, {a, b}}`.
  have hb : upair a b ∈ˢ kpair a d := by
    rw [← h]; exact mem_upair_right _ _
  have hd : upair a d ∈ˢ kpair a b := by
    rw [h]; exact mem_upair_right _ _
  rcases mem_upair.mp hb with h1 | h1
  · -- `{a, b} = {a}`, so `b = a`; then `{a, d}` collapses too, so `d = a = b`.
    obtain ⟨-, hba⟩ := upair_eq_sing h1
    rcases mem_upair.mp hd with h2 | h2
    · obtain ⟨-, hda⟩ := upair_eq_sing h2
      exact hba.trans hda.symm
    · -- `{a, d} = {a, b}`: `d` is `a` or `b`, and `b = a` closes both.
      rcases mem_upair.mp (h2 ▸ mem_upair_right a d) with hda | hdb
      · exact hba.trans hda.symm
      · exact hdb.symm
  · -- `{a, b} = {a, d}`: `b` is `a` or `d`.
    rcases mem_upair.mp (h1 ▸ mem_upair_right a b) with hba | hbd
    · -- `b = a`; then `d ∈ {a, d} = {a, b} = {a, a}`, so `d = a = b`.
      rcases mem_upair.mp (h1.symm ▸ mem_upair_right a d) with hda | hdb
      · exact hba.trans hda.symm
      · exact hdb.symm
    · exact hbd

theorem kpair_ne_empty {a b : V} : kpair a b ≠ empty :=
  ne_empty_of_mem (mem_upair_left (sing a) (upair a b))

/-- Every member of a Kuratowski pair is nonempty — the fact that keeps
`{∅}` (the proof point) out of the pair/graph world. -/
theorem mem_kpair_nonempty {a b z : V} (hz : z ∈ˢ kpair a b) : ∃ w, w ∈ˢ z := by
  rcases mem_upair.mp hz with h | h <;> subst h
  · exact ⟨a, mem_sing.mpr rfl⟩
  · exact ⟨a, mem_upair_left a b⟩

theorem mem_sUnion_kpair_left (a b : V) : a ∈ˢ sUnion (kpair a b) :=
  mem_sUnion.mpr ⟨sing a, mem_upair_left _ _, mem_sing.mpr rfl⟩

theorem mem_sUnion_kpair_right (a b : V) : b ∈ˢ sUnion (kpair a b) :=
  mem_sUnion.mpr ⟨upair a b, mem_upair_right _ _, mem_upair_right a b⟩

end ConLeche.SetTheory
