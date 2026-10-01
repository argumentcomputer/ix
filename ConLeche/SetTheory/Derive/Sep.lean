module

public import ConLeche.SetTheory.Derive.Empty

@[expose] public section

/-!
# Separation, derived from replacement

The classical trick: to separate `{x ∈ a : p x}`, either the result is
empty (take `empty`), or some witness `w₀ ∈ a` with `p w₀` exists and
the total function `x ↦ if p x then x else w₀` replaces `a` onto
exactly the separated set (the default value `w₀` is already a member
of it).  The detour is forced because replacement's antecedent demands
totality.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

open Classical in
/-- Separation: `{x ∈ a : p x}`, for an arbitrary meta-level predicate. -/
noncomputable def sep (a : V) (p : V → Prop) : V :=
  if h : ∃ x, x ∈ˢ a ∧ p x then
    image (fun x => if p x then x else Classical.choose h) a
  else empty

theorem mem_sep {a z : V} {p : V → Prop} : z ∈ˢ sep a p ↔ z ∈ˢ a ∧ p z := by
  unfold sep
  split
  · next h =>
    obtain ⟨hw₀a, hw₀p⟩ := Classical.choose_spec h
    rw [mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      split
      · next hpw => exact ⟨hw, hpw⟩
      · exact ⟨hw₀a, hw₀p⟩
    · rintro ⟨hz, hp⟩
      exact ⟨z, hz, by simp [hp]⟩
  · next h =>
    constructor
    · intro hz; exact absurd hz (not_mem_empty z)
    · intro ⟨hz, hp⟩; exact absurd ⟨z, hz, hp⟩ h

theorem sep_subset {a : V} {p : V → Prop} : sep a p ⊆ˢ a :=
  fun _ hz => (mem_sep.mp hz).1

theorem sep_congr {a : V} {p q : V → Prop} (h : ∀ x, x ∈ˢ a → (p x ↔ q x)) :
    sep a p = sep a q :=
  ext fun z => by
    rw [mem_sep, mem_sep]
    exact ⟨fun ⟨hz, hp⟩ => ⟨hz, (h z hz).mp hp⟩, fun ⟨hz, hq⟩ => ⟨hz, (h z hz).mpr hq⟩⟩

/-- Image congruence, the companion fact. -/
theorem image_congr {a : V} {f g : V → V} (h : ∀ x, x ∈ˢ a → f x = g x) :
    image f a = image g a :=
  ext fun z => by
    rw [mem_image, mem_image]
    exact ⟨fun ⟨w, hw, hz⟩ => ⟨w, hw, hz.trans (h w hw)⟩,
           fun ⟨w, hw, hz⟩ => ⟨w, hw, hz.trans (h w hw).symm⟩⟩

end ConLeche.SetTheory
