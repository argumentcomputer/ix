module

public import ConLeche.SetModel.TaggedSum

@[expose] public section

/-!
# Monotonicity of the tuple towers and the tagged union (task #188)

The constructor-tower functor of a recursive inductive type is
monotone in its argument: enlarging the set at the recursive field
positions enlarges the telescope pointwise (`TeleS.Sub`), the tower
(`towerSet_mono`), and the tagged union (`sumSet_mono`).  These are
the three facts the Knaster–Tarski laws
(`ConLeche/SetTheory/Derive/Lfp.lean`) consume at the tower functor.

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory.Tower

universe u

variable {V : Type u} [SetTheory V]

/-- Pointwise inclusion of dependent telescopes, hereditarily along
the fitting values of the smaller one. -/
inductive TeleS.Sub : {n : Nat} → TeleS V n → TeleS V n → Prop
  | nil : TeleS.Sub .nil .nil
  | cons {n : Nat} {A A' : V} {B B' : V → TeleS V n} :
      A ⊆ˢ A' → (∀ a, a ∈ˢ A → TeleS.Sub (B a) (B' a)) →
      TeleS.Sub (.cons A B) (.cons A' B')

theorem TeleS.Sub.refl : ∀ {n : Nat} (T : TeleS V n), TeleS.Sub T T
  | _, .nil => .nil
  | _, .cons _ B => .cons (Subset.refl _) fun a _ => TeleS.Sub.refl (B a)

/-- A tuple fitting the smaller telescope fits the larger. -/
theorem FitsS.mono : ∀ {n : Nat} {T T' : TeleS V n} {as : List V},
    TeleS.Sub T T' → FitsS T as → FitsS T' as
  | _, _, _, [], .nil, h => h
  | _, _, _, _ :: _, .nil, h => h.elim
  | _, _, _, [], .cons _ _, h => h.elim
  | _, _, _, a :: as, .cons hA hB, h =>
    ⟨hA a h.1, FitsS.mono (as := as) (hB a h.1) h.2⟩

/-- **The tower is monotone** in its telescope, both regimes. -/
theorem towerSet_mono {w : Nat} {n : Nat} {T T' : TeleS V n} (hs : TeleS.Sub T T') :
    towerSet w T ⊆ˢ towerSet w T' := by
  intro x hx
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · obtain ⟨rfl, as, hf⟩ := towerSet_zero_elim T hx
    exact pt_mem_tower (FitsS.mono hs hf)
  · have hw' : w ≠ 0 := Nat.pos_iff_ne_zero.mp hw
    obtain ⟨hf, heta⟩ := towerSet_elim hw' T hx
    rw [heta]
    exact mkTower_mem hw' (FitsS.mono hs hf)

/-- **The tagged union is monotone** in its fibres, both regimes. -/
theorem sumSet_mono {w : Nat} {f g : Nat → V} (h : ∀ i, f i ⊆ˢ g i) :
    sumSet w f ⊆ˢ sumSet w g := by
  intro x hx
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · obtain ⟨rfl, i, a, ha⟩ := sumSet_zero_elim hx
    exact pt_mem_sumSet_zero (h i a ha)
  · have hw' : w ≠ 0 := Nat.pos_iff_ne_zero.mp hw
    obtain ⟨i, a, ha, rfl⟩ := sumSet_elim hw' hx
    exact inj_mem hw' (h i a ha)

end ConLeche.SetTheory.Tower
