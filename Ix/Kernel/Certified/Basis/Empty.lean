/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.Basis.Equality
import Ix.Kernel.Certified.Ordinary.Checked

/-! # Constructor-free families are empty

A parameter-free, index-free ordinary family with no constructors (Lean's
`False` in `Prop`, `Empty` in `Type`) admits the large eliminator
`∀ (motive : F → Sort u) (t : F), motive t`. The interface below is the
syntactic statement that such an eliminator is installed; it is decidable.
In every model that realizes it, the family denotes the empty set: taking the
eliminator at universe 0 and the motive that is constantly the empty
proposition sends any inhabitant to an element of the empty set.

Only the eliminator matters. A family admitted without its recursor is not
constrained by its type alone, since a model may interpret an uneliminated
proposition as true. -/

namespace Ix.Kernel.Certified.Basis.Empty

open Model Model.SetTheory Model.SetModel

universe u v
variable {β : Type u}

/-- A parameter-free, index-free, constructor-free ordinary family in `Sort l`. -/
def shape (l : VLevel) : Ordinary.Shape β := ⟨0, [], [], l, []⟩

/-- The large eliminator's checked type over the family at member 0 of `source`. -/
def recType (source : β) : AExpr β :=
  .forallE (.param 0)
    (.forallE .never (.const (.member source 0) []) (.sort (.param 0)))
    (.forallE (.param 0) (.const (.member source 0) []) (.app (.bvar 1) (.bvar 0)))

theorem shape_recType (l : VLevel) (source : β) :
    (shape l).recursorType source .large = recType source := rfl

/-- The family at member 0 of `source` has the installed large eliminator
`recursor`. -/
def Interface (entries : Environment β) (source : β) (recursor : ConstRef β) : Prop :=
  entries.HasType recursor 1 (recType source)

instance [DecidableEq β] (entries : Environment β) (source : β) (recursor : ConstRef β) :
    Decidable (Interface entries source recursor) :=
  inferInstanceAs (Decidable (entries.HasType recursor 1 (recType source)))

variable {V : Type v} [SetTheory V]

theorem recType_interp (constants : Assignment β V) (source : β) (env : Nat → V) :
    interp constants [0] env (recType source : AExpr β) =
      piR 0 (piR 1 (constants (.member source 0) []) (fun _ => univ 0)) (fun motive =>
        piR 0 (constants (.member source 0) []) (fun t => app motive t)) := by
  have regime_zero : regime (PropWhen.param 0) [0] = 0 := rfl
  simp [recType, interp, VLevel.eval, Valuation.cons, regime_zero]

/-- In every model realizing the interface, the family has no inhabitant. -/
theorem not_mem {entries : Environment β} {source : β} {recursor : ConstRef β}
    {constants : Assignment β V} (h : Interface entries source recursor)
    (hM : Realizes constants entries) (t : V) :
    ¬ t ∈ˢ constants (.member source 0) [] := by
  intro ht
  let family := constants (.member source 0) []
  let motive : V := lamR 1 family (fun _ => empty)
  have hm : motive ∈ˢ piR 1 family (fun _ => univ 0) :=
    lamR_mem fun _ _ => empty_mem_univ 0
  have hr := h.member hM (levels := [0]) rfl (fun _ => empty)
  rw [recType_interp] at hr
  obtain ⟨_, hrm⟩ := Equality.exists_of_mem_piR_zero hr hm
  obtain ⟨result, hresult⟩ := Equality.exists_of_mem_piR_zero hrm ht
  rw [app_lamR_pos (by decide : 1 ≠ 0) ht] at hresult
  exact not_mem_empty _ hresult

theorem value_eq_empty {entries : Environment β} {source : β} {recursor : ConstRef β}
    {constants : Assignment β V} (h : Interface entries source recursor)
    (hM : Realizes constants entries) :
    constants (.member source 0) [] = empty :=
  eq_empty (not_mem h hM)

end Ix.Kernel.Certified.Basis.Empty
