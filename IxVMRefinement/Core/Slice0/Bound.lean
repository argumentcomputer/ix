import IxVMRefinement.Core.Slice0.Specs
import IxVMRefinement.Obs.Lists
import Ix.IxVM.Consistency.Statement
import Mathlib.Data.List.Forall2

/-! # Values in a valid ROM, for the slice

One value of a valid ROM represents lists of one length only (`spine_length_eq`), and the
calls of `Lists::length` on a list reach every suffix (`length_chain`). The bound itself is the
statement's `Bounded` (`IxVMRefinement.Core.RomBound`). -/

namespace IxVM.Refinement.Core.Slice0

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics

set_option linter.unusedVariables false

/-! ## The trace ROM is valid -/

/-- **The compiled circuit's trace ROM is valid** whenever the width ROM is: decoding and typing keep
validity (`WireROM.decode_valid`, `WidthROM.toWireROM_valid`). -/
theorem traceROM_valid {source : Generic.Source F} {entries : List String}
    {specialized : Generic.Specialized source entries} (compiled : Optimized.GenericArtifact specialized)
    {rom : WidthROM F} (valid : rom.Valid) : (compiled.traceROM rom).Valid :=
  WireROM.decode_valid (WidthROM.toWireROM_valid valid _ _)

/-! ## Spines -/

/-- The cells of a list, whatever its elements. -/
abbrev Spine (en : String) (h : Heap F) (xs : List Unit) (p : SourceValue F) : Prop :=
  RepLinkedList en "Nil" "Cons" (fun _ _ _ => True) h xs p

theorem RepLinkedList.spine {α : Type} {en : String} {R : Heap F → α → SourceValue F → Prop}
    {h : Heap F} {xs : List α} {p : SourceValue F}
    (rep : RepLinkedList en "Nil" "Cons" R h xs p) : Spine en h (xs.map fun _ => ()) p := by
  induction rep with
  | nil cell => exact .nil cell
  | cons cell _ _ ih => exact .cons cell trivial ih

theorem represents_ptr_inv {rom : ROM F} {h : Heap F} {t : Aiur.Ty} {loc : Nat} {w : Value F}
    (r : Represents rom h (.ptr t loc) w) :
    ∃ stored address encoded, h[loc]? = some stored ∧ (address, encoded) ∈ rom.entries ∧
      Represents rom h stored encoded ∧ w = .ptr encoded.type address := by
  generalize hp : (Value.ptr t loc : SourceValue F) = p at r
  cases r with
  | ptr source cell contents =>
    injection hp with _ hl
    subst hl
    exact ⟨_, _, _, source, cell, contents, rfl⟩
  | field => cases hp
  | tuple _ => cases hp
  | construct _ => cases hp

theorem represents_construct_inv {rom : ROM F} {h : Heap F} {e c : String}
    {vs : List (SourceValue F)} {w : Value F} (r : Represents rom h (.construct e c vs) w) :
    ∃ ws, w = .construct e c ws ∧ List.Forall₂ (Represents rom h) vs ws := by
  generalize hp : (Value.construct e c vs : SourceValue F) = p at r
  cases r with
  | construct items =>
    injection hp with h1 h2 h3
    subst h1 h2 h3
    exact ⟨_, rfl, items⟩
  | field => cases hp
  | tuple _ => cases hp
  | ptr _ _ _ => cases hp

theorem forall₂_pair {α β : Type} {R : α → β → Prop} {a b : α} {ws : List β}
    (h : List.Forall₂ R [a, b] ws) : ∃ wa wb, ws = [wa, wb] ∧ R a wa ∧ R b wb := by
  obtain ⟨wa, u, ha, hu, rfl⟩ := List.forall₂_cons_left_iff.mp h
  obtain ⟨wb, u', hb, hu', rfl⟩ := List.forall₂_cons_left_iff.mp hu
  rw [List.forall₂_nil_left_iff] at hu'
  subst hu'
  exact ⟨wa, wb, rfl, ha, hb⟩

/-- The value a list cell is represented by, at a represented pointer. -/
theorem cell_represented {rom : ROM F} {h : Heap F} {en c : String} {addr : Nat}
    {vs : List (SourceValue F)} {w : Value F}
    (cell : h[addr]? = some (.construct en c vs)) (r : Represents rom h (.ptr (.enum en) addr) w) :
    ∃ address ws, (address, .construct en c ws) ∈ rom.entries ∧
      List.Forall₂ (Represents rom h) vs ws ∧ w = .ptr (.enum en) address := by
  obtain ⟨stored, address, encoded, src, mem, rep, rfl⟩ := represents_ptr_inv r
  rw [cell] at src
  cases src
  obtain ⟨ws, rfl, items⟩ := represents_construct_inv rep
  exact ⟨address, ws, mem, items, by simp [Value.type]⟩

/-- **In a valid ROM, a value represents lists of one length only.** -/
theorem spine_length_eq {rom : ROM F} (valid : rom.Valid) {en : String} {h₁ h₂ : Heap F}
    {xs₁ xs₂ : List Unit} {p₁ p₂ : SourceValue F} {w : Value F}
    (s₁ : Spine en h₁ xs₁ p₁) (s₂ : Spine en h₂ xs₂ p₂)
    (r₁ : Represents rom h₁ p₁ w) (r₂ : Represents rom h₂ p₂ w) : xs₁.length = xs₂.length := by
  induction s₁ generalizing xs₂ p₂ w with
  | nil cell₁ =>
    obtain ⟨a₁, ws₁, mem₁, items₁, rfl⟩ := cell_represented cell₁ r₁
    cases s₂ with
    | nil _ => rfl
    | cons cell₂ _ _ =>
      obtain ⟨a₂, ws₂, mem₂, items₂, hw⟩ := cell_represented cell₂ r₂
      injection hw with _ ha
      have := valid _ mem₁ _ mem₂ ha (by simp [Value.type])
      injection this with _ hc _
      exact absurd hc (by decide)
  | cons cell₁ _ tail₁ ih =>
    obtain ⟨a₁, ws₁, mem₁, items₁, rfl⟩ := cell_represented cell₁ r₁
    obtain ⟨wh₁, wt₁, rfl, -, rt₁⟩ := forall₂_pair items₁
    cases s₂ with
    | nil cell₂ =>
      obtain ⟨a₂, ws₂, mem₂, items₂, hw⟩ := cell_represented cell₂ r₂
      injection hw with _ ha
      have := valid _ mem₁ _ mem₂ ha (by simp [Value.type])
      injection this with _ hc _
      exact absurd hc (by decide)
    | cons cell₂ _ tail₂ =>
      obtain ⟨a₂, ws₂, mem₂, items₂, hw⟩ := cell_represented cell₂ r₂
      obtain ⟨wh₂, wt₂, rfl, -, rt₂⟩ := forall₂_pair items₂
      injection hw with _ ha
      have := valid _ mem₁ _ mem₂ ha (by simp [Value.type])
      injection this with _ _ hws
      injection hws with _ hrest
      injection hrest with hwt _
      subst hwt
      simp only [List.length_cons]
      rw [ih tail₂ rt₁ rt₂]

/-! ## The chain of `Lists::length` -/

/-- **The calls of `Lists::length` on a list of length `n`**: for every `j ≤ n` one of them
is on a list of length `j`. -/
theorem length_chain (t : Generic.Ty) (n : Nat) :
    ∀ {l : SourceValue F} {h h' : Heap F} {r : SourceValue F} {cs : List (Call F)}
      {xs : List Unit},
      ObsFn W (Instance.mk "Lists::length" [t]).symbol [l] h r h' cs →
      Spine (Instance.mk "Lists::Node" [t]).symbol h xs l → xs.length = n →
      ∀ j ≤ n, ∃ c ∈ (⟨(Instance.mk "Lists::length" [t]).symbol, [l], h⟩ : Call F) :: cs,
        c.name = (Instance.mk "Lists::length" [t]).symbol ∧ ∃ p ys, c.args = [p] ∧
          Spine (Instance.mk "Lists::Node" [t]).symbol c.heap ys p ∧ ys.length = j := by
  induction n with
  | zero =>
    intro l h h' r cs xs ev hs hn j hj
    exact ⟨⟨(Instance.mk "Lists::length" [t]).symbol, [l], h⟩, by simp, rfl, l, xs, rfl, hs,
      by omega⟩
  | succ n ih =>
    intro l h h' r cs xs ev hs hn j hj
    rcases Obs.«Lists::length».obs ev with ⟨ld, -, -, -⟩ |
      ⟨w, rest, x, m, cs', ld, ev', -, -, rfl⟩
    · cases hs with
      | nil _ => simp at hn
      | cons cell _ _ =>
        rw [loadValue_enum_cell cell] at ld
        injection ld with hv
        injection hv with _ hc _
        exact absurd hc (by decide)
    · cases hs with
      | nil _ => simp at hn
      | @cons _ xs' _ _ _ cell _ tail =>
        rw [loadValue_enum_cell cell] at ld
        injection ld with hv
        injection hv with _ _ hargs
        injection hargs with _ htail
        injection htail with hrest _
        subst hrest
        by_cases hjn : j = n + 1
        · subst hjn
          exact ⟨⟨(Instance.mk "Lists::length" [t]).symbol, [_], h⟩, by simp, rfl, _, _, rfl,
            .cons cell trivial tail, hn⟩
        · simp only [List.length_cons, Nat.add_right_cancel_iff] at hn
          obtain ⟨c, hc, rest⟩ := ih ev' tail hn j (by omega)
          exact ⟨c, List.mem_cons_of_mem _ hc, rest⟩


end IxVM.Refinement.Core.Slice0
