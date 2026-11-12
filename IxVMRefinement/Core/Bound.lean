import IxVMRefinement.Core.Specs
import IxVMRefinement.Obs.Lists
import Ix.IxVM.Consistency.Statement
import Mathlib.Data.List.Forall2

/-! # The size bound: a list IxVM measures as a field element is short

`Lists::length` returns a field element, and IxVM computes with it (`red_iota` splits a
constructor's arguments at `Lists::length(ctor_args) - rfields`), so the soundness
of such a step needs the list's length to be below the field's characteristic. The circuit bounds
*distinct calls of each memoized callee* (the consistency statement's `MemoCallsAtMost … (2^39)`), not calls counted with
repetition. The bridge (`length_lt`): the derivation of `Lists::length` on a list of length
`n` makes `n + 1` calls to itself, on the list's suffixes; their arguments are lists of
pairwise different lengths, and two lists of different lengths are never represented by the
same ROM value **when the ROM is valid** (`spine_length_eq`), so the calls need `n + 1`
distinct keys (`chain_bound`).

The ROM's validity is an explicit hypothesis here: `MemoCallsAtMost` alone admits an invalid
ROM, at one address of which two lists of different lengths could both be represented. For
the compiled circuit's trace ROM it follows from the consistency statement's hypothesis `rom.Valid` on the width
ROM (`traceROM_valid`). -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM.Consistency (MemoCallsAtMost memoCall)

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

/-! ## Distinct keys -/

/-- **A chain of calls on lists of every length up to `n` needs `n + 1` keys**, if the
ROM is valid and the callee is memoized (`memoCall`). -/
theorem chain_bound {rom : ROM F} (valid : rom.Valid) {calls : List (Call F)} {N : Nat}
    (bound : MemoCallsAtMost IxVM.source rom calls N) {name en : String}
    (memoized : memoCall IxVM.source name = true) {n : Nat}
    (chain : ∀ j ≤ n, ∃ c ∈ calls, c.name = name ∧ ∃ p ys, c.args = [p] ∧
      Spine en c.heap ys p ∧ ys.length = j) :
    n + 1 ≤ N := by
  obtain ⟨keys, hlen, cover⟩ := bound name memoized
  have pick : ∀ j : Fin (n + 1), ∃ k, k ∈ keys ∧ ∃ (h : Heap F) (p : SourceValue F) (ys : List Unit)
      (w : Value F), k = [w] ∧ Represents rom h p w ∧ Spine en h ys p ∧ ys.length = j := by
    intro j
    obtain ⟨c, hc, hname, p, ys, hargs, hs, hys⟩ := chain j (Nat.lt_succ_iff.mp j.isLt)
    obtain ⟨k, hk, hfa⟩ := cover c hc hname
    rw [hargs] at hfa
    obtain ⟨w, u, hw, hu, hk2⟩ := List.forall₂_cons_left_iff.mp hfa
    rw [List.forall₂_nil_left_iff] at hu
    subst hu
    exact ⟨k, hk, c.heap, p, ys, w, hk2, hw, hs, hys⟩
  let f : Fin (n + 1) → List (Value F) := fun j => Classical.choose (pick j)
  have hf : ∀ j, f j ∈ keys ∧ ∃ (h : Heap F) (p : SourceValue F) (ys : List Unit) (w : Value F),
      f j = [w] ∧ Represents rom h p w ∧ Spine en h ys p ∧ ys.length = j :=
    fun j => Classical.choose_spec (pick j)
  have inj : Function.Injective f := by
    intro j j' heq
    obtain ⟨_, h₁, p₁, ys₁, w₁, hk₁, r₁, s₁, l₁⟩ := hf j
    obtain ⟨_, h₂, p₂, ys₂, w₂, hk₂, r₂, s₂, l₂⟩ := hf j'
    rw [heq, hk₂] at hk₁
    simp only [List.cons.injEq, and_true] at hk₁
    subst hk₁
    have := spine_length_eq valid s₁ s₂ r₁ r₂
    exact Fin.ext (by omega)
  have hnd : ((List.finRange (n + 1)).map f).Nodup := (List.nodup_finRange _).map inj
  have hsub : (List.finRange (n + 1)).map f ⊆ keys := by
    intro k hk
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hk
    exact (hf j).1
  have hle := (hnd.subperm hsub).length_le
  simp only [List.length_map, List.length_finRange] at hle
  omega

/-! ## For the slice -/

/-- `Lists::length` on IxVM's term lists is memoized. -/
theorem length_memoized : memoCall IxVM.source lengthName = true := by
  decide +kernel

/-- **The list `Lists::length` counts is shorter than `2^39`**, in a run whose calls have at
most `2^39` distinct calls of each memoized callee in a valid ROM. -/
theorem length_lt {rom : ROM F} (valid : rom.Valid) {calls : List (Call F)}
    (bound : MemoCallsAtMost IxVM.source rom calls (2 ^ 39))
    {l : SourceValue F} {m m' : Heap F} {r : SourceValue F} {cs : List (Call F)}
    (ev : ObsFn W lengthName [l] m r m' cs)
    (hsub : ∀ x ∈ (⟨lengthName, [l], m⟩ : Call F) :: cs, x ∈ calls)
    {α : Type} {R : Heap F → α → SourceValue F → Prop} {xs : List α}
    (hl : RepLinkedList kexprListEnum "Nil" "Cons" R m xs l) : xs.length < 2 ^ 39 := by
  have hname : (Instance.mk "Lists::length" [kexprTy]).symbol = lengthName :=
    Obs.Names.«Lists::length<&KernelTypes::KExprNode>».symbol
  have henum : (Instance.mk "Lists::Node" [kexprTy]).symbol = kexprListEnum :=
    Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol
  have ev' : ObsFn W (Instance.mk "Lists::length" [kexprTy]).symbol [l] m r m' cs := by
    rw [hname]; exact ev
  have hs : Spine (Instance.mk "Lists::Node" [kexprTy]).symbol m (xs.map fun _ => ()) l := by
    rw [henum]; exact RepLinkedList.spine hl
  have chain := length_chain kexprTy _ ev' hs rfl
  have := chain_bound valid bound (name := lengthName)
    (en := (Instance.mk "Lists::Node" [kexprTy]).symbol) length_memoized
    (n := (xs.map fun _ => ()).length) fun j hj => by
      obtain ⟨c, hc, hcn, rest⟩ := chain j hj
      refine ⟨c, ?_, hcn.trans hname, rest⟩
      apply hsub
      rw [← hname]
      exact hc
  simp only [List.length_map] at this
  exact Nat.lt_of_succ_le this

end IxVM.Refinement.Core
