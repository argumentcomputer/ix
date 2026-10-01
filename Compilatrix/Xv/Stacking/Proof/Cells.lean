import Compilatrix.Xv.Stacking.Proof.Match

/-!
# Frame cells on the machine stack

Each function's checks (`FnAt.checks`: its layout is sound, it changes no
register beyond what its callers allow, its result counts agree), and where
its frame's cells sit: each is `rsp`-relative at an offset (`cell_off`) in
the outgoing arguments, the slots and saves, or the incoming arguments, so
distinct cells do not overlap (`cell_disjoint`) and every cell lies in the
frame (`cell_range`). Stack addresses do not wrap (`addr_toNat`).
-/

namespace Compilatrix.Xv.Stacking.Proof

open Compilatrix.X86 Compilatrix.X86.Stream

/-! ## Each function's checks -/

/-- What `run` checked of each function. -/
theorem FnAt.checks {S : Stk} {k : Lir.FunId} {f : Func Loc} {l : FrameLayout} {pl : Placed}
    (h : FnAt S k f l pl) :
    l.Sound f.facts ∧ extraChanges S.p S.env f k l f.facts = [] ∧ aritiesOk S.p f = true := by
  obtain ⟨-, hcheck, hextra, harity, -⟩ := run_ok S.ok
  have hm := List.mem_of_getElem? (withLayouts_get h.func h.layout)
  exact ⟨FrameLayout.check_sound (hcheck _ hm), hextra _ hm, harity _ hm⟩

/-! ## Words without wrapping -/

theorem addr_toNat {a : Word} {k : Nat} (h : a.toNat + k < 2 ^ 64) : (a + UInt64.ofNat k).toNat = a.toNat + k := by
  rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
  exact Nat.mod_eq_of_lt (by simpa [UInt64.size] using h)

/-- Two eight-byte ranges at word offsets `o₁ ≠ o₂` that are eight apart. -/
theorem ranges_apart {a : Word} {o₁ o₂ : Nat} (h₁ : a.toNat + o₁ + 8 ≤ 2 ^ 64) (h₂ : a.toNat + o₂ + 8 ≤ 2 ^ 64)
    (hsep : o₁ + 8 ≤ o₂ ∨ o₂ + 8 ≤ o₁) :
    ∀ i < 8, ∀ j < 8, a + UInt64.ofNat o₁ + UInt64.ofNat i ≠ a + UInt64.ofNat o₂ + UInt64.ofNat j := by
  intro i hi j hj e
  have := congrArg UInt64.toNat e
  rw [addr_toNat (by rw [addr_toNat (by omega)]; omega), addr_toNat (by omega),
    addr_toNat (by rw [addr_toNat (by omega)]; omega), addr_toNat (by omega)] at this
  omega

/-! ## Cells -/

/-- Where a frame cell sits: an outgoing argument, a slot, or an incoming
argument, at an offset from `rsp`. -/
inductive CellAt (l : FrameLayout) (inArgs : Nat) : Loc → Nat → Prop
  | slot {i o : Nat} : l.slotOff[i]? = some o → CellAt l inArgs (.slot i) o
  | outArg {i : Nat} : i < l.outArgs → CellAt l inArgs (.outArg i) (8 * i)
  | inArg {i : Nat} : i < inArgs → CellAt l inArgs (.inArg i) (l.size + 8 + 8 * i)

theorem cell_off {placed : List Placed} {pl : Placed} {x : Loc} {m : MemAddr}
    (h : (ctxOf placed pl).cell x = .ok m) :
    ∃ o, CellAt pl.layout pl.facts.inArgs x o ∧ m = rspAt o := by
  cases x with
  | reg r => simp [FnCtx.cell, throw, throwThe, MonadExceptOf.throw] at h
  | slot i =>
    simp only [FnCtx.cell, ctxOf] at h
    split at h
    · rename_i o ho
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact ⟨o, .slot ho, h.symm⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  | outArg i =>
    simp only [FnCtx.cell, ctxOf] at h
    by_cases hi : i < pl.layout.outArgs
    · simp only [hi, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
      exact ⟨_, .outArg hi, h.symm⟩
    · simp [hi, throw, throwThe, MonadExceptOf.throw] at h
  | inArg i =>
    simp only [FnCtx.cell, ctxOf] at h
    by_cases hi : i < pl.facts.inArgs
    · simp only [hi, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
      exact ⟨_, .inArg hi, h.symm⟩
    · simp [hi, throw, throwThe, MonadExceptOf.throw] at h

/-- A cell's offset lies in the frame. -/
theorem CellAt.range {l : FrameLayout} {a : Facts} (hs : l.Sound a) {inArgs : Nat} {x : Loc} {o : Nat}
    (h : CellAt l inArgs x o) : o % 8 = 0 ∧ o + 8 ≤ l.size + 8 + 8 * inArgs ∧
      (o + 8 ≤ l.size ∨ l.size + 8 ≤ o) := by
  cases h with
  | slot ho =>
    have hm : o ∈ l.cells := List.mem_append_left _ (List.mem_of_getElem? ho)
    have := hs.inBounds o hm
    exact ⟨hs.aligned o hm, by omega, .inl this.2⟩
  | outArg hi =>
    have := hs.outArgsFit
    refine ⟨by omega, by omega, .inl (by omega)⟩
  | inArg hi =>
    have h8 : l.size % 8 = 0 := by
      by_cases hz : l.size = 0
      · rw [hz]
      · have := hs.aligned16 hz; omega
    exact ⟨by omega, by omega, .inr (by omega)⟩

/-- A save cell's offset lies in the frame, apart from the cells. -/
theorem save_range {l : FrameLayout} {a : Facts} (hs : l.Sound a) {r : GPR} {o : Nat} (h : (r, o) ∈ l.saveOff) :
    o % 8 = 0 ∧ 8 * l.outArgs ≤ o ∧ o + 8 ≤ l.size := by
  have hm : o ∈ l.cells := List.mem_append_right _ (List.mem_map.2 ⟨(r, o), h, rfl⟩)
  exact ⟨hs.aligned o hm, (hs.inBounds o hm).1, (hs.inBounds o hm).2⟩

theorem nodup_getElem?_inj {α : Type} :
    ∀ {l : List α} {i j : Nat} {x : α}, l.Nodup → l[i]? = some x → l[j]? = some x → i = j
  | [], _, _, _, _, h, _ => by simp at h
  | _ :: _, 0, 0, _, _, _, _ => rfl
  | y :: l, 0, j + 1, x, hn, hi, hj => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      simp only [List.getElem?_cons_succ] at hj
      exact absurd (List.mem_of_getElem? hj) (List.nodup_cons.1 hn).1
  | y :: l, i + 1, 0, x, hn, hi, hj => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      simp only [List.getElem?_cons_succ] at hi
      exact absurd (List.mem_of_getElem? hi) (List.nodup_cons.1 hn).1
  | _ :: _, i + 1, j + 1, _, hn, hi, hj => by
      simp only [List.getElem?_cons_succ] at hi hj
      rw [nodup_getElem?_inj (List.nodup_cons.1 hn).2 hi hj]

/-- Distinct cells are eight apart. -/
theorem CellAt.apart {l : FrameLayout} {a : Facts} (hs : l.Sound a) {inArgs : Nat} {x₁ x₂ : Loc} {o₁ o₂ : Nat}
    (h₁ : CellAt l inArgs x₁ o₁) (h₂ : CellAt l inArgs x₂ o₂) (hne : x₁ ≠ x₂) : o₁ + 8 ≤ o₂ ∨ o₂ + 8 ≤ o₁ := by
  have fit := hs.outArgsFit
  cases h₁ with
  | slot ho₁ =>
    have hm₁ : o₁ ∈ l.cells := List.mem_append_left _ (List.mem_of_getElem? ho₁)
    have hb₁ := hs.inBounds o₁ hm₁
    cases h₂ with
    | slot ho₂ =>
      rename_i i j
      have hm₂ : o₂ ∈ l.cells := List.mem_append_left _ (List.mem_of_getElem? ho₂)
      have hij : i ≠ j := fun e => hne (by rw [e])
      have hoo : o₁ ≠ o₂ := by
        intro e
        subst e
        have hnd : l.slotOff.Nodup := (List.nodup_append.1 hs.distinct).1
        exact hij (nodup_getElem?_inj hnd ho₁ ho₂)
      exact hs.separated hm₁ hm₂ hoo
    | outArg hj => omega
    | inArg hj => omega
  | outArg hi =>
    cases h₂ with
    | slot ho₂ =>
      have hm₂ : o₂ ∈ l.cells := List.mem_append_left _ (List.mem_of_getElem? ho₂)
      have := hs.inBounds o₂ hm₂
      omega
    | outArg hj =>
      rename_i i j
      have : i ≠ j := fun e => hne (by rw [e])
      omega
    | inArg hj => omega
  | inArg hi =>
    cases h₂ with
    | slot ho₂ =>
      have hm₂ : o₂ ∈ l.cells := List.mem_append_left _ (List.mem_of_getElem? ho₂)
      have := hs.inBounds o₂ hm₂
      omega
    | outArg hj => omega
    | inArg hj =>
      rename_i i j
      have : i ≠ j := fun e => hne (by rw [e])
      omega

/-- A cell and a save cell are eight apart. -/
theorem CellAt.apart_save {l : FrameLayout} {a : Facts} (hs : l.Sound a) {inArgs : Nat} {x : Loc} {o : Nat}
    (h : CellAt l inArgs x o) {r : GPR} {o' : Nat} (hr : (r, o') ∈ l.saveOff) : o + 8 ≤ o' ∨ o' + 8 ≤ o := by
  have hsv := save_range hs hr
  have hm' : o' ∈ l.cells := List.mem_append_right _ (List.mem_map.2 ⟨(r, o'), hr, rfl⟩)
  cases h with
  | slot ho =>
    have hm : o ∈ l.cells := List.mem_append_left _ (List.mem_of_getElem? ho)
    have hne : o ≠ o' := by
      intro e
      subst e
      have hnd := hs.distinct
      rw [FrameLayout.cells, List.nodup_append] at hnd
      exact hnd.2.2 o (List.mem_of_getElem? ho) o (List.mem_map.2 ⟨(r, o), hr, rfl⟩) rfl
    exact hs.separated hm hm' hne
  | outArg hi => omega
  | inArg hi => omega

end Compilatrix.Xv.Stacking.Proof
