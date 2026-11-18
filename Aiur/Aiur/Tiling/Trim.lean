import Aiur.Tiling.Refinement

/-!
# LogUp fingerprints ignore trailing zeros

multi-stark fingerprints a lookup tuple as `Σ args[i]·γ^i`, so two tuples
meet on the bus exactly when they agree after dropping trailing zeros
(`trimZeros`). Its LogUp balance is therefore the ledger keyed by
`trimZeros`. On the narrow bus every tuple is either a message
(`W + 1` entries, first entry a message tag ≠ `COPY`) or a copy tuple
(three entries, first entry `COPY`); `trimZeros` is injective on those, so the
trimmed balance is the exact balance that `System.sound` assumes
(`System.exact_of_trimmed`).
-/

namespace Aiur.Tiling

variable {F : Type} [Field F] [DecidableEq F]

/-- A tuple without its trailing zeros. -/
def trimZeros : List F → List F
  | [] => []
  | a :: l => if a = 0 ∧ trimZeros l = [] then [] else a :: trimZeros l

theorem trimZeros_inj_of_length : ∀ {t u : List F}, t.length = u.length →
    trimZeros t = trimZeros u → t = u
  | [], [], _, _ => rfl
  | [], _ :: _, len, _ => by simp at len
  | _ :: _, [], len, _ => by simp at len
  | a :: t, b :: u, len, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      simp only [trimZeros] at h
      split at h <;> split at h
      · rename_i ha hb
        rw [ha.1, hb.1, trimZeros_inj_of_length len (ha.2.trans hb.2.symm)]
      · simp at h
      · simp at h
      · obtain ⟨rfl, rest⟩ := List.cons.inj h
        rw [trimZeros_inj_of_length len rest]

theorem trimZeros_head {t u : List F} {a : F} (h : trimZeros t = trimZeros u)
    (head : t.head? = some a) (nonzero : a ≠ 0) : u.head? = some a := by
  cases t with
  | nil => simp at head
  | cons x t =>
      simp only [List.head?_cons, Option.some.injEq] at head
      subst head
      have ht : trimZeros (x :: t) = x :: trimZeros t := by simp [trimZeros, nonzero]
      cases u with
      | nil => rw [ht] at h; simp [trimZeros] at h
      | cons y u =>
          rw [ht] at h
          simp only [trimZeros] at h
          split at h
          · simp at h
          · simp [(List.cons.inj h).1]

/-- Tuples of the narrow bus. -/
def NarrowShape (W : Nat) (t : List F) : Prop :=
  (t.length = W + 1 ∧ t.head? ≠ some (COPY : F)) ∨ (t.length = 3 ∧ t.head? = some (COPY : F))

theorem trimZeros_injOn {W : Nat} (copy : (COPY : F) ≠ 0) :
    Set.InjOn (trimZeros (F := F)) {t | NarrowShape W t} := by
  intro t ht u hu h
  simp only [Set.mem_setOf_eq, NarrowShape] at ht hu
  refine trimZeros_inj_of_length ?_ h
  rcases ht with ⟨lt, ht'⟩ | ⟨lt, ht'⟩ <;> rcases hu with ⟨lu, hu'⟩ | ⟨lu, hu'⟩
  · rw [lt, lu]
  · exact absurd (trimZeros_head h.symm hu' copy) ht'
  · exact absurd (trimZeros_head h ht' copy) hu'
  · rw [lt, lu]

namespace System

variable {sys : System F}

theorem msgTuple_shape (valid : sys.Valid) (copy0 : (0 : F) ≠ COPY) (main : Nat → Nat → F)
    (p : Nat) : NarrowShape sys.width (msgTuple sys main p) := by
  left
  refine ⟨by simp [msgTuple]; have := valid.width.1; omega, ?_⟩
  simp only [msgTuple, List.head?_cons, ne_eq, Option.some.injEq]
  rcases fixedAt_placed_or (p := p) (k := tagCol sys.width) valid with ⟨_, h⟩ | ⟨f, i, r, T, row, placed, h⟩
  · rw [h]; exact copy0
  · rw [h, Row.fixed_tag]
    cases hrow : row with
    | gate => simpa [Row.messageValue] using copy0
    | message sel tag sub cells =>
        simp only [Row.messageValue]
        apply valid.tags ((tag, sub), ((cells.drop 1).filterMap id).length)
        simp only [System.arities, List.mem_flatMap, List.mem_map]
        refine ⟨T, List.mem_of_getElem? placed.template, (sel, tag, sub, cells), ?_, rfl⟩
        simp only [Template.messages, List.mem_filterMap]
        exact ⟨_, List.mem_of_getElem? (hrow ▸ placed.row), rfl⟩

/-- Balance under multi-stark's fingerprint is exact balance on the narrow bus. -/
theorem exact_of_trimmed (valid : sys.Valid) (copy : (COPY : F) ≠ 0) (copy0 : (0 : F) ≠ COPY)
    {N : Nat} {main : Nat → Nat → F} {ext : Ledger F}
    (extShape : ∀ t, ext t ≠ 0 → NarrowShape sys.width t)
    (trimmed : Finsupp.mapDomain trimZeros (sys.narrowLedger N main + ext) = 0) :
    sys.narrowLedger N main + ext = 0 := by
  have outside : ∀ t, ¬ NarrowShape sys.width t → (sys.narrowLedger N main + ext) t = 0 := by
    intro t ht
    rw [narrowLedger_split valid valid.width.1, Finsupp.add_apply, Finsupp.add_apply]
    have e : ext t = 0 := by by_contra ne; exact ht (extShape t ne)
    have m : msgLedger sys N main t = 0 := by
      simp only [msgLedger, Finsupp.finsetSum_apply, Finsupp.single_apply]
      apply Finset.sum_eq_zero; intro p _
      rw [ite_eq_right_iff.mpr]; intro eq; exact absurd (eq ▸ msgTuple_shape valid copy0 main p) ht
    have c : copyLedger sys N main t = 0 := by
      rw [copyLedger_apply]
      apply Finset.sum_eq_zero; intro p _
      apply Finset.sum_eq_zero; intro j _
      rw [ite_eq_right_iff.mpr]; intro eq; exact absurd (eq ▸ Or.inr ⟨rfl, rfl⟩) ht
    rw [e, m, c]; simp
  have support : ((sys.narrowLedger N main + ext).support : Set (List F)) ⊆ {t | NarrowShape sys.width t} := by
    intro t ht
    by_contra h
    exact (Finsupp.mem_support_iff.mp ht) (outside t h)
  ext t
  by_cases ht : NarrowShape sys.width t
  · have := Finsupp.mapDomain_apply' _ _ support (trimZeros_injOn copy) ht
    rw [trimmed] at this
    simpa using this.symm
  · simpa using outside t ht

end System

end Aiur.Tiling
