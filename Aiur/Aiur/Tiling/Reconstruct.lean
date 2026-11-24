import Aiur.Tiling.Narrow

/-!
# Reconstructing wide rows from a narrow trace

Copy balance gives every (circuit, instance, slot) one value, read at the
slot's anchor cell. With those values every gate relation of every instance
holds, so `Template.Checked` yields a valid wide row per instance.
-/

namespace Aiur.Tiling

open Aiur.Scalar.Circuit (ArithExpr Var Satisfies)

variable {F : Type}

/-! ## Template cells -/

section Cells

theorem Template.cell_some {T : Template F} {r j s : Nat} (h : T.cell r j = some s) :
    ∃ row, T.rows[r]? = some row ∧ row.cells[j]? = some (some s) := by
  unfold Template.cell at h
  split at h
  · rename_i row found
    refine ⟨row, found, ?_⟩
    cases e : row.cells[j]? with
    | none => simp [e] at h
    | some c => simp [e] at h; simp [h]
  · simp at h

theorem Template.cell_of {T : Template F} {r j : Nat} {row : Row F} (h : T.rows[r]? = some row) :
    T.cell r j = (row.cells[j]?).getD none := by
  simp [Template.cell, h]

theorem flatMap_cells_getElem? (lanes : List (Lane F)) {l m : Nat} (hl : l < lanes.length) (hm : m < 4) :
    (lanes.flatMap Lane.cells)[4 * l + m]? = lanes[l].cells[m]? := by
  induction lanes generalizing l with
  | nil => simp at hl
  | cons a rest ih =>
      rw [List.flatMap_cons]
      have len : a.cells.length = 4 := rfl
      cases l with
      | zero =>
          rw [List.getElem?_append_left (by omega)]
          simp
      | succ l =>
          rw [List.getElem?_append_right (by omega), len,
            show 4 * (l + 1) + m - 4 = 4 * l + m by omega]
          simpa using ih (l := l) (by simpa using hl)

theorem Template.anchor_spec {T : Template F} {s ra ja : Nat} (h : T.anchor s = some (ra, ja)) :
    ra < T.rows.length ∧ ja < T.width ∧ T.cell ra ja = some s := by
  unfold Template.anchor at h
  have mem := List.mem_of_find?_eq_some h
  have sat := List.find?_some h
  simp only [Template.cellIndices, List.mem_flatMap, List.mem_range, List.mem_map,
    Prod.mk.injEq] at mem
  obtain ⟨r, hr, j, hj, rfl, rfl⟩ := mem
  exact ⟨hr, hj, by simpa using sat⟩

theorem Template.anchor_exists {T : Template F} {r j s : Nat} (hr : r < T.rows.length) (hj : j < T.width)
    (h : T.cell r j = some s) : ∃ ra ja, T.anchor s = some (ra, ja) := by
  cases e : T.anchor s with
  | some x => exact ⟨x.1, x.2, rfl⟩
  | none =>
      unfold Template.anchor at e
      have := List.find?_eq_none.mp e (r, j) (by
        simp only [Template.cellIndices, List.mem_flatMap, List.mem_range, List.mem_map]
        exact ⟨r, hr, j, hj, rfl⟩)
      simp [h] at this

end Cells

/-! ## Placement -/

namespace System

variable (sys : System F)

theorem templates_getElem? {f : Nat} (h : f < sys.templates.length) :
    ∃ T, sys.templates[f]? = some T ∧ sys.rowCount f = T.rows.length ∧
      sys.slotCount f = T.slots.length := by
  refine ⟨sys.templates[f], List.getElem?_eq_getElem h, ?_, ?_⟩ <;>
    simp [rowCount, slotCount, List.getElem?_eq_getElem h]

theorem placed_of_mem {f i r : Nat} (h : (f, i, r) ∈ sys.places) :
    ∃ T row, sys.Placed (sys.row f i r) f i r T row ∧ r < T.rows.length := by
  obtain ⟨hf, _, hr⟩ := sys.mem_places.mp h
  obtain ⟨T, hT, count, _⟩ := sys.templates_getElem? hf
  rw [count] at hr
  refine ⟨T, T.rows[r], ⟨?_, hT, List.getElem?_eq_getElem hr⟩, hr⟩
  rw [List.getElem?_eq_getElem (sys.row_lt h), sys.places_row h]

theorem places_getElem?_none {p : Nat} (h : sys.places.length ≤ p) : sys.places[p]? = none :=
  List.getElem?_eq_none h

theorem copyKey_some {p j : Nat} {k : Nat × Nat × Nat} (h : sys.copyKey p j = some k) :
    ∃ r T, sys.places[p]? = some (k.1, k.2.1, r) ∧ sys.templates[k.1]? = some T ∧
      T.cell r j = some k.2.2 := by
  unfold copyKey at h
  split at h
  · rename_i f i r place
    split at h
    · rename_i T hT
      cases e : T.cell r j with
      | none => simp [e] at h
      | some s =>
          simp only [e, Option.map_some, Option.some.injEq] at h
          subst h
          exact ⟨r, T, place, hT, e⟩
    · simp at h
  · simp at h

theorem labelAt_unplaced [NatCast F] [Zero F] {p j : Nat} (h : sys.places[p]? = none) :
    sys.labelAt p j = 0 := by
  simp [labelAt, copyKey, h]

theorem multAt_unplaced [Zero F] [One F] [Neg F] [Sub F] [NatCast F] {p j : Nat}
    (h : sys.places[p]? = none) : sys.multAt p j = 0 := by
  simp [multAt, h]

theorem fixedAt_unplaced [Zero F] [One F] [Neg F] [Sub F] [NatCast F] [Add F] [Mul F] {p k : Nat}
    (h : sys.places[p]? = none) : sys.fixedAt p k = 0 := by
  simp [fixedAt, h]

end System

/-! ## Copy consistency -/

section Copy

variable [Field F] [DecidableEq F] (sys : System F)

/-- The copy-bus coefficient of `[COPY, L, v]` in a narrow trace. -/
def System.copyCoefficient (N : Nat) (main : Nat → Nat → F) (L v : F) : F :=
  ∑ p ∈ Finset.range N, ∑ j ∈ Finset.range sys.width,
    if sys.labelAt p j = L ∧ main p j = v then sys.multAt p j else 0

/-- What the checker guarantees about every template of the system. -/
structure System.Valid : Prop where
  width : 4 ≤ sys.width ∧ sys.width % 4 = 0
  lengths : sys.circuits.length = sys.templates.length ∧ sys.caps.length = sys.templates.length
  templates : ∀ f (h : f < sys.templates.length) (hc : f < sys.circuits.length),
    sys.templates[f].width = sys.width ∧ sys.templates[f].Checked sys.circuits[f]
  arities : ∀ e ∈ sys.arities, sys.arities.lookup e.1 = some e.2
  tags : ∀ e ∈ sys.arities, e.1.1 ≠ (COPY : F)

theorem System.valid_of_check (ok : sys.check = true) : sys.Valid := by
  simp only [System.check, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨⟨w4, wmod⟩, len1⟩, len2⟩, temps⟩, unch⟩, ar⟩, tg⟩ := ok
  have mem : ∀ f (h : f < sys.templates.length) (hc : f < sys.circuits.length),
      (sys.templates[f], sys.circuits[f]) ∈ sys.templates.zip sys.circuits := by
    intro f h hc
    rw [List.mem_iff_getElem]
    exact ⟨f, by simp [h, hc], by simp⟩
  refine ⟨⟨of_decide_eq_true w4, wmod⟩, ⟨len1, len2⟩, ?_,
    fun e he => by simpa using ar e he, fun e he => by simpa using tg e he⟩
  intro f h hc
  have := temps _ (mem f h hc)
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨this.1, Template.checked_of_check _ this.2⟩

/-- Every template of a system accepted by `System.check` has no chunk group. -/
def System.Unchunked : Prop :=
  ∀ f (h : f < sys.templates.length) (hc : f < sys.circuits.length),
    sys.templates[f].checkUnchunked sys.circuits[f] = true

theorem System.unchunked_of_check (ok : sys.check = true) : sys.Unchunked := by
  simp only [System.check, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  intro f h hc
  apply ok.1.1.2 (sys.templates[f], sys.circuits[f])
  rw [List.mem_iff_getElem]
  exact ⟨f, by simp [h, hc], by simp⟩

variable {sys}

/-- The part of `System.Valid` that the copy argument reads: template widths
and cell slots. -/
structure System.CellsValid : Prop where
  templates : ∀ f (h : f < sys.templates.length), sys.templates[f].width = sys.width ∧
    ∀ row ∈ sys.templates[f].rows, ∀ cell ∈ row.cells, ∀ s ∈ cell, s < sys.templates[f].slots.length

theorem System.Valid.cells (valid : sys.Valid) : sys.CellsValid :=
  ⟨fun f hf => by
    obtain ⟨w, checked⟩ := valid.templates f hf (by rw [valid.lengths.1]; exact hf)
    exact ⟨w, checked.cells⟩⟩

theorem System.CellsValid.copyKey_mem (valid : sys.CellsValid) {p j : Nat} {k : Nat × Nat × Nat}
    (h : sys.copyKey p j = some k) : k ∈ sys.keys := by
  obtain ⟨r, T, place, hT, cell⟩ := sys.copyKey_some h
  obtain ⟨f, i, s⟩ := k
  have mem : (f, i, r) ∈ sys.places := List.mem_of_getElem? place
  obtain ⟨hf, hi, _⟩ := sys.mem_places.mp mem
  obtain ⟨T', hT', _, slots⟩ := sys.templates_getElem? hf
  rw [hT] at hT'
  cases hT'
  have checked := (valid.templates f hf).2
  have eq : sys.templates[f] = T := by
    have := List.getElem?_eq_getElem hf
    rw [hT] at this
    exact (Option.some.inj this).symm
  rw [eq] at checked
  obtain ⟨row, hrow, hcell⟩ := Template.cell_some cell
  have := checked row (List.mem_of_getElem? hrow) (some s) (List.mem_of_getElem? hcell) s rfl
  refine sys.mem_keys.mpr ⟨hf, hi, ?_⟩
  rw [slots]
  simpa [List.getElem?_eq_getElem hf] using this

/-- Cells with the copy label of key `k` are exactly the cells of `k`. -/
theorem System.CellsValid.labelAt_eq (valid : sys.CellsValid) (small : SmallCast F sys.bound) {p j : Nat}
    {k : Nat × Nat × Nat} (hk : k ∈ sys.keys) :
    sys.labelAt p j = (sys.label k.1 k.2.1 k.2.2 : F) ↔ sys.copyKey p j = some k := by
  have lt := sys.label_lt (f := k.1) (i := k.2.1) (s := k.2.2) hk
  have bound : sys.keys.length + 1 ≤ sys.bound := by simp only [System.bound]; omega
  constructor
  · intro h
    cases found : sys.copyKey p j with
    | some k' =>
      simp only [System.labelAt, found] at h
      have hk' := valid.copyKey_mem found
      have lt' := sys.label_lt (f := k'.1) (i := k'.2.1) (s := k'.2.2) hk'
      have := small.inj (Nat.lt_of_lt_of_le lt' bound) (Nat.lt_of_lt_of_le lt bound) h
      simp only [System.label, Nat.add_right_cancel_iff] at this
      rw [sys.label_inj hk' hk this]
    | none =>
      simp only [System.labelAt, found] at h
      have := small (sys.label k.1 k.2.1 k.2.2) (by omega) h.symm
      simp [System.label] at this
  · intro h
    simp [System.labelAt, h]

theorem System.copyKey_placed {p f i r : Nat} {T : Template F} (place : sys.places[p]? = some (f, i, r))
    (hT : sys.templates[f]? = some T) (j : Nat) :
    sys.copyKey p j = (T.cell r j).map fun s => (f, i, s) := by
  simp [System.copyKey, place, hT]

theorem System.multAt_placed {p f i r : Nat} {T : Template F} (place : sys.places[p]? = some (f, i, r))
    (hT : sys.templates[f]? = some T) {j s : Nat} (cell : T.cell r j = some s) :
    sys.multAt p j = if T.anchor s = some (r, j) then (T.occurrences s : F) - 1 else -1 := by
  simp [System.multAt, place, hT, cell]

theorem SmallCast.mono {a b : Nat} (small : SmallCast F b) (le : a ≤ b) : SmallCast F a :=
  fun n lt => small n (by omega)

/-- Copy balance: every cell of a slot holds the value at the slot's anchor. -/
theorem System.CellsValid.copy (valid : sys.CellsValid) (small : SmallCast F sys.bound)
    {N : Nat} (tall : sys.places.length ≤ N) {main : Nat → Nat → F}
    (balanced : ∀ k ∈ sys.keys, ∀ v, sys.copyCoefficient N main (sys.label k.1 k.2.1 k.2.2) v = 0)
    {f i r j s : Nat} (place : (f, i, r) ∈ sys.places) {T : Template F}
    (hT : sys.templates[f]? = some T) (hj : j < sys.width) (cell : T.cell r j = some s) :
    ∃ ra ja, T.anchor s = some (ra, ja) ∧ main (sys.row f i r) j = main (sys.row f i ra) ja := by
  obtain ⟨hf, hi, _⟩ := sys.mem_places.mp place
  have width : T.width = sys.width := by
    have := (valid.templates f hf).1
    rwa [show sys.templates[f] = T by
      have := List.getElem?_eq_getElem hf; rw [hT] at this; exact (Option.some.inj this).symm] at this
  obtain ⟨row, hrow, _⟩ := Template.cell_some cell
  have hr : r < T.rows.length := (List.getElem?_eq_some_iff.mp hrow).1
  obtain ⟨ra, ja, anchor⟩ := Template.anchor_exists hr (by omega) cell
  obtain ⟨hra, hja, acell⟩ := Template.anchor_spec anchor
  refine ⟨ra, ja, anchor, ?_⟩
  have count : sys.rowCount f = T.rows.length := by simp [System.rowCount, hT]
  have placeA : (f, i, ra) ∈ sys.places := sys.mem_places.mpr ⟨hf, hi, by omega⟩
  have rowPlace (r' : Nat) (h : (f, i, r') ∈ sys.places) : sys.places[sys.row f i r']? = some (f, i, r') := by
    rw [List.getElem?_eq_getElem (sys.row_lt h), sys.places_row h]
  set k₀ : Nat × Nat × Nat := (f, i, s)
  have key : ∀ r' j', (f, i, r') ∈ sys.places → T.cell r' j' = some s →
      sys.copyKey (sys.row f i r') j' = some k₀ := by
    intro r' j' h c
    rw [sys.copyKey_placed (rowPlace r' h) hT, c]; rfl
  have hk₀ : k₀ ∈ sys.keys := valid.copyKey_mem (key r j place cell)
  set S := (Finset.range N ×ˢ Finset.range sys.width).filter fun e => sys.copyKey e.1 e.2 = some k₀
  set e₀ : Nat × Nat := (sys.row f i ra, ja)
  have memS : ∀ r' j', (f, i, r') ∈ sys.places → j' < sys.width → T.cell r' j' = some s →
      (sys.row f i r', j') ∈ S := by
    intro r' j' h hj' c
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨by have := sys.row_lt h; omega, hj'⟩, key r' j' h c⟩
  have inS : ∀ e ∈ S, ∃ r', sys.places[e.1]? = some (f, i, r') ∧ T.cell r' e.2 = some s ∧
      e.2 < sys.width := by
    intro e he
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at he
    obtain ⟨r', T', place', hT', c⟩ := sys.copyKey_some he.2
    rw [hT] at hT'; cases hT'
    exact ⟨r', place', c, he.1.2⟩
  have e₀S : e₀ ∈ S := memS ra ja placeA (by omega) acell
  have card : S.card = T.occurrences s := by
    apply Finset.card_bij (fun e _ => ((sys.places[e.1]?.map (·.2.2)).getD 0, e.2))
    · intro e he
      obtain ⟨r', place', c, hj'⟩ := inS e he
      obtain ⟨row', hrow', _⟩ := Template.cell_some c
      simp only [place', Option.map_some, Option.getD_some, Template.occurrences, Finset.mem_filter,
        Finset.mem_product, Finset.mem_range]
      exact ⟨⟨(List.getElem?_eq_some_iff.mp hrow').1, by omega⟩, c⟩
    · intro e he e' he' same
      obtain ⟨r', place', _, _⟩ := inS e he
      obtain ⟨r'', place'', _, _⟩ := inS e' he'
      simp only [place', place'', Option.map_some, Option.getD_some, Prod.mk.injEq] at same
      obtain ⟨rfl, eq2⟩ := same
      have l1 := (List.getElem?_eq_some_iff.mp place').1
      have l2 := (List.getElem?_eq_some_iff.mp place'').1
      have := (sys.places_nodup.getElem_inj_iff (hi := l1) (hj := l2)).mp (by
        rw [(List.getElem?_eq_some_iff.mp place').2, (List.getElem?_eq_some_iff.mp place'').2])
      exact Prod.ext this eq2
    · intro b hb
      simp only [Template.occurrences, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hb
      obtain ⟨⟨hr', hj'⟩, c⟩ := hb
      have h : (f, i, b.1) ∈ sys.places := sys.mem_places.mpr ⟨hf, hi, by omega⟩
      refine ⟨(sys.row f i b.1, b.2), memS b.1 b.2 h (by omega) c, ?_⟩
      simp [rowPlace b.1 h]
  have sub : S ⊆ Finset.range sys.places.length ×ˢ Finset.range sys.width := by
    intro e he
    obtain ⟨_, place', _, hj'⟩ := inS e he
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨(List.getElem?_eq_some_iff.mp place').1, hj'⟩
  have small' : SmallCast F S.card := small.mono (by
    have := Finset.card_le_card sub
    simp only [Finset.card_product, Finset.card_range] at this
    simp only [System.bound]; omega)
  have classEq := copy_class S e₀ e₀S (fun e => sys.multAt e.1 e.2) (fun e => main e.1 e.2)
    (by
      simp only [e₀]
      rw [sys.multAt_placed (rowPlace ra placeA) hT acell, if_pos anchor, card])
    (by
      intro e he ne
      obtain ⟨r', place', c, _⟩ := inS e he
      rw [sys.multAt_placed place' hT c, if_neg]
      intro same
      rw [anchor] at same
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      apply ne
      have l1 := (List.getElem?_eq_some_iff.mp place').1
      have : e.1 = sys.row f i ra := by
        have := sys.row_places l1
        rw [(List.getElem?_eq_some_iff.mp place').2] at this
        exact this.symm
      exact Prod.ext this rfl)
    (by
      have := balanced k₀ hk₀ (main e₀.1 e₀.2)
      unfold System.copyCoefficient at this
      rw [← Finset.sum_product' (f := fun p j =>
        if sys.labelAt p j = (sys.label f i s : F) ∧ main p j = main e₀.1 e₀.2 then sys.multAt p j
        else 0)] at this
      simp only [S]
      rw [Finset.sum_filter, Finset.sum_filter]
      refine Eq.trans ?_ this
      apply Finset.sum_congr rfl
      intro e _
      have iff := valid.labelAt_eq small (p := e.1) (j := e.2) hk₀
      by_cases hc : sys.copyKey e.1 e.2 = some k₀
      · have hl : sys.labelAt e.1 e.2 = (sys.label f i s : F) := iff.mpr hc
        simp only [hc, hl, true_and, ite_true]
      · have hl : ¬ sys.labelAt e.1 e.2 = (sys.label f i s : F) := fun h => hc (iff.mp h)
        simp only [hc, hl, false_and, ite_false])
    small'
  exact classEq (sys.row f i r, j) (memS r j place hj cell)

theorem System.Valid.copy (valid : sys.Valid) (small : SmallCast F sys.bound)
    {N : Nat} (tall : sys.places.length ≤ N) {main : Nat → Nat → F}
    (balanced : ∀ L v, sys.copyCoefficient N main L v = 0)
    {f i r j s : Nat} (place : (f, i, r) ∈ sys.places) {T : Template F}
    (hT : sys.templates[f]? = some T) (hj : j < sys.width) (cell : T.cell r j = some s) :
    ∃ ra ja, T.anchor s = some (ra, ja) ∧ main (sys.row f i r) j = main (sys.row f i ra) ja :=
  valid.cells.copy small tall (fun _ _ v => balanced _ v) place hT hj cell

end Copy

end Aiur.Tiling
