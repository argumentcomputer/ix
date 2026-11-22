import Aiur.Tiling.PeriodicSystem

/-!
# The fixed matrix in closed form

`Sharded.fixedAt L p c` reads the place, label and copy multiplicity of row
`p` through list indices (`System.places[p]?`, `System.label` as an
`idxOf`, `Template.anchor` and `Template.occurrences` as searches over all
cells), so generating a matrix through it is quadratic. `Sharded.fastRow` is
the row of place `(f, i, r)` with closed forms:

* row `p = blockBase rowCount f + i·rowCount f + r` (`System.places_closed`);
* label `blockBase slotCount f + i·slotCount f + s + 1` (`System.label_closed`);
* the copy multiplicity from one pass over the template's cells
  (`Template.multFast`, `Template.multFast_eq`).

`Sharded.fastRow_eq` proves it equal to `fixedAt`.
-/

namespace Aiur.Tiling

variable {F : Type}

namespace System

variable (sys : System F)

/-- The index of circuit `f`'s first entry in `enumerate count`. -/
def blockBase (count : Nat → Nat) (f : Nat) : Nat := ((List.range f).map fun f' => sys.cap f' * count f').sum

theorem enumerate_closed (count : Nat → Nat) {f i x : Nat} (hf : f < sys.templates.length)
    (hi : i < sys.cap f) (hx : x < count f) :
    (sys.enumerate count)[sys.blockBase count f + i * count f + x]? = some (f, i, x) := by
  let inner : Nat → List (Nat × Nat × Nat) := fun f =>
    ((List.range (sys.cap f)).flatMap fun i => (List.range (count f)).map fun x => (i, x)).map fun ix => (f, ix)
  have len : ∀ f, (inner f).length = sys.cap f * count f := by
    intro f; simp [inner, List.length_flatMap, List.map_const', List.sum_replicate, mul_comm]
  have base : ((List.range sys.templates.length).take f).map (fun b => (inner b).length) =
      (List.range f).map fun f' => sys.cap f' * count f' := by
    rw [List.take_range, Nat.min_eq_left hf.le]
    simp [len]
  have lt : i * count f + x < (inner ((List.range sys.templates.length)[f]'(by simpa using hf))).length := by
    rw [List.getElem_range, len]
    have : i * count f + x < (i + 1) * count f := by rw [Nat.succ_mul]; omega
    exact Nat.lt_of_lt_of_le this (Nat.mul_le_mul_right _ hi)
  have outer := Periodic.getElem?_flatMap_base inner (List.range sys.templates.length) (k := f)
    (by simpa using hf) lt
  rw [base] at outer
  simp only [List.getElem_range] at outer
  rw [enumerate, blockBase, Nat.add_assoc, outer]
  simp only [inner, List.getElem?_map]
  let g : Nat → List (Nat × Nat) := fun i => (List.range (count f)).map fun x => (i, x)
  have glen : ∀ i, (g i).length = count f := by simp [g]
  have b2 : ((List.range (sys.cap f)).take i).map (fun b => (g b).length) = List.replicate i (count f) := by
    rw [List.take_range, Nat.min_eq_left hi.le]
    simp [glen, List.map_const']
  have l2 : x < (g ((List.range (sys.cap f))[i]'(by simpa using hi))).length := by
    rw [glen]; exact hx
  have in2 := Periodic.getElem?_flatMap_base g (List.range (sys.cap f)) (k := i) (by simpa using hi) l2
  rw [b2, List.sum_replicate, smul_eq_mul] at in2
  simp only [List.getElem_range] at in2
  rw [in2]
  simp [g, hx]

theorem idxOf_getElem_nodup {α : Type} [BEq α] [LawfulBEq α] {l : List α} (nd : l.Nodup) {n : Nat} (h : n < l.length) :
    l.idxOf l[n] = n := by
  have lt : l.idxOf l[n] < l.length := List.idxOf_lt_length_of_mem (List.getElem_mem h)
  exact (List.Nodup.getElem_inj_iff nd (hi := lt) (hj := h)).mp (List.getElem_idxOf lt)

theorem places_closed {f i r : Nat} (hf : f < sys.templates.length) (hi : i < sys.cap f)
    (hr : r < sys.rowCount f) :
    sys.places[sys.blockBase sys.rowCount f + i * sys.rowCount f + r]? = some (f, i, r) :=
  sys.enumerate_closed _ hf hi hr

theorem label_closed {f i s : Nat} (hf : f < sys.templates.length) (hi : i < sys.cap f)
    (hs : s < sys.slotCount f) :
    sys.label f i s = sys.blockBase sys.slotCount f + i * sys.slotCount f + s + 1 := by
  have h := sys.enumerate_closed sys.slotCount hf hi hs
  have lt := (List.getElem?_eq_some_iff.mp h).1
  have e := (List.getElem?_eq_some_iff.mp h).2
  rw [label, keys, ← e, idxOf_getElem_nodup (sys.enumerate_nodup _) lt]

end System

/-! ## Copy multiplicities from the cell list -/

section Mult

variable [DecidableEq F]

/-- The cells of a template in `cellIndices` order. -/
def Template.cellList (T : Template F) : List (Option Nat) := T.cellIndices.map fun e => T.cell e.1 e.2

theorem find?_eq_getElem_idxOf {α β : Type} [BEq β] [LawfulBEq β] (g : α → β) (v : β) :
    ∀ l : List α, l.find? (fun e => g e == v) = l[(l.map g).idxOf v]?
  | [] => by simp
  | a :: l => by
      by_cases h : g a = v
      · simp [h]
      · rw [List.find?_cons_of_neg (by simpa using h), List.map_cons, List.idxOf_cons]
        simp [h, find?_eq_getElem_idxOf g v l]

theorem Template.anchor_eq (T : Template F) (s : Nat) :
    T.anchor s = T.cellIndices[T.cellList.idxOf (some s)]? := by
  rw [cellList, ← find?_eq_getElem_idxOf (fun e : Nat × Nat => T.cell e.1 e.2) (some s) T.cellIndices]
  unfold anchor
  congr 1

theorem Template.cellIndices_nodup (T : Template F) : T.cellIndices.Nodup := by
  unfold cellIndices
  rw [List.nodup_flatMap]
  refine ⟨fun r _ => List.Nodup.map (fun a b h => by simpa using h) List.nodup_range, ?_⟩
  apply List.Pairwise.imp _ List.nodup_range
  intro a b ne x hx hy
  simp only [List.mem_map] at hx hy
  obtain ⟨_, _, rfl⟩ := hx
  obtain ⟨_, _, e⟩ := hy
  exact ne (by simp at e; omega)

theorem Template.mem_cellIndices {T : Template F} {e : Nat × Nat} :
    e ∈ T.cellIndices ↔ e.1 < T.rows.length ∧ e.2 < T.width := by
  rcases e with ⟨r, j⟩
  simp [cellIndices]

theorem Template.occurrences_eq (T : Template F) (s : Nat) : T.occurrences s = T.cellList.count (some s) := by
  have prod : Finset.range T.rows.length ×ˢ Finset.range T.width = T.cellIndices.toFinset := by
    ext e; simp [Template.mem_cellIndices]
  rw [occurrences, cellList, List.count_eq_countP, List.countP_map, prod, List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((T.cellIndices_nodup).filter _), List.toFinset_filter]
  congr 1
  ext e
  simp

/-- The copy multiplicity of cell `(r, j)`, as `System.multAt` assigns it. -/
def Template.multSpec [Zero F] [One F] [Neg F] [Sub F] [NatCast F] (T : Template F) (r j : Nat) : F :=
  match T.cell r j with
  | some s => if T.anchor s = some (r, j) then (T.occurrences s : F) - 1 else -1
  | none => 0

/-- `multSpec` from the cell list: the first index and the count of each value. -/
def Template.multFast [Zero F] [One F] [Neg F] [Sub F] [NatCast F] (T : Template F) (cells : List (Option Nat))
    (first count : Nat → Nat) (r j : Nat) : F :=
  match cells[r * T.width + j]? with
  | some (some s) => if first s = r * T.width + j then (count s : F) - 1 else -1
  | _ => 0

theorem Template.cellIndices_closed (T : Template F) {r j : Nat} (hr : r < T.rows.length) (hj : j < T.width) :
    T.cellIndices[r * T.width + j]? = some (r, j) := by
  have := Periodic.getElem?_flatMap_base (fun r => (List.range T.width).map fun j => (r, j)) (List.range T.rows.length)
    (k := r) (f' := j) (by simpa using hr) (by simpa using hj)
  rw [List.take_range, Nat.min_eq_left hr.le] at this
  simp only [List.length_map, List.length_range, List.map_const', List.sum_replicate, smul_eq_mul,
    List.getElem_range] at this
  rw [cellIndices, this]
  simp [hj]

theorem Template.multFast_eq [Field F] (T : Template F) {r j : Nat} (hr : r < T.rows.length) (hj : j < T.width) :
    T.multFast T.cellList (fun s => T.cellList.idxOf (some s)) (fun s => T.cellList.count (some s)) r j =
      T.multSpec r j := by
  have ci := T.cellIndices_closed hr hj
  have cl : T.cellList[r * T.width + j]? = some (T.cell r j) := by simp [cellList, ci]
  simp only [multFast, multSpec, cl]
  cases hc : T.cell r j with
  | none => rfl
  | some s =>
      simp only [anchor_eq, occurrences_eq]
      congr 1
      apply propext
      constructor
      · intro h; rw [h, ci]
      · intro h
        have hlen : T.cellList.idxOf (some s) < T.cellIndices.length := by
          by_contra n
          rw [List.getElem?_eq_none (by omega)] at h
          cases h
        have hlt : r * T.width + j < T.cellIndices.length := (List.getElem?_eq_some_iff.mp ci).1
        have e1 := (List.getElem?_eq_some_iff.mp h).2
        have e2 := (List.getElem?_eq_some_iff.mp ci).2
        exact (List.Nodup.getElem_inj_iff T.cellIndices_nodup (hi := hlen) (hj := hlt)).mp (e1.trans e2.symm)

end Mult

/-! ## Fixed rows of a v2 layout -/

namespace Periodic

namespace Sharded

variable [Field F] [DecidableEq F] (S : Sharded F)

/-- The fixed columns of a row that no instance changes: gates, flags, lane messages. -/
def staticCols (T : Template2 F) (row : Row2 F) : List F :=
  (List.range (lanes S.width)).flatMap (fun l => (List.range 6).map (row.gateCoef l)) ++
  (List.range (lanes S.width)).flatMap (fun l => (List.range (flagBlock S.width l)).map fun d => row.flag l (l + d)) ++
  (List.range (lanes S.width)).flatMap (fun l => (List.range 3).map (row.laneMsg T S.buses l))

/-- Whether the row's `rkey` column carries the instance id. -/
def _root_.Aiur.Tiling.Periodic.Row2.keyFlag (T : Template2 F) : Row2 F → Bool
  | .message m key => key && (T.messages[m]?).isSome
  | .gate .. => false

/-- A fixed row from its per-row parts: the static columns `pre`, the row
message columns `rm` at id 0, the cells and multiplicities, the label base
`lb` of the instance and its id. -/
def emit (pre rm : List F) (key : Bool) (cells : List (Option Nat)) (mults : List F) (lb : Nat) (id : F) :
    List F :=
  pre ++ ((List.range 5).map fun k => if k = 3 then (if key then id else 0) else rm.getD k 0) ++
    ((List.range S.width).map fun j =>
      match cells.getD j none with
      | some s => ((lb + s + 1 : Nat) : F)
      | none => 0) ++
    (List.range S.width).map fun j => mults.getD j 0

/-- One template's copy multiplicities, computed once from its cell list. -/
def multTable (T : Template2 F) : Array (Array F) :=
  let cells := T.shadow.cellList
  let first := ((List.range T.slots.length).map fun s => cells.idxOf (some s)).toArray
  let count := ((List.range T.slots.length).map fun s => cells.count (some s)).toArray
  ((List.range T.rows.length).map fun r => ((List.range T.width).map fun j =>
    T.shadow.multFast cells (fun s => first[s]?.getD (cells.idxOf (some s)))
      (fun s => count[s]?.getD (cells.count (some s))) r j).toArray).toArray

def multOf (T : Template2 F) (table : Array (Array F)) (r j : Nat) : F :=
  ((table[r]?).bind (·[j]?)).getD (T.shadow.multSpec r j)

theorem getD_map_range {α : Type} (n : Nat) (g : Nat → α) (s : Nat) :
    (((List.range n).map g).toArray[s]?).getD (g s) = g s := by
  rw [List.getElem?_toArray]
  by_cases h : s < n
  · simp [h]
  · simp [h]

variable {S}

theorem multOf_eq (T : Template2 F) (r j : Nat) : multOf T (multTable T) r j = T.shadow.multSpec r j := by
  have sw : T.shadow.width = T.width := rfl
  have sr : T.shadow.rows.length = T.rows.length := by simp [Template2.shadow]
  unfold multOf multTable
  simp only [getD_map_range]
  by_cases hr : r < T.rows.length
  · by_cases hj : j < T.width
    · simp only [List.getElem?_toArray, List.getElem?_map, List.getElem?_range hr, List.getElem?_range hj,
        Option.map_some, Option.bind_some, Option.getD_some, List.getElem?_toArray]
      exact Template.multFast_eq T.shadow (by rw [sr]; exact hr) (by rw [sw]; exact hj)
    · simp [List.getElem?_toArray, hr, hj]
  · simp [List.getElem?_toArray, hr]

theorem rowMsg_id (T : Template2 F) (buses : Buses F) (row : Row2 F) (id : F) {k : Nat} (hk : k < 5) :
    row.rowMsg T buses id k = if k = 3 then (if row.keyFlag T then id else 0) else row.rowMsg T buses 0 k := by
  cases row with
  | gate => simp [Row2.rowMsg, Row2.keyFlag]
  | message m key =>
      simp only [Row2.rowMsg, Row2.keyFlag]
      split
      · rename_i h
        simp only [h, Option.isSome_some, Bool.and_true]
        match k, hk with
        | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp
      · rename_i h
        simp [h]

theorem getD_map_range' {α : Type} [Zero α] (n : Nat) (g : Nat → α) {k : Nat} (hk : k < n) :
    ((List.range n).map g).getD k 0 = g k := by
  simp [List.getD_eq_getElem?_getD, hk]

/-- **The emitted row is the fixed row.** With `pre`, `rm`, `cells` and
`mults` the row's parts and `lb` the closed-form label base of instance `i`,
`emit` is `Sharded.fixedAt` at the place's closed-form index. -/
theorem emit_eq (L : Layout F) {f i r : Nat} {T : Template2 F} {row : Row2 F} (hf : f < L.templates.length)
    (hT : L.templates[f]? = some T) (hi : i < (L.shadow S.width).cap f) (hrow : T.rows[r]? = some row)
    (inSlots : ∀ s, some s ∈ T.rowCells row → s < T.slots.length) (c : Nat) :
    ((S.emit (S.staticCols T row) ((List.range 5).map (row.rowMsg T S.buses 0)) (row.keyFlag T) (T.rowCells row)
        ((List.range S.width).map (multOf T (multTable T) r))
        ((L.shadow S.width).blockBase (L.shadow S.width).slotCount f + i * (L.shadow S.width).slotCount f)
        ((L.shadow S.width).instId f i : F))[c]?).getD 0 =
      S.fixedAt L ((L.shadow S.width).blockBase (L.shadow S.width).rowCount f +
        i * (L.shadow S.width).rowCount f + r) c := by
  set sh := L.shadow S.width
  have hr : r < T.rows.length := (List.getElem?_eq_some_iff.mp hrow).1
  have hsh : sh.templates[f]? = some T.shadow := by simp [sh, Layout.shadow, hT]
  have rc : sh.rowCount f = T.rows.length := by simp [System.rowCount, hsh, Template2.shadow]
  have sc : sh.slotCount f = T.slots.length := by simp [System.slotCount, hsh, Template2.shadow]
  have hf' : f < sh.templates.length := by simpa [sh, Layout.shadow] using hf
  have place := sh.places_closed (f := f) (i := i) (r := r) hf' hi (by rw [rc]; exact hr)
  set p := sh.blockBase sh.rowCount f + i * sh.rowCount f + r
  have cellEq : ∀ j, (T.rowCells row).getD j none = T.shadow.cell r j := by
    intro j
    rw [Template.cell_of (show T.shadow.rows[r]? = some (.message 0 0 0 (T.rowCells row)) by
      simp [Template2.shadow, hrow])]
    simp [Row.cells, List.getD_eq_getElem?_getD]
  have lab : ∀ j, (match (T.rowCells row).getD j none with
      | some s => (((sh.blockBase sh.slotCount f + i * sh.slotCount f) + s + 1 : Nat) : F)
      | none => 0) = sh.labelAt p j := by
    intro j
    simp only [System.labelAt, sh.copyKey_placed place hsh j, ← cellEq j]
    cases hc : (T.rowCells row).getD j none with
    | none => rfl
    | some s =>
        have mem : some s ∈ T.rowCells row := by
          rw [List.getD_eq_getElem?_getD] at hc
          cases h : (T.rowCells row)[j]? with
          | none => rw [h] at hc; cases hc
          | some x => rw [h] at hc; simp at hc; subst hc; exact List.mem_of_getElem? h
        simp only [Option.map_some]
        rw [sh.label_closed hf' hi (by rw [sc]; exact inSlots s mem)]
  have mul : ∀ j, multOf T (multTable T) r j = sh.multAt p j := by
    intro j
    rw [multOf_eq]
    cases hc : T.shadow.cell r j with
    | none => simp [Template.multSpec, hc, System.multAt, place, hsh]
    | some s => rw [sh.multAt_placed place hsh hc]; simp [Template.multSpec, hc]
  have row_eq : S.emit (S.staticCols T row) ((List.range 5).map (row.rowMsg T S.buses 0)) (row.keyFlag T)
      (T.rowCells row) ((List.range S.width).map (multOf T (multTable T) r))
      (sh.blockBase sh.slotCount f + i * sh.slotCount f) (sh.instId f i : F) =
      fixedRow S.width row.gateCoef row.flag (row.laneMsg T S.buses)
        (row.rowMsg T S.buses (sh.instId f i : F)) (sh.labelAt p) (sh.multAt p) := by
    have e1 : ((List.range 5).map fun k => if k = 3 then (if row.keyFlag T then (sh.instId f i : F) else 0)
        else ((List.range 5).map (row.rowMsg T S.buses 0)).getD k 0) =
        (List.range 5).map (row.rowMsg T S.buses (sh.instId f i : F)) := by
      apply List.map_congr_left
      intro k hk
      have hk := List.mem_range.mp hk
      rw [rowMsg_id T S.buses row _ hk, getD_map_range' 5 _ hk]
    have e2 : ((List.range S.width).map fun j => match (T.rowCells row).getD j none with
        | some s => (((sh.blockBase sh.slotCount f + i * sh.slotCount f) + s + 1 : Nat) : F)
        | none => 0) = (List.range S.width).map (sh.labelAt p) :=
      List.map_congr_left (fun j _ => lab j)
    have e3 : ((List.range S.width).map fun j => ((List.range S.width).map (multOf T (multTable T) r)).getD j 0) =
        (List.range S.width).map (sh.multAt p) := by
      apply List.map_congr_left
      intro j hj
      rw [getD_map_range' _ _ (List.mem_range.mp hj), mul j]
    simp only [emit, staticCols, fixedRow, List.append_assoc]
    rw [e1, e2, e3]
  have place' : (L.shadow S.width).places[p]? = some (f, i, r) := place
  rw [row_eq]
  unfold fixedAt
  simp only [place', hT, hrow]
  rfl

end Sharded

end Periodic

end Aiur.Tiling
