import Aiur.Tiling.PeriodicSystem

/-!
# Relations of the logical system hold

Given shard traces whose rows satisfy their shard circuit and whose physical
cells hold their slots' anchor values, the logical system with the synthetic
trace `mainV` is a `System.Logical`: every span row holds by `Placed.span`,
and every pin row holds because `valV` gives invocation slots the instance's
id.
-/

namespace Aiur.Tiling.Periodic

open Aiur.Scalar.Circuit (ArithExpr Var Satisfies)

variable {F : Type} [Field F] [DecidableEq F]

theorem mem_logical_rows {T : Template2 F} {row : Row F} (h : row ∈ T.logical.rows) :
    (∃ (r : Nat) (ls : List (LaneUse F)) (spans : List Span) (sp : Span),
        T.rows[r]? = some (Row2.gate ls spans) ∧ sp ∈ spans ∧
        row = .gate (spanLanes T.width ls sp) true [sp.role]) ∨
      (∃ s, T.slots[s]? = some .invocation ∧ row = pinRow T.width s) ∨
      (∃ s ∈ T.virtual, row = virtualRow T.width s ((T.slots[s]?).getD (.key 0))) ∨
      (∃ v ∈ T.booleans, row = boolRow T.width v) ∨
      (∃ sel tag sub cells, row = .message sel tag sub cells) := by
  simp only [Template2.logical, List.mem_append, List.mem_flatMap] at h
  rcases h with (((⟨r2, hr2, hrow⟩ | hpin) | hvirt) | hbool) | hmsg
  · left
    obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hr2
    cases hrw : T.rows[r] with
    | message => rw [hrw] at hrow; simp [Row2.logical] at hrow
    | gate ls spans =>
        rw [hrw] at hrow
        simp only [Row2.logical, List.mem_map] at hrow
        obtain ⟨sp, hsp, rfl⟩ := hrow
        exact ⟨r, ls, spans, sp, by rw [List.getElem?_eq_getElem hr, hrw], hsp, rfl⟩
  · right; left
    simp only [Template2.pins, List.mem_filterMap] at hpin
    obtain ⟨⟨d, s⟩, hds, hrow⟩ := hpin
    split at hrow
    · rename_i hd
      simp only [Option.some.injEq] at hrow
      subst hrow hd
      exact ⟨s, (List.mk_mem_zipIdx_iff_getElem?.mp hds), rfl⟩
    · simp at hrow
  · right; right; left
    simp only [Template2.virtualRows, List.mem_map] at hvirt
    obtain ⟨s, hs, rfl⟩ := hvirt
    exact ⟨s, hs, rfl⟩
  · right; right; right; left
    simp only [Template2.boolRows, List.mem_map] at hbool
    obtain ⟨v, hv, rfl⟩ := hbool
    exact ⟨v, hv, rfl⟩
  · right; right; right; right
    simp only [Template2.messageRows, List.mem_map] at hmsg
    obtain ⟨⟨sel, tag, sub, cells⟩, _, rfl⟩ := hmsg
    exact ⟨sel, tag, sub, cells, rfl⟩

theorem cell_of_mem {T : Template F} {row : Row F} (h : row ∈ T.rows) {j s : Nat}
    (hc : row.cells[j]? = some (some s)) : ∃ r < T.rows.length, T.cell r j = some s := by
  obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem h
  exact ⟨r, hr, by rw [Template.cell_of (List.getElem?_eq_getElem hr), hc]; rfl⟩

theorem length_laneCells (T : Template2 F) (u : LaneUse F) : (T.laneCells u).length = 4 := by
  cases u <;> simp [Template2.laneCells, Lane.cells]

theorem flatMap_laneCells_getElem? (T : Template2 F) (ls : List (LaneUse F)) {l m : Nat}
    (hl : l < ls.length) (hm : m < 4) : (ls.flatMap T.laneCells)[4 * l + m]? = (T.laneCells ls[l])[m]? := by
  induction ls generalizing l with
  | nil => simp at hl
  | cons a rest ih =>
      rw [List.flatMap_cons]
      cases l with
      | zero => rw [List.getElem?_append_left (by rw [length_laneCells]; omega)]; simp
      | succ l =>
          rw [List.getElem?_append_right (by rw [length_laneCells]; omega), length_laneCells,
            show 4 * (l + 1) + m - 4 = 4 * l + m by omega]
          simpa using ih (l := l) (by simpa using hl)

theorem Lane.zero_poly (idv : Nat) (val : Nat → F) : (Lane.poly idv (Lane.zero : Lane F)).denote val = 0 := by
  simp [Lane.poly, Lane.zero, cellPoly]

theorem sum_spanLanes (W : Nat) (ls : List (LaneUse F)) (sp : Span) (fits : sp.start + sp.len ≤ ls.length)
    (g : Lane F → F) (zero : g Lane.zero = 0) :
    ((spanLanes W ls sp).map g).sum = ((List.range' sp.start sp.len).map fun l => g (laneAt ls l)).sum := by
  rw [spanLanes, List.map_append, List.sum_append, List.map_replicate, zero, List.sum_replicate,
    smul_zero, add_zero, List.map_map]
  congr 1
  apply List.ext_getElem (by simp; omega)
  intro d h1 h2
  simp only [List.getElem_map, List.getElem_range', Function.comp, laneAt, List.getElem_take,
    List.getElem_drop, Nat.mul_one]
  rw [Nat.one_mul, List.getElem?_eq_getElem (show sp.start + d < ls.length by simp at h2; omega)]
  rfl

namespace Sharded

variable {S : Sharded F}

/-- The facts about shard traces that the logical relations read. -/
structure ShardTrace (S : Sharded F) (H : Nat → Nat) (main : Nat → Nat → Nat → F) : Prop where
  tall : ∀ k < S.shards.length, ((S.layout k).shadow S.width).places.length ≤ H k
  rows : ∀ k < S.shards.length, ∀ p < H k, Satisfies (S.circuit k).constraints (S.assign k (main k) p)
  consistent : ∀ k < S.shards.length, ∀ f i r, (f, i, r) ∈ ((S.layout k).shadow S.width).places →
    ∀ T, ((S.layout k).shadow S.width).templates[f]? = some T → ∀ j < S.width, ∀ s, T.cell r j = some s →
      main k (((S.layout k).shadow S.width).row f i r) j = ((S.layout k).shadow S.width).slotValue (main k) f i s

theorem valV_physical {main : Nat → Nat → Nat → F} {k f' : Nat} (hk : k < S.shards.length)
    (hf : f' < (S.layout k).templates.length) {T : Template2 F} (hT : (S.layout k).templates[f']? = some T)
    {s : Nat} (ns : T.slots[s]? ≠ some .invocation) (nv : s ∉ T.virtual) (i : Nat) :
    S.valV main (S.base k + f') i s = ((S.layout k).shadow S.width).slotValue (main k) f' i s := by
  have ht := system_template k hk hf
  rw [hT] at ht
  simp only [valV, ht, Option.map_some, Option.bind_some, Template2.logical, locate_at hk hf, hT]
  rw [if_neg ns, if_neg nv]

theorem valV_virtual {main : Nat → Nat → Nat → F} {k f' : Nat} (hk : k < S.shards.length)
    (hf : f' < (S.layout k).templates.length) {T : Template2 F} (hT : (S.layout k).templates[f']? = some T)
    {s : Nat} (ns : T.slots[s]? ≠ some .invocation) (hv : s ∈ T.virtual) (i : Nat) :
    S.valV main (S.base k + f') i s =
      T.virtualValue (((S.layout k).shadow S.width).slotValue (main k) f' i) s := by
  have ht := system_template k hk hf
  rw [hT] at ht
  simp only [valV, ht, Option.map_some, Option.bind_some, Template2.logical, locate_at hk hf, hT]
  rw [if_neg ns, if_pos hv]

theorem VirtualOk.cell (virt : S.VirtualOk) {k : Nat} (hk : k < S.shards.length) {T : Template2 F}
    (hT : T ∈ (S.layout k).templates) {row : Row2 F} (hrow : row ∈ T.rows) {s : Nat}
    (hc : some s ∈ T.rowCells row) : s ∉ T.virtual := by
  have := virt k hk T hT
  simp only [Template2.checkVirtual, Bool.and_eq_true, List.all_eq_true] at this
  have := this.1.1 row hrow _ hc
  simpa using this

/-- A virtual slot is `k + c·x` with `x` neither virtual nor an invocation slot,
or a constant. -/
theorem VirtualOk.def (virt : S.VirtualOk) {k : Nat} (hk : k < S.shards.length) {T : Template2 F}
    (hT : T ∈ (S.layout k).templates) {v : Nat} (hv : v ∈ T.virtual) :
    (∃ c x k', T.slots[v]? = some (.sum [.linear c x] k') ∧ x < T.slots.length ∧
        T.slots[x]? ≠ some .invocation ∧ x ∉ T.virtual) ∨
      ∃ k', T.slots[v]? = some (.sum [] k') := by
  have := virt k hk T hT
  simp only [Template2.checkVirtual, Bool.and_eq_true, List.all_eq_true] at this
  have ok := this.1.2 v hv
  simp only [Template2.virtualOk] at ok
  split at ok
  · rename_i c x k' h
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, Bool.not_eq_true',
      List.contains_iff_mem] at ok
    left; exact ⟨c, x, k', h, ok.1.1, ok.1.2, by simpa using ok.2⟩
  · rename_i k' h; right; exact ⟨k', h⟩
  · simp at ok

/-- A message with a virtual multiplicity slot has `sel = 1`. -/
theorem VirtualOk.sel (virt : S.VirtualOk) {k : Nat} (hk : k < S.shards.length) {T : Template2 F}
    (hT : T ∈ (S.layout k).templates) {sel tag sub : F} {v : Nat} {rest : List (Option Nat)}
    (hm : (sel, tag, sub, some v :: rest) ∈ T.messages) (hv : v ∈ T.virtual) : sel = 1 := by
  have := virt k hk T hT
  simp only [Template2.checkVirtual, Bool.and_eq_true, List.all_eq_true] at this
  have := this.2 _ hm
  simp only [Bool.or_eq_true, Bool.not_eq_true', List.contains_iff_mem, beq_iff_eq] at this
  rcases this with h | h
  · exact absurd hv (by simpa using h)
  · exact h

/-- **The logical trace.** The logical system, read through `mainV`, satisfies
every relation of every instance. -/
theorem logical (lens : S.Lengths) (rowsOk : S.RowsOk) (virt : S.VirtualOk) (bools : S.BoolOk)
    (valid : S.system.Valid) {H : Nat → Nat}
    {main : Nat → Nat → Nat → F} (trace : S.ShardTrace H main) : S.system.Logical (S.mainV main) := by
  refine ⟨valid, fun f hf i hi T hT => ?_⟩
  obtain ⟨k, f', hk, hf', rfl⟩ := decompose hf
  obtain ⟨T2, hT2⟩ : ∃ T2, (S.layout k).templates[f']? = some T2 :=
    ⟨_, List.getElem?_eq_getElem hf'⟩
  have hsys := system_template k hk hf'
  rw [hT2, hT] at hsys
  simp only [Option.map_some, Option.some.injEq] at hsys
  subst hsys
  have hc : S.base k + f' < S.system.circuits.length := by rw [valid.lengths.1]; exact hf
  obtain ⟨wT, checked⟩ := valid.templates _ hf hc
  have eqT : S.system.templates[S.base k + f'] = T2.logical :=
    Option.some.inj ((List.getElem?_eq_getElem hf).symm.trans hT)
  rw [eqT] at wT checked
  obtain ⟨w2, phys⟩ := rowsOk k hk T2 (List.mem_of_getElem? hT2)
  have physCells := phys
  simp only [Template2.checkPhysical, Bool.and_eq_true, List.all_eq_true] at physCells
  have cap : i < ((S.layout k).shadow S.width).cap f' := by rw [← system_cap lens k hk hf']; exact hi
  have idv : S.system.slotValue (S.mainV main) (S.base k + f') i T2.logical.idVar =
      (S.system.instId (S.base k + f') i : F) := slotValue_idVar hT
  have hsh : ((S.layout k).shadow S.width).templates[f']? = some T2.shadow := by
    simp [Layout.shadow, hT2]
  have logicalCell : ∀ row ∈ T2.logical.rows, ∀ j s, j < T2.width → row.cells[j]? = some (some s) →
      s < T2.slots.length →
      S.system.slotValue (S.mainV main) (S.base k + f') i s = S.valV main (S.base k + f') i s := by
    intro row hrow j s hj hc hs
    obtain ⟨r, hr, cell⟩ := cell_of_mem hrow hc
    exact slotValue_mainV hf hi hT hr hj cell hs
  have spanHolds : ∀ (r : Nat) (ls : List (LaneUse F)) (spans : List Span) (sp : Span), T2.rows[r]? = some (Row2.gate ls spans) → sp ∈ spans →
      Poly.denote (S.system.slotValue (S.mainV main) (S.base k + f') i)
        ((spanLanes T2.width ls sp).flatMap (Lane.poly T2.logical.idVar)) = 0 := by
    intro r ls spans sp hr hsp
    have hrow : Row.gate (spanLanes T2.width ls sp) true [sp.role] ∈ T2.logical.rows := by
      simp only [Template2.logical, List.mem_append, List.mem_flatMap]
      refine Or.inl (Or.inl (Or.inl (Or.inl ⟨_, List.mem_of_getElem? hr, ?_⟩)))
      simp only [Row2.logical, List.mem_map]
      exact ⟨sp, hsp, rfl⟩
    have rowOk := physCells.1.1.1.2 _ (List.mem_of_getElem? hr)
    obtain ⟨lenLs, _, spansOk, _⟩ := checkRow_gate rowOk
    have spOk := spansOk sp hsp
    simp only [Template2.checkSpan, Bool.and_eq_true, decide_eq_true_eq] at spOk
    have fits : sp.start + sp.len ≤ ls.length := by rw [lenLs]; exact spOk.1.2
    rw [Poly.denote_flatMap, sum_spanLanes _ ls sp fits _ (Lane.zero_poly _ _)]
    have hrlt : r < T2.rows.length := (List.getElem?_eq_some_iff.mp hr).1
    have place : (f', i, r) ∈ ((S.layout k).shadow S.width).places :=
      ((S.layout k).shadow S.width).mem_places.mpr ⟨by simpa [Layout.shadow] using hf', cap,
        by simp [System.rowCount, Layout.shadow, hT2, Template2.shadow, hrlt]⟩
    set p := ((S.layout k).shadow S.width).row f' i r
    have placed : Placed S k p f' i r T2 (.gate ls spans) :=
      ⟨by rw [List.getElem?_eq_getElem (((S.layout k).shadow S.width).row_lt place),
          ((S.layout k).shadow S.width).places_row place], hT2, hr⟩
    have pH : p < H k := Nat.lt_of_lt_of_le (((S.layout k).shadow S.width).row_lt place) (trace.tall k hk)
    rw [← placed.span w2 rowOk (trace.rows k hk p pH) hsp (S.system.instId (S.base k + f') i : F)]
    congr 1
    apply List.map_congr_left
    intro l hl
    have hl' := List.mem_range'_1.mp hl
    have lL : l < ls.length := by omega
    have hlg : laneAt ls l = ls[l].lane := by simp [laneAt, List.getElem?_eq_getElem lL]
    have wTW : T2.width = S.width := w2
    have L4 : 4 * lanes T2.width ≤ T2.width := by simp only [lanes]; omega
    have lenSpan : (spanLanes T2.width ls sp).length = lanes T2.width := by
      simp [spanLanes]; rw [lenLs] at fits; omega
    have spanAt : (spanLanes T2.width ls sp)[l - sp.start]'(by rw [lenSpan]; rw [lenLs] at lL; omega) =
        laneAt ls l := by
      rw [hlg]
      simp only [spanLanes]
      rw [List.getElem_append_left (by simp; omega)]
      simp [show sp.start + (l - sp.start) = l by omega]
    symm
    apply Lane.value_poly
    · have wf := checked.rows _ hrow
      simp only [Row.wellFormed, Bool.and_eq_true, List.all_eq_true] at wf
      apply wf.1.2
      rw [← spanAt]
      exact List.getElem_mem _
    · intro m s' hcs
      have hm : m < 4 := by
        have := (List.getElem?_eq_some_iff.mp hcs).1
        simpa [Lane.cells] using this
      have physCell : (T2.rowCells (.gate ls spans))[4 * l + m]? = some (some s') := by
        simp only [Template2.rowCells]
        rw [flatMap_laneCells_getElem? T2 ls lL hm]
        rw [hlg] at hcs
        rcases hu : ls[l] with _ | lane | m'
        · rw [hu] at hcs; simp [LaneUse.lane, Lane.zero, Lane.cells] at hcs
          rcases m with _ | _ | _ | _ | m <;> simp at hcs
        · rw [hu] at hcs; simpa [Template2.laneCells, LaneUse.lane] using hcs
        · rw [hu] at hcs; simp [LaneUse.lane, Lane.zero, Lane.cells] at hcs
          rcases m with _ | _ | _ | _ | m <;> simp at hcs
      have physFacts := physCells.1.1.1.1 _ (List.mem_of_getElem? hr) _ (List.mem_of_getElem? physCell)
      simp only [Option.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at physFacts
      obtain ⟨hs', ns⟩ := physFacts s' rfl
      have jW : 4 * l + m < S.width := by rw [lenLs] at lL; simp only [lanes] at lL; omega
      have shCell : T2.shadow.cell r (4 * l + m) = some s' := by
        rw [Template.cell_of (show T2.shadow.rows[r]? = some (.message 0 0 0 (T2.rowCells (.gate ls spans))) by
          simp [Template2.shadow, hr])]
        simp only [Row.cells, physCell, Option.getD_some]
      have nv := VirtualOk.cell virt hk (List.mem_of_getElem? hT2) (List.mem_of_getElem? hr)
        (List.mem_of_getElem? physCell)
      rw [trace.consistent k hk f' i r place T2.shadow hsh _ jW s' shCell,
        ← valV_physical hk hf' hT2 ns nv i]
      symm
      apply logicalCell _ hrow (4 * (l - sp.start) + m) s' (by rw [lenLs] at lL; omega) ?_ hs'
      simp only [Row.cells]
      rw [flatMap_cells_getElem? _ (by rw [lenSpan]; rw [lenLs] at lL; omega) hm, spanAt]
      rw [hlg] at hcs ⊢
      exact hcs
    · exact idv
  intro rel hrel
  obtain ⟨row, hrow, hrel⟩ := List.mem_flatMap.mp hrel
  rcases mem_logical_rows hrow with ⟨r, ls, spans, sp, hr, hsp, rfl⟩ | ⟨s, hs, rfl⟩ | ⟨v, hv, rfl⟩ |
    ⟨v, hv, rfl⟩ | ⟨sel, tag, sub, cells, rfl⟩
  · simp only [Row.relations, List.headD_cons, List.mem_singleton] at hrel
    subst hrel
    exact spanHolds r ls spans sp hr hsp
  · simp only [pinRow, Row.relations, List.headD_cons, List.mem_singleton] at hrel
    subst hrel
    simp only
    rw [Poly.denote_flatMap, List.map_cons, List.sum_cons, List.map_replicate, Lane.zero_poly,
      List.sum_replicate, smul_zero, add_zero]
    have hs' : s < T2.slots.length := (List.getElem?_eq_some_iff.mp hs).1
    have w4 : 4 ≤ T2.width := checked.width.1
    have vs := logicalCell _ hrow 0 s (by omega) (by simp [pinRow, Row.cells, pinLane, Lane.cells]) hs'
    have inv : S.valV main (S.base k + f') i s = (S.system.instId (S.base k + f') i : F) := by
      simp [valV, hT, Template2.logical, hs]
    rw [← Lane.value_poly (pinLane s) (by simp [Lane.wellFormed, pinLane, Lane.zero])
      (fun _ => S.system.slotValue (S.mainV main) (S.base k + f') i s) _ (fun m s' h => ?_) idv]
    · simp only [Lane.value, pinLane, Lane.zero]
      rw [vs, inv]; ring
    · rcases m with _ | _ | _ | _ | m <;> simp [pinLane, Lane.cells, Lane.zero] at h
      rw [h]
  · simp only [virtualRow, Row.relations, List.headD_cons, List.mem_singleton] at hrel
    subst hrel
    simp only
    rw [Poly.denote_flatMap, List.map_cons, List.sum_cons, List.map_replicate, Lane.zero_poly,
      List.sum_replicate, smul_zero, add_zero]
    have w4 : 4 ≤ T2.width := checked.width.1
    have memT := List.mem_of_getElem? hT2
    have hvlt : v < T2.slots.length := by
      rcases VirtualOk.def virt hk memT hv with ⟨_, _, _, h, _⟩ | ⟨_, h⟩ <;>
        exact (List.getElem?_eq_some_iff.mp h).1
    have nsv : T2.slots[v]? ≠ some .invocation := by
      rcases VirtualOk.def virt hk memT hv with ⟨_, _, _, h, _⟩ | ⟨_, h⟩ <;> rw [h] <;> simp
    have vv := valV_virtual (main := main) hk hf' hT2 nsv hv i
    rcases VirtualOk.def virt hk memT hv with ⟨c, x, k', hdef, hx, nsx, nvx⟩ | ⟨k', hdef⟩
    · have cv := logicalCell _ hrow 1 v (by omega) (by simp [virtualRow, Row.cells, virtualLane, hdef, Lane.cells]) hvlt
      have cx := logicalCell _ hrow 0 x (by omega) (by simp [virtualRow, Row.cells, virtualLane, hdef, Lane.cells]) hx
      have vx := valV_physical (main := main) hk hf' hT2 nsx nvx i
      simp only [hdef, Option.getD_some] at cv cx ⊢
      rw [← Lane.value_poly (virtualLane v (.sum [.linear c x] k'))
        (by simp [Lane.wellFormed, virtualLane, Lane.zero])
        (fun m => if m = 0 then S.system.slotValue (S.mainV main) (S.base k + f') i x
          else S.system.slotValue (S.mainV main) (S.base k + f') i v) _ (fun m s' h => ?_) idv]
      · simp only [Lane.value, virtualLane, Lane.zero]
        rw [cv, cx, vv, vx]
        simp [Template2.virtualValue, hdef]
      · rcases m with _ | _ | _ | _ | m <;> simp [virtualLane, Lane.cells, Lane.zero] at h <;> rw [h] <;> simp
    · have cv := logicalCell _ hrow 0 v (by omega) (by simp [virtualRow, Row.cells, virtualLane, hdef, Lane.cells]) hvlt
      simp only [hdef, Option.getD_some] at cv ⊢
      rw [← Lane.value_poly (virtualLane v (.sum [] k'))
        (by simp [Lane.wellFormed, virtualLane, Lane.zero])
        (fun _ => S.system.slotValue (S.mainV main) (S.base k + f') i v) _ (fun m s' h => ?_) idv]
      · simp only [Lane.value, virtualLane, Lane.zero]
        rw [cv, vv]
        simp [Template2.virtualValue, hdef]
      · rcases m with _ | _ | _ | _ | m <;> simp [virtualLane, Lane.cells, Lane.zero] at h
        rw [h]
  · simp only [boolRow, Row.relations, List.headD_cons, List.mem_singleton] at hrel
    subst hrel
    simp only
    rw [Poly.denote_flatMap, List.map_cons, List.sum_cons, List.map_replicate, Lane.zero_poly,
      List.sum_replicate, smul_zero, add_zero]
    have w4 : 4 ≤ T2.width := checked.width.1
    have memT := List.mem_of_getElem? hT2
    have ok := List.all_eq_true.mp (bools k hk T2 memT) v hv
    simp only [Template2.boolOk, Bool.and_eq_true, List.contains_iff_mem] at ok
    obtain ⟨hvirt, ok⟩ := ok
    have hvlt : v < T2.slots.length := by
      rcases VirtualOk.def virt hk memT hvirt with ⟨_, _, _, h, _⟩ | ⟨_, h⟩ <;>
        exact (List.getElem?_eq_some_iff.mp h).1
    have nsv : T2.slots[v]? ≠ some .invocation := by
      rcases VirtualOk.def virt hk memT hvirt with ⟨_, _, _, h, _⟩ | ⟨_, h⟩ <;> rw [h] <;> simp
    have vv := valV_virtual (main := main) hk hf' hT2 nsv hvirt i
    have cv := logicalCell _ hrow 0 v (by omega) (by simp [boolRow, Row.cells, boolLane, Lane.cells]) hvlt
    set val := S.system.slotValue (S.mainV main) (S.base k + f') i
    have lanePoly : Poly.denote val (Lane.poly T2.logical.idVar (boolLane v)) = val v * val v - val v := by
      simp only [Lane.poly, boolLane, Lane.zero, cellPoly]
      simp [Mono.eval_insert]; ring
    rw [lanePoly, cv, vv]
    split at ok
    · rename_i c x k' hdef
      rcases VirtualOk.def virt hk memT hvirt with ⟨c2, x2, k2, h2, hx, nsx, nvx⟩ | ⟨_, h2⟩
      · rw [hdef] at h2
        simp only [Option.some.injEq, SlotDef.sum.injEq, List.cons.injEq, Term.linear.injEq,
          and_true] at h2
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
        simp only [List.any_eq_true] at ok
        obtain ⟨row, hrowT, hspan⟩ := ok
        obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hrowT
        cases hrw : T2.rows[r] with
        | message => rw [hrw] at hspan; simp at hspan
        | gate ls spans =>
          rw [hrw] at hspan
          simp only [List.any_eq_true] at hspan
          obtain ⟨sp, hsp, same⟩ := hspan
          have hold := spanHolds r ls spans sp (by rw [List.getElem?_eq_getElem hr, hrw]) hsp
          have e : Poly.denote val (T2.spanPoly ls sp) = Poly.denote val (virtualBoolPoly c x k') :=
            Poly.Identical.denote val same
          rw [show T2.spanPoly ls sp = (spanLanes T2.width ls sp).flatMap (Lane.poly T2.logical.idVar)
            from rfl, hold] at e
          have vrow : virtualRow T2.width v ((T2.slots[v]?).getD (.key 0)) ∈ T2.logical.rows := by
            simp only [Template2.logical, List.mem_append, Template2.virtualRows, List.mem_map]
            exact Or.inl (Or.inl (Or.inr ⟨v, hvirt, rfl⟩))
          have cx := logicalCell _ vrow 0 x (by omega)
            (by simp [virtualRow, Row.cells, virtualLane, hdef, Lane.cells]) hx
          have vx := valV_physical (main := main) hk hf' hT2 nsx nvx i
          simp only [Template2.virtualValue, hdef]
          rw [← vx, ← cx]
          simp [virtualBoolPoly, Mono.eval] at e
          linear_combination -e
      · rw [hdef] at h2; simp at h2
    · rename_i k' hdef
      simp only [beq_iff_eq] at ok
      simp only [Template2.virtualValue, hdef]
      rw [ok, sub_self]
    · simp at ok
  · simp [Row.relations] at hrel

end Sharded

end Aiur.Tiling.Periodic
