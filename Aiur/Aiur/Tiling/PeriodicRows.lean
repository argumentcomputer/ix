import Aiur.Tiling.PeriodicTemplate

/-!
# Per-row semantics of a v2 shard

For a physical row of a shard, with its layout's fixed columns:

* the fixed columns are the row's gate coefficients, flags, message columns,
  labels and multiplicities (`fixedRow_*`);
* every span of a gate row enforces the sum of its lanes (`span_lanes`), in
  the form `Lane.value` that the logical template's span row denotes;
* a key row has `x1 = 0` (`key_cell`).
-/

namespace Aiur.Tiling.Periodic

open Aiur.Scalar.Circuit (ArithExpr Var Satisfies)

variable {F : Type}

/-! ## Indexing a fixed row -/

theorem length_flatMap_range {α : Type} (g : Nat → List α) (L : Nat) :
    ((List.range L).flatMap g).length = ((List.range L).map fun l => (g l).length).sum := by
  induction L with
  | zero => simp
  | succ L ih => simp [List.range_succ, List.flatMap_append, ih]

theorem getElem?_flatMap_range {α : Type} (g : Nat → List α) : ∀ {L l j : Nat}, l < L →
    j < (g l).length →
    ((List.range L).flatMap g)[((List.range l).map fun l' => (g l').length).sum + j]? = (g l)[j]?
  | 0, _, _, hl, _ => absurd hl (Nat.not_lt_zero _)
  | L + 1, l, j, hl, hj => by
      rw [List.range_succ, List.flatMap_append]
      by_cases lt : l < L
      · have le : ((List.range l).map fun l' => (g l').length).sum + j <
            ((List.range L).flatMap g).length := by
          rw [length_flatMap_range]
          have : ((List.range (l + 1)).map fun l' => (g l').length).sum ≤
              ((List.range L).map fun l' => (g l').length).sum := sum_range_mono _ lt
          rw [List.range_succ, List.map_append, List.sum_append] at this
          simp at this
          omega
        rw [List.getElem?_append_left le]
        exact getElem?_flatMap_range g lt hj
      · have eq : l = L := by omega
        subst eq
        rw [List.getElem?_append_right (by rw [length_flatMap_range]; omega), length_flatMap_range]
        simp

theorem sum_range_const (n l : Nat) : ((List.range l).map fun _ => n).sum = n * l := by
  rw [List.map_const', List.sum_replicate, List.length_range, smul_eq_mul, Nat.mul_comm]

section FixedRow

variable (W : Nat) (gate flag laneMsg : Nat → Nat → F) (rowMsg label mult : Nat → F)

private abbrev A1 := (List.range (lanes W)).flatMap (fun l => (List.range 6).map (gate l))
private abbrev A2 := (List.range (lanes W)).flatMap (fun l => (List.range (flagBlock W l)).map fun d => flag l (l + d))
private abbrev A3 := (List.range (lanes W)).flatMap (fun l => (List.range 3).map (laneMsg l))

theorem length_A1 : (A1 W gate).length = 6 * lanes W := by
  rw [length_flatMap_range]; simp [sum_range_const, Nat.mul_comm]

theorem length_A2 : (A2 W flag).length = flagCount W := by
  rw [length_flatMap_range]; simp [flagCount]

theorem length_A3 : (A3 W laneMsg).length = 3 * lanes W := by
  rw [length_flatMap_range]; simp [sum_range_const, Nat.mul_comm]

theorem fixedRow_eq : fixedRow W gate flag laneMsg rowMsg label mult =
    A1 W gate ++ (A2 W flag ++ (A3 W laneMsg ++ ((List.range 5).map rowMsg ++ ((List.range W).map label ++
      (List.range W).map mult)))) := by
  simp only [fixedRow, List.append_assoc]

theorem fixedRow_gate {l m : Nat} (hl : l < lanes W) (hm : m < 6) :
    (fixedRow W gate flag laneMsg rowMsg label mult)[gateCol l m]? = some (gate l m) := by
  have h1 : gateCol l m < (A1 W gate).length := by rw [length_A1]; simp only [gateCol]; omega
  rw [fixedRow_eq, List.getElem?_append_left h1]
  have := getElem?_flatMap_range (fun l => (List.range 6).map (gate l)) hl (j := m) (by simpa using hm)
  simp only [List.length_map, List.length_range, sum_range_const] at this
  rw [show gateCol l m = 6 * l + m from rfl, this]
  simp [hm]

theorem fixedRow_flag {l l' : Nat} (hl : l ≤ l') (hl' : l' < lanes W) :
    (fixedRow W gate flag laneMsg rowMsg label mult)[flagCol W l l']? = some (flag l l') := by
  have le : ((List.range (l + 1)).map (flagBlock W)).sum ≤ ((List.range (lanes W)).map (flagBlock W)).sum :=
    sum_range_mono _ (by omega)
  rw [List.range_succ, List.map_append, List.sum_append] at le
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at le
  have hb : flagBlock W l = lanes W - l := rfl
  have lenA2 := length_A2 W flag
  unfold flagCount at lenA2
  have lenA1 := length_A1 W gate
  rw [fixedRow_eq, List.getElem?_append_right (by rw [lenA1, flagCol]; omega),
    List.getElem?_append_left (by rw [lenA1, lenA2, flagCol]; omega),
    show flagCol W l l' - (A1 W gate).length = ((List.range l).map (flagBlock W)).sum + (l' - l) by
      rw [lenA1, flagCol]; omega]
  have := getElem?_flatMap_range (fun l => (List.range (flagBlock W l)).map fun d => flag l (l + d))
    (L := lanes W) (l := l) (j := l' - l) (by omega) (by simp [flagBlock]; omega)
  simp only [List.length_map, List.length_range] at this
  rw [show (fun l' => flagBlock W l') = flagBlock W from rfl] at this
  rw [this]
  simp [flagBlock, show l' - l < lanes W - l by omega, show l + (l' - l) = l' by omega]

theorem fixedRow_laneMsg {l k : Nat} (hl : l < lanes W) (hk : k < 3) :
    (fixedRow W gate flag laneMsg rowMsg label mult)[laneMsgCol W l k]? = some (laneMsg l k) := by
  have lenA1 := length_A1 W gate
  have lenA2 := length_A2 W flag
  have lenA3 := length_A3 W laneMsg
  rw [fixedRow_eq, List.getElem?_append_right (by rw [lenA1, laneMsgCol]; omega),
    List.getElem?_append_right (by rw [lenA1, lenA2, laneMsgCol]; omega),
    List.getElem?_append_left (by rw [lenA1, lenA2, lenA3, laneMsgCol]; omega),
    show laneMsgCol W l k - (A1 W gate).length - (A2 W flag).length = 3 * l + k by
      rw [lenA1, lenA2, laneMsgCol]; omega]
  have := getElem?_flatMap_range (fun l => (List.range 3).map (laneMsg l)) hl (j := k) (by simpa using hk)
  simp only [List.length_map, List.length_range, sum_range_const] at this
  rw [this]
  simp [hk]

theorem fixedRow_rowMsg {k : Nat} (hk : k < 5) :
    (fixedRow W gate flag laneMsg rowMsg label mult)[rowMsgCol W k]? = some (rowMsg k) := by
  have lenA1 := length_A1 W gate
  have lenA2 := length_A2 W flag
  have lenA3 := length_A3 W laneMsg
  rw [fixedRow_eq, List.getElem?_append_right (by rw [lenA1, rowMsgCol]; omega),
    List.getElem?_append_right (by rw [lenA1, lenA2, rowMsgCol]; omega),
    List.getElem?_append_right (by rw [lenA1, lenA2, lenA3, rowMsgCol]; omega),
    List.getElem?_append_left (by rw [lenA1, lenA2, lenA3, rowMsgCol]; simp; omega),
    show rowMsgCol W k - (A1 W gate).length - (A2 W flag).length - (A3 W laneMsg).length = k by
      rw [lenA1, lenA2, lenA3, rowMsgCol]; omega]
  simp [hk]

theorem fixedRow_label {j : Nat} (hj : j < W) :
    (fixedRow W gate flag laneMsg rowMsg label mult)[labelCol W j]? = some (label j) := by
  have lenA1 := length_A1 W gate
  have lenA2 := length_A2 W flag
  have lenA3 := length_A3 W laneMsg
  rw [fixedRow_eq, List.getElem?_append_right (by rw [lenA1, labelCol, rowMsgCol]; omega),
    List.getElem?_append_right (by rw [lenA1, lenA2, labelCol, rowMsgCol]; omega),
    List.getElem?_append_right (by rw [lenA1, lenA2, lenA3, labelCol, rowMsgCol]; omega),
    List.getElem?_append_right (by rw [lenA1, lenA2, lenA3, labelCol, rowMsgCol]; simp; omega),
    List.getElem?_append_left (by rw [lenA1, lenA2, lenA3, labelCol, rowMsgCol]; simp; omega),
    show labelCol W j - (A1 W gate).length - (A2 W flag).length - (A3 W laneMsg).length -
      ((List.range 5).map rowMsg).length = j by
      rw [lenA1, lenA2, lenA3, labelCol, rowMsgCol]; simp; omega]
  simp [hj]

theorem fixedRow_mult {j : Nat} (hj : j < W) :
    (fixedRow W gate flag laneMsg rowMsg label mult)[multCol W j]? = some (mult j) := by
  have lenA1 := length_A1 W gate
  have lenA2 := length_A2 W flag
  have lenA3 := length_A3 W laneMsg
  rw [fixedRow_eq, List.getElem?_append_right (by rw [lenA1, multCol, rowMsgCol]; omega),
    List.getElem?_append_right (by rw [lenA1, lenA2, multCol, rowMsgCol]; omega),
    List.getElem?_append_right (by rw [lenA1, lenA2, lenA3, multCol, rowMsgCol]; omega),
    List.getElem?_append_right (by rw [lenA1, lenA2, lenA3, multCol, rowMsgCol]; simp; omega),
    List.getElem?_append_right (by rw [lenA1, lenA2, lenA3, multCol, rowMsgCol]; simp; omega),
    show multCol W j - (A1 W gate).length - (A2 W flag).length - (A3 W laneMsg).length -
      ((List.range 5).map rowMsg).length - ((List.range W).map label).length = j by
      rw [lenA1, lenA2, lenA3, multCol, rowMsgCol]; simp; omega]
  simp [hj]

end FixedRow

/-! ## A placed row of a shard -/

section Shard

variable [Field F] [DecidableEq F] {S : Sharded F} {k : Nat} {main : Nat → Nat → F} {p f i r : Nat}
  {T : Template2 F} {row : Row2 F}

/-- Physical row `p` of shard `k` holds row `r` of template `T` (instance `i` of circuit `f`). -/
structure Placed (S : Sharded F) (k p f i r : Nat) (T : Template2 F) (row : Row2 F) : Prop where
  place : ((S.layout k).shadow S.width).places[p]? = some (f, i, r)
  template : (S.layout k).templates[f]? = some T
  row : T.rows[r]? = some row

abbrev Placed.fixedRowOf (S : Sharded F) (k p f i : Nat) (T : Template2 F) (row : Row2 F) : List F :=
  fixedRow S.width row.gateCoef row.flag (row.laneMsg T S.buses)
    (row.rowMsg T S.buses (((S.layout k).shadow S.width).instId f i : F))
    (((S.layout k).shadow S.width).labelAt p) (((S.layout k).shadow S.width).multAt p)

theorem Placed.fixed (placed : Placed S k p f i r T row) (c : Nat) :
    S.assign k main p (S.width + c) = ((Placed.fixedRowOf S k p f i T row)[c]?).getD 0 := by
  simp [Sharded.assign, Sharded.fixedAt, placed.place, placed.template, placed.row]

theorem Sharded.assign_main {v : Nat} (h : v < S.width) : S.assign k main p v = main p v := by
  simp [Sharded.assign, h]

theorem Placed.gate (placed : Placed S k p f i r T row) {l m : Nat} (hl : l < lanes S.width) (hm : m < 6) :
    S.assign k main p (S.width + gateCol l m) = row.gateCoef l m := by
  rw [placed.fixed, fixedRow_gate _ _ _ _ _ _ _ hl hm]; rfl

theorem Placed.flag (placed : Placed S k p f i r T row) {l l' : Nat} (hl : l ≤ l') (hl' : l' < lanes S.width) :
    S.assign k main p (S.width + flagCol S.width l l') = row.flag l l' := by
  rw [placed.fixed, fixedRow_flag _ _ _ _ _ _ _ hl hl']; rfl

theorem Placed.laneMsg (placed : Placed S k p f i r T row) {l c : Nat} (hl : l < lanes S.width) (hc : c < 3) :
    S.assign k main p (S.width + laneMsgCol S.width l c) = row.laneMsg T S.buses l c := by
  rw [placed.fixed, fixedRow_laneMsg _ _ _ _ _ _ _ hl hc]; rfl

theorem Placed.rowMsg (placed : Placed S k p f i r T row) {c : Nat} (hc : c < 5) :
    S.assign k main p (S.width + rowMsgCol S.width c) =
      row.rowMsg T S.buses (((S.layout k).shadow S.width).instId f i : F) c := by
  rw [placed.fixed, fixedRow_rowMsg _ _ _ _ _ _ _ hc]; rfl

theorem Placed.label (placed : Placed S k p f i r T row) {j : Nat} (hj : j < S.width) :
    S.assign k main p (S.width + labelCol S.width j) = ((S.layout k).shadow S.width).labelAt p j := by
  rw [placed.fixed, fixedRow_label _ _ _ _ _ _ _ hj]; rfl

theorem Placed.mult (placed : Placed S k p f i r T row) {j : Nat} (hj : j < S.width) :
    S.assign k main p (S.width + multCol S.width j) = ((S.layout k).shadow S.width).multAt p j := by
  rw [placed.fixed, fixedRow_mult _ _ _ _ _ _ _ hj]; rfl

/-- The lane of a gate row at position `l` (zero if not a gate lane). -/
def laneAt (ls : List (LaneUse F)) (l : Nat) : Lane F := ((ls[l]?).map LaneUse.lane).getD Lane.zero

theorem lane_value {ls : List (LaneUse F)} {spans : List Span} (qid : ∀ lane, LaneUse.gate lane ∈ ls → lane.qid = 0)
    (a : Var → F) (W l : Nat) (gate : ∀ m < 6, a (W + gateCol l m) = (Row2.gate ls spans).gateCoef l m) (id : F) :
    (laneAt ls l).value id (fun m => a (4 * l + m)) =
      (Row2.gate ls spans).gateCoef l 0 * a (4 * l) * a (4 * l + 1) + lin W l a := by
  simp only [lin]
  rw [gate 1 (by omega), gate 2 (by omega), gate 3 (by omega), gate 4 (by omega), gate 5 (by omega)]
  simp only [Row2.gateCoef, laneAt]
  cases h : ls[l]? with
  | none => simp [Lane.value, Lane.zero]
  | some u =>
      cases u with
      | gate lane =>
          have := qid lane (List.mem_of_getElem? h)
          simp [Lane.value, LaneUse.lane, Lane.gateCoef, this]; ring
      | empty => simp [Lane.value, Lane.zero, LaneUse.lane]
      | message m => simp [Lane.value, Lane.zero, LaneUse.lane]

theorem checkRow_gate {ls : List (LaneUse F)} {spans : List Span} (h : T.checkRow S.buses (.gate ls spans) = true) :
    ls.length = lanes T.width ∧ (∀ lane, LaneUse.gate lane ∈ ls → lane.qid = 0) ∧
      (∀ sp ∈ spans, Template2.checkSpan ls (lanes T.width) sp = true) ∧ (spans.map (·.start)).Nodup := by
  simp only [Template2.checkRow, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨len, lanesOk⟩, spansOk⟩, nodup⟩ := h
  refine ⟨len, fun lane hl => by simpa using lanesOk _ hl, spansOk, nodup⟩

/-- **Spans.** Every span of a placed gate row enforces the sum of its lanes. -/
theorem Placed.span (placed : Placed S k p f i r T (.gate ls spans)) (hW : T.width = S.width)
    (ok : T.checkRow S.buses (.gate ls spans) = true)
    (holds : Satisfies (S.circuit k).constraints (S.assign k main p)) {sp : Span} (hsp : sp ∈ spans) (id : F) :
    ((List.range' sp.start sp.len).map fun l =>
      (laneAt ls l).value id (fun m => main p (4 * l + m))).sum = 0 := by
  obtain ⟨_, qid, spansOk, nodup⟩ := checkRow_gate ok
  have spOk := spansOk sp hsp
  simp only [Template2.checkSpan, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at spOk
  obtain ⟨⟨one, fits⟩, cont⟩ := spOk
  rw [hW] at fits
  have gate : ∀ l < lanes S.width, ∀ m < 6, S.assign k main p (S.width + gateCol l m) = (Row2.gate ls spans).gateCoef l m :=
    fun l hl m hm => placed.gate hl hm
  have flags : ∀ l', sp.start ≤ l' → l' < lanes S.width →
      S.assign k main p (S.width + flagCol S.width sp.start l') = if l' < sp.start + sp.len then 1 else 0 := by
    intro l' h1 h2
    rw [placed.flag h1 h2]
    simp only [Row2.flag]
    congr 1
    apply propext
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨sp', hsp', st, lt⟩
      have : sp' = sp := by
        have := List.inj_on_of_nodup_map nodup hsp' hsp st
        exact this
      subst this; exact lt
    · intro lt; exact ⟨sp, hsp, rfl, lt⟩
  have sh := span_holds (W := S.width) (l := sp.start) (e := sp.start + sp.len) (a := S.assign k main p) holds
    (by omega) (by omega) flags
  rw [show sp.start + sp.len - sp.start = sp.len by omega] at sh
  have cell : ∀ l m : Nat, l < lanes S.width → m < 4 → S.assign k main p (4 * l + m) = main p (4 * l + m) := by
    intro l m hl hm
    apply Sharded.assign_main
    simp only [lanes] at hl
    omega
  have value : ∀ l, l < lanes S.width → (laneAt ls l).value id (fun m => main p (4 * l + m)) =
      (Row2.gate ls spans).gateCoef l 0 * S.assign k main p (4 * l) * S.assign k main p (4 * l + 1) +
        lin S.width l (S.assign k main p) := by
    intro l hl
    rw [← lane_value qid (S.assign k main p) S.width l (gate l hl) id]
    simp only [Lane.value]
    have c0 := cell l 0 hl (by norm_num)
    have c1 := cell l 1 hl (by norm_num)
    have c2 := cell l 2 hl (by norm_num)
    have c3 := cell l 3 hl (by norm_num)
    rw [c0, c1, c2, c3]
  have split : List.range' sp.start sp.len = sp.start :: List.range' (sp.start + 1) (sp.len - 1) := by
    conv_lhs => rw [show sp.len = (sp.len - 1) + 1 by omega]
    rw [List.range'_succ]
  rw [split, List.map_cons, List.sum_cons] at sh ⊢
  rw [value sp.start (by omega), gate sp.start (by omega) 0 (by omega)] at *
  have rest : ((List.range' (sp.start + 1) (sp.len - 1)).map fun l =>
      (laneAt ls l).value id (fun m => main p (4 * l + m))) =
      (List.range' (sp.start + 1) (sp.len - 1)).map fun l => lin S.width l (S.assign k main p) := by
    apply List.map_congr_left
    intro l hl
    have hl' := List.mem_range'_1.mp hl
    rw [value l (by omega)]
    have qm : (Row2.gate ls spans).gateCoef l 0 = 0 := by
      have := cont l hl
      simp only [Row2.gateCoef]
      cases h : ls[l]? with
      | none => rfl
      | some u =>
          cases u with
          | gate lane => rw [h] at this; simpa [Lane.gateCoef] using this
          | empty => rfl
          | message => rfl
    rw [qm]; ring
  rw [rest]
  rw [← sh]
  ring

/-- On a key row, the row's own span forces `x1 = 0`, so the message's key
coordinate is the fixed invocation id. -/
theorem Placed.key_cell {m : Nat} (placed : Placed S k p f i r T (.message m true)) (w4 : 4 ≤ S.width)
    (holds : Satisfies (S.circuit k).constraints (S.assign k main p)) : main p 1 = 0 := by
  have L1 : 0 < lanes S.width := by simp only [lanes]; omega
  have flags : ∀ l', 0 ≤ l' → l' < lanes S.width →
      S.assign k main p (S.width + flagCol S.width 0 l') = if l' < 0 + 1 then 1 else 0 := by
    intro l' _ h2
    rw [placed.flag (Nat.zero_le _) h2]
    simp only [Row2.flag, true_and]
    by_cases h : l' = 0 <;> simp [h]
  have sh := span_holds (W := S.width) (l := 0) (e := 0 + 1) (a := S.assign k main p) holds
    (by omega) (by omega) flags
  simp only [List.range', List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, lin] at sh
  rw [placed.gate L1 (by norm_num), placed.gate L1 (by norm_num), placed.gate L1 (by norm_num),
    placed.gate L1 (by norm_num), placed.gate L1 (by norm_num), placed.gate L1 (by norm_num)] at sh
  simp only [Row2.gateCoef, true_and] at sh
  have := Sharded.assign_main (S := S) (k := k) (main := main) (p := p) (v := 1) (by omega)
  simp only [Nat.mul_zero, Nat.zero_add] at sh
  rw [this] at sh
  simpa using sh

end Shard

end Aiur.Tiling.Periodic
