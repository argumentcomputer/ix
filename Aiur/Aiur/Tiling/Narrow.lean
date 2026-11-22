import Aiur.Tiling.Enumerate

/-! Semantics of the narrow circuit on a placed row. -/

namespace Aiur.Tiling

open Aiur.Scalar.Circuit (ArithExpr Var Satisfies)

variable {F : Type}

theorem sum_range_getElem {α M : Type} [AddCommMonoid M] (l : List α) (g : Nat → M) (φ : α → M)
    (h : ∀ r (lt : r < l.length), g r = φ l[r]) :
    ((List.range l.length).map g).sum = (l.map φ).sum := by
  induction l generalizing g with
  | nil => simp
  | cons a l ih =>
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map,
        List.map_cons, List.sum_cons, h 0 (by simp)]
      simp only [List.getElem_cons_zero]
      congr 1
      apply ih
      intro r lt
      have := h (r + 1) (by simp [lt])
      rw [List.getElem_cons_succ] at this
      exact this

section Field

variable [Field F]

def Lane.value (lane : Lane F) (id : F) (x : Nat → F) : F :=
  lane.qm * x 0 * x 1 + lane.q0 * x 0 + lane.q1 * x 1 + lane.q2 * x 2 + lane.q3 * x 3 +
    (lane.qc + lane.qid * id)

theorem Lane.value_poly [DecidableEq F] (lane : Lane F) (wf : lane.wellFormed = true) (x val : Nat → F)
    (cells : ∀ m s, lane.cells[m]? = some (some s) → x m = val s) {idv : Nat} {id : F} (hid : val idv = id) :
    lane.value id x = Poly.denote val (Lane.poly idv lane) := by
  rcases lane with ⟨qm, q0, q1, q2, q3, qc, c0, c1, c2, c3, qid⟩
  have e0 := cells 0; have e1 := cells 1; have e2 := cells 2; have e3 := cells 3
  simp only [Lane.cells, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at e0 e1 e2 e3
  simp only [Lane.wellFormed, Bool.and_eq_true, Bool.or_eq_true, Option.isSome_iff_exists,
    beq_iff_eq] at wf
  obtain ⟨⟨⟨⟨w01, w0⟩, w1⟩, w2⟩, w3⟩ := wf
  subst hid
  by_cases hq : qid = 0 <;>
  cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;>
    simp_all [Lane.value, Lane.poly, cellPoly, Mono.eval_insert] <;> ring

variable (sys : System F) (main : Nat → Nat → F)

/-- Physical row `p` holds row `row` of template `T` (circuit `f`, instance `i`). -/
structure System.Placed (p f i r : Nat) (T : Template F) (row : Row F) : Prop where
  place : sys.places[p]? = some (f, i, r)
  template : sys.templates[f]? = some T
  row : T.rows[r]? = some row

theorem System.assign_main {p v : Nat} (h : v < sys.width) : sys.assign main p v = main p v := by
  simp [System.assign, h]

theorem System.assign_fixed (p k : Nat) : sys.assign main p (sys.width + k) = sys.fixedAt p k := by
  simp [System.assign]

theorem System.Placed.fixed {sys : System F} {p f i r T row} (placed : sys.Placed p f i r T row) (k : Nat) :
    sys.fixedAt p k = row.fixed sys.width (sys.labelAt p) (sys.multAt p) (sys.instId f i : F) k := by
  simp [System.fixedAt, placed.place, placed.template, placed.row]

section RowFixed

variable [DecidableEq F] (W : Nat) (row : Row F) (lab mul : Nat → F) (id : F)

theorem Row.fixed_lane {l m : Nat} (hl : l < W / 4) (hm : m < 6) :
    row.fixed W lab mul id (6 * l + m) = (row.lane l).coef id m := by
  have h1 : 6 * l + m < joinCol W := by simp only [joinCol]; omega
  have h2 : (6 * l + m) / 6 = l := by omega
  have h3 : (6 * l + m) % 6 = m := by omega
  simp [Row.fixed, h1, h2, h3]

theorem Row.fixed_join : row.fixed W lab mul id (joinCol W) = row.joinValue := by
  simp [Row.fixed]

theorem Row.fixed_sel : row.fixed W lab mul id (selCol W) = row.messageValue.1 := by
  simp [Row.fixed, selCol]

theorem Row.fixed_tag : row.fixed W lab mul id (tagCol W) = row.messageValue.2.1 := by
  simp [Row.fixed, tagCol, selCol]

theorem Row.fixed_sub : row.fixed W lab mul id (subCol W) = row.messageValue.2.2 := by
  simp [Row.fixed, subCol, tagCol, selCol]

theorem Row.fixed_label {j : Nat} (hj : j < W) : row.fixed W lab mul id (labelCol W j) = lab j := by
  unfold Row.fixed labelCol selCol tagCol subCol fixedWidth
  split_ifs <;> first | omega | (congr 1; omega)

theorem Row.fixed_mult {j : Nat} (hj : j < W) : row.fixed W lab mul id (multCol W j) = mul j := by
  unfold Row.fixed multCol selCol tagCol subCol fixedWidth
  split_ifs <;> first | omega | (congr 1; omega)

end RowFixed

theorem laneExpr_denote (W l : Nat) (a : Var → F) :
    (laneExpr W l : ArithExpr F).denote a =
      a (W + 6 * l) * a (4 * l) * a (4 * l + 1) + a (W + (6 * l + 1)) * a (4 * l) +
        a (W + (6 * l + 2)) * a (4 * l + 1) + a (W + (6 * l + 3)) * a (4 * l + 2) +
          a (W + (6 * l + 4)) * a (4 * l + 3) + a (W + (6 * l + 5)) := by
  simp [laneExpr, fixedVar, ArithExpr.denote]

theorem lanesSum_denote (W : Nat) (ls : List Nat) (a : Var → F) :
    (lanesSum W ls : ArithExpr F).denote a = (ls.map fun l => (laneExpr W l : ArithExpr F).denote a).sum := by
  induction ls with
  | nil => simp [lanesSum, ArithExpr.denote]
  | cons l ls ih => simp [lanesSum, ArithExpr.denote, ih]

variable [DecidableEq F]

theorem System.Placed.lane {sys : System F} {main : Nat → Nat → F} {p f i r T row}
    (placed : sys.Placed p f i r T row) {l : Nat} (hl : l < sys.width / 4) :
    (laneExpr sys.width l : ArithExpr F).denote (sys.assign main p) =
      (row.lane l).value (sys.instId f i) fun m => main p (4 * l + m) := by
  rw [laneExpr_denote]
  rw [sys.assign_main main (p := p) (v := 4 * l) (by omega),
    sys.assign_main main (p := p) (v := 4 * l + 1) (by omega),
    sys.assign_main main (p := p) (v := 4 * l + 2) (by omega),
    sys.assign_main main (p := p) (v := 4 * l + 3) (by omega)]
  have q : ∀ m < 6, sys.assign main p (sys.width + (6 * l + m)) = (row.lane l).coef (sys.instId f i) m := by
    intro m hm
    rw [sys.assign_fixed, placed.fixed, Row.fixed_lane _ _ _ _ _ hl hm]
  have q0 := q 0 (by norm_num)
  simp only [Nat.add_zero] at q0
  rw [q0, q 1 (by norm_num), q 2 (by norm_num), q 3 (by norm_num), q 4 (by norm_num),
    q 5 (by norm_num)]
  simp [Lane.value, Lane.coef]

/-- The gate relations a narrow row enforces. -/
theorem System.Placed.gate {sys : System F} {main : Nat → Nat → F} {p f i r T lanes join roles}
    (placed : sys.Placed p f i r T (.gate lanes join roles)) (w4 : 4 ≤ sys.width)
    (valid : Satisfies (narrowConstraints sys.width) (sys.assign main p)) :
    (join = true → ((List.range (sys.width / 4)).map fun l =>
        ((Row.gate lanes join roles).lane l).value (sys.instId f i) fun m => main p (4 * l + m)).sum = 0) ∧
    (join = false → ∀ l < sys.width / 4,
        ((Row.gate lanes join roles).lane l).value (sys.instId f i) (fun m => main p (4 * l + m)) = 0) := by
  have sum := valid _ (List.mem_cons_self ..)
  rw [lanesSum_denote] at sum
  have sum' : ((List.range (sys.width / 4)).map fun l =>
      ((Row.gate lanes join roles).lane l).value (sys.instId f i) fun m => main p (4 * l + m)).sum = 0 := by
    rw [← sum]
    congr 1
    apply List.map_congr_left
    intro l hl
    exact (placed.lane (List.mem_range.mp hl)).symm
  refine ⟨fun _ => sum', fun off => ?_⟩
  have each : ∀ l < sys.width / 4 - 1,
      ((Row.gate lanes join roles).lane l).value (sys.instId f i) (fun m => main p (4 * l + m)) = 0 := by
    intro l hl
    have h := valid _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩))
    simp only [ArithExpr.denote] at h
    rw [placed.lane (by omega), show fixedVar (F := F) sys.width (joinCol sys.width) =
      .var (sys.width + joinCol sys.width) from rfl] at h
    simp only [ArithExpr.denote] at h
    rw [sys.assign_fixed, placed.fixed, Row.fixed_join] at h
    simpa [Row.joinValue, off] using h
  intro l hl
  by_cases last : l < sys.width / 4 - 1
  · exact each l last
  · have eq : l = sys.width / 4 - 1 := by omega
    have split : List.range (sys.width / 4) = List.range (sys.width / 4 - 1) ++ [sys.width / 4 - 1] := by
      rw [← List.range_succ]; congr 1; omega
    rw [split, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton] at sum'
    have zero : ((List.range (sys.width / 4 - 1)).map fun l =>
        ((Row.gate lanes join roles).lane l).value (sys.instId f i) fun m => main p (4 * l + m)).sum = 0 := by
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hx
      exact each l' (List.mem_range.mp hl')
    rw [zero, zero_add] at sum'
    rw [eq]; exact sum'

end Field

end Aiur.Tiling
