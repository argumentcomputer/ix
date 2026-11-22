import Aiur.Tiling.Reconstruct
import Aiur.Tiling.Groups

/-!
# Refinement: narrow traces yield wide traces

`System.sound`: a narrow trace that satisfies the narrow circuit on every
row, with the generated fixed columns, and whose lookups balance against an
external ledger with no copy-bus tuples, determines for every circuit `f`
and instance `i < cap f` a row of circuit `f`. Every such row satisfies its
circuit's constraints, and the rows' lookups, together with the external
ledger with each tuple cut to its message arity, balance. The narrow
message tuples are exactly the wide lookups padded with unused cells
(`System.message_ledger`).
-/

namespace Aiur.Tiling

open Aiur.Scalar.Circuit (ArithExpr Var Satisfies)

variable {F : Type} [Field F] [DecidableEq F]

theorem Poly.denote_flatMap {α : Type} (val : Nat → F) (g : α → Poly F) (l : List α) :
    Poly.denote val (l.flatMap g) = (l.map fun x => Poly.denote val (g x)).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]

namespace System

variable (sys : System F)

/-- Slot values of instance `i` of circuit `f`, read at each slot's anchor;
the variable past the last slot is the instance's invocation id. -/
def slotValue (main : Nat → Nat → F) (f i s : Nat) : F :=
  match sys.templates[f]? with
  | some T =>
      if s = T.idVar then (sys.instId f i : F)
      else
        match T.anchor s with
        | some (ra, ja) => main (sys.row f i ra) ja
        | none => 0
  | none => 0

/-- The reconstructed wide row of instance `i` of circuit `f`. -/
def wideRow (main : Nat → Nat → F) (f i : Nat) : Var → F :=
  match sys.templates[f]? with
  | some T => T.wide (sys.slotValue main f i)
  | none => fun _ => 0

/-- The hypotheses shared by the refinement lemmas. -/
structure Trace (N : Nat) (main : Nat → Nat → F) : Prop where
  valid : sys.Valid
  small : SmallCast F sys.bound
  tall : sys.places.length ≤ N
  rows : ∀ p < N, Satisfies (narrowConstraints sys.width) (sys.assign main p)
  copies : ∀ L v, sys.copyCoefficient N main L v = 0

variable {sys} {N : Nat} {main : Nat → Nat → F} (trace : sys.Trace N main)
include trace

theorem Trace.template {f : Nat} (hf : f < sys.templates.length) {T : Template F}
    (hT : sys.templates[f]? = some T) :
    ∃ C, sys.circuits[f]? = some C ∧ T.width = sys.width ∧ T.Checked C := by
  have hc : f < sys.circuits.length := by rw [trace.valid.lengths.1]; exact hf
  have eq : sys.templates[f] = T := by
    have := List.getElem?_eq_getElem hf; rw [hT] at this; exact (Option.some.inj this).symm
  obtain ⟨w, checked⟩ := trace.valid.templates f hf hc
  rw [eq] at w checked
  exact ⟨sys.circuits[f], List.getElem?_eq_getElem hc, w, checked⟩

omit trace in
theorem Unchunked.at (unch : sys.Unchunked) {f : Nat} (hf : f < sys.templates.length) {T : Template F}
    (hT : sys.templates[f]? = some T) {C : Circuit F} (hC : sys.circuits[f]? = some C) :
    T.checkUnchunked C = true := by
  have hc : f < sys.circuits.length := (List.getElem?_eq_some_iff.mp hC).1
  have := unch f hf hc
  rw [List.getElem?_eq_getElem hf] at hT
  rw [List.getElem?_eq_getElem hc] at hC
  rwa [Option.some.inj hT, Option.some.inj hC] at this

theorem Trace.consistent {f i r j s : Nat} (place : (f, i, r) ∈ sys.places) {T : Template F}
    (hT : sys.templates[f]? = some T) (hj : j < sys.width) (cell : T.cell r j = some s) :
    main (sys.row f i r) j = sys.slotValue main f i s := by
  obtain ⟨ra, ja, anchor, eq⟩ := trace.valid.copy trace.small trace.tall trace.copies place hT hj cell
  have lt : s < T.slots.length := by
    obtain ⟨hf, _, _⟩ := sys.mem_places.mp place
    obtain ⟨C, _, _, checked⟩ := trace.template hf hT
    obtain ⟨row, hrow, hcell⟩ := Template.cell_some cell
    exact checked.cells row (List.mem_of_getElem? hrow) _ (List.mem_of_getElem? hcell) s rfl
  have ne : s ≠ T.idVar := by simp [Template.idVar]; omega
  simp [slotValue, hT, anchor, eq, ne]

theorem Trace.relations {f i : Nat} (hf : f < sys.templates.length) (hi : i < sys.cap f)
    {T : Template F} (hT : sys.templates[f]? = some T) :
    T.RelationsHold (sys.slotValue main f i) := by
  obtain ⟨C, _, width, checked⟩ := trace.template hf hT
  intro rel hrel
  obtain ⟨row, hrow, hrel⟩ := List.mem_flatMap.mp hrel
  obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hrow
  have idv : sys.slotValue main f i T.idVar = (sys.instId f i : F) := by simp [slotValue, hT]
  have count : sys.rowCount f = T.rows.length := by simp [System.rowCount, hT]
  have place : (f, i, r) ∈ sys.places := sys.mem_places.mpr ⟨hf, hi, by omega⟩
  have placeAt : sys.places[sys.row f i r]? = some (f, i, r) := by
    rw [List.getElem?_eq_getElem (sys.row_lt place), sys.places_row place]
  have pN : sys.row f i r < N := Nat.lt_of_lt_of_le (sys.row_lt place) trace.tall
  have wf := checked.rows _ hrow
  have w4 : 4 ≤ sys.width := width ▸ checked.width.1
  cases hrw : T.rows[r] with
  | message sel tag sub cells => rw [hrw] at hrel; simp [Row.relations] at hrel
  | gate lanes join roles =>
      rw [hrw] at hrel wf
      have placed : sys.Placed (sys.row f i r) f i r T (.gate lanes join roles) :=
        ⟨placeAt, hT, by rw [List.getElem?_eq_getElem hr, hrw]⟩
      simp only [Row.wellFormed, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, width] at wf
      obtain ⟨⟨lengthEq, lanesWf⟩, _⟩ := wf
      have laneAt : ∀ l (hl : l < lanes.length), (Row.gate lanes join roles).lane l = lanes[l] := by
        intro l hl; simp [Row.lane, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
      have value : ∀ l (hl : l < lanes.length),
          ((Row.gate lanes join roles).lane l).value (sys.instId f i)
              (fun m => main (sys.row f i r) (4 * l + m)) =
            Poly.denote (sys.slotValue main f i) (Lane.poly T.idVar lanes[l]) := by
        intro l hl
        rw [laneAt l hl]
        refine Lane.value_poly _ (lanesWf _ (List.getElem_mem hl)) _ _ ?_ idv
        intro m s hs
        have hm : m < 4 := by
          have := (List.getElem?_eq_some_iff.mp hs).1
          simpa [Lane.cells] using this
        apply trace.consistent place hT (by omega)
        rw [Template.cell_of (by rw [List.getElem?_eq_getElem hr, hrw])]
        simp only [Row.cells]
        rw [flatMap_cells_getElem? lanes hl hm, hs]
        rfl
      have gate := placed.gate w4 (trace.rows _ pN)
      cases join with
      | true =>
          simp only [Row.relations, List.mem_singleton] at hrel
          subst hrel
          rw [Poly.denote_flatMap, ← gate.1 rfl, ← lengthEq]
          symm
          exact sum_range_getElem lanes _ _ fun l hl => value l hl
      | false =>
          simp only [Row.relations] at hrel
          obtain ⟨role, p⟩ := rel
          have mem := (List.of_mem_zip hrel).2
          obtain ⟨lane, hlane, rfl⟩ := List.mem_map.mp mem
          obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hlane
          rw [← value l hl]
          exact gate.2 rfl l (by omega)

omit trace in
/-- A valid system with slot values under which every instance's relations
hold: what the constraint and ledger arguments read from a trace. -/
structure Logical (sys : System F) (main : Nat → Nat → F) : Prop where
  valid : sys.Valid
  relations : ∀ f (_hf : f < sys.templates.length), ∀ i < sys.cap f, ∀ T : Template F,
    sys.templates[f]? = some T → T.RelationsHold (sys.slotValue main f i)

theorem Trace.logical : sys.Logical main :=
  ⟨trace.valid, fun _ hf _ hi _ hT => trace.relations hf hi hT⟩

omit trace in
theorem Logical.template (logical : sys.Logical main) {f : Nat} (hf : f < sys.templates.length)
    {T : Template F} (hT : sys.templates[f]? = some T) :
    ∃ C, sys.circuits[f]? = some C ∧ T.width = sys.width ∧ T.Checked C := by
  have hc : f < sys.circuits.length := by rw [logical.valid.lengths.1]; exact hf
  have eq : sys.templates[f] = T := by
    have := List.getElem?_eq_getElem hf; rw [hT] at this; exact (Option.some.inj this).symm
  obtain ⟨w, checked⟩ := logical.valid.templates f hf hc
  rw [eq] at w checked
  exact ⟨sys.circuits[f], List.getElem?_eq_getElem hc, w, checked⟩

omit trace in
/-- Every reconstructed wide row satisfies its circuit. -/
theorem Logical.wide_holds (logical : sys.Logical main) {f i : Nat} (hf : f < sys.circuits.length)
    (hi : i < sys.cap f) : sys.circuits[f].Holds (sys.wideRow main f i) := by
  have hft : f < sys.templates.length := by rw [← logical.valid.lengths.1]; exact hf
  obtain ⟨T, hT, _, _⟩ := sys.templates_getElem? hft
  obtain ⟨C, hC, _, checked⟩ := logical.template hft hT
  have : sys.circuits[f] = C := by
    have := List.getElem?_eq_getElem hf; rw [hC] at this; exact (Option.some.inj this).symm
  rw [this]
  have := checked.constraints_hold (logical.relations f hft i hi T hT)
  simpa [wideRow, hT] using this

theorem Trace.wide_holds {f i : Nat} (hf : f < sys.circuits.length) (hi : i < sys.cap f) :
    sys.circuits[f].Holds (sys.wideRow main f i) :=
  trace.logical.wide_holds hf hi

omit trace in
theorem fixedAt_placed_or {p k : Nat} (valid : sys.Valid) :
    (sys.places[p]? = none ∧ sys.fixedAt p k = 0) ∨
      ∃ f i r T row, sys.Placed p f i r T row ∧ sys.fixedAt p k = row.fixed sys.width (sys.labelAt p) (sys.multAt p) (sys.instId f i : F) k := by
  cases hp : sys.places[p]? with
  | none => exact Or.inl ⟨rfl, sys.fixedAt_unplaced hp⟩
  | some x =>
      obtain ⟨f, i, r⟩ := x
      have mem : (f, i, r) ∈ sys.places := List.mem_of_getElem? hp
      obtain ⟨hf, _, hr⟩ := sys.mem_places.mp mem
      obtain ⟨T, hT, count, _⟩ := sys.templates_getElem? hf
      rw [count] at hr
      have placed : sys.Placed p f i r T T.rows[r] := ⟨hp, hT, List.getElem?_eq_getElem hr⟩
      exact Or.inr ⟨f, i, r, T, T.rows[r], placed, placed.fixed k⟩

omit trace in
theorem fixedAt_label (valid : sys.Valid) {p j : Nat} (hj : j < sys.width) :
    sys.fixedAt p (labelCol sys.width j) = sys.labelAt p j := by
  rcases fixedAt_placed_or (k := labelCol sys.width j) valid with ⟨none, h⟩ | ⟨_, _, _, _, row, _, h⟩
  · rw [h, sys.labelAt_unplaced none]
  · rw [h, Row.fixed_label _ _ _ _ _ hj]

omit trace in
theorem fixedAt_mult (valid : sys.Valid) {p j : Nat} (hj : j < sys.width) :
    sys.fixedAt p (multCol sys.width j) = sys.multAt p j := by
  rcases fixedAt_placed_or (k := multCol sys.width j) valid with ⟨none, h⟩ | ⟨_, _, _, _, row, _, h⟩
  · rw [h, sys.multAt_unplaced none]
  · rw [h, Row.fixed_mult _ _ _ _ _ hj]

/-- Message tuple and multiplicity of physical row `p`. -/
def msgTuple (sys : System F) (main : Nat → Nat → F) (p : Nat) : List F :=
  sys.fixedAt p (tagCol sys.width) :: sys.fixedAt p (subCol sys.width) ::
    (List.range (sys.width - 1)).map fun j => main p (j + 1)

def msgMult (sys : System F) (main : Nat → Nat → F) (p : Nat) : F :=
  sys.fixedAt p (selCol sys.width) * main p 0

noncomputable def msgLedger (sys : System F) (N : Nat) (main : Nat → Nat → F) : Ledger F :=
  ∑ p ∈ Finset.range N, Finsupp.single (msgTuple sys main p) (msgMult sys main p)

noncomputable def copyLedger (sys : System F) (N : Nat) (main : Nat → Nat → F) : Ledger F :=
  ∑ p ∈ Finset.range N, ∑ j ∈ Finset.range sys.width,
    Finsupp.single [(COPY : F), sys.labelAt p j, main p j] (sys.multAt p j)

omit trace in
theorem ledger_list_sum (l : List (Ledger F)) (t : List F) : l.sum t = (l.map fun x => x t).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]

omit trace in
theorem finset_sum_range_list {M : Type} [AddCommMonoid M] (n : Nat) (g : Nat → M) :
    ∑ p ∈ Finset.range n, g p = ((List.range n).map g).sum := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]; simp

omit trace in
theorem narrowLedger_split (valid : sys.Valid) (w4 : 4 ≤ sys.width) :
    sys.narrowLedger N main = msgLedger sys N main + copyLedger sys N main := by
  unfold System.narrowLedger msgLedger copyLedger
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Circuit.rowLedger, narrowCircuit, List.map_cons, List.sum_cons, List.map_map]
  congr 1
  · simp only [Lookup.entry, Lookup.tuple, messageLookup, msgTuple, msgMult, fixedVar,
      ArithExpr.denote, List.map_cons, List.map_map]
    rw [sys.assign_fixed, sys.assign_fixed, sys.assign_fixed, sys.assign_main main (by omega)]
    congr 1
    simp only [List.cons.injEq, true_and, List.map_inj_left]
    intro j hj
    simp only [Function.comp, ArithExpr.denote]
    rw [sys.assign_main main (by have := List.mem_range.mp hj; omega)]
  · rw [finset_sum_range_list]
    congr 1
    apply List.map_congr_left
    intro j hj
    have hj := List.mem_range.mp hj
    simp only [Function.comp, Lookup.entry, Lookup.tuple, copyLookup, fixedVar, ArithExpr.denote,
      List.map_cons, List.map_nil]
    rw [sys.assign_fixed, sys.assign_fixed, sys.assign_main main hj, fixedAt_label valid hj,
      fixedAt_mult valid hj]

omit trace in
theorem copyLedger_apply (t : List F) :
    copyLedger sys N main t = ∑ p ∈ Finset.range N, ∑ j ∈ Finset.range sys.width,
      if [(COPY : F), sys.labelAt p j, main p j] = t then sys.multAt p j else 0 := by
  simp [copyLedger, Finsupp.finsetSum_apply, Finsupp.single_apply]

omit trace in
theorem msgLedger_apply_short (w4 : 4 ≤ sys.width) {t : List F} (short : t.length = 3) :
    msgLedger sys N main t = 0 := by
  simp only [msgLedger, Finsupp.finsetSum_apply, Finsupp.single_apply]
  apply Finset.sum_eq_zero
  intro p _
  rw [if_neg]
  intro h
  have := congrArg List.length h
  simp [msgTuple] at this
  omega

omit trace in
/-- Balance with an external ledger that has no copy tuples silences the copy bus. -/
theorem copy_balance (valid : sys.Valid) (w4 : 4 ≤ sys.width) {ext : Ledger F}
    (extCopy : ∀ L v, ext [(COPY : F), L, v] = 0) (balanced : sys.narrowLedger N main + ext = 0) :
    copyLedger sys N main = 0 ∧ msgLedger sys N main + ext = 0 ∧
      ∀ L v, sys.copyCoefficient N main L v = 0 := by
  rw [narrowLedger_split valid w4] at balanced
  have atCopy : ∀ L v, copyLedger sys N main [(COPY : F), L, v] = 0 := by
    intro L v
    have := congrArg (fun x : Ledger F => x [(COPY : F), L, v]) balanced
    simp only [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply, extCopy, add_zero] at this
    rw [msgLedger_apply_short w4 rfl, zero_add] at this
    exact this
  have copy : copyLedger sys N main = 0 := by
    ext t
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    match t with
    | [c, L, v] =>
        by_cases hc : c = (COPY : F)
        · subst hc; exact atCopy L v
        · rw [copyLedger_apply]
          apply Finset.sum_eq_zero; intro p _
          apply Finset.sum_eq_zero; intro j _
          rw [if_neg]; intro h; exact hc (List.cons.inj h).1.symm
    | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ =>
        rw [copyLedger_apply]
        apply Finset.sum_eq_zero; intro p _
        apply Finset.sum_eq_zero; intro j _
        rw [if_neg]; intro h; have := congrArg List.length h; simp at this
  refine ⟨copy, by simpa [copy] using balanced, fun L v => ?_⟩
  have := atCopy L v
  rw [copyLedger_apply] at this
  rw [System.copyCoefficient, ← this]
  apply Finset.sum_congr rfl; intro p _
  apply Finset.sum_congr rfl; intro j _
  congr 1
  simp

/-! ## The message ledger -/

/-- The wide lookup a checked message row carries, given slot values. -/
noncomputable def msgEntry (val : Nat → F) : F × F × F × List (Option Nat) → Ledger F
  | (sel, tag, sub, cells) =>
      Finsupp.single (tag :: sub :: ((cells.drop 1).filterMap id).map val)
        (sel * val ((cells.head?.join).getD 0))

noncomputable def rowEntry (val : Nat → F) : Row F → Ledger F
  | .gate .. => 0
  | .message sel tag sub cells => msgEntry val (sel, tag, sub, cells)

omit trace in
theorem rowEntry_sum (val : Nat → F) (T : Template F) :
    (T.rows.map (rowEntry val)).sum = (T.messages.map (msgEntry val)).sum := by
  unfold Template.messages
  induction T.rows with
  | nil => simp
  | cons row rows ih =>
      cases row with
      | gate => simp [rowEntry, ih]
      | message => simp [rowEntry, ih]

omit trace in
theorem forall₂_mem {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {x : α} (hx : x ∈ xs) : ∃ y ∈ ys, R x y := by
  induction h with
  | nil => simp at hx
  | cons r _ ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨_, List.mem_cons_self .., r⟩
      · obtain ⟨y, hy, ry⟩ := ih hx
        exact ⟨y, List.mem_cons_of_mem _ hy, ry⟩

omit trace in
theorem messageCells_drop (W mult : Nat) (ps : List Nat) :
    ((messageCells W mult ps).drop 1).filterMap id = ps := by
  simp [messageCells, List.filterMap_append, List.filterMap_map]

omit trace in
theorem messageCells_succ (W mult : Nat) (ps : List Nat) {j : Nat} (hj : j < ps.length) :
    (messageCells W mult ps)[j + 1]? = some (some ps[j]) := by
  simp only [messageCells, List.getElem?_cons_succ]
  rw [List.getElem?_append_left (by simpa using hj)]
  simp [hj]

omit trace in
theorem msgEntry_lookup {W : Nat} {val : Nat → F} {a : Var → F} {m : F × F × F × List (Option Nat)}
    {l : Lookup F} (h : MessageSound W val a m l) : msgEntry val m = l.entry a := by
  obtain ⟨sel, tag, sub, cells⟩ := m
  obtain ⟨mult, payload, cellsEq, _, multEq, tupleEq⟩ := h
  simp only at cellsEq multEq tupleEq
  simp only [msgEntry, Lookup.entry, multEq, tupleEq, cellsEq, messageCells_drop]
  simp [messageCells]

omit trace in
theorem msgEntries {W : Nat} {val : Nat → F} {a : Var → F} {ms : List (F × F × F × List (Option Nat))}
    {ls : List (Lookup F)} (h : List.Forall₂ (MessageSound W val a) ms ls) :
    (ms.map (msgEntry val)).sum = (ls.map (·.entry a)).sum := by
  induction h with
  | nil => rfl
  | cons r _ ih => simp [msgEntry_lookup r, ih]

/-- Physical row `p`'s message, cut to its arity, is its template row's wide lookup. -/
theorem Trace.row_message {f i r : Nat} (place : (f, i, r) ∈ sys.places) {T : Template F}
    (hT : sys.templates[f]? = some T) (hr : r < T.rows.length) :
    Finsupp.single (sys.proj (msgTuple sys main (sys.row f i r))) (msgMult sys main (sys.row f i r)) =
      rowEntry (sys.slotValue main f i) T.rows[r] := by
  obtain ⟨hf, hi, _⟩ := sys.mem_places.mp place
  obtain ⟨C, hC, width, checked⟩ := trace.template hf hT
  have placeAt : sys.places[sys.row f i r]? = some (f, i, r) := by
    rw [List.getElem?_eq_getElem (sys.row_lt place), sys.places_row place]
  have placed : sys.Placed (sys.row f i r) f i r T T.rows[r] :=
    ⟨placeAt, hT, List.getElem?_eq_getElem hr⟩
  cases hrw : T.rows[r] with
  | gate lanes join roles =>
      simp [msgMult, placed.fixed, Row.fixed_sel, hrw, Row.messageValue, rowEntry]
  | message sel tag sub cells =>
      have mem : (sel, tag, sub, cells) ∈ T.messages := by
        simp only [Template.messages, List.mem_filterMap]
        exact ⟨_, List.getElem_mem hr |> (hrw ▸ ·), by simp⟩
      obtain ⟨mult, ps, cellsEq, wide⟩ := checked.rowShaped (trace.relations hf hi hT) _ mem
      simp only at cellsEq
      rw [width] at cellsEq wide
      have cellAt : ∀ j, T.cell r j = (cells[j]?).getD none := fun j => by
        rw [Template.cell_of (List.getElem?_eq_getElem hr), hrw]; rfl
      have main0 : main (sys.row f i r) 0 = sys.slotValue main f i mult :=
        trace.consistent place hT (by omega) (by rw [cellAt, cellsEq]; rfl)
      have mainSucc : ∀ j (hj : j < ps.length),
          main (sys.row f i r) (j + 1) = sys.slotValue main f i ps[j] := fun j hj =>
        trace.consistent place hT (by omega) (by rw [cellAt, cellsEq, messageCells_succ _ _ _ hj]; rfl)
      have tagV : sys.fixedAt (sys.row f i r) (tagCol sys.width) = tag := by
        rw [placed.fixed, Row.fixed_tag, hrw]; rfl
      have subV : sys.fixedAt (sys.row f i r) (subCol sys.width) = sub := by
        rw [placed.fixed, Row.fixed_sub, hrw]; rfl
      have selV : sys.fixedAt (sys.row f i r) (selCol sys.width) = sel := by
        rw [placed.fixed, Row.fixed_sel, hrw]; rfl
      have arity : sys.arityOf (msgTuple sys main (sys.row f i r)) = ps.length := by
        have entry : ((tag, sub), ((cells.drop 1).filterMap id).length) ∈ sys.arities := by
          simp only [System.arities, List.mem_flatMap, List.mem_map]
          exact ⟨T, List.mem_of_getElem? hT, _, mem, rfl⟩
        have := trace.valid.arities _ entry
        rw [cellsEq, messageCells_drop] at this
        simp only [System.arityOf, msgTuple, tagV, subV, this, Option.getD_some]
      simp only [rowEntry, msgEntry, System.proj, arity, msgMult, selV, main0]
      rw [cellsEq, messageCells_drop]
      congr 1
      simp only [msgTuple, tagV, subV]
      rw [show 2 + ps.length = ps.length + 1 + 1 by omega, List.take_succ_cons, List.take_succ_cons,
        ← List.map_take, List.take_range, Nat.min_eq_left (by omega)]
      congr 2
      apply List.ext_getElem (by simp)
      intro j h1 h2
      simp only [List.getElem_map, List.getElem_range]
      exact mainSucc j (by simpa using h1)

omit trace in
theorem sum_map_flatMap {α β M : Type} [AddCommMonoid M] (l : List α) (g : α → List β) (H : β → M) :
    ((l.flatMap g).map H).sum = (l.map fun a => ((g a).map H).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

omit trace in
/-- Every instance's template message rows read at its slot values. A chunk
row contributes its keyed chunk `[tag, sub_c, key, chunk_c]`. -/
noncomputable def msgSum (sys : System F) (main : Nat → Nat → F) : Ledger F :=
  ((List.range sys.templates.length).map fun f =>
    ((List.range (sys.cap f)).map fun i =>
      ((sys.templates[f]?.map fun T => (T.messages.map (msgEntry (sys.slotValue main f i))).sum).getD 0)).sum).sum

/-- The message ledger, cut to arities, is the sum over instances of their
template's message rows read at the instance's slot values. -/
theorem Trace.message_rows :
    Finsupp.mapDomain sys.proj (msgLedger sys N main) = sys.msgSum main := by
  unfold msgSum
  let G : Nat → Ledger F := fun p =>
    Finsupp.single (sys.proj (msgTuple sys main p)) (msgMult sys main p)
  have step1 : Finsupp.mapDomain sys.proj (msgLedger sys N main) = ∑ p ∈ Finset.range N, G p := by
    simp only [msgLedger, Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single, G]
  have step2 : ∑ p ∈ Finset.range N, G p = ∑ p ∈ Finset.range sys.places.length, G p := by
    symm
    apply Finset.sum_subset (Finset.range_subset_range.mpr trace.tall)
    intro p _ out
    have none := sys.places_getElem?_none (by simpa using out)
    simp [G, msgMult, sys.fixedAt_unplaced none]
  have step3 : ∑ p ∈ Finset.range sys.places.length, G p =
      (sys.places.map fun x => G (sys.row x.1 x.2.1 x.2.2)).sum := by
    rw [finset_sum_range_list]
    apply sum_range_getElem
    intro p lt
    rw [sys.row_places lt]
  rw [step1, step2, step3]
  simp only [System.places, System.enumerate, sum_map_flatMap, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro f hf
  have hf := List.mem_range.mp hf
  obtain ⟨T, hT, count, _⟩ := sys.templates_getElem? hf
  try simp only [sum_map_flatMap, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  simp only [Function.comp_def, Option.map_some, Option.getD_some, hT]
  rw [count, sum_range_getElem T.rows _ (rowEntry (sys.slotValue main f i)) (fun r hr =>
    trace.row_message (sys.mem_places.mpr ⟨hf, hi, by omega⟩) hT hr)]
  rw [rowEntry_sum]

/-- The message ledger, cut to arities, is the wide ledger of the reconstructed rows. -/
theorem Trace.message_ledger (unch : sys.Unchunked) :
    Finsupp.mapDomain sys.proj (msgLedger sys N main) = sys.wideLedger (sys.wideRow main) := by
  rw [trace.message_rows]
  unfold System.wideLedger
  rw [trace.valid.lengths.1]
  apply congrArg List.sum
  apply List.map_congr_left
  intro f hf
  have hf := List.mem_range.mp hf
  obtain ⟨T, hT, _, _⟩ := sys.templates_getElem? hf
  obtain ⟨C, hC, _, checked⟩ := trace.template hf hT
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  simp only [hC, hT, Option.map_some, Option.getD_some, System.wideRow]
  exact msgEntries (checked.messages_sound (trace.relations hf hi hT) (unch.at hf hT hC))

end System

/-- **Refinement of the tiled layout.** A narrow trace of `N` rows that
satisfies the narrow circuit on every row, with the generated fixed columns,
and whose lookups balance against an external ledger carrying no copy-bus
tuples, yields for every circuit `f` and instance `i < cap f` a row of
circuit `f`. Every such row satisfies its circuit, and the rows' lookups
balance against the external ledger cut to message arities. -/
theorem System.sound {sys : System F} (ok : sys.check = true) (small : SmallCast F sys.bound)
    {N : Nat} (tall : sys.places.length ≤ N) {main : Nat → Nat → F}
    (rows : ∀ p < N, Satisfies (narrowCircuit (F := F) sys.width).constraints (sys.assign main p))
    {ext : Ledger F} (extCopy : ∀ L v, ext [(COPY : F), L, v] = 0)
    (balanced : sys.narrowLedger N main + ext = 0) :
    (∀ f (hf : f < sys.circuits.length), ∀ i < sys.cap f,
        sys.circuits[f].Holds (sys.wideRow main f i)) ∧
      sys.wideLedger (sys.wideRow main) + Finsupp.mapDomain sys.proj ext = 0 := by
  have valid := sys.valid_of_check ok
  obtain ⟨_, msgBal, copies⟩ := System.copy_balance valid valid.width.1 extCopy balanced
  have trace : sys.Trace N main := ⟨valid, small, tall, rows, copies⟩
  have unch := sys.unchunked_of_check ok
  refine ⟨fun f hf i hi => trace.wide_holds hf hi, ?_⟩
  have := congrArg (Finsupp.mapDomain sys.proj) msgBal
  rwa [Finsupp.mapDomain_add, trace.message_ledger unch, Finsupp.mapDomain_zero] at this

end Aiur.Tiling
