import Aiur.Tiling.Shape
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Soundness of the template checker

If `T.check C` holds, every slot valuation that satisfies all of `T`'s gate
relations yields a row of `C`: the wide assignment reads each column from its
column slot, satisfies every constraint of `C`, and the message rows carry
exactly `C`'s lookups (multiplicity and tuple), in order.
-/

namespace Aiur.Tiling

open Aiur.Scalar.Circuit (ArithExpr Var Satisfies)

variable {F : Type}

/-! ## Polynomial facts -/

section PolyFacts

variable [CommRing F]

theorem Mono.eval_congr {f g : Nat → F} (m : Mono) (h : ∀ v ∈ m, f v = g v) :
    Mono.eval f m = Mono.eval g m := by
  induction m with
  | nil => rfl
  | cons v m ih =>
      simp only [Mono.eval_cons]
      rw [h v (by simp), ih (fun w hw => h w (by simp [hw]))]

theorem Poly.denote_congr {f g : Nat → F} (p : Poly F) (h : ∀ t ∈ p, ∀ v ∈ t.1, f v = g v) :
    p.denote f = p.denote g := by
  induction p with
  | nil => rfl
  | cons t p ih =>
      simp only [Poly.denote_cons]
      rw [Mono.eval_congr t.1 (h t (by simp)), ih (fun u hu => h u (by simp [hu]))]

def Term.value (val : Nat → F) : Term F → F
  | .linear c s => c * val s
  | .product c s t => c * (val s * val t)

def Term.slots : Term F → List Nat
  | .linear _ s => [s]
  | .product _ s t => [s, t]

theorem Term.value_congr {f g : Nat → F} (t : Term F) (h : ∀ v ∈ t.slots, f v = g v) :
    t.value f = t.value g := by
  cases t with
  | linear c s => simp [Term.value, h s (by simp [Term.slots])]
  | product c s u =>
      simp [Term.value, h s (by simp [Term.slots]), h u (by simp [Term.slots])]

theorem Term.denote_poly (val : Nat → F) (t : Term F) : (Term.poly t).denote val = t.value val := by
  cases t with
  | linear c s => simp [Term.poly, Term.value]
  | product c s u =>
      simp [Term.poly, Term.value, Mono.eval_insert]

theorem Term.denote_subst (val : Nat → F) (f : Nat → Poly F) (t : Term F) :
    (Term.subst f t).denote val = t.value (fun u => (f u).denote val) := by
  cases t <;> simp [Term.subst, Term.value]

theorem denote_substTerms (val : Nat → F) (f : Nat → Poly F) (terms : List (Term F)) :
    (substTerms f terms).denote val = (terms.map (Term.value fun u => (f u).denote val)).sum := by
  induction terms with
  | nil => simp [substTerms]
  | cons t terms ih =>
      simp only [substTerms, List.flatMap_cons, Poly.denote_append, List.map_cons,
        List.sum_cons] at ih ⊢
      rw [Term.denote_subst, ih]

theorem denote_flatMap_poly (val : Nat → F) (terms : List (Term F)) :
    Poly.denote val (terms.flatMap Term.poly) = (terms.map (Term.value val)).sum := by
  induction terms with
  | nil => simp
  | cons t terms ih =>
      simp only [List.flatMap_cons, Poly.denote_append, List.map_cons, List.sum_cons, ih,
        Term.denote_poly]

theorem denote_defPoly (val : Nat → F) (s : Nat) (terms : List (Term F)) (k : F) :
    (defPoly s terms k).denote val = k + (terms.map (Term.value val)).sum - val s := by
  simp [defPoly, denote_flatMap_poly]; ring

theorem Term.slotsBelow_iff [DecidableEq F] (s : Nat) (t : Term F) :
    t.slotsBelow s = true ↔ ∀ u ∈ t.slots, u < s := by
  cases t <;> simp [Term.slotsBelow, Term.slots]

/-- A substitution guarded by `u < s` agrees with the unguarded one on terms
whose slots are below `s`. -/
theorem denote_substTerms_guarded [DecidableEq F] (val : Nat → F) (s : Nat) (f : Nat → Poly F)
    (terms : List (Term F)) (below : terms.all (Term.slotsBelow s) = true) :
    (substTerms (fun u => if _h : u < s then f u else []) terms).denote val =
      (terms.map (Term.value fun u => (f u).denote val)).sum := by
  rw [denote_substTerms]
  congr 1
  apply List.map_congr_left
  intro t member
  apply Term.value_congr
  intro u present
  have below := (Term.slotsBelow_iff s t).mp (List.all_eq_true.mp below t member) u present
  simp [below]

theorem Poly.denote_eq_zero_of_norm [DecidableEq F] (p : Poly F) (h : (Poly.norm p).isEmpty = true)
    (a : Nat → F) : p.denote a = 0 := by
  rw [← Poly.denote_norm a p, List.isEmpty_iff.mp h]; rfl

theorem allPairs_iff {α β : Type} (f : α → β → Bool) (xs : List α) (ys : List β) :
    allPairs f xs ys = true ↔ List.Forall₂ (fun x y => f x y = true) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [allPairs]
  | cons x xs ih => cases ys <;> simp [allPairs, ih]

end PolyFacts

/-! ## Unfolding the slot semantics -/

section Template

variable [Field F] [DecidableEq F] (T : Template F)

def Template.RelationsHold (val : Nat → F) : Prop :=
  ∀ rel ∈ T.relations, rel.2.denote val = 0

/-- The wide row: each column is read from its column slot. -/
def Template.wide (val : Nat → F) (c : Nat) : F :=
  match T.colSlot c with
  | some s => val s
  | none => 0

theorem Template.meaning_column {s c : Nat} (h : T.slots[s]? = some (.column c)) :
    T.meaning s = Poly.var c := by
  rw [Template.meaning, h]

theorem Template.meaning_sum {s : Nat} {terms : List (Term F)} {k : F}
    (h : T.slots[s]? = some (.sum terms k)) :
    T.meaning s = Poly.const k ++ substTerms (fun u => if _h : u < s then T.meaning u else []) terms := by
  rw [Template.meaning, h]

theorem Template.expandAbove_sum {s t : Nat} {terms : List (Term F)} {k : F}
    (h : T.slots[t]? = some (.sum terms k)) (above : s < t) :
    T.expandAbove s t =
      Poly.const k ++ substTerms (fun u => if _h : u < t then T.expandAbove s u else []) terms := by
  rw [Template.expandAbove, h]; simp [above]

theorem Template.expandAbove_var {s t : Nat}
    (h : ∀ terms k, T.slots[t]? = some (.sum terms k) → t ≤ s) :
    T.expandAbove s t = Poly.var t := by
  rw [Template.expandAbove]
  split
  · rename_i terms k found
    have := h terms k found
    simp only [show ¬ s < t by omega, ↓reduceIte]
  · rfl

theorem Template.wideSlot_lt {s : Nat} (h : T.wideSlot s = true) : s < T.slots.length := by
  unfold Template.wideSlot at h
  cases found : T.slots[s]? with
  | none => rw [found] at h; simp at h
  | some d => exact (List.getElem?_eq_some_iff.mp found).1

theorem Template.wideTerm_slots {t : Term F} (h : T.wideTerm t = true) : ∀ v ∈ t.slots, T.wideSlot v = true := by
  cases t <;> simp_all [Template.wideTerm, Term.slots]

/-! ## The checker's conjuncts -/

structure Template.Checked (C : Circuit F) : Prop where
  width : 4 ≤ T.width ∧ T.width % 4 = 0
  rows : ∀ row ∈ T.rows, row.wellFormed T.width = true
  cells : ∀ row ∈ T.rows, ∀ cell ∈ row.cells, ∀ s ∈ cell, s < T.slots.length
  slots : ∀ s (h : s < T.slots.length), T.checkSlot s T.slots[s] = true
  relations : ∀ rel ∈ T.relations, T.checkRelation C rel = true
  constraints : ∀ j (h : j < C.constraints.length), T.checkConstraint j C.constraints[j] = true
  messages : T.checkUnchunked C = true ∨ T.checkGroups C = true

theorem Template.checked_of_check {C : Circuit F} (ok : T.check C = true) : T.Checked C := by
  simp only [Template.check, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, decide_eq_true_eq,
    beq_iff_eq] at ok
  obtain ⟨⟨⟨⟨⟨⟨⟨w4, wmod⟩, rows⟩, cells⟩, slots⟩, relations⟩, constraints⟩, messages⟩ := ok
  refine ⟨⟨w4, wmod⟩, rows, ?_, ?_, relations, ?_, messages⟩
  · intro row hrow cell hcell s hs
    have := cells row hrow cell hcell
    simp only [Option.all_eq_true, decide_eq_true_eq] at this
    exact this s (Option.mem_def.mp hs)
  · intro s h
    exact slots (T.slots[s], s) (List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [h]))
  · intro j h
    exact constraints (C.constraints[j], j) (List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [h]))

theorem Template.Checked.unchunked {C : Circuit F} (_checked : T.Checked C) (h : T.checkUnchunked C = true) :
    List.Forall₂ (fun m l => T.checkMessage m l = true) T.messages C.lookups := by
  simp only [Template.checkUnchunked, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  rw [List.forall₂_iff_zip]
  exact ⟨h.1, fun hm => h.2 _ hm⟩

/-! ## Slot values -/

variable {T} {C : Circuit F} (checked : T.Checked C) {val : Nat → F} (holds : T.RelationsHold val)
include checked holds

omit holds in
theorem Template.Checked.slot_sum {s : Nat} {terms : List (Term F)} {k : F}
    (h : T.slots[s]? = some (.sum terms k)) :
    terms.all (Term.slotsBelow s) = true ∧ terms.all T.wideTerm = true ∧
      ∃ rel ∈ T.relations, rel.1 = .defines s := by
  obtain ⟨lt, found⟩ := List.getElem?_eq_some_iff.mp h
  have := checked.slots s lt
  rw [found] at this
  simp only [Template.checkSlot, Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- Every sum slot equals its definition. By descending induction: a
relation defining `s` may mention carry slots above `s`, whose own
definitions are already established. -/
theorem Template.Checked.defined :
    ∀ s, ∀ terms k, T.slots[s]? = some (.sum terms k) →
      val s = k + (terms.map (Term.value val)).sum := by
  have main : ∀ n, ∀ s, T.slots.length - s ≤ n → ∀ terms k,
      T.slots[s]? = some (.sum terms k) → val s = k + (terms.map (Term.value val)).sum := by
    intro n
    induction n with
    | zero =>
        intro s small terms k h
        have := (List.getElem?_eq_some_iff.mp h).1
        omega
    | succ n ih =>
        intro s small terms k h
        obtain ⟨_, _, rel, hrel, role⟩ := checked.slot_sum h
        have relCheck := checked.relations rel hrel
        obtain ⟨role', p⟩ := rel
        simp only at role
        subst role
        simp only [Template.checkRelation, h] at relCheck
        have expand : ∀ t, (T.expandAbove s t).denote val = val t := by
          intro t
          induction t using Nat.strong_induction_on with
          | _ t iht =>
              by_cases sum : ∃ terms' k', T.slots[t]? = some (.sum terms' k') ∧ s < t
              · obtain ⟨terms', k', ht, above⟩ := sum
                rw [T.expandAbove_sum ht above, Poly.denote_append, Poly.denote_const]
                have below := (checked.slot_sum ht).1
                rw [denote_substTerms_guarded val t _ terms' below]
                have lt := (List.getElem?_eq_some_iff.mp ht).1
                have : T.slots.length - t ≤ n := by omega
                rw [ih t this terms' k' ht]
                congr 2
                apply List.map_congr_left
                intro u member
                apply Term.value_congr
                intro v present
                exact iht v ((Term.slotsBelow_iff t u).mp (List.all_eq_true.mp below u member) v present)
              · rw [T.expandAbove_var (fun terms' k' ht => by
                  by_contra above
                  exact sum ⟨terms', k', ht, by omega⟩)]
                simp
        have zero := holds _ hrel
        have identity := Poly.Identical.denote val relCheck
        rw [Poly.denote_subst] at identity
        simp only at zero
        rw [show (fun v => (T.expandAbove s v).denote val) = val from funext expand, zero,
          denote_defPoly] at identity
        linear_combination identity
  intro s
  exact main _ s le_rfl

/-- Every wide slot's value is its meaning over the wide row. -/
theorem Template.Checked.meaning_val :
    ∀ s, T.wideSlot s = true → (T.meaning s).denote (T.wide val) = val s := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
      intro wide
      have lt := T.wideSlot_lt wide
      have check := checked.slots s lt
      cases found : T.slots[s] with
      | column c =>
          rw [T.meaning_column (c := c) (by simp [lt, found]), Poly.denote_var]
          rw [found] at check
          simp only [Template.checkSlot, beq_iff_eq] at check
          simp [Template.wide, check]
      | sum terms k =>
          have h : T.slots[s]? = some (.sum terms k) := by simp [lt, found]
          rw [T.meaning_sum h, Poly.denote_append, Poly.denote_const]
          obtain ⟨below, wideTerms, _⟩ := checked.slot_sum h
          rw [denote_substTerms_guarded _ s _ terms below, checked.defined holds s terms k h]
          congr 2
          apply List.map_congr_left
          intro t member
          apply Term.value_congr
          intro u present
          have := (Term.slotsBelow_iff s t).mp (List.all_eq_true.mp below t member) u present
          exact ih u this (T.wideTerm_slots (List.all_eq_true.mp wideTerms t member) u present)
      | invocation => simp [Template.wideSlot, lt, found] at wide
      | key _ => simp [Template.wideSlot, lt, found] at wide

theorem Template.Checked.subst_meaning {p : Poly F} (wide : T.widePoly p = true) :
    (Poly.subst T.meaning p).denote (T.wide val) = p.denote val := by
  rw [Poly.denote_subst]
  apply Poly.denote_congr
  intro t member v present
  simp only [Template.widePoly, List.all_eq_true] at wide
  exact checked.meaning_val holds v (wide t member v present)

/-- An invocation slot holds the invocation id. -/
theorem Template.Checked.invocation {s : Nat} (h : T.slots[s]? = some .invocation) :
    val s = val T.idVar := by
  have lt := (List.getElem?_eq_some_iff.mp h).1
  have check := checked.slots s lt
  rw [(List.getElem?_eq_some_iff.mp h).2] at check
  simp only [Template.checkSlot, List.any_eq_true, beq_iff_eq] at check
  obtain ⟨rel, hrel, role⟩ := check
  have relCheck := checked.relations rel hrel
  obtain ⟨role', p⟩ := rel
  simp only at role
  subst role
  simp only [Template.checkRelation, Bool.and_eq_true] at relCheck
  have := Poly.Identical.denote val relCheck.2
  rw [holds _ hrel, Poly.denote_sub, Poly.denote_var, Poly.denote_var] at this
  exact (sub_eq_zero.mp this.symm)

/-! ## Constraints and messages -/

theorem Template.Checked.constraints_hold : C.Holds (T.wide val) := by
  intro p member
  obtain ⟨j, lt, rfl⟩ := List.getElem_of_mem member
  have check := checked.constraints j lt
  simp only [Template.checkConstraint, Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at check
  rcases check with empty | ⟨rel, hrel, role⟩
  · rw [← Poly.denote_ofExpr]
    exact Poly.denote_eq_zero_of_norm _ empty _
  · have relCheck := checked.relations rel hrel
    obtain ⟨role', p⟩ := rel
    simp only at role
    subst role
    simp only [Template.checkRelation, List.getElem?_eq_getElem lt, Bool.and_eq_true] at relCheck
    have identity := Poly.Identical.denote (T.wide val) relCheck.2
    rw [checked.subst_meaning holds relCheck.1, Poly.denote_ofExpr] at identity
    rw [← identity]
    exact holds _ hrel

/-- What a checked message row carries. -/
def MessageSound (W : Nat) (val : Nat → F) (a : Var → F)
    (message : F × F × F × List (Option Nat)) (lookup : Lookup F) : Prop :=
  ∃ mult payload, message.2.2.2 = messageCells W mult payload ∧ payload.length + 1 ≤ W ∧
    lookup.multiplicity.denote a = message.1 * val mult ∧
    lookup.tuple a = message.2.1 :: message.2.2.1 :: payload.map val

omit checked holds in
theorem Template.checkMessage_true {sel tag sub : F} {cells : List (Option Nat)} {lookup : Lookup F}
    (h : T.checkMessage (sel, tag, sub, cells) lookup = true) :
    ∃ tagExpr subExpr payload mult rest,
      lookup.args = tagExpr :: subExpr :: payload ∧ cells = some mult :: rest ∧
      Poly.Identical (Poly.ofExpr tagExpr) (Poly.const tag) = true ∧
      Poly.Identical (Poly.ofExpr subExpr) (Poly.const sub) = true ∧
      payload.length + 1 ≤ T.width ∧
      cells = messageCells T.width mult ((rest.take payload.length).filterMap id) ∧
      T.wideSlot mult = true ∧
      Poly.Identical (Poly.scale sel (T.meaning mult)) (Poly.ofExpr lookup.multiplicity) = true ∧
      allPairs (fun s expr => T.wideSlot s && Poly.Identical (T.meaning s) (Poly.ofExpr expr))
        ((rest.take payload.length).filterMap id) payload = true := by
  rcases lookup with ⟨m, args⟩
  rcases args with _ | ⟨tagExpr, _ | ⟨subExpr, payload⟩⟩ <;>
    rcases cells with _ | ⟨_ | mult, rest⟩ <;>
    simp only [Template.checkMessage, Bool.false_eq_true] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨tagOk, subOk⟩, wide⟩, shape⟩, multLt⟩, multOk⟩, pairs⟩ := h
  exact ⟨tagExpr, subExpr, payload, mult, rest, rfl, rfl, tagOk, subOk, wide, shape, multLt,
    multOk, pairs⟩

theorem Template.Checked.message_sound {m : F × F × F × List (Option Nat)} {lookup : Lookup F}
    (check : T.checkMessage m lookup = true) : MessageSound T.width val (T.wide val) m lookup := by
  obtain ⟨sel, tag, sub, cells⟩ := m
  obtain ⟨tagExpr, subExpr, payload, mult, rest, args, cellsEq, tagOk, subOk, wide, shape,
    multLt, multOk, pairs⟩ := T.checkMessage_true check
  set slots := (rest.take payload.length).filterMap id
  have pairs := (allPairs_iff _ slots payload).mp pairs
  refine ⟨mult, slots, shape, by have := pairs.length_eq; omega, ?_, ?_⟩
  · have := Poly.Identical.denote (T.wide val) multOk
    rw [Poly.denote_scale, checked.meaning_val holds mult multLt, Poly.denote_ofExpr] at this
    exact this.symm
  · have tagEq := Poly.Identical.denote (T.wide val) tagOk
    have subEq := Poly.Identical.denote (T.wide val) subOk
    rw [Poly.denote_ofExpr, Poly.denote_const] at tagEq subEq
    simp only [Lookup.tuple, args, List.map_cons, tagEq, subEq, List.cons.injEq, true_and]
    have key : ∀ (ss : List Nat) (es : List (ArithExpr F)),
        List.Forall₂ (fun s expr => (T.wideSlot s &&
          Poly.Identical (T.meaning s) (Poly.ofExpr expr)) = true) ss es →
        es.map (ArithExpr.denote (T.wide val)) = ss.map val := by
      intro ss es h
      induction h with
      | nil => rfl
      | @cons s e _ _ step _ ih =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at step
          have := Poly.Identical.denote (T.wide val) step.2
          rw [checked.meaning_val holds s step.1, Poly.denote_ofExpr] at this
          simp only [List.map_cons, this, ih]
    exact key slots payload pairs

theorem Template.Checked.messages_sound (unchunked : T.checkUnchunked C = true) :
    List.Forall₂ (MessageSound T.width val (T.wide val)) T.messages C.lookups :=
  (Template.Checked.unchunked T checked unchunked).imp fun {_ _} check => checked.message_sound holds check

end Template

end Aiur.Tiling
