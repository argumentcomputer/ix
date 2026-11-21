import Aiur.Generic.OpenSource
import Aiur.Generic.PreparationPatternFacts

namespace Aiur.Generic.Consts
open SourceSemantics

/-- Exactly the expression forms allowed in a closed declaration body. Global
references establish their own scope; there are no local variable reads. -/
inductive Closed : Expr F → Prop where
  | literal : Closed (.literal x)
  | global : Closed (.global name type)
  | tuple (items : ∀ e ∈ es, Closed e) : Closed (.tuple es)
  | array (items : ∀ e ∈ es, Closed e) : Closed (.array es)
  | «repeat» (item : Closed e) : Closed (.repeat e n)
  | store (item : Closed e) : Closed (.store e)
  | construct (items : ∀ e ∈ es, Closed e) : Closed (.construct name types ctor es)
  | record (items : ∀ e ∈ es, Closed e) : Closed (.record head es)
  | constructAs (items : ∀ e ∈ es, Closed e) : Closed (.constructAs params type ctor es)

theorem toExpr_closed (pat : Pattern F) {expr : Expr F}
    (interpreted : toExpr pat = .ok expr) : Closed expr := by
  have sub (p : Pattern F) (smaller : sizeOf p < sizeOf pat) {e : Expr F}
      (h : toExpr p = .ok e) : Closed e := toExpr_closed p h
  have children (ps : List (Pattern F)) (smaller : ∀ p ∈ ps, sizeOf p < sizeOf pat)
      (es : List (Expr F)) (mapped : ps.mapM toExpr = .ok es) : ∀ e ∈ es, Closed e := by
    have rel := Preparation.mapM_relation mapped
    have both : List.Forall₂ (fun p e => Closed e ∧ toExpr p = .ok e) ps es := by
      have withMem : List.Forall₂ (fun p e => p ∈ ps ∧ toExpr p = .ok e) ps es :=
        (List.forall₂_and_left _ _).mpr ⟨fun _ h => h, rel⟩
      exact withMem.imp (fun p e h => ⟨sub p (smaller p h.1) h.2, h.2⟩)
    intro e he
    clear smaller mapped rel
    induction both with
    | nil => simp at he
    | cons h _ ih =>
        rcases List.mem_cons.mp he with rfl | he
        · exact h.1
        · exact ih he
  cases pat with
  | literal | global =>
      simp only [toExpr, except_pure_ok] at interpreted
      subst expr
      constructor
  | wildcard | bind | orElse => simp [toExpr] at interpreted
  | load p | «repeat» p n =>
      simp only [toExpr, except_bind_ok, except_pure_ok] at interpreted
      obtain ⟨e, h, rfl⟩ := interpreted
      constructor
      exact sub p (by simp_wf <;> omega) h
  | record _ ps | tuple ps | array ps | constructAs params t c ps =>
      simp only [toExpr, except_bind_ok, except_pure_ok] at interpreted
      obtain ⟨es, h, rfl⟩ := interpreted
      constructor
      exact children ps (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega) es h
  | construct t c ps =>
      cases t <;> simp only [toExpr] at interpreted
      all_goals first | contradiction | skip
      simp only [except_bind_ok, except_pure_ok] at interpreted
      obtain ⟨es, h, rfl⟩ := interpreted
      constructor
      exact children ps (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega) es h
termination_by sizeOf pat
decreasing_by exact smaller

/-- A const expression has the same value and allocation history in any
surrounding local scope. In particular, inlining cannot capture caller names. -/
theorem Closed.openChangeLocals [Field F] [DecidableEq F] {world : World F} {calls : CallRelation F}
    {expr : Expr F} (closed : Closed expr)
    (evaluated : OpenSource.EvalExpr world calls types locals expr before result after)
    (other : Environment F Nat) : OpenSource.EvalExpr world calls types other expr before result after := by
  induction evaluated using OpenSource.EvalExpr.rec
    (motive_2 := fun ts ls es b vs a _ =>
      (∀ e ∈ es, Closed e) → ∀ other, OpenSource.EvalArgs world calls ts other es b vs a)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ _ => True) generalizing other with
  | literal => exact .literal
  | global lookup interpreted ev _ => exact .global lookup interpreted ev
  | tuple _ ih => cases closed with | tuple h => exact .tuple (ih h other)
  | array _ ih => cases closed with | array h => exact .array (ih h other)
  | «repeat» _ ih => cases closed with | «repeat» h => exact .repeat (ih h other)
  | construct _ ih => cases closed with | construct h => exact .construct (ih h other)
  | record _ ih => cases closed with | record h => exact .record (ih h other)
  | constructAs _ ih => cases closed with | constructAs h => exact .constructAs (ih h other)
  | store _ ih => cases closed with | store h => exact .store (ih h other)
  | nil => exact .nil
  | cons _ _ ih1 ih2 =>
      rename_i h other
      exact .cons (ih1 (h _ (by simp)) other) (ih2 (fun e he => h e (by simp [he])) other)
  | _ => first | cases closed | trivial

theorem Closed.openLocals_iff [Field F] [DecidableEq F] {world : World F} {calls : CallRelation F}
    {expr : Expr F} (closed : Closed expr) :
    OpenSource.EvalExpr world calls types left expr before result after ↔
      OpenSource.EvalExpr world calls types right expr before result after :=
  ⟨fun h => closed.openChangeLocals h right, fun h => closed.openChangeLocals h left⟩

theorem Closed.changeLocals [Field F] [DecidableEq F] {world : World F}
    {expr : Expr F} (closed : Closed expr)
    (evaluated : SourceSemantics.EvalExpr world types locals expr before result after)
    (other : Environment F Nat) : SourceSemantics.EvalExpr world types other expr before result after :=
  (closed.openChangeLocals (OpenSource.of_closed evaluated) other).close

theorem Closed.locals_iff [Field F] [DecidableEq F] {world : World F}
    {expr : Expr F} (closed : Closed expr) :
    SourceSemantics.EvalExpr world types left expr before result after ↔
      SourceSemantics.EvalExpr world types right expr before result after :=
  ⟨fun h => closed.changeLocals h right, fun h => closed.changeLocals h left⟩

end Aiur.Generic.Consts
