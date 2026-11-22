import IxCC.Src.Relevance.Proof.P1.Defs

/-! # P1, relevance preservation: the induction's measure

The core of P1 is one well-founded induction over `Step` (`IxCC.Src.Relevance.Proof.P1.Cases`).
Its measure is SrcEval's own termination measure (`Src/Semantics.lean`'s `termination_by`), and
every step decreases it (`step_lt`), so every call a call's evaluation makes, its children and
their descendants, lies below it (`transGen_lt`) and is reached from the same top call
(`reach_transGen`). -/

set_option autoImplicit false

namespace IxCC.Src.Relevance.Proof.P1

open IxCC.Src

variable {p : Program}

/-- SrcEval's termination measure of a call (`Src/Semantics.lean`'s `termination_by`). -/
noncomputable def Call.measure : Call → Nat × Nat × Nat
  | .eval k _ _ t => (k, sizeOf t + 3, 0)
  | .evalConst k _ _ => (k, 2, 0)
  | .headValue k _ _ => (k, 1, 1)
  | .apply k _ _ => (k, 2, 0)
  | .applyAll k _ ss => (k, 2, ss.length + 1)
  | .fire k _ _ _ => (k, 1, 0)
  | .force k _ => (k, 0, 0)
  | .forceAll k ss => (k, 0, ss.length + 1)

/-- `c'` is below `c` in the measure's lexicographic order. -/
def CallLt (c' c : Call) : Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) c'.measure c.measure

theorem callLt_wf : WellFounded CallLt :=
  InvImage.wf Call.measure (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel Nat.lt_wfRel)).wf

/-- A lexicographic order of transitive orders is transitive. -/
theorem lex_trans {α β : Type} {ra : α → α → Prop} {rb : β → β → Prop}
    (ta : ∀ x y z, ra x y → ra y z → ra x z) (tb : ∀ x y z, rb x y → rb y z → rb x z)
    {x y z : α × β} (h1 : Prod.Lex ra rb x y) (h2 : Prod.Lex ra rb y z) : Prod.Lex ra rb x z := by
  cases h1 with
  | left _ _ h =>
    cases h2 with
    | left _ _ h' => exact .left _ _ (ta _ _ _ h h')
    | right _ _ => exact .left _ _ h
  | right _ h =>
    cases h2 with
    | left _ _ h' => exact .left _ _ h'
    | right _ h' => exact .right _ (tb _ _ _ h h')

theorem callLt_trans {a b c : Call} (h1 : CallLt a b) (h2 : CallLt b c) : CallLt a c := by
  unfold CallLt at *
  exact @lex_trans Nat (Nat × Nat) (· < ·) (Prod.Lex (· < ·) (· < ·)) (fun _ _ _ => Nat.lt_trans)
    (fun _ _ _ h h' => @lex_trans Nat Nat (· < ·) (· < ·) (fun _ _ _ => Nat.lt_trans)
      (fun _ _ _ => Nat.lt_trans) _ _ _ h h') _ _ _ h1 h2

/-- Each step decreases the measure. -/
theorem step_lt {c c' : Call} (h : Step p c c') : CallLt c' c := by
  cases h <;> simp only [CallLt, Call.measure, List.length_cons] <;>
    first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; apply Prod.Lex.left; first | omega | (simp <;> omega))
    | (apply Prod.Lex.right; apply Prod.Lex.right; omega)

/-- Every call a call's evaluation makes lies below it. -/
theorem transGen_lt {c c' : Call} (h : Relation.TransGen (Step p) c c') : CallLt c' c := by
  induction h with
  | single h => exact step_lt h
  | tail _ h ih => exact callLt_trans (step_lt h) ih

/-- A call a reached call's evaluation makes is reached. -/
theorem reach_transGen {top c c' : Call} (hr : Reach p top c)
    (h : Relation.TransGen (Step p) c c') : Reach p top c' := by
  induction h with
  | single h => exact .step hr h
  | tail _ h ih => exact .step ih h

end IxCC.Src.Relevance.Proof.P1
