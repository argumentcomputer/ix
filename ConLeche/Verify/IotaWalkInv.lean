module

public import ConLeche.Kernel.Checker

public section

/-!
# Inverting the iota-install list checks

`checkDefEqList`, `checkTypedList` and `checkAnnotList` are the three
list-shaped checks the modeled-inductive install runs over an iota
rule's spines.  Their specifications (`DefEqListOk`, `TypedListOk`,
`AnnotListOk`) and inversion lemmas are statements about the kernel's
fueled operations on an `Env` and a list of `Expr`s — no valuation, no
`SetTheory` — which is what lets the frame-crossing walk of the model
tier consume them as they stand.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche

variable {mode : CheckMode}

open Expr

/-! ## Fueled spine equalities -/

theorem fueledOpsW_isDefEq (F : Nat) (env : Env) (d : Nat) (a b : Expr) :
    (fueledOps mode F).isDefEq env d a b = isDefEqCore mode env F d a b := rfl

/-- Pairwise fueled definitional equality of two spines (the semantic
content of a successful `checkDefEqList`). -/
@[expose] def DefEqListOk (mode : CheckMode) (F : Nat) (env : Env) (d : Nat) :
    List Expr → List Expr → Prop
  | [], [] => True
  | a :: as, b :: bs =>
    isDefEqCore mode env F d a b = .ok true ∧ DefEqListOk mode F env d as bs
  | _, _ => False

/-- Pairwise fueled inferred-type check of a spine against expected
types (the semantic content of a successful `checkTypedList`). -/
@[expose] def TypedListOk (mode : CheckMode) (F : Nat) (env : Env) (d : Nat) :
    List Expr → List Expr → Prop
  | [], [] => True
  | a :: as, b :: bs =>
    (∃ ty, inferTypeCore mode env F d a = .ok ty ∧
      isDefEqCore mode env F d ty b = .ok true) ∧
    TypedListOk mode F env d as bs
  | _, _ => False

/-- Each expression is a fixed point of the annotation pass (the
semantic content of a successful `checkAnnotList`). -/
@[expose] def AnnotListOk (mode : CheckMode) (F : Nat) (env : Env) (d : Nat) (l : List Expr) : Prop :=
  ∀ a ∈ l, annotateCore mode env F d a = .ok a

/-- Extract a member's inference run from a `TypedListOk` package
(task #100 stage 6: this is the `AnnotOk` source for the nested pins —
the typed check's inference run establishes truthfulness via the
restructured claims; the annotate-fixed-point check no longer
carries semantic content). -/
theorem TypedListOk.infer_of_mem {F : Nat} {env : Env} {d : Nat} :
    ∀ {as bs : List Expr}, TypedListOk mode F env d as bs →
      ∀ a ∈ as, ∃ ty, inferTypeCore mode env F d a = .ok ty := by
  intro as
  induction as with
  | nil => intro bs h a ha; cases ha
  | cons x xs ih =>
    intro bs h a ha
    match bs, h with
    | b :: bs, ⟨⟨ty, hty, _⟩, hrest⟩ =>
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨ty, hty⟩
      · exact ih hrest a ha

theorem DefEqListOk.length {F : Nat} {env : Env} {d : Nat} :
    ∀ {as bs : List Expr}, DefEqListOk mode F env d as bs →
      as.length = bs.length := by
  intro as
  induction as with
  | nil =>
    intro bs h
    match bs, h with
    | [], _ => rfl
  | cons a as ih =>
    intro bs h
    match bs, h with
    | b :: bs, ⟨_, h⟩ => simpa using ih h

theorem DefEqListOk.pointwise {F : Nat} {env : Env} {d : Nat} :
    ∀ {as bs : List Expr}, DefEqListOk mode F env d as bs →
      ∀ (i : Nat) {a b : Expr}, as[i]? = some a → bs[i]? = some b →
        isDefEqCore mode env F d a b = .ok true := by
  intro as
  induction as with
  | nil =>
    intro bs h i a b ha hb
    exact nomatch ha
  | cons a₀ as ih =>
    intro bs h i a b ha hb
    match bs, h with
    | b₀ :: bs, ⟨h₀, h⟩ =>
      match i, ha, hb with
      | 0, ha, hb =>
        obtain rfl := Option.some.inj ha
        obtain rfl := Option.some.inj hb
        exact h₀
      | i + 1, ha, hb => exact ih h i (by simpa using ha) (by simpa using hb)

theorem DefEqListOk.take {F : Nat} {env : Env} {d : Nat} :
    ∀ {as bs : List Expr} (n : Nat), DefEqListOk mode F env d as bs →
      DefEqListOk mode F env d (as.take n) (bs.take n) := by
  intro as
  induction as with
  | nil =>
    intro bs n h
    match bs, h with
    | [], _ =>
      simp only [List.take_nil]
      trivial
  | cons a as ih =>
    intro bs n h
    match bs, h with
    | b :: bs, ⟨h₀, h⟩ =>
      cases n with
      | zero => trivial
      | succ n =>
        simp only [List.take_succ_cons]
        exact ⟨h₀, ih n h⟩

/-- Invert a successful `checkDefEqList` run. -/
theorem checkDefEqList_inv {F : Nat} {env : Env} {d : Nat} :
    ∀ {as bs : List Expr} {u : Unit},
    checkDefEqList (fueledOps mode F) env d as bs = .ok u →
    DefEqListOk mode F env d as bs := by
  intro as
  induction as with
  | nil =>
    intro bs u h
    match bs with
    | [] => trivial
    | _ :: _ =>
      simp only [checkDefEqList] at h
      exact nomatch h
  | cons a as ih =>
    intro bs u h
    match bs with
    | [] =>
      simp only [checkDefEqList] at h
      exact nomatch h
    | b :: bs =>
      simp only [checkDefEqList, fueledOpsW_isDefEq, Bind.bind,
        Except.bind] at h
      revert h
      cases hde : isDefEqCore mode env F d a b with
      | error e => intro h; exact nomatch h
      | ok v =>
        cases v with
        | false =>
          intro h
          simp [throw, throwThe, MonadExceptOf.throw] at h
        | true =>
          intro h
          simp only [↓reduceIte, pure, Except.pure] at h
          exact ⟨hde, ih h⟩

/-- Invert the boolean equality-head test. -/
theorem isEqHead_inv {e : Expr} (h : isEqHead e = true) :
    ∃ ℓA, e = .const eqName [ℓA] := by
  match e, h with
  | .const c [ℓ], h =>
    refine ⟨ℓ, ?_⟩
    have hc : (c == eqName) = true := by simpa [isEqHead] using h
    rw [eq_of_beq hc]
  | .const _ [], h => simp [isEqHead] at h
  | .const _ (_ :: _ :: _), h => simp [isEqHead] at h
  | .bvar _, h => simp [isEqHead] at h
  | .fvar _ _, h => simp [isEqHead] at h
  | .sort _, h => simp [isEqHead] at h
  | .app _ _, h => simp [isEqHead] at h
  | .lam _ _ _, h => simp [isEqHead] at h
  | .forallE _ _ _, h => simp [isEqHead] at h
  | .letE _ _ _, h => simp [isEqHead] at h
  | .lit _, h => simp [isEqHead] at h
  | .proj _ _ _, h => simp [isEqHead] at h

theorem fueledOpsW_inferType (F : Nat) (env : Env) (d : Nat) (e : Expr) :
    (fueledOps mode F).inferType env d e = inferTypeCore mode env F d e := rfl

theorem checkTypedList_inv {F : Nat} {env : Env} {d : Nat} :
    ∀ {as bs : List Expr} {u : Unit},
      checkTypedList (fueledOps mode F) env d as bs = .ok u →
      TypedListOk mode F env d as bs := by
  intro as
  induction as with
  | nil =>
    intro bs u h
    match bs with
    | [] => trivial
    | _ :: _ =>
      simp only [checkTypedList] at h
      exact nomatch h
  | cons a as ih =>
    intro bs u h
    match bs with
    | [] =>
      simp only [checkTypedList] at h
      exact nomatch h
    | b :: bs =>
      simp only [checkTypedList, fueledOpsW_inferType, fueledOpsW_isDefEq,
        Bind.bind, Except.bind] at h
      revert h
      cases hty : inferTypeCore mode env F d a with
      | error e => intro h; exact nomatch h
      | ok ty =>
        intro h
        dsimp only at h
        cases hde : isDefEqCore mode env F d ty b with
        | error e =>
          rw [hde] at h
          exact nomatch h
        | ok v =>
          rw [hde] at h
          dsimp only at h
          cases v with
          | false =>
            simp [throw, throwThe, MonadExceptOf.throw] at h
          | true =>
            rw [if_pos rfl] at h
            exact ⟨⟨ty, hty, hde⟩, ih h⟩

theorem fueledOpsW_annotate (F : Nat) (env : Env) (d : Nat) (e : Expr) :
    (fueledOps mode F).annotate env d e = annotateCore mode env F d e := rfl

/-- Invert a successful `checkAnnotList` run. -/
theorem checkAnnotList_inv {F : Nat} {env : Env} {d : Nat} :
    ∀ {as : List Expr} {u : Unit},
      checkAnnotList (fueledOps mode F) env d as = .ok u →
      AnnotListOk mode F env d as := by
  intro as
  induction as with
  | nil =>
    intro u _ a ha
    exact nomatch ha
  | cons a as ih =>
    intro u h
    simp only [checkAnnotList, fueledOpsW_annotate, Bind.bind,
      Except.bind] at h
    revert h
    cases hann : annotateCore mode env F d a with
    | error e => intro h; exact nomatch h
    | ok aA =>
      intro h
      dsimp only at h
      by_cases heq : (aA == a) = true
      case neg =>
        rw [if_neg heq] at h
        exact nomatch h
      case pos =>
        rw [if_pos heq] at h
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · rw [hann, eq_of_beq heq]
        · exact ih h x hx

end ConLeche
