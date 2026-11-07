/-! # Lists related pointwise

`Forall2 R as bs`: `as` and `bs` have the same length and are related by `R`
position by position, with the list facts the simulation proofs use
(lookups, append, reverse, take, drop). -/

set_option autoImplicit false

namespace IxCC.Sem

/-- Two lists related pointwise. -/
inductive Forall2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall2 R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} :
      R a b → Forall2 R as bs → Forall2 R (a :: as) (b :: bs)

namespace Forall2

variable {α β : Type} {R : α → β → Prop}

theorem length {as : List α} {bs : List β} (h : Forall2 R as bs) : as.length = bs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem get {as : List α} {bs : List β} (h : Forall2 R as bs) :
    ∀ {i : Nat} {a : α}, as[i]? = some a → ∃ b, bs[i]? = some b ∧ R a b := by
  induction h with
  | nil => intro i a ha; simp at ha
  | cons hab _ ih =>
    intro i a ha
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at ha ⊢; subst ha; exact ⟨_, rfl, hab⟩
    | succ i => simpa using ih (by simpa using ha)

theorem get' {as : List α} {bs : List β} (h : Forall2 R as bs) :
    ∀ {i : Nat} {b : β}, bs[i]? = some b → ∃ a, as[i]? = some a ∧ R a b := by
  induction h with
  | nil => intro i b hb; simp at hb
  | cons hab _ ih =>
    intro i b hb
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hb ⊢; subst hb; exact ⟨_, rfl, hab⟩
    | succ i => simpa using ih (by simpa using hb)

theorem append {as as' : List α} {bs bs' : List β} (h : Forall2 R as bs) (h' : Forall2 R as' bs') :
    Forall2 R (as ++ as') (bs ++ bs') := by
  induction h with
  | nil => exact h'
  | cons hab _ ih => exact .cons hab ih

theorem reverse {as : List α} {bs : List β} (h : Forall2 R as bs) : Forall2 R as.reverse bs.reverse := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => simpa using ih.append (.cons hab .nil)

theorem take {as : List α} {bs : List β} (h : Forall2 R as bs) :
    ∀ n, Forall2 R (as.take n) (bs.take n) := by
  induction h with
  | nil => intro n; simpa using Forall2.nil
  | cons hab _ ih =>
    intro n
    cases n with
    | zero => exact .nil
    | succ n => exact .cons hab (ih n)

theorem drop {as : List α} {bs : List β} (h : Forall2 R as bs) :
    ∀ n, Forall2 R (as.drop n) (bs.drop n) := by
  induction h with
  | nil => intro n; simpa using Forall2.nil
  | cons hab h' ih =>
    intro n
    cases n with
    | zero => exact .cons hab h'
    | succ n => exact ih n

theorem of_get {as : List α} {bs : List β} (hl : as.length = bs.length)
    (h : ∀ (i : Nat) a b, as[i]? = some a → bs[i]? = some b → R a b) : Forall2 R as bs := by
  induction as generalizing bs with
  | nil => cases bs with
    | nil => exact .nil
    | cons => simp at hl
  | cons a as ih =>
    cases bs with
    | nil => simp at hl
    | cons b bs =>
      refine .cons (h 0 a b rfl rfl) (ih (by simpa using hl) fun i a b ha hb => h (i + 1) a b ?_ ?_)
      · simpa using ha
      · simpa using hb

theorem mono {S : α → β → Prop} (hRS : ∀ a b, R a b → S a b) {as : List α} {bs : List β}
    (h : Forall2 R as bs) : Forall2 S as bs := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (hRS _ _ hab) ih

end Forall2

end IxCC.Sem
