import Aiur.Generic.AST

/-! # `==` on generic patterns and expressions is equality

`Generic.Pattern` and `Generic.Expr` compare with the hand-written
`Pattern.beq` and `Expr.beq` (`Aiur.Generic.AST`), and the annotations inside
them (`RecordHead`, `FieldRef`, `UpdateStep`, `OrBindings`, `Control`,
`Builtin`, and core Aiur's `BinOp` and `Assertion`) with derived `BEq`
instances. None of them came with a proof that `a == b` gives `a = b`, so a
Boolean check that compares two function bodies with `==` proved nothing
about the bodies.

This file supplies the proofs: the deriving handler's instances for the
annotation types, and `LawfulBEq (Pattern α)` and `LawfulBEq (Expr α)` over
any lawful `α`. `Generic.Ty` needs nothing: its `BEq` is the one its
`DecidableEq` induces. -/

namespace Aiur.Generic

deriving instance ReflBEq, LawfulBEq for Aiur.BinOp
deriving instance ReflBEq, LawfulBEq for Aiur.Assertion
deriving instance ReflBEq, LawfulBEq for RecordHead
deriving instance ReflBEq, LawfulBEq for FieldRef
deriving instance ReflBEq, LawfulBEq for UpdateStep
deriving instance ReflBEq, LawfulBEq for OrBindings
deriving instance ReflBEq, LawfulBEq for Control
deriving instance ReflBEq, LawfulBEq for Builtin

variable {α : Type}

/-! ## Patterns -/

mutual
  theorem Pattern.eq_of_beq [BEq α] [LawfulBEq α] :
      ∀ (a b : Pattern α), Pattern.beq a b = true → a = b
    | .literal x, b, h => by
      cases b with
      | literal y => simp only [Pattern.beq, beq_iff_eq] at h; rw [h]
      | _ => simp [Pattern.beq] at h
    | .wildcard, b, h => by
      cases b with
      | wildcard => rfl
      | _ => simp [Pattern.beq] at h
    | .bind x, b, h => by
      cases b with
      | bind y => simp only [Pattern.beq, beq_iff_eq] at h; rw [h]
      | _ => simp [Pattern.beq] at h
    | .global n t, b, h => by
      cases b with
      | global n' t' =>
        simp only [Pattern.beq, Bool.and_eq_true, beq_iff_eq] at h
        rw [h.1, h.2]
      | _ => simp [Pattern.beq] at h
    | .load p, b, h => by
      cases b with
      | load p' => simp only [Pattern.beq] at h; rw [Pattern.eq_of_beq p p' h]
      | _ => simp [Pattern.beq] at h
    | .orElse l r bs, b, h => by
      cases b with
      | orElse l' r' bs' =>
        simp only [Pattern.beq, Bool.and_eq_true, beq_iff_eq] at h
        rw [Pattern.eq_of_beq l l' h.1.1, Pattern.eq_of_beq r r' h.1.2, h.2]
      | _ => simp [Pattern.beq] at h
    | .tuple xs, b, h => by
      cases b with
      | tuple ys => simp only [Pattern.beq] at h; rw [Pattern.list_eq_of_beq xs ys h]
      | _ => simp [Pattern.beq] at h
    | .array xs, b, h => by
      cases b with
      | array ys => simp only [Pattern.beq] at h; rw [Pattern.list_eq_of_beq xs ys h]
      | _ => simp [Pattern.beq] at h
    | .repeat p n, b, h => by
      cases b with
      | «repeat» p' n' =>
        simp only [Pattern.beq, Bool.and_eq_true, beq_iff_eq] at h
        rw [Pattern.eq_of_beq p p' h.1, h.2]
      | _ => simp [Pattern.beq] at h
    | .record hd xs, b, h => by
      cases b with
      | record hd' ys =>
        simp only [Pattern.beq, Bool.and_eq_true, beq_iff_eq] at h
        rw [h.1, Pattern.list_eq_of_beq xs ys h.2]
      | _ => simp [Pattern.beq] at h
    | .construct t c xs, b, h => by
      cases b with
      | construct t' c' ys =>
        simp only [Pattern.beq, Bool.and_eq_true, beq_iff_eq] at h
        rw [h.1.1, h.1.2, Pattern.list_eq_of_beq xs ys h.2]
      | _ => simp [Pattern.beq] at h
    | .constructAs ps t c xs, b, h => by
      cases b with
      | constructAs ps' t' c' ys =>
        simp only [Pattern.beq, Bool.and_eq_true, beq_iff_eq] at h
        rw [h.1.1.1, h.1.1.2, h.1.2, Pattern.list_eq_of_beq xs ys h.2]
      | _ => simp [Pattern.beq] at h

  theorem Pattern.list_eq_of_beq [BEq α] [LawfulBEq α] :
      ∀ (xs ys : List (Pattern α)), Pattern.listBeq xs ys = true → xs = ys
    | [], ys, h => by
      cases ys with
      | nil => rfl
      | cons y ys => simp [Pattern.listBeq] at h
    | x :: xs, ys, h => by
      cases ys with
      | nil => simp [Pattern.listBeq] at h
      | cons y ys =>
        simp only [Pattern.listBeq, Bool.and_eq_true] at h
        rw [Pattern.eq_of_beq x y h.1, Pattern.list_eq_of_beq xs ys h.2]
end

mutual
  theorem Pattern.beq_refl [BEq α] [LawfulBEq α] : ∀ (a : Pattern α), Pattern.beq a a = true
    | .literal _ => by simp [Pattern.beq]
    | .wildcard => by simp [Pattern.beq]
    | .bind _ => by simp [Pattern.beq]
    | .global _ _ => by simp [Pattern.beq]
    | .load p => by simp [Pattern.beq, Pattern.beq_refl p]
    | .orElse l r _ => by simp [Pattern.beq, Pattern.beq_refl l, Pattern.beq_refl r]
    | .tuple xs => by simp [Pattern.beq, Pattern.listBeq_refl xs]
    | .array xs => by simp [Pattern.beq, Pattern.listBeq_refl xs]
    | .repeat p _ => by simp [Pattern.beq, Pattern.beq_refl p]
    | .record _ xs => by simp [Pattern.beq, Pattern.listBeq_refl xs]
    | .construct _ _ xs => by simp [Pattern.beq, Pattern.listBeq_refl xs]
    | .constructAs _ _ _ xs => by simp [Pattern.beq, Pattern.listBeq_refl xs]

  theorem Pattern.listBeq_refl [BEq α] [LawfulBEq α] :
      ∀ (xs : List (Pattern α)), Pattern.listBeq xs xs = true
    | [] => by simp [Pattern.listBeq]
    | x :: xs => by simp [Pattern.listBeq, Pattern.beq_refl x, Pattern.listBeq_refl xs]
end

/-- `==` on patterns is equality. -/
instance [BEq α] [LawfulBEq α] : LawfulBEq (Pattern α) where
  rfl := Pattern.beq_refl _
  eq_of_beq := Pattern.eq_of_beq _ _

/-! ## Expressions -/

mutual
  theorem Expr.eq_of_beq [BEq α] [LawfulBEq α] :
      ∀ (a b : Expr α), Expr.beq a b = true → a = b
    | .literal x, b, h => by
      cases b with
      | literal y => simp only [Expr.beq, beq_iff_eq] at h; rw [h]
      | _ => simp [Expr.beq] at h
    | .var x, b, h => by
      cases b with
      | var y => simp only [Expr.beq, beq_iff_eq] at h; rw [h]
      | _ => simp [Expr.beq] at h
    | .global n t, b, h => by
      cases b with
      | global n' t' =>
        simp only [Expr.beq, Bool.and_eq_true, beq_iff_eq] at h
        rw [h.1, h.2]
      | _ => simp [Expr.beq] at h
    | .tuple xs, b, h => by
      cases b with
      | tuple ys => simp only [Expr.beq] at h; rw [Expr.list_eq_of_beq xs ys h]
      | _ => simp [Expr.beq] at h
    | .array xs, b, h => by
      cases b with
      | array ys => simp only [Expr.beq] at h; rw [Expr.list_eq_of_beq xs ys h]
      | _ => simp [Expr.beq] at h
    | .repeat v n, b, h => by
      cases b with
      | «repeat» v' n' =>
        simp only [Expr.beq, Bool.and_eq_true, beq_iff_eq] at h
        rw [Expr.eq_of_beq v v' h.1, h.2]
      | _ => simp [Expr.beq] at h
    | .index v i, b, h => by
      cases b with
      | index v' i' =>
        simp only [Expr.beq, Bool.and_eq_true, beq_iff_eq] at h
        rw [Expr.eq_of_beq v v' h.1, h.2]
      | _ => simp [Expr.beq] at h
    | .slice v s e, b, h => by
      cases b with
      | slice v' s' e' =>
        simp only [Expr.beq, Bool.and_eq_true, beq_iff_eq] at h
        rw [Expr.eq_of_beq v v' h.1.1, h.1.2, h.2]
      | _ => simp [Expr.beq] at h
    | .construct n ts c xs, b, h => by
      cases b with
      | construct n' ts' c' ys =>
        simp only [Expr.beq, Bool.and_eq_true, beq_iff_eq] at h
        rw [h.1.1.1, h.1.1.2, h.1.2, Expr.list_eq_of_beq xs ys h.2]
      | _ => simp [Expr.beq] at h
    | .constructAs ps t c xs, b, h => by
      cases b with
      | constructAs ps' t' c' ys =>
        simp only [Expr.beq, Bool.and_eq_true, beq_iff_eq] at h
        rw [h.1.1.1, h.1.1.2, h.1.2, Expr.list_eq_of_beq xs ys h.2]
      | _ => simp [Expr.beq] at h
    | .record hd xs, b, h => by
      cases b with
      | record hd' ys =>
        simp only [Expr.beq, Bool.and_eq_true, beq_iff_eq] at h
        rw [h.1, Expr.list_eq_of_beq xs ys h.2]
      | _ => simp [Expr.beq] at h
    | .member v f, b, h => by
      cases b with
      | member v' f' =>
        simp only [Expr.beq, Bool.and_eq_true, beq_iff_eq] at h
        rw [Expr.eq_of_beq v v' h.1, h.2]
      | _ => simp [Expr.beq] at h
    | .update ps os, b, h => by
      cases b with
      | update ps' os' =>
        simp only [Expr.beq, Bool.and_eq_true, beq_iff_eq] at h
        rw [h.1, Expr.list_eq_of_beq os os' h.2]
      | _ => simp [Expr.beq] at h
    | .builtin op os, b, h => by
      cases b with
      | builtin op' os' =>
        simp only [Expr.beq, Bool.and_eq_true, beq_iff_eq] at h
        rw [h.1, Expr.list_eq_of_beq os os' h.2]
      | _ => simp [Expr.beq] at h
    | .project v i, b, h => by
      cases b with
      | project v' i' =>
        simp only [Expr.beq, Bool.and_eq_true, beq_iff_eq] at h
        rw [Expr.eq_of_beq v v' h.1, h.2]
      | _ => simp [Expr.beq] at h
    | .letValue p v body, b, h => by
      cases b with
      | letValue p' v' body' =>
        simp only [Expr.beq, Bool.and_eq_true, beq_iff_eq] at h
        rw [h.1.1, Expr.eq_of_beq v v' h.1.2, Expr.eq_of_beq body body' h.2]
      | _ => simp [Expr.beq] at h
    | .store v, b, h => by
      cases b with
      | store v' => simp only [Expr.beq] at h; rw [Expr.eq_of_beq v v' h]
      | _ => simp [Expr.beq] at h
    | .load p, b, h => by
      cases b with
      | load p' => simp only [Expr.beq] at h; rw [Expr.eq_of_beq p p' h]
      | _ => simp [Expr.beq] at h
    | .hint t k c, b, h => by
      cases b with
      | hint t' k' c' =>
        simp only [Expr.beq, Bool.and_eq_true, beq_iff_eq] at h
        rw [h.1.1, Expr.eq_of_beq k k' h.1.2, h.2]
      | _ => simp [Expr.beq] at h
    | .neg v, b, h => by
      cases b with
      | neg v' => simp only [Expr.beq] at h; rw [Expr.eq_of_beq v v' h]
      | _ => simp [Expr.beq] at h
    | .binary op l r, b, h => by
      cases b with
      | binary op' l' r' =>
        simp only [Expr.beq, Bool.and_eq_true, beq_iff_eq] at h
        rw [h.1.1, Expr.eq_of_beq l l' h.1.2, Expr.eq_of_beq r r' h.2]
      | _ => simp [Expr.beq] at h
    | .call n ts xs, b, h => by
      cases b with
      | call n' ts' ys =>
        simp only [Expr.beq, Bool.and_eq_true, beq_iff_eq] at h
        rw [h.1.1, h.1.2, Expr.list_eq_of_beq xs ys h.2]
      | _ => simp [Expr.beq] at h
    | .matchValue s arms, b, h => by
      cases b with
      | matchValue s' arms' =>
        simp only [Expr.beq, Bool.and_eq_true] at h
        rw [Expr.eq_of_beq s s' h.1, Expr.arms_eq_of_beq arms arms' h.2]
      | _ => simp [Expr.beq] at h
    | .control k body, b, h => by
      cases b with
      | control k' body' =>
        simp only [Expr.beq, Bool.and_eq_true, beq_iff_eq] at h
        rw [h.1, Expr.eq_of_beq body body' h.2]
      | _ => simp [Expr.beq] at h

  theorem Expr.list_eq_of_beq [BEq α] [LawfulBEq α] :
      ∀ (xs ys : List (Expr α)), Expr.listBeq xs ys = true → xs = ys
    | [], ys, h => by
      cases ys with
      | nil => rfl
      | cons y ys => simp [Expr.listBeq] at h
    | x :: xs, ys, h => by
      cases ys with
      | nil => simp [Expr.listBeq] at h
      | cons y ys =>
        simp only [Expr.listBeq, Bool.and_eq_true] at h
        rw [Expr.eq_of_beq x y h.1, Expr.list_eq_of_beq xs ys h.2]

  theorem Expr.arms_eq_of_beq [BEq α] [LawfulBEq α] :
      ∀ (xs ys : List (Pattern α × Expr α)), Expr.armsBeq xs ys = true → xs = ys
    | [], ys, h => by
      cases ys with
      | nil => rfl
      | cons y ys => simp [Expr.armsBeq] at h
    | (p, e) :: xs, ys, h => by
      cases ys with
      | nil => simp [Expr.armsBeq] at h
      | cons y ys =>
        obtain ⟨p', e'⟩ := y
        simp only [Expr.armsBeq, Bool.and_eq_true, beq_iff_eq] at h
        rw [h.1.1, Expr.eq_of_beq e e' h.1.2, Expr.arms_eq_of_beq xs ys h.2]
end

mutual
  theorem Expr.beq_refl [BEq α] [LawfulBEq α] : ∀ (a : Expr α), Expr.beq a a = true
    | .literal _ => by simp [Expr.beq]
    | .var _ => by simp [Expr.beq]
    | .global _ _ => by simp [Expr.beq]
    | .tuple xs => by simp [Expr.beq, Expr.listBeq_refl xs]
    | .array xs => by simp [Expr.beq, Expr.listBeq_refl xs]
    | .repeat v _ => by simp [Expr.beq, Expr.beq_refl v]
    | .index v _ => by simp [Expr.beq, Expr.beq_refl v]
    | .slice v _ _ => by simp [Expr.beq, Expr.beq_refl v]
    | .construct _ _ _ xs => by simp [Expr.beq, Expr.listBeq_refl xs]
    | .constructAs _ _ _ xs => by simp [Expr.beq, Expr.listBeq_refl xs]
    | .record _ xs => by simp [Expr.beq, Expr.listBeq_refl xs]
    | .member v _ => by simp [Expr.beq, Expr.beq_refl v]
    | .update _ os => by simp [Expr.beq, Expr.listBeq_refl os]
    | .builtin _ os => by simp [Expr.beq, Expr.listBeq_refl os]
    | .project v _ => by simp [Expr.beq, Expr.beq_refl v]
    | .letValue _ v body => by simp [Expr.beq, Expr.beq_refl v, Expr.beq_refl body]
    | .store v => by simp [Expr.beq, Expr.beq_refl v]
    | .load p => by simp [Expr.beq, Expr.beq_refl p]
    | .hint _ k _ => by simp [Expr.beq, Expr.beq_refl k]
    | .neg v => by simp [Expr.beq, Expr.beq_refl v]
    | .binary _ l r => by simp [Expr.beq, Expr.beq_refl l, Expr.beq_refl r]
    | .call _ _ xs => by simp [Expr.beq, Expr.listBeq_refl xs]
    | .matchValue s arms => by simp [Expr.beq, Expr.beq_refl s, Expr.armsBeq_refl arms]
    | .control _ body => by simp [Expr.beq, Expr.beq_refl body]

  theorem Expr.listBeq_refl [BEq α] [LawfulBEq α] :
      ∀ (xs : List (Expr α)), Expr.listBeq xs xs = true
    | [] => by simp [Expr.listBeq]
    | x :: xs => by simp [Expr.listBeq, Expr.beq_refl x, Expr.listBeq_refl xs]

  theorem Expr.armsBeq_refl [BEq α] [LawfulBEq α] :
      ∀ (xs : List (Pattern α × Expr α)), Expr.armsBeq xs xs = true
    | [] => by simp [Expr.armsBeq]
    | (_, e) :: xs => by simp [Expr.armsBeq, Expr.beq_refl e, Expr.armsBeq_refl xs]
end

/-- `==` on expressions is equality. -/
instance [BEq α] [LawfulBEq α] : LawfulBEq (Expr α) where
  rfl := Expr.beq_refl _
  eq_of_beq := Expr.eq_of_beq _ _

end Aiur.Generic
