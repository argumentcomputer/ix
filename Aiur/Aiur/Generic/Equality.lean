import Aiur.AST

namespace Aiur.Generic

mutual
  def exprDecEq [DecidableEq α] (a b : Aiur.Expr α) : Decidable (a = b) :=
    match a, b with
    | .literal x, .literal y => by
        exact decidable_of_iff (x = y) (by simp only [Aiur.Expr.literal.injEq])
    | .var x, .var y => by
        exact decidable_of_iff (x = y) (by simp only [Aiur.Expr.var.injEq])
    | .tuple xs, .tuple ys => by
        letI := exprListDecEq xs ys
        exact decidable_of_iff (xs = ys) (by simp only [Aiur.Expr.tuple.injEq])
    | .construct n c xs, .construct m d ys => by
        letI := exprListDecEq xs ys
        exact decidable_of_iff (n = m ∧ c = d ∧ xs = ys) (by simp only [Aiur.Expr.construct.injEq])
    | .project x i, .project y j => by
        letI := exprDecEq x y
        exact decidable_of_iff (x = y ∧ i = j) (by simp only [Aiur.Expr.project.injEq])
    | .letValue p x b, .letValue q y c => by
        letI := exprDecEq x y
        letI := exprDecEq b c
        exact decidable_of_iff (p = q ∧ x = y ∧ b = c) (by simp only [Aiur.Expr.letValue.injEq])
    | .store x, .store y => by
        letI := exprDecEq x y
        exact decidable_of_iff (x = y) (by simp only [Aiur.Expr.store.injEq])
    | .load x, .load y => by
        letI := exprDecEq x y
        exact decidable_of_iff (x = y) (by simp only [Aiur.Expr.load.injEq])
    | .hint t x channel, .hint u y otherChannel => by
        letI := exprDecEq x y
        exact decidable_of_iff (t = u ∧ x = y ∧ channel = otherChannel) (by simp only [Aiur.Expr.hint.injEq])
    | .neg x, .neg y => by
        letI := exprDecEq x y
        exact decidable_of_iff (x = y) (by simp only [Aiur.Expr.neg.injEq])
    | .assertEq op x y, .assertEq oq z w => by
        letI := exprDecEq x z
        letI := exprDecEq y w
        exact decidable_of_iff (op = oq ∧ x = z ∧ y = w) (by simp only [Aiur.Expr.assertEq.injEq])    | .binary op x y, .binary oq z w => by
        letI := exprDecEq x z
        letI := exprDecEq y w
        exact decidable_of_iff (op = oq ∧ x = z ∧ y = w) (by simp only [Aiur.Expr.binary.injEq])
    | .call n xs, .call m ys => by
        letI := exprListDecEq xs ys
        exact decidable_of_iff (n = m ∧ xs = ys) (by simp only [Aiur.Expr.call.injEq])
    | .matchValue x arms, .matchValue y bs => by
        letI := exprDecEq x y
        letI := armListDecEq arms bs
        exact decidable_of_iff (x = y ∧ arms = bs) (by simp only [Aiur.Expr.matchValue.injEq])
    | .literal _, .var _ => isFalse (by intro h; cases h)
    | .literal _, .tuple _ => isFalse (by intro h; cases h)
    | .literal _, .construct _ _ _ => isFalse (by intro h; cases h)
    | .literal _, .project _ _ => isFalse (by intro h; cases h)
    | .literal _, .letValue _ _ _ => isFalse (by intro h; cases h)
    | .literal _, .store _ => isFalse (by intro h; cases h)
    | .literal _, .load _ => isFalse (by intro h; cases h)
    | .literal _, .hint _ _ _ => isFalse (by intro h; cases h)
    | .literal _, .neg _ => isFalse (by intro h; cases h)
    | .literal _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .literal _, .call _ _ => isFalse (by intro h; cases h)
    | .literal _, .matchValue _ _ => isFalse (by intro h; cases h)
    | .var _, .literal _ => isFalse (by intro h; cases h)
    | .var _, .tuple _ => isFalse (by intro h; cases h)
    | .var _, .construct _ _ _ => isFalse (by intro h; cases h)
    | .var _, .project _ _ => isFalse (by intro h; cases h)
    | .var _, .letValue _ _ _ => isFalse (by intro h; cases h)
    | .var _, .store _ => isFalse (by intro h; cases h)
    | .var _, .load _ => isFalse (by intro h; cases h)
    | .var _, .hint _ _ _ => isFalse (by intro h; cases h)
    | .var _, .neg _ => isFalse (by intro h; cases h)
    | .var _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .var _, .call _ _ => isFalse (by intro h; cases h)
    | .var _, .matchValue _ _ => isFalse (by intro h; cases h)
    | .tuple _, .literal _ => isFalse (by intro h; cases h)
    | .tuple _, .var _ => isFalse (by intro h; cases h)
    | .tuple _, .construct _ _ _ => isFalse (by intro h; cases h)
    | .tuple _, .project _ _ => isFalse (by intro h; cases h)
    | .tuple _, .letValue _ _ _ => isFalse (by intro h; cases h)
    | .tuple _, .store _ => isFalse (by intro h; cases h)
    | .tuple _, .load _ => isFalse (by intro h; cases h)
    | .tuple _, .hint _ _ _ => isFalse (by intro h; cases h)
    | .tuple _, .neg _ => isFalse (by intro h; cases h)
    | .tuple _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .tuple _, .call _ _ => isFalse (by intro h; cases h)
    | .tuple _, .matchValue _ _ => isFalse (by intro h; cases h)
    | .construct _ _ _, .literal _ => isFalse (by intro h; cases h)
    | .construct _ _ _, .var _ => isFalse (by intro h; cases h)
    | .construct _ _ _, .tuple _ => isFalse (by intro h; cases h)
    | .construct _ _ _, .project _ _ => isFalse (by intro h; cases h)
    | .construct _ _ _, .letValue _ _ _ => isFalse (by intro h; cases h)
    | .construct _ _ _, .store _ => isFalse (by intro h; cases h)
    | .construct _ _ _, .load _ => isFalse (by intro h; cases h)
    | .construct _ _ _, .hint _ _ _ => isFalse (by intro h; cases h)
    | .construct _ _ _, .neg _ => isFalse (by intro h; cases h)
    | .construct _ _ _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .construct _ _ _, .call _ _ => isFalse (by intro h; cases h)
    | .construct _ _ _, .matchValue _ _ => isFalse (by intro h; cases h)
    | .project _ _, .literal _ => isFalse (by intro h; cases h)
    | .project _ _, .var _ => isFalse (by intro h; cases h)
    | .project _ _, .tuple _ => isFalse (by intro h; cases h)
    | .project _ _, .construct _ _ _ => isFalse (by intro h; cases h)
    | .project _ _, .letValue _ _ _ => isFalse (by intro h; cases h)
    | .project _ _, .store _ => isFalse (by intro h; cases h)
    | .project _ _, .load _ => isFalse (by intro h; cases h)
    | .project _ _, .hint _ _ _ => isFalse (by intro h; cases h)
    | .project _ _, .neg _ => isFalse (by intro h; cases h)
    | .project _ _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .project _ _, .call _ _ => isFalse (by intro h; cases h)
    | .project _ _, .matchValue _ _ => isFalse (by intro h; cases h)
    | .letValue _ _ _, .literal _ => isFalse (by intro h; cases h)
    | .letValue _ _ _, .var _ => isFalse (by intro h; cases h)
    | .letValue _ _ _, .tuple _ => isFalse (by intro h; cases h)
    | .letValue _ _ _, .construct _ _ _ => isFalse (by intro h; cases h)
    | .letValue _ _ _, .project _ _ => isFalse (by intro h; cases h)
    | .letValue _ _ _, .store _ => isFalse (by intro h; cases h)
    | .letValue _ _ _, .load _ => isFalse (by intro h; cases h)
    | .letValue _ _ _, .hint _ _ _ => isFalse (by intro h; cases h)
    | .letValue _ _ _, .neg _ => isFalse (by intro h; cases h)
    | .letValue _ _ _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .letValue _ _ _, .call _ _ => isFalse (by intro h; cases h)
    | .letValue _ _ _, .matchValue _ _ => isFalse (by intro h; cases h)
    | .store _, .literal _ => isFalse (by intro h; cases h)
    | .store _, .var _ => isFalse (by intro h; cases h)
    | .store _, .tuple _ => isFalse (by intro h; cases h)
    | .store _, .construct _ _ _ => isFalse (by intro h; cases h)
    | .store _, .project _ _ => isFalse (by intro h; cases h)
    | .store _, .letValue _ _ _ => isFalse (by intro h; cases h)
    | .store _, .load _ => isFalse (by intro h; cases h)
    | .store _, .hint _ _ _ => isFalse (by intro h; cases h)
    | .store _, .neg _ => isFalse (by intro h; cases h)
    | .store _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .store _, .call _ _ => isFalse (by intro h; cases h)
    | .store _, .matchValue _ _ => isFalse (by intro h; cases h)
    | .load _, .literal _ => isFalse (by intro h; cases h)
    | .load _, .var _ => isFalse (by intro h; cases h)
    | .load _, .tuple _ => isFalse (by intro h; cases h)
    | .load _, .construct _ _ _ => isFalse (by intro h; cases h)
    | .load _, .project _ _ => isFalse (by intro h; cases h)
    | .load _, .letValue _ _ _ => isFalse (by intro h; cases h)
    | .load _, .store _ => isFalse (by intro h; cases h)
    | .load _, .hint _ _ _ => isFalse (by intro h; cases h)
    | .load _, .neg _ => isFalse (by intro h; cases h)
    | .load _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .load _, .call _ _ => isFalse (by intro h; cases h)
    | .load _, .matchValue _ _ => isFalse (by intro h; cases h)
    | .hint _ _ _, .literal _ => isFalse (by intro h; cases h)
    | .hint _ _ _, .var _ => isFalse (by intro h; cases h)
    | .hint _ _ _, .tuple _ => isFalse (by intro h; cases h)
    | .hint _ _ _, .construct _ _ _ => isFalse (by intro h; cases h)
    | .hint _ _ _, .project _ _ => isFalse (by intro h; cases h)
    | .hint _ _ _, .letValue _ _ _ => isFalse (by intro h; cases h)
    | .hint _ _ _, .store _ => isFalse (by intro h; cases h)
    | .hint _ _ _, .load _ => isFalse (by intro h; cases h)
    | .hint _ _ _, .neg _ => isFalse (by intro h; cases h)
    | .hint _ _ _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .hint _ _ _, .call _ _ => isFalse (by intro h; cases h)
    | .hint _ _ _, .matchValue _ _ => isFalse (by intro h; cases h)
    | .neg _, .literal _ => isFalse (by intro h; cases h)
    | .neg _, .var _ => isFalse (by intro h; cases h)
    | .neg _, .tuple _ => isFalse (by intro h; cases h)
    | .neg _, .construct _ _ _ => isFalse (by intro h; cases h)
    | .neg _, .project _ _ => isFalse (by intro h; cases h)
    | .neg _, .letValue _ _ _ => isFalse (by intro h; cases h)
    | .neg _, .store _ => isFalse (by intro h; cases h)
    | .neg _, .load _ => isFalse (by intro h; cases h)
    | .neg _, .hint _ _ _ => isFalse (by intro h; cases h)
    | .neg _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .neg _, .call _ _ => isFalse (by intro h; cases h)
    | .neg _, .matchValue _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .literal _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .var _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .tuple _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .construct _ _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .project _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .letValue _ _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .store _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .load _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .hint _ _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .neg _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .call _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .matchValue _ _ => isFalse (by intro h; cases h)
    | .call _ _, .literal _ => isFalse (by intro h; cases h)
    | .call _ _, .var _ => isFalse (by intro h; cases h)
    | .call _ _, .tuple _ => isFalse (by intro h; cases h)
    | .call _ _, .construct _ _ _ => isFalse (by intro h; cases h)
    | .call _ _, .project _ _ => isFalse (by intro h; cases h)
    | .call _ _, .letValue _ _ _ => isFalse (by intro h; cases h)
    | .call _ _, .store _ => isFalse (by intro h; cases h)
    | .call _ _, .load _ => isFalse (by intro h; cases h)
    | .call _ _, .hint _ _ _ => isFalse (by intro h; cases h)
    | .call _ _, .neg _ => isFalse (by intro h; cases h)
    | .call _ _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .call _ _, .matchValue _ _ => isFalse (by intro h; cases h)
    | .matchValue _ _, .literal _ => isFalse (by intro h; cases h)
    | .matchValue _ _, .var _ => isFalse (by intro h; cases h)
    | .matchValue _ _, .tuple _ => isFalse (by intro h; cases h)
    | .matchValue _ _, .construct _ _ _ => isFalse (by intro h; cases h)
    | .matchValue _ _, .project _ _ => isFalse (by intro h; cases h)
    | .matchValue _ _, .letValue _ _ _ => isFalse (by intro h; cases h)
    | .matchValue _ _, .store _ => isFalse (by intro h; cases h)
    | .matchValue _ _, .load _ => isFalse (by intro h; cases h)
    | .matchValue _ _, .hint _ _ _ => isFalse (by intro h; cases h)
    | .matchValue _ _, .neg _ => isFalse (by intro h; cases h)
    | .matchValue _ _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .matchValue _ _, .call _ _ => isFalse (by intro h; cases h)
    | .assertEq _ _ _, .literal _ => isFalse (by intro h; cases h)
    | .literal _, .assertEq _ _ _ => isFalse (by intro h; cases h)
    | .assertEq _ _ _, .var _ => isFalse (by intro h; cases h)
    | .var _, .assertEq _ _ _ => isFalse (by intro h; cases h)
    | .assertEq _ _ _, .tuple _ => isFalse (by intro h; cases h)
    | .tuple _, .assertEq _ _ _ => isFalse (by intro h; cases h)
    | .assertEq _ _ _, .construct _ _ _ => isFalse (by intro h; cases h)
    | .construct _ _ _, .assertEq _ _ _ => isFalse (by intro h; cases h)
    | .assertEq _ _ _, .project _ _ => isFalse (by intro h; cases h)
    | .project _ _, .assertEq _ _ _ => isFalse (by intro h; cases h)
    | .assertEq _ _ _, .letValue _ _ _ => isFalse (by intro h; cases h)
    | .letValue _ _ _, .assertEq _ _ _ => isFalse (by intro h; cases h)
    | .assertEq _ _ _, .store _ => isFalse (by intro h; cases h)
    | .store _, .assertEq _ _ _ => isFalse (by intro h; cases h)
    | .assertEq _ _ _, .load _ => isFalse (by intro h; cases h)
    | .load _, .assertEq _ _ _ => isFalse (by intro h; cases h)
    | .assertEq _ _ _, .hint _ _ _ => isFalse (by intro h; cases h)
    | .hint _ _ _, .assertEq _ _ _ => isFalse (by intro h; cases h)
    | .assertEq _ _ _, .neg _ => isFalse (by intro h; cases h)
    | .neg _, .assertEq _ _ _ => isFalse (by intro h; cases h)
    | .assertEq _ _ _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .assertEq _ _ _ => isFalse (by intro h; cases h)
    | .assertEq _ _ _, .call _ _ => isFalse (by intro h; cases h)
    | .call _ _, .assertEq _ _ _ => isFalse (by intro h; cases h)
    | .assertEq _ _ _, .matchValue _ _ => isFalse (by intro h; cases h)
    | .matchValue _ _, .assertEq _ _ _ => isFalse (by intro h; cases h)
  termination_by sizeOf a

  def exprListDecEq [DecidableEq α] (a b : List (Aiur.Expr α)) : Decidable (a = b) :=
    match a, b with
    | [], [] => isTrue rfl
    | x :: xs, y :: ys => by
        letI := exprDecEq x y
        letI := exprListDecEq xs ys
        exact decidable_of_iff (x = y ∧ xs = ys) (by simp only [List.cons.injEq])
    | [], _ :: _ | _ :: _, [] => isFalse (by intro h; cases h)
  termination_by sizeOf a

  def armListDecEq [DecidableEq α] (a b : List (Aiur.Pattern α × Aiur.Expr α)) : Decidable (a = b) :=
    match a, b with
    | [], [] => isTrue rfl
    | (p, x) :: xs, (q, y) :: ys => by
        letI := exprDecEq x y
        letI := armListDecEq xs ys
        exact decidable_of_iff (p = q ∧ x = y ∧ xs = ys) (by simp [and_assoc])
    | [], _ :: _ | _ :: _, [] => isFalse (by intro h; cases h)
  termination_by sizeOf a
end

instance [DecidableEq α] : DecidableEq (Aiur.Expr α) := exprDecEq

deriving instance DecidableEq for Aiur.Function

end Aiur.Generic
