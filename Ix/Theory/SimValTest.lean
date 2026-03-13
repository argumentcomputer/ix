import Ix.Theory.EvalSubst

namespace Ix.Theory.SimValTest
open SExpr

variable {L : Type}

mutual
def SimVal (n : Nat) (v1 v2 : SVal L) (d : Nat) : Prop :=
  match v1, v2 with
  | .sort u1, .sort u2 => u1 = u2
  | .lit n1, .lit n2 => n1 = n2
  | .neutral h1 sp1, .neutral h2 sp2 =>
      h1 = h2 ∧ SimSpine n sp1 sp2 d
  | .lam d1 b1 e1, .lam d2 b2 e2 =>
      match n with
      | 0 => True
      | n' + 1 => SimVal n' d1 d2 d
  | _, _ => False
def SimSpine (n : Nat) (sp1 sp2 : List (SVal L)) (d : Nat) : Prop :=
  match sp1, sp2 with
  | [], [] => True
  | v1 :: r1, v2 :: r2 => SimVal n v1 v2 d ∧ SimSpine n r1 r2 d
  | _, _ => False
end

-- Test: equation with unfold (concrete constructors)
example : SimVal (L := L) n (.sort u1) (.sort u2) d = (u1 = u2) := by
  unfold SimVal; rfl

-- Test: cross-constructor
example : SimVal (L := L) n (.sort u) (.lit l) d = False := by
  unfold SimVal; rfl

-- Test: lam at 0
example : SimVal (L := L) 0 (.lam d1 b1 e1) (.lam d2 b2 e2) d = True := by
  unfold SimVal; rfl

-- Test: mono using cases then unfold
theorem mono (h : n' ≤ n) (hs : SimVal n v1 v2 d) : SimVal (L := L) n' v1 v2 d := by
  cases v1 <;> cases v2
  -- After cases, v1/v2 are concrete. unfold SimVal should reduce.
  all_goals unfold SimVal at hs ⊢
  -- Now each goal should have the reduced form
  all_goals sorry

end Ix.Theory.SimValTest
