import Ix.Compile.SourceContract.Elab

/-!
# Annotated recursive definitions for the unfolding-equation export

Structural and well-founded recursion with header contracts, and a contract
written inside the body. `EquationCheck` realizes their unfolding equations
and checks the contracts they carry (R1 amendment).
-/

namespace Tests.Ix.SourceContract.EquationFixture

/-- Structural recursion with a unique accumulator. -/
def revAccU (xs : List Nat) (! acc : List Nat) : ! List Nat :=
  match xs with
  | [] => acc
  | x :: rest => revAccU rest (x :: acc)

/-- Well-founded recursion with an erased proof argument. -/
def countdownWF (n : Nat) (0 h : 0 ≤ n) : Nat :=
  if hn : n = 0 then 0 else countdownWF (n - 1) (Nat.zero_le _) + 1
termination_by n
decreasing_by omega

/-- A linear let inside the body. -/
def withLet (n : Nat) (! acc : List Nat) : ! List Nat :=
  match n with
  | 0 => acc
  | k + 1 =>
    let (1 y : Nat) := k
    withLet y (y :: acc)

end Tests.Ix.SourceContract.EquationFixture
