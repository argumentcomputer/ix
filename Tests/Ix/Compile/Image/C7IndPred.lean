/- image-gen fixture (`Tests/Ix/Compile/Image.lean`), elaborated at run time and in no Lake library:
   the prototype's `exp-prototype/CertProto/Cases/C7IndPred.lean` without its commands. -/
/-! Case 7: Prop inductive predicate families with structural recursion over proofs, so that
Lean's `IndPredBelow` `.below` inductives are part of the Lean view.
7a: collapse (PropCollapse with a base case); 7b: split of an independent Prop member R that is
also a cross field (R gains large elimination when alone). -/
set_option Elab.async false

namespace C7
namespace Src
mutual
inductive P : Nat → Prop
  | base : P 0
  | step : ∀ n, Q n → P n
inductive Q : Nat → Prop
  | base : Q 0
  | step : ∀ n, P n → Q n
end

theorem p_cases (h : P 0) : True := by
  cases h with
  | base => trivial
  | step q => trivial

mutual
theorem P.toQ : ∀ {n}, P n → Q n
  | _, .base => .base
  | _, .step n q => .step n (Q.toP q)
theorem Q.toP : ∀ {n}, Q n → P n
  | _, .base => .base
  | _, .step n p => .step n (P.toQ p)
end
end Src

namespace Can
inductive X : Nat → Prop
  | base : X 0
  | step : ∀ n, X n → X n
theorem X.self : ∀ {n}, X n → X n
  | _, .base => .base
  | _, .step n x => .step n (X.self x)
end Can
end C7

namespace C7b
namespace Src
mutual
inductive EvenP : Nat → Prop
  | zero : R → EvenP 0
  | succ : OddP n → EvenP (n+1)
inductive OddP : Nat → Prop
  | succ : EvenP n → OddP (n+1)
inductive R : Prop
  | mk : R
end

mutual
theorem EvenP.toR : EvenP n → R
  | .zero r => r
  | .succ h => OddP.toR h
theorem OddP.toR : OddP n → R
  | .succ h => EvenP.toR h
end

theorem EvenP.two : EvenP 2 := .succ (.succ (.zero .mk))
end Src

namespace Can
inductive R : Prop
  | mk : R
-- Ix canonical order (OddP, EvenP)
mutual
inductive OddP : Nat → Prop
  | succ : EvenP n → OddP (n+1)
inductive EvenP : Nat → Prop
  | zero : R → EvenP 0
  | succ : OddP n → EvenP (n+1)
end
mutual
theorem EvenP.toR : EvenP n → R
  | .zero r => r
  | .succ h => OddP.toR h
theorem OddP.toR : OddP n → R
  | .succ h => EvenP.toR h
end
end Can
end C7b

