/-! H2: recursive inductives whose constructor names have more than one
component. Lean names the Prop `.below` constructors `<below> ++ minorName`
(IndPredBelow.mkBelowInductive), with the minor named by the constructor's
suffix after the inductive name. -/
namespace DotCtor
inductive P : Nat → Prop
  | z : P 0
  | s.t {n : Nat} : P n → P (n + 1)

theorem P.triv {n : Nat} : P n → True
  | .z => trivial
  | P.s.t h => P.triv h

inductive T
  | leaf
  | n.o : T → T

def T.size : T → Nat
  | .leaf => 0
  | T.n.o t => t.size + 1

mutual
inductive A : Prop
  | x.y : B → A
  | base : A
inductive B : Prop
  | x.y : A → B
end

mutual
theorem A.triv : A → True
  | A.x.y b => B.triv b
  | .base => trivial
theorem B.triv : B → True
  | B.x.y a => A.triv a
end
end DotCtor
