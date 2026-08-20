module

@[expose] public section

namespace FixtureB

inductive Flavor where
  | mild
  | strong
deriving Repr, BEq

structure Token where
  flavor : Flavor
  amount : Nat
deriving Repr, BEq

def Token.score (token : Token) : Nat :=
  match token.flavor with
  | .mild => token.amount
  | .strong => token.amount * 2

def defaultToken : Token := ⟨.strong, 21⟩

end FixtureB
