def double (n : Nat) : Nat := n + n
def smokeInput : Nat := double 21
def smokeOutput : Nat := nat_lit 42
structure P where
  a : Int
  b : List Int
def pairInput : P := ⟨-3 * 5, [1 - 4, 2 * 3]⟩
def pairOutput : P := P.mk (Int.negSucc (nat_lit 14)) (@List.cons Int (Int.negSucc (nat_lit 2)) (@List.cons Int (Int.ofNat (nat_lit 6)) (@List.nil Int)))
