namespace Tests.Ix.CompileCert.NatOpDefs

/-! Fixture roots for the source-named Nat-operation pins and the pinned `Eq`
basis under `Quot` (`Tests/Ix/CompileCert/StrongPins.lean`). -/

/-- One root per pin-certified operation, applied directly. -/
def half (n : Nat) : Nat := Nat.div n 2
def parity (n : Nat) : Nat := Nat.mod n 2
def common (a b : Nat) : Nat := Nat.gcd a b
def both (a b : Nat) : Nat := Nat.land a b
def either (a b : Nat) : Nat := Nat.lor a b
def differ (a b : Nat) : Nat := Nat.xor a b
def double (a : Nat) : Nat := Nat.shiftLeft a 1
def halve (a : Nat) : Nat := Nat.shiftRight a 1

/-- All eight through the notation and its instances, as library code reaches them. -/
def mixed (a b : Nat) : Nat :=
  a / b + a % b + (a &&& b) + (a ||| b) + (a ^^^ b) + (a <<< b) + (a >>> b) + Nat.gcd a b

/-- A quotient and a function out of it: the cone has `Quot`, `Quot.mk`,
`Quot.lift` and `Eq` (in `Quot.lift`'s type). -/
def Parity : Type := Quot (fun a b : Nat => Nat.mod a 2 = Nat.mod b 2)
def Parity.mk (n : Nat) : Parity := Quot.mk _ n
def Parity.val (p : Parity) : Nat := Quot.lift (fun n => Nat.mod n 2) (fun _ _ h => h) p

/-- A quotient whose cone has no `Eq` (the relation is `True`). -/
def Blur (α : Type) : Type := Quot (fun _ _ : α => True)
def Blur.mk {α : Type} (a : α) : Blur α := Quot.mk _ a

end Tests.Ix.CompileCert.NatOpDefs
