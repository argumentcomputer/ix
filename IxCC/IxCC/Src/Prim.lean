import IxCC.Src.Syntax

/-! # Nat primitives

The exact meaning of every `PrimOp` on literals:
`Tc.computeNatBin` without the kernel's checker caps (`pow` exponent,
shift width), which are limits of the checker, not meaning. Division by zero
gives `0` and remainder by zero gives the dividend. -/

namespace IxCC.Src

/-- A primitive result: a `Nat` or a `Bool`. -/
inductive PrimResult where
  | nat (n : Nat)
  | bool (b : Bool)
  deriving BEq, DecidableEq, Repr

namespace PrimOp

def eval2 : PrimOp → Nat → Nat → PrimResult
  | .add, a, b => .nat (a + b)
  | .sub, a, b => .nat (a - b)
  | .mul, a, b => .nat (a * b)
  | .div, a, b => .nat (if b == 0 then 0 else a / b)
  | .mod, a, b => .nat (if b == 0 then a else a % b)
  | .pow, a, b => .nat (a ^ b)
  | .gcd, a, b => .nat (Nat.gcd a b)
  | .beq, a, b => .bool (a == b)
  | .ble, a, b => .bool (decide (a ≤ b))
  | .land, a, b => .nat (a &&& b)
  | .lor, a, b => .nat (a ||| b)
  | .xor, a, b => .nat (a ^^^ b)
  | .shiftLeft, a, b => .nat (a * 2 ^ b)
  | .shiftRight, a, b => .nat (if a.log2 < b then 0 else a / 2 ^ b)
  | .pred, a, _ => .nat (a - 1)

/-- The result on literal arguments; `none` on an arity mismatch. -/
def evalLits (op : PrimOp) : List Nat → Option PrimResult
  | [a] => if op.arity == 1 then some (op.eval2 a 0) else none
  | [a, b] => if op.arity == 2 then some (op.eval2 a b) else none
  | _ => none

end PrimOp

end IxCC.Src
