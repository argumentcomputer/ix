/-!
The Phase 1 boundary corpus (phase 1 plan, MT.3; research §9.4.1): one tiny
root per `Nat` primitive and operand shape, run at the 2⁶³ edge of every
argument, result and intermediate value.

Phase 1 words hold `Nat` values below 2⁶³ (`2n + 1`); a value at or above it
is `natOverflow` (status 3). Each root isolates one primitive, so a case's
expectation reads as the specification of `Rt.Lower`'s check for it. The
primitives are `Nat.add`, `Nat.sub`, … as Lean's elaborator emits them for
`+`, `-`, `*`, `/`, `%`, `^`, `&&&`, `|||`, `^^^`, `<<<`, `>>>`, `==`, `≤`,
`<`. The `…K` and `k…` roots put a literal on the right or the left, since
`Rt.lower` lowers an immediate operand differently.

The oracle driver at the end is not part of any closure: each stdin line
`ROOT ARG…` prints that root's value (`true`/`false` for `Bool`).
-/

namespace Boundary

/-! ## Binary primitives, both operands variable -/

def add (a b : Nat) : Nat := a + b
def sub (a b : Nat) : Nat := a - b
def mul (a b : Nat) : Nat := a * b
def div (a b : Nat) : Nat := a / b
def mod (a b : Nat) : Nat := a % b
def pow (a b : Nat) : Nat := a ^ b
def gcd (a b : Nat) : Nat := Nat.gcd a b
def land (a b : Nat) : Nat := a &&& b
def lor (a b : Nat) : Nat := a ||| b
def xor (a b : Nat) : Nat := a ^^^ b
def shl (a b : Nat) : Nat := a <<< b
def shr (a b : Nat) : Nat := a >>> b

/-! ## Comparisons -/

def beq (a b : Nat) : Bool := Nat.beq a b
def ble (a b : Nat) : Bool := Nat.ble a b
def blt (a b : Nat) : Bool := Nat.blt a b
def decEq (a b : Nat) : Bool := decide (a = b)
def decLe (a b : Nat) : Bool := decide (a ≤ b)
def decLt (a b : Nat) : Bool := decide (a < b)
def decGt (a b : Nat) : Bool := decide (a > b)
def bne (a b : Nat) : Bool := a != b
/-- A comparison whose only use is a branch (`Rt.lower` fuses it). -/
def ltBranch (a b : Nat) : Nat := if a < b then 1 else 0
def leBranch (a b : Nat) : Nat := if a ≤ b then 1 else 0
def minN (a b : Nat) : Nat := min a b
def maxN (a b : Nat) : Nat := max a b

/-! ## Unary -/

def pred (a : Nat) : Nat := a.pred
def succ (a : Nat) : Nat := a.succ
def ident (a : Nat) : Nat := a

/-! ## A literal operand on the right (`…K`) or the left (`k…`) -/

def addK (a : Nat) : Nat := a + 1
def kAdd (a : Nat) : Nat := 1 + a
def subK (a : Nat) : Nat := a - 1
def kSub (a : Nat) : Nat := 9223372036854775807 - a
def mulK (a : Nat) : Nat := a * 2
def kMul (a : Nat) : Nat := 2 * a
def divK (a : Nat) : Nat := a / 2
def kDiv (a : Nat) : Nat := 9223372036854775807 / a
def modK (a : Nat) : Nat := a % 7
def kMod (a : Nat) : Nat := 9223372036854775807 % a
def shlK (a : Nat) : Nat := a <<< 1
def kShl (a : Nat) : Nat := 1 <<< a
def shrK (a : Nat) : Nat := a >>> 62
def kShr (a : Nat) : Nat := 9223372036854775807 >>> a
def powK (a : Nat) : Nat := a ^ 2
def kPow (a : Nat) : Nat := 3 ^ a
def landK (a : Nat) : Nat := a &&& 4611686018427387904
def xorK (a : Nat) : Nat := a ^^^ 9223372036854775807
def ltK (a : Nat) : Bool := decide (a < 9223372036854775807)
def leK (a : Nat) : Bool := decide (a ≤ 9223372036854775807)
def eqK (a : Nat) : Bool := a == 9223372036854775807

/-! ## Literals -/

/-- `2⁶³ − 1`, the largest word, in live code. -/
def litMax (n : Nat) : Nat := if n == 0 then 9223372036854775807 else n
/-- `2⁶³` in live code at `n = 0` (the result has no word). -/
def litWord (n : Nat) : Nat := if n == 0 then 9223372036854775808 else n
/-- `2⁶⁴` in a branch no argument takes: it must not fail. -/
def litDead (n : Nat) : Nat := if n + 1 == 0 then 18446744073709551616 else n
/-- `2¹²⁸` in a `match` arm taken only at `n = 1`. -/
def litArm (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | 1 => 340282366920938463463374607431768211456
  | k + 2 => k
/-- `2⁶³` as an operand: every result is below `2⁶³` for `n ≥ 1`, but the
literal itself has no word. -/
def litOperand (n : Nat) : Nat := 9223372036854775808 - n
/-- `2⁶⁴` compared, never produced. -/
def litCompare (n : Nat) : Bool := decide (n < 18446744073709551616)

/-! ## Intermediate values -/

/-- `a + b` may reach `2⁶³` although `a + b - c` does not. -/
def addSub (a b c : Nat) : Nat := a + b - c
def mulDiv (a b c : Nat) : Nat := a * b / c
def shlShr (a b : Nat) : Nat := (a <<< b) >>> b
def powMod (a b m : Nat) : Nat := a ^ b % m
/-- `(a + 1) - 1`: the source computes `a + 1`. -/
def succPred (a : Nat) : Nat := (a + 1).pred

end Boundary

/-- The oracle driver: each stdin line `ROOT ARG…` prints one value. -/
def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  for line in input.splitOn "\n" do
    match (line.splitOn " ").filter (· != "") with
    | [] => pure ()
    | root :: args =>
      let a := args.map String.toNat!
      IO.println <| match root, a with
        | "Boundary.add", [x, y] => toString (Boundary.add x y)
        | "Boundary.sub", [x, y] => toString (Boundary.sub x y)
        | "Boundary.mul", [x, y] => toString (Boundary.mul x y)
        | "Boundary.div", [x, y] => toString (Boundary.div x y)
        | "Boundary.mod", [x, y] => toString (Boundary.mod x y)
        | "Boundary.pow", [x, y] => toString (Boundary.pow x y)
        | "Boundary.gcd", [x, y] => toString (Boundary.gcd x y)
        | "Boundary.land", [x, y] => toString (Boundary.land x y)
        | "Boundary.lor", [x, y] => toString (Boundary.lor x y)
        | "Boundary.xor", [x, y] => toString (Boundary.xor x y)
        | "Boundary.shl", [x, y] => toString (Boundary.shl x y)
        | "Boundary.shr", [x, y] => toString (Boundary.shr x y)
        | "Boundary.beq", [x, y] => toString (Boundary.beq x y)
        | "Boundary.ble", [x, y] => toString (Boundary.ble x y)
        | "Boundary.blt", [x, y] => toString (Boundary.blt x y)
        | "Boundary.decEq", [x, y] => toString (Boundary.decEq x y)
        | "Boundary.decLe", [x, y] => toString (Boundary.decLe x y)
        | "Boundary.decLt", [x, y] => toString (Boundary.decLt x y)
        | "Boundary.decGt", [x, y] => toString (Boundary.decGt x y)
        | "Boundary.bne", [x, y] => toString (Boundary.bne x y)
        | "Boundary.ltBranch", [x, y] => toString (Boundary.ltBranch x y)
        | "Boundary.leBranch", [x, y] => toString (Boundary.leBranch x y)
        | "Boundary.minN", [x, y] => toString (Boundary.minN x y)
        | "Boundary.maxN", [x, y] => toString (Boundary.maxN x y)
        | "Boundary.pred", [x] => toString (Boundary.pred x)
        | "Boundary.succ", [x] => toString (Boundary.succ x)
        | "Boundary.ident", [x] => toString (Boundary.ident x)
        | "Boundary.addK", [x] => toString (Boundary.addK x)
        | "Boundary.kAdd", [x] => toString (Boundary.kAdd x)
        | "Boundary.subK", [x] => toString (Boundary.subK x)
        | "Boundary.kSub", [x] => toString (Boundary.kSub x)
        | "Boundary.mulK", [x] => toString (Boundary.mulK x)
        | "Boundary.kMul", [x] => toString (Boundary.kMul x)
        | "Boundary.divK", [x] => toString (Boundary.divK x)
        | "Boundary.kDiv", [x] => toString (Boundary.kDiv x)
        | "Boundary.modK", [x] => toString (Boundary.modK x)
        | "Boundary.kMod", [x] => toString (Boundary.kMod x)
        | "Boundary.shlK", [x] => toString (Boundary.shlK x)
        | "Boundary.kShl", [x] => toString (Boundary.kShl x)
        | "Boundary.shrK", [x] => toString (Boundary.shrK x)
        | "Boundary.kShr", [x] => toString (Boundary.kShr x)
        | "Boundary.powK", [x] => toString (Boundary.powK x)
        | "Boundary.kPow", [x] => toString (Boundary.kPow x)
        | "Boundary.landK", [x] => toString (Boundary.landK x)
        | "Boundary.xorK", [x] => toString (Boundary.xorK x)
        | "Boundary.ltK", [x] => toString (Boundary.ltK x)
        | "Boundary.leK", [x] => toString (Boundary.leK x)
        | "Boundary.eqK", [x] => toString (Boundary.eqK x)
        | "Boundary.litMax", [x] => toString (Boundary.litMax x)
        | "Boundary.litWord", [x] => toString (Boundary.litWord x)
        | "Boundary.litDead", [x] => toString (Boundary.litDead x)
        | "Boundary.litArm", [x] => toString (Boundary.litArm x)
        | "Boundary.litOperand", [x] => toString (Boundary.litOperand x)
        | "Boundary.litCompare", [x] => toString (Boundary.litCompare x)
        | "Boundary.addSub", [x, y, z] => toString (Boundary.addSub x y z)
        | "Boundary.mulDiv", [x, y, z] => toString (Boundary.mulDiv x y z)
        | "Boundary.shlShr", [x, y] => toString (Boundary.shlShr x y)
        | "Boundary.powMod", [x, y, z] => toString (Boundary.powMod x y z)
        | "Boundary.succPred", [x] => toString (Boundary.succPred x)
        | _, _ => s!"unknown root {root} {args}"
