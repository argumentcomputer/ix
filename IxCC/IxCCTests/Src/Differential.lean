import IxCCTests.Src.Support
import IxCCTests.Src.Rules
import IxCCTests.Fixtures.K1

/-! SrcEval against native Lean. The fixture
`IxCCTests/Fixtures/K1.lean` is compiled into this executable as the
test module `IxCCTests.Fixtures.K1`, so each K1 definition runs natively
beside its SrcEval run on the same `k1.ixe` closure. Primitives are compared
with Lean's `Nat` at the word boundaries, and the primitive route against
the `eqn`/kernel-body route (`noPrims`). -/

namespace IxCCTests.Src.Differential

open IxCC IxCC.Src IxCCTests.Src IxCCTests.Src.Rules
open IxCC.Sem (Result)

def clock : Nat := 1 <<< 40

def agree (a : Assert) (l : Loaded) (root : CId) (label : String) (args : List Nat)
    (native : Nat) : IO Unit := do
  let r ← runRoot l.program clock root args
  expect a (natOf r == some native) s!"{label} {args}: SrcEval {outcome r}, Lean {native}"

def k1 (a : Assert) : IO Unit := do
  let l ← loadK1
  let fib ← rootNamed l "K1.fib"
  for n in [0:26] do agree a l fib "fib" [n] (K1.fib n)
  let ack ← rootNamed l "K1.ack"
  for m in [0:4] do
    for n in [0:6] do agree a l ack "ack" [m, n] (K1.ack m n)
  let tak ← rootNamed l "K1.tak"
  let mut g : Gen := { seed := 7 }
  for _ in [0:120] do
    let (f, g1) := g.next 9
    let (x, g2) := g1.next 13
    let (y, g3) := g2.next 13
    let (z, g4) := g3.next 13
    g := g4
    agree a l tak "tak" [f, x, y, z] (K1.tak f x y z)
  let sumLoop ← rootNamed l "K1.sumLoop"
  for n in [0, 1, 2, 3, 10, 99, 1000, 10000] do agree a l sumLoop "sumLoop" [n] (K1.sumLoop n)
  let gcd ← rootNamed l "K1.gcd"
  for _ in [0:1000] do
    let (x, g1) := g.next (1 <<< 40)
    let (y, g2) := g1.next (1 <<< 40)
    g := g2
    agree a l gcd "gcd" [x, y] (K1.gcd x y)
  for (x, y) in [(0, 0), (0, 7), (7, 0), (2 ^ 40 - 1, 2 ^ 39 + 1)] do
    agree a l gcd "gcd" [x, y] (K1.gcd x y)

/-- Word-boundary values. -/
def edges : List Nat :=
  [0, 1, 2, 3, 63, 64, 65, 2 ^ 32, 2 ^ 63 - 1, 2 ^ 63, 2 ^ 63 + 1, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 64 + 1,
   2 ^ 128 + 12345]

def leanOp : PrimOp → Nat → Nat → PrimResult
  | .add, a, b => .nat (a + b)
  | .sub, a, b => .nat (a - b)
  | .mul, a, b => .nat (a * b)
  | .div, a, b => .nat (a / b)
  | .mod, a, b => .nat (a % b)
  | .pow, a, b => .nat (a ^ b)
  | .gcd, a, b => .nat (Nat.gcd a b)
  | .beq, a, b => .bool (a == b)
  | .ble, a, b => .bool (Nat.ble a b)
  | .land, a, b => .nat (Nat.land a b)
  | .lor, a, b => .nat (Nat.lor a b)
  | .xor, a, b => .nat (Nat.xor a b)
  | .shiftLeft, a, b => .nat (Nat.shiftLeft a b)
  | .shiftRight, a, b => .nat (Nat.shiftRight a b)
  | .pred, a, _ => .nat (Nat.pred a)

def primsAgainstLean (a : Assert) : IO Unit := do
  for op in PrimOp.all do
    for x in edges do
      for y in edges do
        -- Keep `pow` and `shiftLeft` to exponents Lean computes quickly.
        if (op == .pow || op == .shiftLeft || op == .shiftRight) && y > 200 then continue
        let expected := leanOp op x y
        expect a (op.eval2 x y == expected) s!"{op.name} {x} {y}"
  -- Shifts beyond the width give zero without computing `2 ^ b`.
  for x in edges do
    for y in [2 ^ 64, 2 ^ 64 + 1, 2 ^ 100] do
      expect a (PrimOp.shiftRight.eval2 x y == .nat 0) s!"shiftRight {x} {y}"
  -- Zero divisors.
  for x in edges do
    expect a (PrimOp.div.eval2 x 0 == .nat 0 && PrimOp.mod.eval2 x 0 == .nat x) s!"div/mod {x} 0"

/-- Every pinned primitive in `k1.ixe`, run through SrcEval's prim route on
edge values, against Lean. -/
def primsThroughSrcEval (a : Assert) (l : Loaded) : IO Unit := do
  for (op, _, hex) in Pinned.primRows do
    let some c := l.program.lookup (Pinned.addr hex) | continue
    for x in edges do
      for y in edges do
        if (op == .pow || op == .shiftLeft || op == .shiftRight) && y > 200 then continue
        let args := if op.arity == 1 then [x] else [x, y]
        let r ← runRoot l.program 10 c args
        let ok := match r, leanOp op x y with
          | .ok (.lit n), .nat m => n == m
          | .ok (.con k _ _ []), .bool b => some k == (if b then l.program.known.boolTrue else l.program.known.boolFalse)
          | _, _ => false
        expect a ok s!"SrcEval {op.name} {args}: {outcome r}"

/-- Primitives on against `noPrims` (the `eqn` and kernel bodies) for `add`,
`sub`, `mul`, `beq` and `ble` on small values. -/
def primsAgainstNoPrims (a : Assert) (l : Loaded) : IO Unit := do
  let ops := [PrimOp.add, .sub, .mul, .beq, .ble]
  let noPrims ← loadK1Roots (ops.toArray.map Pinned.primAddr)
    { typecheck := false, table := { prims := [] } }
  for op in ops do
    let some c := l.program.lookup (Pinned.primAddr op) | continue
    for x in [0, 1, 2, 5, 13, 30] do
      for y in [0, 1, 3, 7, 20] do
        let r1 ← runRoot l.program 10 c [x, y]
        let r2 ← runRoot noPrims.program clock c [x, y]
        expect a (sameOutcome l.program r1 r2 &&
            (readbackAll l.program <$> (match r1 with | .ok v => some v | _ => none)) ==
            (readbackAll noPrims.program <$> (match r2 with | .ok v => some v | _ => none)))
          s!"{op.name} {x} {y}: prim {outcome r1}, noPrims {outcome r2}"

def run (a : Assert) : IO Unit := do
  k1 a
  primsAgainstLean a
  let l ← loadK1
  primsThroughSrcEval a l
  primsAgainstNoPrims a l

end IxCCTests.Src.Differential
