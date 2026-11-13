import IxCC.Anf.Walk
import IxCCTests.Src.Support

/-! The shrink walk's `succBle` rule (`Anf.Walk.succBle`): `natBle [x, m]`, where `x = y + 1` is a
recorded fact, becomes `natBlt [y, m]`. Lean's `x < y` on `Nat`, and every fixed-width word's
`decLt`, is `Nat.ble (x + 1) y`; natively that `x + 1` fails with `natOverflow` at `x = 2^63 − 1`,
and `natBlt` never builds it.

* **When it applies**: on `natBle` whose first operand is a level holding `succ y`, and nowhere
  else (the swapped `natBle [m, x]`, another primitive, a level holding another fact or none, a
  literal operand).
* **Exactness**: `natBlt [y, m]` and `natBle [y + 1, m]` have the same meaning (`Lam.Prim.sem`)
  on every pair of boundary values.
* **Mutants**: dropping the `+ 1` (`natBle [y, m]`) or swapping the operands (`natBlt [m, y]`)
  disagrees on some pair, so the exactness check would catch either. -/

namespace IxCCTests.Anf.SuccBle

open IxCC IxCC.Anf IxCCTests.Src

/-- Values around the tagged boundary (`2^63`) and small ones. -/
def boundary : List Nat := [0, 1, 2, 2 ^ 62, 2 ^ 63 - 2, 2 ^ 63 - 1, 2 ^ 63, 2 ^ 64]

def boolOf : Option Src.PrimResult → Option Bool
  | some (.bool b) => some b
  | _ => none

/-- The pairs `(y, m)` of `boundary` where `f y m` and `natBle [y + 1, m]` differ. -/
def misses (f : Nat → Nat → Option Src.PrimResult) : List (Nat × Nat) :=
  boundary.flatMap fun y => boundary.filterMap fun m =>
    if boolOf (f y m) == boolOf (Lam.Prim.sem .natBle [y + 1, m]) && (boolOf (f y m)).isSome then none
    else some (y, m)

def run (a : Assert) : IO (Array String) := do
  let facts : Src.NatMap Walk.Fact :=
    ((Src.NatMap.empty.insert 3 (.succ (.lvl 1))).insert 4 (.prim .natAdd [.lvl 1, .lit (.nat 2)]))
  let x : Opd := .lvl 3
  let m : Opd := .lvl 2
  expect a (Walk.succBle facts .natBle [x, m] == some [.lvl 1, m])
    "succBle: natBle [x, m] with x = y + 1 is not natBlt [y, m]"
  let declined : List (String × Lam.Prim × List Opd) :=
    [("the swapped natBle [m, x]", .natBle, [m, x]),
     ("natBeq [x, m]", .natBeq, [x, m]),
     ("natBlt [x, m]", .natBlt, [x, m]),
     ("x holding y + 2 (a prim fact)", .natBle, [.lvl 4, m]),
     ("x holding no fact", .natBle, [.lvl 5, m]),
     ("a literal first operand", .natBle, [.lit (.nat 1), m])]
  for (label, p, os) in declined do
    expect a (Walk.succBle facts p os).isNone s!"succBle applies to {label}"
  let exact := misses fun y m => Lam.Prim.sem .natBlt [y, m]
  expect a exact.isEmpty s!"natBlt [y, m] differs from natBle [y + 1, m] at {exact}"
  let noSucc := misses fun y m => Lam.Prim.sem .natBle [y, m]
  let swapped := misses fun y m => Lam.Prim.sem .natBlt [m, y]
  expect a (!noSucc.isEmpty && !swapped.isEmpty)
    s!"a mutant agrees on every boundary pair: natBle [y, m] {noSucc.length}, natBlt [m, y] {swapped.length}"
  let n := boundary.length * boundary.length
  return #[s!"succBle: applies to natBle [x, m] with x = y + 1, to none of {declined.length} other forms",
    s!"natBlt [y, m] = natBle [y + 1, m] on all {n} boundary pairs; the mutants natBle [y, m] and \
      natBlt [m, y] miss {noSucc.length} and {swapped.length}"]

end IxCCTests.Anf.SuccBle
