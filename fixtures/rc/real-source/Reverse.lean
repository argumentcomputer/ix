/-! H0 real-source fixture candidate. Production roots call Lean's actual
`List.reverse`; main is an independent, full-result reference oracle.
No production fixture identity is frozen until G2 selects its producer. -/

namespace CompilatrixTests.Own.H0

def descending (n seed : Nat) : List Nat :=
  match n with
  | 0 => []
  | k + 1 => (seed + k) :: descending k seed

def repeated (n value : Nat) : List Nat :=
  match n with
  | 0 => []
  | k + 1 => value :: repeated k value

/-- Runtime arguments prevent a fixed precomputed list result. -/
def reverseList (n seed : Nat) : List Nat :=
  List.reverse (descending n seed)

def reverseRepeated (n value : Nat) : List Nat :=
  List.reverse (repeated n value)

/-- Both original and reversed list escape: sharing is observable. -/
def sharedReverse (n seed : Nat) : List Nat × List Nat :=
  let xs := descending n seed
  let ys := List.reverse xs
  (xs, ys)

end CompilatrixTests.Own.H0

private def ascendingOracle (n seed : Nat) : List Nat :=
  (List.range n).map fun i => seed + i

private def descendingOracle (n seed : Nat) : List Nat :=
  (List.range n).map fun i => seed + (n - 1 - i)

def main : IO UInt32 := do
  let cases := [(0, 7), (1, 42), (4, 3), (7, 0), (32, 11), (128, 100)]
  for (n, seed) in cases do
    let actual := CompilatrixTests.Own.H0.reverseList n seed
    let expected := ascendingOracle n seed
    unless actual == expected do
      throw (IO.userError s!"reverseList {n} {seed}: {actual} != {expected}")
    IO.println s!"reverseList {n} {seed}: {actual}"
    let actualShared := CompilatrixTests.Own.H0.sharedReverse n seed
    let expectedShared := (descendingOracle n seed, expected)
    unless actualShared == expectedShared do
      throw (IO.userError s!"sharedReverse {n} {seed}: {actualShared} != {expectedShared}")
    IO.println s!"sharedReverse {n} {seed}: {actualShared}"
  for (n, value) in [(0, 9), (1, 2), (5, 7), (64, 3)] do
    let actual := CompilatrixTests.Own.H0.reverseRepeated n value
    let expected := List.replicate n value
    unless actual == expected do
      throw (IO.userError s!"reverseRepeated {n} {value}: {actual} != {expected}")
    IO.println s!"reverseRepeated {n} {value}: {actual}"
  unless ascendingOracle 4 3 != descendingOracle 4 3 do
    throw (IO.userError "order oracle failed to distinguish reversal")
  unless ascendingOracle 4 3 != [3, 4, 5, 5] do
    throw (IO.userError "element oracle failed to distinguish corruption")
  IO.println "PASS: 16 full-value cases; 2 independent oracle discrimination controls"
  pure 0
