/-! K4 `array-qsort`: standalone total in-place quicksort over `Array UInt32`
with median-of-three Hoare partitioning on a deterministic 32-bit LCG input. -/

namespace ArrayQsortBench

def mkArray (n : Nat) : Array UInt32 := Id.run do
  let mut arr := Array.emptyWithCapacity n
  let mut s : UInt32 := 123456789
  for _ in [0:n] do
    s := s * 1664525 + 1013904223
    arr := arr.push s
  return arr

def scanRight (arr : Array UInt32) (pivot : UInt32) : Nat → Nat → Nat
  | 0, i => i
  | fuel + 1, i =>
    if arr[i]! < pivot then scanRight arr pivot fuel (i + 1) else i

def scanLeft (arr : Array UInt32) (pivot : UInt32) : Nat → Nat → Nat
  | 0, j => j
  | fuel + 1, j =>
    if arr[j]! > pivot then scanLeft arr pivot fuel (j - 1) else j

def hoareLoop (lo hi : Nat) (pivot : UInt32) :
    Nat → Array UInt32 → Nat → Nat → Array UInt32 × Nat
  | 0, arr, _, j => (arr, j)
  | fuel + 1, arr, i, j =>
    if i > j then (arr, j)
    else
      let i' := scanRight arr pivot (hi - i) i
      let j' := scanLeft arr pivot (j - lo) j
      if i' ≥ j' then (arr, j')
      else
        let arr' := arr.swapIfInBounds i' j'
        hoareLoop lo hi pivot fuel arr' (i' + 1) (j' - 1)

def partition (arr : Array UInt32) (lo hi : Nat) : Array UInt32 × Nat :=
  let mid := lo + (hi - lo) / 2
  let arr := if arr[mid]! < arr[lo]! then arr.swapIfInBounds lo mid else arr
  let arr := if arr[hi]! < arr[lo]! then arr.swapIfInBounds lo hi else arr
  let arr := if arr[hi]! < arr[mid]! then arr.swapIfInBounds mid hi else arr
  let pivot := arr[mid]!
  hoareLoop lo hi pivot (hi - lo + 1) arr lo hi

def qsortAux : Nat → Array UInt32 → Nat → Nat → Array UInt32
  | 0, arr, _, _ => arr
  | fuel + 1, arr, lo, hi =>
    if lo ≥ hi then arr
    else
      let (arr, p) := partition arr lo hi
      let arr := qsortAux fuel arr lo p
      qsortAux fuel arr (p + 1) hi

def qsort (arr : Array UInt32) : Array UInt32 :=
  if arr.size ≤ 1 then arr
  else qsortAux arr.size arr 0 (arr.size - 1)

def isSorted (arr : Array UInt32) : Bool := Id.run do
  if arr.size ≤ 1 then return true
  for i in [0:arr.size - 1] do
    if arr[i]! > arr[i + 1]! then return false
  return true

def checksum (arr : Array UInt32) : Nat := Id.run do
  let mut h : Nat := 0
  for i in [0:arr.size] do
    h := (h * 31 + (arr[i]!).toNat) % 1000000007
  return h

end ArrayQsortBench

/-- The pure benchmark entry: verifies sortedness and returns `n * (10^9+7) + checksum`
(or `0` if unsorted). Fits below `2^62` for `n <= 10^9`. -/
def entry (n : Nat) : Nat :=
  let arr := ArrayQsortBench.qsort (ArrayQsortBench.mkArray n)
  if ArrayQsortBench.isSorted arr then
    arr.size * 1000000007 + ArrayQsortBench.checksum arr
  else
    0

def main : List String → IO UInt32
  | [n] => do IO.println (toString (entry n.toNat!)); pure 0
  | _ => do IO.eprintln "usage: array-qsort N"; pure 1
