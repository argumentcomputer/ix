/-! K5 `factorial`: binary-splitting product-tree `n!` over Lean's exact `Nat`,
returning a compact non-modular fingerprint (exact bit length, top 32 bits, and
remainder mod `10^9 + 7`). -/

namespace FactorialBench

def bitLen (v : Nat) : Nat :=
  if v == 0 then 0
  else
    let rec findHi : Nat → Nat → Nat
      | 0, hi => hi
      | fuel + 1, hi => if (v >>> hi) == 0 then hi else findHi fuel (hi * 2)
    let hi := findHi 32 1
    let rec bsearch : Nat → Nat → Nat → Nat
      | 0, lo, _ => lo + 1
      | fuel + 1, lo, hi =>
        if lo + 1 ≥ hi then lo + 1
        else
          let mid := (lo + hi) / 2
          if (v >>> mid) == 0 then bsearch fuel lo mid
          else bsearch fuel mid hi
    bsearch 32 (hi / 2) hi

def bignumDigest (v : Nat) : Nat :=
  let bl := bitLen v
  let top := if bl > 32 then v >>> (bl - 32) else v
  let rem := v % 1000000007
  bl * 1000000007 + ((rem * 31 + top) % 1000000007)

/-- Product `lo * (lo + 1) * ... * hi` via balanced binary splitting. -/
def prodRangeAux : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if lo > hi then 1
    else if lo == hi then lo
    else if lo + 1 == hi then lo * hi
    else
      let mid := (lo + hi) / 2
      prodRangeAux fuel lo mid * prodRangeAux fuel (mid + 1) hi

def factorial (n : Nat) : Nat :=
  if n ≤ 1 then 1 else prodRangeAux 64 1 n

end FactorialBench

/-- The pure benchmark entry: compact fingerprint of `n!`. -/
def entry (n : Nat) : Nat := FactorialBench.bignumDigest (FactorialBench.factorial n)

def main : List String → IO UInt32
  | [n] => do IO.println (toString (entry n.toNat!)); pure 0
  | _ => do IO.eprintln "usage: factorial N"; pure 1
