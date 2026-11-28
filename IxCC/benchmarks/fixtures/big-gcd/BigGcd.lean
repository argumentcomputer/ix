/-! K5 `big-gcd`: repeated arbitrary-precision `Nat.gcd` on dense `limbs`-limb
operands sharing a nontrivial `(limbs / 4)`-limb common factor. -/

namespace BigGcdBench

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

def lcg (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

def mkLimb (seed : Nat) : Nat :=
  let s1 := lcg (seed % 2147483648)
  let s2 := lcg s1
  let hi31 := (s1 % 1073741824) + 1073741824
  let lo31 := s2 ||| 1
  hi31 * 2147483648 + lo31

def mkBigAux : Nat → Nat → Nat → Nat
  | 0, seed, _ => mkLimb seed
  | fuel + 1, seed, limbs =>
    if limbs ≤ 1 then mkLimb seed
    else
      let half := limbs / 2
      let lo := mkBigAux fuel seed half
      let hi := mkBigAux fuel ((seed + half * 2654435761) % 2147483648) (limbs - half)
      (hi <<< (half * 64)) + lo

def mkBig (seed limbs : Nat) : Nat := mkBigAux 64 seed limbs

def gcdLoop (g : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | reps + 1, a, b, acc =>
    let d := Nat.gcd a b
    let da := (d % 1000003) + 1
    let db := (d % 1000033) + 3
    gcdLoop g reps (a + g * da) (b + g * db) (acc + d)

def runBigGcd (limbs reps : Nat) : Nat :=
  let l := if limbs < 4 then 4 else limbs
  let gLimbs := l / 4
  let xLimbs := l - gLimbs
  let g := mkBig 77 gLimbs
  let a := mkBig 17 xLimbs * g
  let b := mkBig 53 xLimbs * g
  bignumDigest (gcdLoop g reps a b 0)

end BigGcdBench

/-- The pure benchmark entry: compact fingerprint of accumulated `Nat.gcd` results. -/
def entry (limbs reps : Nat) : Nat := BigGcdBench.runBigGcd limbs reps

def main : List String → IO UInt32
  | [limbs, reps] => do IO.println (toString (entry limbs.toNat! reps.toNat!)); pure 0
  | _ => do IO.eprintln "usage: big-gcd LIMBS REPS"; pure 1
