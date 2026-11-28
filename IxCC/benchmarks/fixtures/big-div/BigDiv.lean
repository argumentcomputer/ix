/-! K5 `big-div`: repeated full-density `(2*limbs)`-limb by `limbs`-limb
Euclidean division and remainder over Lean's exact `Nat`, keeping dividend and
divisor widths stable via data-dependent fold-back. -/

namespace BigDivBench

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

def divLoop (shift : Nat) : Nat → Nat → Nat → Nat
  | 0, a, b => a + b
  | reps + 1, a, b =>
    let q := a / b
    let r := a % b
    let a' := ((r + b) <<< shift) + q
    let b' := b + (q % 65537) + 1
    divLoop shift reps a' b'

def runBigDiv (limbs reps : Nat) : Nat :=
  let l := if limbs == 0 then 1 else limbs
  let shift := l * 64
  let a := mkBig 101 (2 * l)
  let b := mkBig 37 l
  bignumDigest (divLoop shift reps a b)

end BigDivBench

/-- The pure benchmark entry: compact fingerprint after `reps` `(2*limbs) / limbs` divisions. -/
def entry (limbs reps : Nat) : Nat := BigDivBench.runBigDiv limbs reps

def main : List String → IO UInt32
  | [limbs, reps] => do IO.println (toString (entry limbs.toNat! reps.toNat!)); pure 0
  | _ => do IO.eprintln "usage: big-div LIMBS REPS"; pure 1
