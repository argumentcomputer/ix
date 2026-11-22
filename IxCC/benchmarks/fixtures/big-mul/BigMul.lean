/-! K5 `big-mul`: repeated full-density `limbs`-limb (`64*limbs`-bit) arbitrary-precision
multiplications over Lean's exact `Nat`, keeping operand bit-width constant via
data-dependent fold-back. -/

namespace BigMulBench

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

def mulLoop (b : Nat) (bits : Nat) (mask topBit : Nat) : Nat → Nat → Nat
  | 0, a => a
  | reps + 1, a =>
    let p := a * b
    let lo := p &&& mask
    let hi := p >>> bits
    let a' := (((lo ^^^ hi) &&& mask) ||| topBit) ||| 1
    mulLoop b bits mask topBit reps a'

def runBigMul (limbs reps : Nat) : Nat :=
  let l := if limbs == 0 then 1 else limbs
  let bits := l * 64 - 1
  let topBit := 1 <<< (bits - 1)
  let mask := (1 <<< bits) - 1
  let a := mkBig 17 l
  let b := mkBig 53 l
  bignumDigest (mulLoop b bits mask topBit reps a)

end BigMulBench

/-- The pure benchmark entry: compact fingerprint after `reps` `limbs`-limb multiplications. -/
def entry (limbs reps : Nat) : Nat := BigMulBench.runBigMul limbs reps

def main : List String → IO UInt32
  | [limbs, reps] => do IO.println (toString (entry limbs.toNat! reps.toNat!)); pure 0
  | _ => do IO.eprintln "usage: big-mul LIMBS REPS"; pure 1
