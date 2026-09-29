/-!
# Deterministic pseudo-random numbers for generators

SplitMix64 (Steele, Lea and Flood, 2014): a 64-bit state, one addition and
three xor-shift-multiply rounds per output. Streams are fully determined by
their seed and identical on every platform, so a failing generated case is
reproduced from its seed alone.
-/

namespace CompilatrixTests.Support

structure Rng where
  state : UInt64
  deriving Repr, Inhabited

namespace Rng

def ofSeed (seed : UInt64) : Rng := ⟨seed⟩

def next (g : Rng) : UInt64 × Rng :=
  let s := g.state + 0x9e3779b97f4a7c15
  let z := (s ^^^ (s >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- An independent seed for a sub-stream, derived from `seed` and `index`. -/
def derive (seed : UInt64) (index : Nat) : UInt64 :=
  (next ⟨seed ^^^ (UInt64.ofNat index * 0xd1b54a32d192ed03)⟩).1

end Rng

/-- Computations that draw random numbers. -/
abbrev RngM := StateM Rng

namespace RngM

def word : RngM UInt64 := modifyGet Rng.next

/-- Uniform-ish in `[0, n)`; `0` when `n = 0`. -/
def below (n : Nat) : RngM Nat := do
  if n == 0 then return 0
  return (← word).toNat % n

/-- In `[lo, hi]`. -/
def range (lo hi : Nat) : RngM Nat := do
  return lo + (← below (hi + 1 - lo))

/-- True with probability `percent`/100. -/
def chance (percent : Nat) : RngM Bool := do
  return (← below 100) < percent

def pick {α : Type} [Inhabited α] (xs : Array α) : RngM α := do
  return xs[← below xs.size]!

/-- Pick an index by weight. -/
def weighted (weights : List Nat) : RngM Nat := do
  let total := weights.foldl (· + ·) 0
  let mut r ← below total
  let mut i := 0
  for w in weights do
    if r < w then return i
    r := r - w
    i := i + 1
  return 0

end RngM

end CompilatrixTests.Support
