/-!
# Deterministic pseudo-random numbers for generators

SplitMix64 (Steele, Lea and Flood, 2014): a 64-bit state, one addition and
three xor-shift-multiply rounds per output. Streams are fully determined by
their seed and identical on every platform, so a failing generated case is
reproduced from its seed alone.

**Choice sequences** (MT.5). Every draw goes through `Rng.draw`: a choice
in `[0, n)` (`below n`, and so `range`, `chance`, `pick`, `weighted`), or a
whole word (`word`, `n = 0`). An `Rng` may carry a `Tape`:

* recording: draws come from the seed's stream, as without a tape, and the
  tape logs each choice;
* replaying: draws come from a given choice sequence instead (a value is
  reduced below the draw's bound, and a sequence that runs out gives 0), and
  the tape logs the choices actually returned.

A generator is thereby a parser of choice sequences: recording its run on a
seed and replaying the log gives the same output, and any edited sequence
still gives a generator output, which is what the shrinker
(`CompilatrixTests.Support.Shrink`) relies on. Without a tape a draw is
exactly the word stream's (`below n = word % n`), so every existing seed
generates what it always did.
-/

namespace CompilatrixTests.Support

/-- A recorded or replayed choice sequence. -/
structure Tape where
  /-- The choices to replay; `none` while recording. -/
  replay : Option (Array Nat) := none
  /-- The next replayed choice. -/
  pos : Nat := 0
  /-- The choices returned so far. -/
  log : Array Nat := #[]
  deriving Repr, Inhabited

structure Rng where
  state : UInt64
  tape : Option Tape := none
  deriving Repr, Inhabited

namespace Rng

def ofSeed (seed : UInt64) : Rng := { state := seed }

/-- The seed's stream, recording its choices. -/
def recording (seed : UInt64) : Rng := { state := seed, tape := some {} }

/-- A choice sequence replayed in place of a stream. -/
def replaying (choices : Array Nat) : Rng := { state := 0, tape := some { replay := some choices } }

def next (g : Rng) : UInt64 × Rng :=
  let s := g.state + 0x9e3779b97f4a7c15
  let z := (s ^^^ (s >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  (z ^^^ (z >>> 31), { g with state := s })

/-- An independent seed for a sub-stream, derived from `seed` and `index`. -/
def derive (seed : UInt64) (index : Nat) : UInt64 :=
  (next { state := seed ^^^ (UInt64.ofNat index * 0xd1b54a32d192ed03) }).1

/-- One choice: in `[0, n)`, or a whole word when `n = 0`. -/
def draw (g : Rng) (n : Nat) : Nat × Rng :=
  let bound := fun (v : Nat) => if n == 0 then v % 2 ^ 64 else v % n
  match g.tape with
  | none =>
    let (w, g) := g.next
    (bound w.toNat, g)
  | some t =>
    match t.replay with
    | none =>
      let (w, g) := g.next
      let v := bound w.toNat
      (v, { g with tape := some { t with log := t.log.push v } })
    | some cs =>
      let v := bound (cs.getD t.pos 0)
      (v, { g with tape := some { t with pos := t.pos + 1, log := t.log.push v } })

/-- The choices drawn so far (empty without a tape). -/
def log (g : Rng) : Array Nat := (g.tape.map (·.log)).getD #[]

end Rng

/-- Computations that draw random numbers. -/
abbrev RngM := StateM Rng

namespace RngM

def word : RngM UInt64 := modifyGet fun g => let (v, g) := g.draw 0; (UInt64.ofNat v, g)

/-- Uniform-ish in `[0, n)`; `0` when `n = 0`. -/
def below (n : Nat) : RngM Nat := do
  if n == 0 then return 0
  modifyGet (·.draw n)

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

/-- Run `m` on `seed`'s stream, with the choices it drew. -/
def record {α : Type} (seed : UInt64) (m : RngM α) : α × Array Nat :=
  let (a, g) := m.run (Rng.recording seed)
  (a, g.log)

/-- Run `m` on a choice sequence, with the choices it actually returned
(reduced below each draw's bound, and padded with 0 where the sequence ran
out; a replay of the result gives the same output). -/
def replay {α : Type} (choices : Array Nat) (m : RngM α) : α × Array Nat :=
  let (a, g) := m.run (Rng.replaying choices)
  (a, g.log)

end RngM

end CompilatrixTests.Support
