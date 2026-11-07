import IxCCTests.Support.Rng
import Lean.Data.Json

/-!
# Shrinking failing generated cases by their choice sequences (MT.5)

Hypothesis-style test-case reduction (MacIver and Donaldson, ECOOP 2020;
research note §9.2.6): a generated case is the output of a generator run on
a *choice sequence* (`Rng`'s tape), so a smaller sequence replayed through
the same generator is a smaller case of the same type, well formed by
construction. A failing case is reduced by editing its sequences and
keeping an edit when the failure persists:

* deleting a block of 16, 8, 4, 2 or 1 consecutive choices;
* setting a choice to 0 (the generators' first alternative: a leaf, a
  literal, no recursion), then to its half, then to one less.

A case may be drawn from several sequences (a program and its arguments, or
a program and a mutation of it); each is reduced in turn. An edit is kept
only when the replay still fails *the same way* (the caller's `test`
compares the failure's signature, the first level that diverges) and its
normalised sequences (the choices the replay actually used) are smaller in
shortlex order: fewer choices in all, then lexicographically smaller. The
passes repeat until a round keeps nothing or the budget of replays runs
out. -/

namespace IxCCTests.Support.Shrink

/-- A case's choice sequences. -/
abbrev Seqs := Array (Array Nat)

def total (s : Seqs) : Nat := s.foldl (· + ·.size) 0

def lexLt : List Nat → List Nat → Bool
  | [], _ :: _ => true
  | a :: as, b :: bs => a < b || (a == b && lexLt as bs)
  | _, _ => false

/-- Shortlex: fewer choices, then lexicographically smaller. -/
def smaller (a b : Seqs) : Bool :=
  let la := total a
  let lb := total b
  la < lb || (la == lb && lexLt (a.toList.flatMap (·.toList)) (b.toList.flatMap (·.toList)))

structure Stats where
  /-- Replays run. -/
  tries : Nat := 0
  /-- Edits kept. -/
  kept : Nat := 0
  rounds : Nat := 0
  deriving Inhabited, Repr

/-- Reduce `start` while `test` (a replay of the sequences: `some` the
normalised sequences when the failure persists) keeps failing; at most
`budget` replays. -/
def shrink (test : Seqs → IO (Option Seqs)) (start : Seqs) (budget : Nat := 3000) :
    IO (Seqs × Stats) := do
  let cur ← IO.mkRef start
  let st ← IO.mkRef ({} : Stats)
  let attempt := fun (cand : Seqs) => do
    if (← st.get).tries ≥ budget then return false
    st.modify fun s => { s with tries := s.tries + 1 }
    match ← test cand with
    | some n =>
      if smaller n (← cur.get) then
        cur.set n
        st.modify fun s => { s with kept := s.kept + 1 }
        return true
      return false
    | none => return false
  let mut progress := true
  while progress && (← st.get).tries < budget do
    progress := false
    st.modify fun s => { s with rounds := s.rounds + 1 }
    for si in [0:start.size] do
      -- delete blocks
      for k in [16, 8, 4, 2, 1] do
        let mut i := 0
        while i + k ≤ ((← cur.get)[si]?.map (·.size)).getD 0 && (← st.get).tries < budget do
          let s := (← cur.get)
          let seq := s[si]!
          let cand := s.set! si (seq.extract 0 i ++ seq.extract (i + k) seq.size)
          if ← attempt cand then progress := true else i := i + 1
      -- lower single choices: 0, half, one less
      let mut i := 0
      while i < ((← cur.get)[si]?.map (·.size)).getD 0 && (← st.get).tries < budget do
        let s := (← cur.get)
        let v := s[si]![i]!
        let mut done := false
        for w in [0, v / 2, v - 1] do
          if !done && w < v then
            if ← attempt (s.set! si (s[si]!.set! i w)) then
              progress := true
              done := true
        i := i + 1
  return (← cur.get, ← st.get)

end IxCCTests.Support.Shrink
