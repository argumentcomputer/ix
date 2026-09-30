/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Tc.Level
import Ix.Kernel.Level

/-! # Level-order differential gate

`Ix.Kernel.Certified.LevelNorm.levelLe` is proved to decide the pointwise
order of universe levels (`levelLe_iff`). This host-only gate compares it on
every level up to a small size with two oracles:

* brute-force evaluation over bounded valuations, which it must match exactly
  (a bounded valuation can only miss a counterexample, so a disagreement in
  which the checker accepts is a failure, and one in which it rejects is
  reported as an oracle gap);
* Ix.Tc's `univGeq`, which mirrors the Rust kernel and must agree exactly,
  and Ix.Tc's `univEq`, which must never accept what the checker rejects. The
  checker may accept equalities `univEq` misses: Ix.Tc's subsumption bounds a
  node's constant by the node's own variables, a slip Lean4Lean fixed, which
  leaves its canonical forms non-unique. Those are counted, not failures.

Output is one summary line; the exit code is nonzero on any failure. -/

namespace Tests.Ix.Kernel.LevelDifferential

open _root_.Ix.Kernel
open _root_.Ix.Tc (KUniv)

/-- Every level with exactly `size` constructors over `params` parameters. -/
partial def levelsOfSize (params : Nat) (size : Nat) : Array VLevel :=
  if size = 0 then #[]
  else if size = 1 then #[.zero] ++ (List.range params).toArray.map .param
  else Id.run do
    let mut out : Array VLevel := (levelsOfSize params (size - 1)).map .succ
    for i in [1:size - 1] do
      let left := levelsOfSize params i
      let right := levelsOfSize params (size - 1 - i)
      for a in left do
        for b in right do
          out := out.push (.max a b) |>.push (.imax a b)
    return out

def levelsUpTo (params size : Nat) : Array VLevel :=
  (List.range (size + 1)).foldl (fun acc n => acc ++ levelsOfSize params n) #[]

/-- All valuations of `params` parameters with values below `bound`. -/
def valuations (params bound : Nat) : List (List Nat) :=
  (List.range params).foldr (fun _ rest => (List.range bound).flatMap fun v => rest.map (v :: ·)) [[]]

def bruteLe (vals : List (List Nat)) (a b : VLevel) : Bool :=
  vals.all fun ls => a.eval ls ≤ b.eval ls

def tcLevel : VLevel → KUniv .anon
  | .zero => .mkZero
  | .succ u => .mkSucc (tcLevel u)
  | .max u v => .mkMaxRaw (tcLevel u) (tcLevel v)
  | .imax u v => .mkIMaxRaw (tcLevel u) (tcLevel v)
  | .param i => .mkParam i.toUInt64 ()

structure Counts where
  pairs : Nat := 0
  unsound : Nat := 0
  oracleGap : Nat := 0
  tcLeDisagree : Nat := 0
  tcEqUnsound : Nat := 0
  tcEqIncomplete : Nat := 0
  witness : Option String := none
  deriving Inhabited

partial def levelString : VLevel → String
  | .zero => "0"
  | .succ l => s!"({levelString l})+1"
  | .max a b => s!"max({levelString a},{levelString b})"
  | .imax a b => s!"imax({levelString a},{levelString b})"
  | .param i => s!"u{i}"

def compare (params size bound : Nat) (counts : Counts) : Counts := Id.run do
  let levels := levelsUpTo params size
  let vals := valuations params bound
  let tc := levels.map tcLevel
  let mut c := counts
  for i in [0:levels.size] do
    for j in [0:levels.size] do
      let a := levels[i]!
      let b := levels[j]!
      let le := Certified.LevelNorm.levelLe a b
      let brute := bruteLe vals a b
      let tcLe := _root_.Ix.Tc.univGeq tc[j]! tc[i]!
      c := { c with pairs := c.pairs + 1 }
      if le && !brute then
        c := { c with unsound := c.unsound + 1,
                      witness := c.witness <|> some s!"{levelString a} ≤ {levelString b}" }
      if !le && brute then c := { c with oracleGap := c.oracleGap + 1 }
      if le != tcLe then
        c := { c with tcLeDisagree := c.tcLeDisagree + 1,
                      witness := c.witness <|> some s!"Ix.Tc ≤ differs: {levelString a} ≤ {levelString b}" }
      if i < j then
        let eq := levelEquiv a b
        let tcEq := _root_.Ix.Tc.univEq tc[i]! tc[j]!
        if tcEq && !eq then c := { c with tcEqUnsound := c.tcEqUnsound + 1 }
        if eq && !tcEq then c := { c with tcEqIncomplete := c.tcEqIncomplete + 1 }
  return c

/-- A deterministic pseudo-random level of at most `size` constructors. -/
partial def randomLevel (params : Nat) (size : Nat) (seed : UInt64) : VLevel × UInt64 :=
  let seed := seed * 6364136223846793005 + 1442695040888963407
  let pick := ((seed >>> 33) % 8).toNat
  if size ≤ 1 || pick < 2 then
    (if pick % 2 = 0 then .zero else .param (((seed >>> 40).toNat) % params), seed)
  else if pick < 3 then
    let (a, seed) := randomLevel params (size - 1) seed
    (.succ a, seed)
  else
    let (a, seed) := randomLevel params (size / 2) seed
    let (b, seed) := randomLevel params (size / 2) seed
    (if pick < 5 then .max a b else .imax a b, seed)

/-- Random pairs, and each random level against a rearrangement of itself
(`max` commuted), so that true equalities are frequent. -/
def randomCompare (params size bound count : Nat) (counts : Counts) : Counts := Id.run do
  let vals := valuations params bound
  let mut c := counts
  let mut seed : UInt64 := 17
  for _ in [0:count] do
    let (a, s1) := randomLevel params size seed
    let (b, s2) := randomLevel params size s1
    seed := s2
    for (x, y) in [(a, b), (.max a b, .max b a), (.max a (.imax a b), .max a b)] do
      let le := Certified.LevelNorm.levelLe x y
      let brute := bruteLe vals x y
      let tcLe := _root_.Ix.Tc.univGeq (tcLevel y) (tcLevel x)
      let eq := levelEquiv x y
      let tcEq := _root_.Ix.Tc.univEq (tcLevel x) (tcLevel y)
      c := { c with pairs := c.pairs + 1 }
      if le && !brute then
        c := { c with unsound := c.unsound + 1,
                      witness := c.witness <|> some s!"{levelString x} ≤ {levelString y}" }
      if !le && brute then c := { c with oracleGap := c.oracleGap + 1 }
      if le != tcLe then
        c := { c with tcLeDisagree := c.tcLeDisagree + 1,
                      witness := c.witness <|> some s!"Ix.Tc ≤ differs: {levelString x} ≤ {levelString y}" }
      if tcEq && !eq then c := { c with tcEqUnsound := c.tcEqUnsound + 1 }
      if eq && !tcEq then c := { c with tcEqIncomplete := c.tcEqIncomplete + 1 }
  return c

def main : IO UInt32 := do
  -- Two parameters up to five constructors, three up to four, and random
  -- levels of up to sixteen constructors.
  let counts := compare 3 4 5 (compare 2 5 6 {})
  let counts := randomCompare 3 16 4 100000 counts
  -- Ix.Tc's subsumption slip: these are equal, and Ix.Tc's `univEq` misses it.
  let u : VLevel := .param 0
  let v : VLevel := .param 1
  let two : VLevel := .succ (.succ .zero)
  let x : VLevel := .max (.succ v) (.imax (.imax two u) v)
  let y : VLevel := .max (.succ v) (.imax u v)
  unless levelEquiv x y && !(_root_.Ix.Tc.univEq (tcLevel x) (tcLevel y)) do
    IO.eprintln "the recorded Ix.Tc subsumption witness no longer behaves as documented"
    return 1
  IO.println s!"Level order differential: {counts.pairs} pairs; unsound {counts.unsound}; \
    oracle gaps {counts.oracleGap}; Ix.Tc ≤ disagreements {counts.tcLeDisagree}; \
    Ix.Tc equalities the checker rejects {counts.tcEqUnsound}; \
    checker equalities Ix.Tc misses {counts.tcEqIncomplete}"
  if let some w := counts.witness then IO.eprintln s!"first failure: {w}"
  let failed := counts.unsound + counts.tcLeDisagree + counts.tcEqUnsound
  return if failed == 0 then 0 else 1

end Tests.Ix.Kernel.LevelDifferential

def main : IO UInt32 := Tests.Ix.Kernel.LevelDifferential.main
