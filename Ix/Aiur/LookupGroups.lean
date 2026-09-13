/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.KeyCodec

/-! Total lookup-group selection for the production FFT cost comparison.
Machine-size and u128 intermediate checks match the native selector. The
authored graph remains fixed; grouping determines the direct LogUp evaluator's
degree, accumulator width and constraint count. -/

namespace Aiur.NativeAIR.LookupGroups

structure FftCost where
  one : Nat
  two : Nat
  slope : Nat
  intercept : Nat
  deriving DecidableEq, Repr

def checked128 (value : Nat) : Option Nat :=
  if value < 2^128 then some value else none

def FftCost.make (stage2 quotient blowup degree : Nat) : Option FftCost := do
  if stage2 ≥ 2^64 || quotient ≥ 2^64 || blowup ≥ 2^64 || degree ≥ 2^64 then none else do
  if quotient = 0 || quotient.nextPowerOfTwo != quotient ||
      blowup = 0 || blowup.nextPowerOfTwo != blowup then none else do
  let logQ := quotient.log2
  let logB := blowup.log2
  let qd ← checked128 (quotient * degree)
  let trace ← checked128 ((blowup + 1) * stage2)
  let combined ← checked128 (stage2 + qd)
  let slope ← checked128 ((blowup + 1) * combined)
  let scaledLog ← checked128 (blowup * logB)
  let logs ← checked128 (logQ + scaledLog)
  let intercept ← checked128 (qd * logs)
  let scaledOneLog ← checked128 (blowup * max logB 1)
  let oneLogs ← checked128 (max logQ 1 + scaledOneLog)
  let quotientOne ← checked128 (qd * oneLogs)
  let one ← checked128 (trace + quotientOne)
  let two ← checked128 (slope + intercept)
  return ⟨one, two, slope, intercept⟩

def FftCost.noWorse (candidate baseline : FftCost) : Bool :=
  candidate.one ≤ baseline.one && candidate.two ≤ baseline.two && candidate.slope ≤ baseline.slope

def FftCost.scoreLess (candidate current : FftCost) : Bool :=
  candidate.slope < current.slope ||
    (candidate.slope == current.slope &&
      (candidate.intercept < current.intercept ||
        (candidate.intercept == current.intercept && candidate.one < current.one)))

def quotientDegree (circuit : KeyCodec.Circuit) : Nat :=
  (max circuit.maxConstraintDegree 2 - 1).nextPowerOfTwo

def withGroup (circuit : KeyCodec.Circuit) (group : Nat) : Option KeyCodec.Circuit := do
  let candidate := { circuit with lookupGroupSize := group }
  let degree ← candidate.computedDegree
  return { candidate with maxConstraintDegree := degree }

def selectGroup (circuit : KeyCodec.Circuit) (blowup : Nat) : Option Nat := do
  if circuit.graph.nodes.any (fun node => match node with
      | .var column => column.source == .stage2 | _ => false) then none else do
  let baseline ← FftCost.make circuit.widths.stage2 (quotientDegree circuit) blowup 2
  let best := (List.range (min 8 (max 1 circuit.graph.lookups.length))).foldl
    (fun best offset =>
      let group := offset + 1
      match withGroup circuit group with
      | none => best
      | some candidate =>
        let quotient := quotientDegree candidate
        if quotient ≥ 2^64 || quotient > blowup then best else
        match FftCost.make candidate.widths.stage2 quotient blowup 2 with
        | none => best
        | some cost =>
          if cost.noWorse baseline && cost.scoreLess best.2 then (group, cost) else best)
    (circuit.lookupGroupSize, baseline)
  return best.1

def retune (circuit : KeyCodec.Circuit) (blowup : Nat) : KeyCodec.Circuit :=
  match selectGroup circuit blowup with
  | none => circuit
  | some group => (withGroup circuit group).getD circuit

/-- Fields consumed by the authored AIR and the preprocessed commitment. -/
def AuthoredFields (circuit : KeyCodec.Circuit) :=
  (circuit.graph, circuit.mainWidth, circuit.preprocessedWidth, circuit.preprocessedHeight)

theorem withGroup_authored {circuit result : KeyCodec.Circuit} {group : Nat}
    (selected : withGroup circuit group = some result) : AuthoredFields result = AuthoredFields circuit := by
  simp only [withGroup, bind, Option.bind] at selected
  split at selected
  · cases selected
  · cases selected
    rfl

theorem retune_authored (circuit : KeyCodec.Circuit) (blowup : Nat) :
    AuthoredFields (retune circuit blowup) = AuthoredFields circuit := by
  unfold retune
  split
  · rfl
  · rename_i group _
    cases selected : withGroup circuit group with
    | none => rfl
    | some result => exact withGroup_authored selected

end Aiur.NativeAIR.LookupGroups
