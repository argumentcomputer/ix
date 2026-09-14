/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.ReturnGates

/-! Native/Lean comparison for the actual shared argument combiner, block
selectors, selector polynomial projection and nearest-continuation yield
collection. Fixtures include arbitrary field assignments, nested continuations,
early returns, inactive branches and different raw message lengths. -/

open Aiur Aiur.AIR Aiur.Bytecode

namespace AiurTests.SelectorControl

private def appendNat (out : ByteArray) (value : Nat) : ByteArray := Id.run do
  let mut out := out
  for i in [:8] do
    out := out.push ((value >>> (8 * i)) % 256).toUInt8
  return out

private def appendValues (out : ByteArray) (values : List G) : ByteArray :=
  values.foldl (fun out value => appendNat out value.n) (appendNat out values.length)

private def leaf (seed next : Nat) : Block × Nat :=
  (⟨#[], if seed % 2 == 0 then .return next #[] else .yield next #[]⟩, next + 1)

private def fixture : Nat → Nat → Nat → Block × Nat
  | 0, seed, next => leaf seed next
  | depth + 1, seed, next =>
    if seed % 5 == 0 then leaf seed next
    else
      let (left, next) := fixture depth (seed * 3 + 1) next
      let (right, next) := fixture depth (seed * 3 + 2) next
      let (fallback, next) := if seed % 2 == 0 then
          let (block, next) := fixture depth (seed * 3 + 3) next
          (some block, next)
        else (none, next)
      let branches := #[(0, left), (1, right)]
      if seed % 3 == 0 then (⟨#[], .match 0 branches fallback⟩, next)
      else
        let (continuation, next) := fixture depth (seed * 3 + 4) next
        (⟨#[], .matchContinue 0 branches fallback 0 0 0 continuation⟩, next)

private def assignment (pattern index count : Nat) : G :=
  match pattern with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 0 - 1
  | 4 => G.ofNat (index + 1)
  | 5 => 0 - G.ofNat (index + 1)
  | 6 => if index % 2 == 0 then 1 else 0
  | 7 => [0, 0 - 1, 1, 2][index % 4]?.getD 0
  | pattern => if pattern < 8 + count then
      (if index == pattern - 8 then 1 else 0)
    else if index != pattern - 8 - count then 1 else 0

private def expected : ByteArray × Nat × Nat := Id.run do
  let mut out := appendNat "Aiur selector control v1\n".toUTF8 48
  let mut controls := 0
  let mut messages := 0
  for depth in [:4] do
    for seed in [:12] do
      let (block, count) := fixture depth seed 0
      out := appendNat out count
      out := appendNat out (8 + 2 * count)
      for pattern in [:8 + 2 * count] do
        let flow := block.selectorFlow fun index => assignment pattern index count
        out := appendNat out flow.entry.n
        out := appendValues out ([99, 100] ++ flow.yields)
        out := appendValues out flow.equations
        let gates := block.returnGates (fun index => assignment pattern index count) flow.entry
        out := appendValues out (weightedMessage
          (gates.map fun selector => (selector, [0, 37, 3, 19, 257])))
        controls := controls + 1
  out := appendNat out (2 * 7 * 32 * 8)
  for branchless in [false, true] do
    for count in [:7] do
      for seed in [:32] do
        for pattern in [:8] do
          let parts := (List.range count).map fun index =>
            (assignment pattern index count,
              (List.range ((seed + index * 3) % 8)).map fun offset =>
                let value := G.ofNat (17 + seed + index * 5 + offset * 11)
                if (seed + offset) % 2 == 0 then value else 0 - value)
          out := appendNat out (selectorSum (parts.map Prod.fst)).n
          out := appendValues out (slotMessage branchless parts)
          messages := messages + 1
  return (out, controls, messages)

def run (path : System.FilePath) : IO Unit := do
  let native ← IO.FS.readBinFile path
  let (expected, controls, messages) := expected
  unless messages == 3584 do
    throw (IO.userError "incomplete shared-message corpus")
  unless native.size == expected.size do
    throw (IO.userError s!"selector-control snapshot size differs: {native.size} / {expected.size}")
  for i in [:expected.size] do
    unless native[i]! == expected[i]! do
      throw (IO.userError s!"selector-control mismatch at byte {i}: {native[i]!} / {expected[i]!}")
  IO.println s!"selector control: {controls} native/Lean assignments and {messages} shared messages match"

end AiurTests.SelectorControl

def main (args : List String) : IO Unit := do
  match args with
  | [path] => AiurTests.SelectorControl.run path
  | _ => throw (IO.userError "expected native selector-control snapshot path")
