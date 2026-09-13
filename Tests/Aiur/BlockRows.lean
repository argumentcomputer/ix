/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.QuerySlotMessages

open Aiur Aiur.AIR Aiur.Bytecode

namespace AiurTests.BlockRows

private def appendNat (out : ByteArray) (value : Nat) : ByteArray := Id.run do
  let mut out := out
  for i in [:8] do
    out := out.push ((value >>> (8 * i)) % 256).toUInt8
  return out

private def appendValues (out : ByteArray) (values : List G) : ByteArray :=
  values.foldl (fun out value => appendNat out value.n) (appendNat out values.length)

private def appendMap (out : ByteArray) (values : Array RowValue) : ByteArray :=
  values.foldl (fun out value => appendNat (appendNat (appendNat out value.value.n)
    value.degree) (if value.constant then 1 else 0)) (appendNat out values.size)

private def blockOps (seed initial : Nat) : Array Op × Nat :=
  let size := seed % 3
  let pointer := initial + 3 + size
  (#[.const (G.ofNat (seed + 17)), .mul 0 1,
    .eqZero (if seed % 2 == 0 then initial else 0),
    .call 17 #[0, initial] size false, .store #[0, initial + 1],
    .load size pointer, .u8Add 0 1, .assertEq #[initial + 1] #[0] none],
    initial + 6 + 2 * size)

private def fixture (depth seed initial next : Nat) : Block × Nat :=
  let (ops, count) := blockOps seed initial
  let leaf := (⟨ops, if seed % 2 == 0 then .return next #[count - 2, count - 1]
    else .yield next #[count - 2, count - 1]⟩, next + 1)
  match depth with
  | 0 => leaf
  | depth + 1 =>
    if seed % 5 == 0 then leaf else
      let (left, next) := fixture depth (seed * 3 + 1) count next
      let (right, next) := fixture depth (seed * 3 + 2) count next
      let (fallback, next) := if seed % 2 == 0 then
          let (block, next) := fixture depth (seed * 3 + 3) count next
          (some block, next)
        else (none, next)
      let branches := #[(0, left), (1, right)]
      let matched := if seed % 2 == 0 then initial else 0
      if seed % 3 == 0 then (⟨ops, .match matched branches fallback⟩, next)
      else
        let (continuation, next) := fixture depth (seed * 3 + 4) (count + 2) next
        (⟨ops, .matchContinue matched branches fallback 2 0 0 continuation⟩, next)

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

private def row (seed pattern count index : Nat) : G :=
  if 2 ≤ index ∧ index < 2 + count then assignment pattern (index - 2) count
  else
    let choices : List G := [0, 1, 0 - 1, 255, 256, G.ofNat (2^32), G.ofNat (2^48 - 1), 17]
    choices[(seed + 5 * index) % 8]?.getD 0

private def expected : Except String (ByteArray × Nat) := do
  let mut out := appendNat "Aiur block rows v1\n".toUTF8 96
  let mut checked := 0
  for branchless in [false, true] do
    for depth in [:4] do
      for seed in [:12] do
        let (block, count) := fixture depth seed 2 0
        out := appendNat out count
        out := appendNat out (8 + 2 * count)
        for pattern in [:8 + 2 * count] do
          let row := row seed pattern count
          let selector := fun index => row (2 + index)
          let values := #[RowValue.variable (row 0), RowValue.variable (row 1)]
          let some emission := block.emitRow row selector ⟨37, 2, 257⟩
              (block.selectorFlow selector).entry values (2 + count) 1
            | throw s!"emission failed at depth {depth}, seed {seed}, pattern {pattern}"
          out := appendNat out emission.column
          out := appendNat out emission.lookup
          out := appendMap out emission.values
          out := appendValues out emission.equations
          for slot in [:emission.lookup] do
            let parts := if slot == 0 then emission.returns.map fun part =>
                (part.1, functionMessage part.2)
              else querySlotParts emission.queries slot
            out := appendNat out (if slot == 0 then 0 else querySlotMultiplicity emission.queries slot).n
            out := appendValues out (slotMessage branchless parts)
          let yields := [(99, values), (100, values)] ++ emission.yields
          out := appendNat out yields.length
          for (gate, values) in yields do
            out := appendNat out gate.n
            out := appendMap out values
          checked := checked + 1
  return (out, checked)

def run (path : System.FilePath) : IO Unit := do
  let native ← IO.FS.readBinFile path
  let (expected, checked) ← match expected with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  unless checked == 2028 do throw (IO.userError "incomplete block-row corpus")
  unless native.size == expected.size do
    throw (IO.userError s!"block-row snapshot size differs: {native.size} / {expected.size}")
  for i in [:expected.size] do
    unless native[i]! == expected[i]! do
      throw (IO.userError s!"block-row mismatch at byte {i}: {native[i]!} / {expected[i]!}")
  IO.println s!"block rows: {checked} native/Lean assignments with shared columns and slots match"

end AiurTests.BlockRows

def main (args : List String) : IO Unit := do
  match args with
  | [path] => AiurTests.BlockRows.run path
  | _ => throw (IO.userError "expected native block-row snapshot path")
