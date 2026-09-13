/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Stages.Bytecode

/-! Native comparison/hash compatibility fixtures. The frozen output was
captured from the original compiler derivations before making them total.
Every operation constructor and all control forms occur, including nested
branches, defaults, continuations and deliberately different metadata. -/

open Aiur Aiur.Bytecode

namespace Tests.Aiur.BytecodeCompare

private def operations (n : Nat) : Array Op :=
  let a := #[n, n + 1, n + 2, n + 3]
  #[.const (G.ofNat n), .add n (n + 1), .sub n (n + 1), .mul n (n + 1),
    .eqZero n, .call n a 4 false, .call n a 4 true, .call n #[] 0 false,
    .store a, .load 4 n, .assertEq a a none, .assertEq a a (some "same fields"),
    .ioGetInfo n a, .ioSetInfo n a n (n + 1), .ioRead n (n + 1) 4, .ioWrite n a,
    .u8BitDecomposition n, .u8ShiftLeft n, .u8ShiftRight n,
    .u8Xor n (n + 1), .u8Add n (n + 1), .u8Mul n (n + 1), .u8Sub n (n + 1),
    .u8And n (n + 1), .u8Or n (n + 1), .u8LessThan n (n + 1), .u32LessThan n (n + 1),
    .u8XorSplit7 n (n + 1), .u8XorSplit4 n (n + 1),
    .debug "comparison fixture" none, .debug "comparison fixture" (some a),
    .u8RangeCheck n (n + 1), .unconstrainedBigUintDivMod n (n + 1),
    .unconstrainedGToBytes n, .unconstrainedGInverse n,
    .unconstrainedU32Add a a.reverse, .unconstrainedU32Add3 a a.reverse a,
    .u32ToField a]

def fixtures : Array Block := Id.run do
  let mut blocks := #[]
  for n in #[0, 1, 255, 256, 65536] do
    let ret : Block := ⟨#[], .return n #[n, n + 1]⟩
    let yielded : Block := ⟨#[], .yield n #[n, n + 1]⟩
    blocks := blocks ++ #[ret, yielded]
    for op in operations n do
      blocks := blocks.push ⟨#[op], ret.ctrl⟩
    for fallback in #[none, some ret, some yielded] do
      for branches in #[#[], #[(G.ofNat n, ret)], #[(G.ofNat n, ret), (G.ofNat (n + 1), yielded)]] do
        blocks := blocks.push ⟨#[], .match n branches fallback⟩
        for metadata in #[0, 1, 7] do
          blocks := blocks.push ⟨#[], .matchContinue n branches fallback metadata
            (n + metadata + 1) (2 * metadata + 3) ret⟩
    -- Long shared prefixes and deep control trees exercise recursive calls
    -- beyond the immediate constructor comparisons.
    let mut nested := ret
    for depth in [:24] do
      nested := ⟨(operations n).extract 0 (depth % 8),
        .matchContinue n #[(G.ofNat depth, nested)] (some yielded) 2 depth (depth + 1) ret⟩
    blocks := blocks ++ #[nested, nested, ⟨(operations n).reverse, nested.ctrl⟩]
  return blocks

private def report (blocks : Array Block) : IO Unit := do
  IO.println s!"BYTECODE COMPARISON FIXTURES {blocks.size}"
  for h : i in [:blocks.size] do
    let block := blocks[i]
    unless block == block do throw (IO.userError s!"block comparison is not reflexive: {i}")
    let mut equalIndices : Array Nat := #[]
    for k : j in [:blocks.size] do
      if block == blocks[j] then equalIndices := equalIndices.push j
    IO.println s!"BLOCK {i} HASH {hash block} CONTROL {hash block.ctrl} EQUAL {equalIndices}"

def main : IO Unit := report fixtures

end Tests.Aiur.BytecodeCompare

def main := Tests.Aiur.BytecodeCompare.main
