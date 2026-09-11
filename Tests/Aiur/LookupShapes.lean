/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.LookupShapes

/-! Native parity for the structural validators. The corpus deliberately
varies shapes independently of value indices and layouts. These programs
are used only by the validators, never by an evaluator or AIR emitter. -/

namespace AiurTests.LookupShapes

open Aiur Aiur.Bytecode

def returning (size : Nat) : Block := ⟨#[], .return 0 (Array.replicate size 0)⟩

def yielding (size : Nat) : Block := ⟨#[], .yield 0 (Array.replicate size 0)⟩

def matched (arm fallback : Option Block) : Block :=
  ⟨#[], .match 0 (match arm with | none => #[] | some block => #[(0, block)]) fallback⟩

def continued (arm continuation : Block) : Block :=
  ⟨#[], .matchContinue 0 #[(0, arm)] (some (yielding 2)) 2 0 0 continuation⟩

def body : Nat → Block
  | 0 => returning 0
  | 1 => returning 1
  | 2 => returning 2
  | 3 => yielding 0
  | 4 => yielding 1
  | 5 => matched (some (returning 1)) (some (returning 1))
  | 6 => matched (some (returning 0)) (some (returning 1))
  | 7 => matched (some (returning 1)) none
  | 8 => matched none none
  | 9 => continued (yielding 2) (returning 1)
  | 10 => continued (returning 1) (returning 1)
  | 11 => continued (returning 0) (returning 1)
  | 12 => continued (yielding 1) (returning 1)
  | 13 => continued (yielding 2) (yielding 0)
  | 14 => continued (continued (yielding 2) (yielding 2)) (returning 1)
  | 15 => continued (continued (yielding 2) (yielding 1)) (returning 1)
  | _ => matched (some (continued (returning 1) (returning 1))) (some (returning 1))

def function (body : Block) (inputs : Nat) (entry constrained : Bool) : Function :=
  ⟨body, ⟨inputs, 1, 7, 4⟩, entry, constrained⟩

def expected : ByteArray := Id.run do
  let mut out := "Aiur lookup shapes v1\n".toUTF8
  for tag in [:17] do
    for size in [:4] do
      out := out.push (if (body tag).returnsHaveSize size then 1 else 0)
  for tag in [:17] do
    for calleeInputs in [:4] do
      for callerInputs in [:4] do
        for outputs in [:4] do
          for advice in [false, true] do
            for constrained in [false, true] do
              let caller := function
                ⟨#[.call 1 (Array.replicate callerInputs 0) outputs advice], .return 0 #[]⟩
                3 true true
              let callee := function (body tag) calleeInputs false constrained
              let program : Toplevel := ⟨#[caller, callee], #[], #[]⟩
              out := out.push (if program.validateLookupShapes then 1 else 0)
  for tag in [:17] do
    for inputs in [:4] do
      for entry in [false, true] do
        for constrained in [false, true] do
          let program : Toplevel := ⟨#[function (body tag) inputs entry constrained], #[], #[]⟩
          for channel in [:3] do
            for functionIndex in [0, 1, 99] do
              for arguments in [:7] do
                let claim := #[G.ofNat channel, G.ofNat functionIndex] ++ Array.replicate arguments 0
                out := out.push (if program.validClaimShape claim then 1 else 0)
  return out

def run (path : System.FilePath) : IO Unit := do
  let native ← IO.FS.readBinFile path
  unless expected.size == "Aiur lookup shapes v1\n".toUTF8.size + 21556 do
    throw (IO.userError "incomplete lookup-shape corpus")
  unless native.size == expected.size do
    throw (IO.userError s!"lookup-shape snapshot size differs: {native.size} / {expected.size}")
  for i in [:expected.size] do
    unless native[i]! == expected[i]! do
      throw (IO.userError s!"lookup-shape mismatch at byte {i}: {native[i]!} / {expected[i]!}")
  IO.println "lookup shapes: 21,556 native/Lean return, call, continuation and public-claim checks match"

end AiurTests.LookupShapes

def main (args : List String) : IO Unit := do
  match args with
  | [path] => AiurTests.LookupShapes.run path
  | _ => throw (IO.userError "expected native lookup-shape snapshot path")
