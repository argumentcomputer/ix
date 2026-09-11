/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.CircuitRows
import Ix.Aiur.RowCounts

open Aiur Aiur.AIR Aiur.Bytecode

namespace AiurTests.CircuitRows

private def appendNat (out : ByteArray) (value : Nat) : ByteArray := Id.run do
  let mut out := out
  for i in [:8] do
    out := out.push ((value >>> (8 * i)) % 256).toUInt8
  return out

private def appendValues (out : ByteArray) (values : List G) : ByteArray :=
  values.foldl (fun out value => appendNat out value.n) (appendNat out values.length)

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

private def closeReturns (width : Nat) (escapes : Bool) : Nat → Block → Block
  | 0, block => block
  | fuel + 1, block => { block with ctrl := match block.ctrl with
      | .return index outputs => .return index (outputs.extract 0 width)
      | .yield index outputs => if escapes then .return index (outputs.extract 0 width) else .yield index outputs
      | .match index branches fallback => .match index
          (branches.map fun pair => (pair.1, closeReturns width escapes fuel pair.2))
          (fallback.map (closeReturns width escapes fuel))
      | .matchContinue index branches fallback size aux slots continuation => .matchContinue index
          (branches.map fun pair => (pair.1, closeReturns width false fuel pair.2))
          (fallback.map (closeReturns width false fuel)) size aux slots
          (closeReturns width escapes fuel continuation) }

private def fixtureFunction (seed index : Nat) : Except String Function := do
  let inputSize := 2 + (seed + index) % 3
  let depth := (seed + index) % 3
  let (body, selectors) := fixture depth (seed * 4 + index) inputSize 0
  let body := closeReturns (index % 3) true (depth + 1) body
  let body := if seed % 4 == 0 && index == 0 then
      { ops := #[], ctrl := .match 0 #[(0, { ops := #[.store #[]], ctrl := .match 0 #[] none }), (1, body)] none }
    else body
  let some measured := body.emitRow (fun _ => 0) (fun _ => 0) ⟨37, inputSize, 0⟩
      (body.selectorFlow (fun _ => 0)).entry (rowAdvice (fun _ => 0) 0 inputSize)
      (inputSize + selectors + 7) 4
    | throw "fixture layout emission failed"
  return ⟨body, ⟨inputSize, selectors, measured.column - inputSize - selectors, measured.lookup⟩, true, true⟩

private def circuitLayout (functions : Array Function) (members : Array Nat) : Bytecode.FunctionLayout :=
  members.foldl (fun layout index => match functions[index]? with
    | none => layout
    | some function => layout.merge function.layout) ⟨0, 0, 7, 4⟩

private def groups : List (Array Nat) := [#[0], #[1], #[2], #[3], #[0, 1], #[2, 0, 3], #[3, 2, 1, 0], #[]]

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

private def row (seed pattern start count index : Nat) : G :=
  if start ≤ index ∧ index < start + count then assignment pattern (index - start) count
  else
    let choices : List G := [0, 1, 0 - 1, 255, 256, G.ofNat (2^32), G.ofNat (2^48 - 1), 17]
    choices[(seed + 5 * index + 3 * pattern) % 8]?.getD 0

private def expected : Except String (ByteArray × Nat) := do
  let mut out := appendNat "Aiur circuit rows v3\n".toUTF8 96
  let mut checked := 0
  for seed in [:12] do
    let functions ← (List.range 4).mapM (fixtureFunction seed)
    let functions := functions.toArray
    let circuits := groups.map fun members => Circuit.mk "fixture" members (circuitLayout functions members)
    let top : Toplevel := ⟨functions, #[], circuits.toArray⟩
    for function in functions do
      let counts := function.body.controlCounts
      unless counts.leaves == function.layout.selectors do throw "leaf allocation differs"
      for count in [counts.nodes, counts.leaves, counts.returns, counts.yields] do
        out := appendNat out count
    unless top.validateRowCounts do throw "circuit count validation failed"
    out := out.push (if top.validateRowCounts then 1 else 0)
    for circuit in circuits do
      let layout := circuit.layout
      for limit in [0, layout.selectors - 1, layout.selectors, layout.selectors + 1] do
        let variant := { circuit with layout := { layout with selectors := limit } }
        out := out.push (if variant.validateRowCounts top then 1 else 0)
      let missing := { circuit with members := circuit.members.push functions.size }
      unless !missing.validateRowCounts top do throw "missing circuit member accepted"
      out := out.push (if missing.validateRowCounts top then 1 else 0)
      let doubled := { circuit with members := circuit.members ++ circuit.members }
      out := out.push (if doubled.validateRowCounts top then 1 else 0)
      let branchless := circuitBranchless layout.selectors
        (circuit.members.toList.filterMap fun index => functions[index]?)
      out := out.push (if branchless then 1 else 0)
      out := appendNat out layout.width
      out := appendNat out layout.inputSize
      out := appendNat out layout.selectors
      out := appendNat out layout.lookups
      out := appendNat out (8 + 2 * layout.selectors)
      for pattern in [:8 + 2 * layout.selectors] do
        let row := row seed pattern layout.inputSize layout.selectors
        let some emission := circuit.emitRow row top | throw "circuit emission failed"
        unless emission.branchless == branchless do throw "branchless selection differs"
        out := appendValues out emission.equations
        for slot in [:layout.lookups] do
          let (multiplicity, message) := emission.lookup slot
          out := appendNat out multiplicity.n
          out := appendValues out message
        checked := checked + 1
  return (out, checked)

def run (path : System.FilePath) : IO Unit := do
  let native ← IO.FS.readBinFile path
  let (expected, checked) ← match expected with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  unless checked == 2022 do throw (IO.userError "incomplete circuit-row corpus")
  unless native.size == expected.size do
    throw (IO.userError s!"circuit-row snapshot size differs: {native.size} / {expected.size}")
  for i in [:expected.size] do
    unless native[i]! == expected[i]! do
      throw (IO.userError s!"circuit-row mismatch at byte {i}: {native[i]!} / {expected[i]!}")
  IO.println s!"circuit rows: {checked} native/Lean assignments, 48 control counts, 588 count checks and 96 branchless decisions match"

end AiurTests.CircuitRows

def main (args : List String) : IO Unit := do
  match args with
  | [path] => AiurTests.CircuitRows.run path
  | _ => throw (IO.userError "expected native circuit-row snapshot path")
