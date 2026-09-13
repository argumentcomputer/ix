/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.CompiledVerifier
import Ix.Aiur.Meta

/-! Nonvacuity and rejection tests for the generic program binding component.
The arithmetic source exercises the backend API; it is not a certified Ix
checker and does not license a logical claim about Ix declarations. -/

namespace AiurTests.Backend

open Aiur Aiur.BoundVerifier

def product := ⟦
  pub fn product(a: G, b: G) -> G { a * b }
⟧

def changedProduct := ⟦
  pub fn product(a: G, b: G) -> G { a + b }
⟧

def groupedProgram := ⟦
  fn double(x: G) -> G { x + x }
  fn bump(x: G) -> G { x + 1 }
  pub fn grouped_product(a: G, b: G) -> G { double(a) * bump(b) }
⟧

def requireRejected (label : String) (result : Except String α) : IO Unit :=
  match result with
  | .error _ => IO.println s!"PASS {label}: rejected"
  | .ok _ => throw (IO.userError s!"unexpected acceptance: {label}")

def run : IO Unit := do
  let compiled ← IO.ofExcept product.compile
  let some function := compiled.getFuncIdx `product
    | throw (IO.userError "missing product entrypoint")
  let cp : CommitmentParameters := { logBlowup := 1, capHeight := 0 }
  let fp : FriParameters := {
    logFinalPolyLen := 0, maxLogArity := 1,
    numQueries := 64, commitProofOfWorkBits := 0, queryProofOfWorkBits := 0 }
  let system := AiurSystem.build compiled.bytecode cp fp
  let selection : Selection := {
    source := product, entrypoint := `product,
    function, inputSize := 2, success := #[15], commitment := cp, fri := fp,
    key := system.vkBytes }
  let backend ← IO.ofExcept (buildCompiled selection)
  let (claim, proof, _) ← IO.ofExcept (system.prove function #[3, 5] default)
  unless claim == buildClaim function #[3, 5] #[15] do
    throw (IO.userError "unexpected public claim")
  let bytes := proof.toBytes
  IO.ofExcept (verifyCompiled backend #[3, 5] bytes)
  IO.println "PASS selected program/key/function/input/result: accepted"
  requireRejected "changed public input" (verifyCompiled backend #[3, 4] bytes)
  requireRejected "public input arity" (verifyCompiled backend #[3] bytes)
  requireRejected "malformed proof" (verifyCompiled backend #[3, 5] ByteArray.empty)
  let changedResult ← IO.ofExcept (buildCompiled { selection with success := #[16] })
  requireRejected "changed success result" (verifyCompiled changedResult #[3, 5] bytes)
  requireRejected "missing success output" (buildCompiled { selection with success := #[] })
  requireRejected "extra zero success output" (buildCompiled { selection with success := #[15, 0] })
  requireRejected "unselected key" (buildCompiled { selection with key := ByteArray.empty })
  requireRejected "changed program" (buildCompiled { selection with source := changedProduct })
  requireRejected "changed function index" (buildCompiled { selection with function := function + 1 })
  requireRejected "changed entrypoint" (buildCompiled { selection with entrypoint := `missing })
  requireRejected "changed expected arity" (buildCompiled { selection with inputSize := 3 })
  requireRejected "unselected grouping" (buildCompiled { selection with groups := #[("bad", #["product"])] })
  requireRejected "changed commitment parameters" (buildCompiled {
    selection with commitment := { cp with logBlowup := 2 } })
  requireRejected "changed FRI parameters" (buildCompiled {
    selection with fri := { fp with numQueries := 32 } })

  let initial ← IO.ofExcept groupedProgram.compile
  let groups := #[("helpers", #["double", "bump"])]
  let grouped ← IO.ofExcept (initial.groupFunctions groups)
  unless grouped.bytecode.circuits.size + 1 == initial.bytecode.circuits.size do
    throw (IO.userError "grouping did not merge the two helper circuits")
  let some groupedFunction := grouped.getFuncIdx `grouped_product
    | throw (IO.userError "missing grouped entrypoint")
  let groupedSystem := AiurSystem.build grouped.bytecode cp fp
  let groupedSelection : Selection := {
    source := groupedProgram, groups, entrypoint := `grouped_product,
    function := groupedFunction, inputSize := 2, success := #[30],
    commitment := cp, fri := fp, key := groupedSystem.vkBytes }
  let groupedBackend ← IO.ofExcept (buildCompiled groupedSelection)
  let (groupedClaim, groupedProof, _) ←
    IO.ofExcept (groupedSystem.prove groupedFunction #[3, 4] default)
  unless groupedClaim == buildClaim groupedFunction #[3, 4] #[30] do
    throw (IO.userError "unexpected grouped public claim")
  IO.ofExcept (verifyCompiled groupedBackend #[3, 4] groupedProof.toBytes)
  IO.println "PASS selected grouped program: accepted"
  requireRejected "grouped key with ungrouped program"
    (buildCompiled { groupedSelection with groups := #[] })
  IO.println "backend binding: 2 accepted, 15 rejected, 0 unexpected outcomes"

end AiurTests.Backend

def main : IO Unit := AiurTests.Backend.run
