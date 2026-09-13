/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur

/-! Source-to-proof regressions for constants produced by expression folding
whose conservative compiler degree remains positive. -/

open Aiur

namespace AiurTests.ConstantDegree

def source := ⟦
  fn zero_left(x: G) -> G { eq_zero(0 * x) }
  fn zero_right(x: G) -> G { eq_zero(x * 0) }
  fn shifted_one(x: G) -> G { eq_zero(0 * x + 1) }
  fn negated_zero(x: G) -> G { eq_zero(0 - 0 * x) }
  fn nested_zero(x: G) -> G { eq_zero(eq_zero(0 * x)) }
  fn following_mul(x: G) -> G { eq_zero(0 * x) * x }
  pub fn check(x: G) -> [G; 6] {
    [zero_left(x), zero_right(x), shifted_one(x), negated_zero(x), nested_zero(x), following_mul(x)]
  }
⟧

def run : IO Unit := do
  let decls ← IO.ofExcept (source.mkDecls.mapError toString)
  let compiled ← IO.ofExcept source.compile
  let cp : CommitmentParameters := { logBlowup := 1, capHeight := 0 }
  let fp : FriParameters := {
    logFinalPolyLen := 0, maxLogArity := 1, numQueries := 64,
    commitProofOfWorkBits := 0, queryProofOfWorkBits := 0 }
  let grouped ← IO.ofExcept (compiled.groupFunctions #[
    ("zeroes", #["zero_left", "zero_right"]),
    ("shifted", #["shifted_one", "negated_zero"])])
  let mut accepted := 0
  let mut rejected := 0
  for program in [compiled, grouped] do
    let some index := program.getFuncIdx `check | throw (IO.userError "missing constant-degree entry")
    for input in ([0, 1, 17, 0 - 1] : List Aiur.G) do
      let expected : Array Aiur.G := #[1, 1, 0, 1, 0, input]
      let (sourceValue, sourceIo) ← IO.ofExcept
        ((Source.Eval.runFunction decls (Global.init "check") [.field input] default 100).mapError reprStr)
      unless flattenValue decls (fun _ => none) sourceValue == expected && sourceIo == default do
        throw (IO.userError "constant-degree source reference differs")
      let (reference, _) ← IO.ofExcept
        ((Bytecode.Eval.runFunction program.bytecode index #[input] default 100).mapError reprStr)
      let (native, _, _) ← IO.ofExcept (program.bytecode.execute index #[input] default)
      unless reference == expected && native == expected do throw (IO.userError "constant-degree execution differs")
      IO.println s!"constant-degree reference/execution match for input {input}"
      let system := AiurSystem.build program.bytecode cp fp
      let (claim, proof, _) ← IO.ofExcept (system.prove index #[input] default)
      unless claim == buildClaim index #[input] expected do throw (IO.userError "constant-degree proof claim differs")
      IO.ofExcept (system.verify claim proof)
      accepted := accepted + 1
      match system.verify (buildClaim index #[input] (expected.set! 0 0)) proof with
      | .error _ => rejected := rejected + 1
      | .ok _ => throw (IO.userError "changed constant-degree output accepted")
  unless accepted == 8 && rejected == 8 do throw (IO.userError "incomplete constant-degree proof corpus")
  IO.println s!"constant degree: {accepted} honest proofs, {rejected} changed-output rejections"

end AiurTests.ConstantDegree

def main : IO Unit := AiurTests.ConstantDegree.run
