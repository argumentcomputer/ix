/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.CompiledKey
import Ix.IxVM.Toplevel
import Ix.IxVM.FunctionGroups

/-! Compare the complete native key of the pruned production `verify_claim`
image with the checked compiler. These are test protocol parameters; this
regression neither certifies the guest checker nor instantiates release
cryptographic security. -/

open Aiur Aiur.NativeAIR

def main : IO Unit := do
  let source ← IO.ofExcept (IxVM.ixVM.mapError toString)
  let compiled ← IO.ofExcept source.compile
  let compiled ← IO.ofExcept (compiled.groupFunctions IxVM.functionGroups)
  let program := compiled.bytecode
  unless !program.callComponents.isEmpty && program.validCallComponents do
    throw (IO.userError "production image lacks its checked component assignment")
  let some entry := compiled.getFuncIdx `verify_claim
    | throw (IO.userError "production claim entrypoint is missing")
  for debugEntry in [`verify_const, `verify_check, `verify_check_env] do
    unless (compiled.getFuncIdx debugEntry).isNone do
      throw (IO.userError s!"debug entrypoint remains in the production image: {debugEntry}")
  IO.println s!"production IxVM: {program.functions.size} functions, {program.circuits.size} function circuits, claim entry {entry}"
  let commitment : CommitmentParameters := { logBlowup := 2, capHeight := 0 }
  let fri : FriParameters := {
    logFinalPolyLen := 0, maxLogArity := 1, numQueries := 64,
    commitProofOfWorkBits := 0, queryProofOfWorkBits := 0 }
  let system := AiurSystem.build program commitment fri
  let bytes := system.vkBytes
  let some key := KeyCodec.decodeCanonical bytes
    | throw (IO.userError "production native key failed canonical decoding")
  IO.println s!"production native key: {key.circuits.length} circuits, {bytes.size} bytes"
  unless CompiledKey.check program key do
    throw (IO.userError "production native key differs from the checked native-layout compiler")
  IO.println "PASS production verify_claim image: every native circuit and retuned lookup group matches the checked key"
