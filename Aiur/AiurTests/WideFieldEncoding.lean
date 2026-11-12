import Aiur.Ixon.Field
import Aiur.Trace.Export

namespace AiurWideFieldEncodingTests
open Aiur.Ixon

private def encoded (value : Nat) : Except String ByteArray :=
  run (putWideNat value)

private def limbs (values : List Nat) : Except String ByteArray :=
  run do
    nat values.length
    for value in values do nat value

def run : IO Unit := do
  let values := [0, 1, 127, 128, 2^64 - 1, 2^64, 2^64 + 1,
    2^128 - 1, 2^128, 2^192 - 1, 2^192, 2^256 - 1]
  for value in values do
    let bytes ← IO.ofExcept (encoded value)
    let decoded ← IO.ofExcept (decode getWideNat bytes)
    unless value == decoded do
      throw (IO.userError s!"wide field integer changed in transport: {value}")
  unless (← IO.ofExcept (encoded 0)) == (← IO.ofExcept (limbs [])) do
    throw (IO.userError "zero has a nonempty wide encoding")
  unless (← IO.ofExcept (encoded (2^128 + 7))) == (← IO.ofExcept (limbs [7, 0, 1])) do
    throw (IO.userError "wide integer limbs are not minimal little-endian UInt64 words")
  unless (encoded (2^256)).toOption.isNone do
    throw (IO.userError "wide field integer exceeded 256 bits")
  for invalid in [[0], [1, 0], [0, 0, 0, 0], [1, 0, 0, 0, 1]] do
    let bytes ← IO.ofExcept (limbs invalid)
    unless (decode getWideNat bytes).toOption.isNone do
      throw (IO.userError "noncanonical wide integer limbs accepted")
  let bytes ← IO.ofExcept (encoded (2^256 - 1))
  for stop in [0:bytes.size] do
    unless (decode getWideNat (bytes.extract 0 stop)).toOption.isNone do
      throw (IO.userError "truncated wide integer accepted")
  unless (decode getWideNat (bytes.push 0)).toOption.isNone do
    throw (IO.userError "trailing wide integer byte accepted")
  let overflowLimb := ByteArray.mk #[1, 195, 255, 255, 255, 255, 255, 255, 255, 255]
  unless (decode getWideNat overflowLimb).toOption.isNone do
    throw (IO.userError "wide scalar limb exceeded UInt64")
  for modulus in [0, 1, 2^256] do
    unless (Aiur.Ixon.run (FieldEncoding.wide.putModulus modulus)).toOption.isNone do
      throw (IO.userError "invalid wide artifact modulus accepted")
  let modulus := 21888242871839275222246405745257275088548364400416034343698204186575808495617
  let scalar ← IO.ofExcept (Aiur.Ixon.run (FieldEncoding.wide.putScalar modulus (modulus - 1)))
  unless (← IO.ofExcept (decode getWideNat scalar)) == modulus - 1 do
    throw (IO.userError "BN254 scalar boundary changed in transport")
  for value in [modulus, modulus + 1] do
    unless (Aiur.Ixon.run (FieldEncoding.wide.putScalar modulus value)).toOption.isNone do
      throw (IO.userError "noncanonical wide field representative accepted")
  let instructions : List (Aiur.Execution.Instruction Nat) := [
    .literal 0 modulus, .guard [(0, modulus)] "guard", .branch [(0, modulus)] 0]
  for instruction in instructions do
    unless (Aiur.Ixon.run (Aiur.Execution.putInstructionWith
        (FieldEncoding.wide.putScalar modulus) id instruction)).toOption.isNone do
      throw (IO.userError "noncanonical wide bytecode constant accepted")
  let indices : List (Aiur.Execution.Instruction Nat) := [
    .literal (2^64) 0, .guard [(2^64, 0)] "guard", .branch [(0, 0)] (2^64)]
  for instruction in indices do
    unless (Aiur.Ixon.run (Aiur.Execution.putInstructionWith
        (FieldEncoding.wide.putScalar modulus) id instruction)).toOption.isNone do
      throw (IO.userError "wide scalar encoding widened a bytecode index")
  let pool ← IO.ofExcept (Aiur.Ixon.run do
    Aiur.Trace.withNodesWithEncoding .wide (modulus := some modulus) do
      let constant ← Aiur.Trace.NodePool.node 0 (modulus - 1) 0
      let varNode ← Aiur.Trace.NodePool.node 1 7 0
      let sum ← Aiur.Trace.NodePool.node 2 constant varNode
      nat sum)
  let decoded ← IO.ofExcept (decode (do
    let count ← getNat
    let constTag ← getU8
    let constant ← getWideNat
    let varTag ← getU8
    let varIndex ← getNat
    let sumTag ← getU8
    let left ← getNat
    let right ← getNat
    let root ← getNat
    return (count, constTag, constant, varTag, varIndex, sumTag, left, right, root)) pool)
  unless decoded == (3, 0, modulus - 1, 1, 7, 2, 2, 1, 2) do
    throw (IO.userError "wide trace node constants or narrow backreferences changed")
  for (tag, value) in [(0, modulus), (1, 2^64)] do
    unless (Aiur.Ixon.run do
        Aiur.Trace.withNodesWithEncoding .wide (modulus := some modulus) do
          discard (Aiur.Trace.NodePool.node tag value 0)).toOption.isNone do
      throw (IO.userError "invalid wide trace node accepted")
  IO.println "Passed canonical wide integer limb, truncation, modulus and field-boundary checks."

end AiurWideFieldEncodingTests
