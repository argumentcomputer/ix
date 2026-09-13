module
import Tests.Ixby.Common
import Ix.Ixby.Flock.Trace
import Ix.Ixby.Commitment

/-! Independent reference vectors for the byte-capable native Exec profile.
The append trace below is a Lean proof about the decoded reference machine.
It is not a native R1CS-to-reference refinement theorem. -/

namespace Tests.Ixby.Flock.Bytes

open Ix.Ixby
open Ix.Ixby.FlockBackend.ControlModel

private def profile : Profile := {
  limits := {
    functions := 1, constructors := 0, blocks := 2, locals := 4,
    operands := 3, continuations := 1, inputNodes := 3,
    natBits := 0, stringBytes := 0, byteArrayBytes := 65 }
  programBytes := 192, valueBytes := 192, valueDepth := 1, maxSteps := 3 }

private def b (data : Array UInt8) : Value := .scalar (.bytes data)
private def w (n : UInt32) : Value := .scalar (.word32 n)
private def g (n : Nat) : Value := .scalar (.field (Goldilocks.reduce n))
private def boolean (value : Bool) : Value := .scalar (.bool value)
private def data : Array UInt8 := (List.range 65).toArray.map fun i => (i * 73 + 19).toUInt8

private def program (op : Primitive) : Program := { functions := #[{
  arity := op.arity, blocks := #[
    ⟨op.arity, .letOp (.primitive op ((List.range op.arity).map Operand.local)) 1⟩,
    ⟨op.arity + 1, .ret (.local op.arity)⟩] }] }

private def artifacts (op : Primitive) (args : Array Value) (expected : Value) :
    Except Codec.Error (Codec.Bytes × Codec.Bytes × Codec.Bytes) := do
  let code ← Codec.encodeProgram profile (program op)
  let input ← Codec.encodeInput profile (program op) args
  let output ← Codec.encodeOutput profile (program op) expected
  return (code, input, output)

private def agrees (op : Primitive) (args : Array Value) (expected : Value) : Bool :=
  match artifacts op args expected with
  | .error _ => false
  | .ok (code, input, output) => match Codec.execute profile code input 3 with
    | .error _ => false
    | .ok execution => execution.output == expected && execution.outputBytes == output

private def digestWords (digest : Commitment.Digest) : List Nat :=
  (List.range 4).map fun word =>
    (List.range 8).foldl (fun n byte =>
      n + digest.bytes[word * 8 + byte]!.toNat * 2 ^ (8 * byte)) 0

private def sharedGolden : Bool :=
  match artifacts .blake3 #[b data] (b (Blake3.hash data)) with
  | .error _ => false
  | .ok (code, input, output) => match Commitment.ofArtifacts profile code input output with
    | .error _ => false
    | .ok statement => digestWords statement.digest ==
      [15935915575136097193, 10006034811852012573, 15504166987277840427, 12112749443985250975]

namespace AppendTrace

private def code : Program := { functions := #[{
  arity := 1, blocks := #[
    ⟨1, .letOp (.primitive .bytesAppend [.local 0, .literal (.bytes #[3])]) 1⟩,
    ⟨2, .ret (.local 1)⟩] }] }
private def initial : Frame := ⟨0, 0, #[b #[1, 2]]⟩
private def bound : Frame := append initial 1 (b #[1, 2, 3])

private theorem append_step : Step profile.limits code ⟨.eval initial, #[]⟩
    (.next ⟨.eval bound, #[]⟩) :=
  .bind (op := .primitive .bytesAppend [.local 0, .literal (.bytes #[3])])
    (declared := 1) (next := ⟨2, .ret (.local 1)⟩) rfl
    (.primitive (args := [b #[1, 2], b #[3]]) rfl rfl) rfl

private theorem return_step : Step profile.limits code ⟨.eval bound, #[]⟩
    (.next ⟨.ret (b #[1, 2, 3]), #[]⟩) :=
  .ret (operand := .local 1) (declared := 2) rfl rfl

private theorem three_steps : Trace profile.limits code 3
    (.active 3 ⟨.eval initial, #[]⟩) (.halted 0 (b #[1, 2, 3])) :=
  .cons (.next append_step)
    (.cons (.next return_step)
      (.cons (.halt (.halt (b #[1, 2, 3]))) (.nil _)))

example : Ix.Ixby.execute profile.limits code #[b #[1, 2]] 3 = .ok (b #[1, 2, 3]) :=
  three_steps.reference_execution (by
    simp only [Machine.decode, ActiveControl.decode, Array.map_empty]
    rfl)

example : Ix.Ixby.execute profile.limits code #[b #[1, 2]] 2 = .error .outOfFuel := rfl

end AppendTrace

private def checks : IO (List Check) := pure [
  ("Word32 to LE byte array", agrees .word32ToBytes #[w 0x89abcdef] (b #[0xef, 0xcd, 0xab, 0x89])),
  ("LE byte array to Word32", agrees .bytesToWord32 #[b #[0xef, 0xcd, 0xab, 0x89]] (w 0x89abcdef)),
  ("field to exact LE bytes", agrees .fieldToBytes #[g 0xffffffff00000000] (b #[0,0,0,0,255,255,255,255])),
  ("exact canonical field bytes", agrees .bytesToField #[b #[0,0,0,0,255,255,255,255]] (g 0xffffffff00000000)),
  ("byte length 65", agrees .bytesLength #[b data] (w 65)),
  ("last byte past a compression boundary", agrees .bytesGet #[b data, w 64] (w data[64]!.toUInt32)),
  ("append fills the admitted array", agrees .bytesAppend #[b (data.extract 0 31), b (data.extract 31 65)] (b data)),
  ("slice crosses packed-word boundaries", agrees .bytesSlice #[b data, w 15, w 18] (b (data.extract 15 33))),
  ("empty slice at the end", agrees .bytesSlice #[b data, w 65, w 0] (b #[])),
  ("equal complete bytes", agrees .bytesEq #[b data, b data] (boolean true)),
  ("length distinguishes zero from empty", agrees .bytesEq #[b #[0], b #[]] (boolean false)),
  ("pure multi-block guest BLAKE3", agrees .blake3 #[b data] (b (Blake3.hash data))),
  ("pure empty guest BLAKE3", agrees .blake3 #[b #[]] (b (Blake3.hash #[]))),
  ("shared native byte-profile statement golden", sharedGolden)
]

public def suite : IO UInt32 := runChecks "ixby-flock-bytes" checks

end Tests.Ixby.Flock.Bytes
