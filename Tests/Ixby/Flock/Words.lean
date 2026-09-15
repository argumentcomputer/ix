module
import Tests.Ixby.Common
import Ix.Ixby.Flock.Trace
import Ix.Ixby.Commitment

/-! Pure reference vectors for the complete native crypto-v0 primitive set.
The reference trace is kernel-checked; it does not assert refinement of the
native Boolean matrices or certification of a compiled Stage 2 guest. -/

namespace Tests.Ixby.Flock.Words

open Ix.Ixby
open Ix.Ixby.FlockBackend.ControlModel

private def profile : Profile := {
  limits := {
    functions := 1, constructors := 0, blocks := 2, locals := 4,
    operands := 3, continuations := 1, inputNodes := 3,
    natBits := 0, stringBytes := 0, byteArrayBytes := 65 }
  programBytes := 192, valueBytes := 192, valueDepth := 1, maxSteps := 3 }

private def w (n : UInt32) : Value := .scalar (.word32 n)
private def b (data : Array UInt8) : Value := .scalar (.bytes data)

private def program (op : Primitive) : Program := { functions := #[{
  arity := 2, blocks := #[
    ⟨2, .letOp (.primitive op [.local 0, .local 1]) 1⟩,
    ⟨3, .ret (.local 2)⟩] }] }

private def artifacts (p : Profile) (code : Program) (args : Array Value) (expected : Value) :
    Except Codec.Error (Codec.Bytes × Codec.Bytes × Codec.Bytes) := do
  let codeBytes ← Codec.encodeProgram p code
  let input ← Codec.encodeInput p code args
  let output ← Codec.encodeOutput p code expected
  return (codeBytes, input, output)

private def agrees (p : Profile) (code : Program) (args : Array Value) (expected : Value) : Bool :=
  match artifacts p code args expected with
  | .error _ => false
  | .ok (code, input, output) => match Codec.execute p code input p.maxSteps with
    | .error _ => false
    | .ok execution => execution.output == expected && execution.outputBytes == output

private def word (op : Primitive) (a count expected : UInt32) : Bool :=
  agrees profile (program op) #[w a, w count] (w expected)

private def pipelineProfile : Profile := {
  limits := {
    functions := 1, constructors := 0, blocks := 6, locals := 7,
    operands := 2, continuations := 1, inputNodes := 2,
    natBits := 0, stringBytes := 0, byteArrayBytes := 33 }
  programBytes := 256, valueBytes := 128, valueDepth := 1, maxSteps := 7 }

private def pipeline : Program := { functions := #[{
  arity := 2, blocks := #[
    ⟨2, .letOp (.primitive .word32Mul [.local 0, .local 1]) 1⟩,
    ⟨3, .letOp (.primitive .word32Sub [.local 2, .literal (.word32 0x01020304)]) 2⟩,
    ⟨4, .letOp (.primitive .word32Rotr [.local 3, .literal (.word32 33)]) 3⟩,
    ⟨5, .letOp (.primitive .word32ToBytes [.local 4]) 4⟩,
    ⟨6, .letOp (.primitive .blake3 [.local 5]) 5⟩,
    ⟨7, .ret (.local 6)⟩] }] }

-- 0x89abcdef * 17 - 0x01020304 = 0x2366a9db modulo 2^32;
-- rotating right by 33 gives 0x91b354ed, then exact LE bytes are hashed.
private def pipelineOutput : Value := b (Blake3.hash #[0xed, 0x54, 0xb3, 0x91])

private def digestWords (digest : Commitment.Digest) : List Nat :=
  (List.range 4).map fun word =>
    (List.range 8).foldl (fun n byte =>
      n + digest.bytes[word * 8 + byte]!.toNat * 2 ^ (8 * byte)) 0

private def sharedGolden : Bool :=
  match artifacts pipelineProfile pipeline #[w 0x89abcdef, w 17] pipelineOutput with
  | .error _ => false
  | .ok (code, input, output) => match Commitment.ofArtifacts pipelineProfile code input output with
    | .error _ => false
    | .ok statement => digestWords statement.digest ==
      [14389074313148614759, 10767949013559195315, 6352501931959032028, 13433562327032146821]

namespace MultiplyTrace

private def code : Program := program .word32Mul
private def initial : Frame := ⟨0, 0, #[w 0xffffffff, w 0xffffffff]⟩
private def bound : Frame := append initial 1 (w 1)

private theorem multiply_step : Step profile.limits code ⟨.eval initial, #[]⟩
    (.next ⟨.eval bound, #[]⟩) :=
  .bind (op := .primitive .word32Mul [.local 0, .local 1])
    (declared := 2) (next := ⟨3, .ret (.local 2)⟩) rfl
    (.primitive (args := [w 0xffffffff, w 0xffffffff]) rfl rfl) rfl

private theorem return_step : Step profile.limits code ⟨.eval bound, #[]⟩
    (.next ⟨.ret (w 1), #[]⟩) :=
  .ret (operand := .local 2) (declared := 3) rfl rfl

private theorem three_steps : Trace profile.limits code 3
    (.active 3 ⟨.eval initial, #[]⟩) (.halted 0 (w 1)) :=
  .cons (.next multiply_step)
    (.cons (.next return_step)
      (.cons (.halt (.halt (w 1))) (.nil _)))

example : Ix.Ixby.execute profile.limits code #[w 0xffffffff, w 0xffffffff] 3 = .ok (w 1) :=
  three_steps.reference_execution (by
    simp only [Machine.decode, ActiveControl.decode, Array.map_empty]
    rfl)

example : Ix.Ixby.execute profile.limits code #[w 0xffffffff, w 0xffffffff] 2 = .error .outOfFuel := rfl

end MultiplyTrace

private def checks : IO (List Check) := pure [
  ("wrapping word subtraction", word .word32Sub 0 1 0xffffffff),
  ("equal word subtraction", word .word32Sub 0xffffffff 0xffffffff 0),
  ("full multiplication carry", word .word32Mul 0xffffffff 0xffffffff 1),
  ("multiplication discards bit 32", word .word32Mul 0x10000 0x10000 0),
  ("mixed multiplication", word .word32Mul 0x89abcdef 17 0x2468acdf),
  ("left shift zero", word .word32Shl 0x89abcdef 0 0x89abcdef),
  ("left shift 31", word .word32Shl 0x89abcdef 31 0x80000000),
  ("left shift 32 is zero", word .word32Shl 0x89abcdef 32 0),
  ("left shift 33 is not modulo 32", word .word32Shl 0x89abcdef 33 0),
  ("left shift maximum count", word .word32Shl 0x89abcdef 0xffffffff 0),
  ("right shift zero", word .word32Shr 0x89abcdef 0 0x89abcdef),
  ("right shift 31", word .word32Shr 0x89abcdef 31 1),
  ("right shift 32 is zero", word .word32Shr 0x89abcdef 32 0),
  ("right shift full high count bit", word .word32Shr 0x89abcdef 0x80000000 0),
  ("rotate zero", word .word32Rotr 0x89abcdef 0 0x89abcdef),
  ("rotate 31", word .word32Rotr 0x89abcdef 31 0x13579bdf),
  ("rotate 32", word .word32Rotr 0x89abcdef 32 0x89abcdef),
  ("rotate 33 wraps modulo 32", word .word32Rotr 0x89abcdef 33 0xc4d5e6f7),
  ("rotate maximum count", word .word32Rotr 0x89abcdef 0xffffffff 0x13579bdf),
  ("word arithmetic to canonical bytes to guest hash", agrees pipelineProfile pipeline #[w 0x89abcdef, w 17] pipelineOutput),
  ("shared native crypto pipeline statement golden", sharedGolden)
]

public def suite : IO UInt32 := runChecks "ixby-flock-words" checks

end Tests.Ixby.Flock.Words
