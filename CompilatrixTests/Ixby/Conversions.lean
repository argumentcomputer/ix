import Compilatrix.Ixby.Binary
import Compilatrix.Tools.Check

namespace CompilatrixTests.Ixby.Conversions

open Ix.Ixby Compilatrix.Ixby Compilatrix.Tools.Check

-- These examples reduce through the reference evaluator in the Lean kernel.
example : Primitive.natToWord32.eval { natBits := 0 } [.scalar (.nat 0)] =
    .ok (.scalar (.word32 0)) := rfl
example : Primitive.word32ToNat.eval { natBits := 0 } [.scalar (.word32 0)] =
    .ok (.scalar (.nat 0)) := rfl
example : Primitive.natToWord32.eval { natBits := 66 } [.scalar (.nat (2 ^ 65 + 37))] =
    .ok (.scalar (.word32 37)) := rfl
example : Primitive.natToWord32.eval { natBits := 65 } [.scalar (.nat (2 ^ 65 + 37))] =
    .error (.limit .natBits) := rfl
example : Primitive.word32ToNat.eval { natBits := 32 } [.scalar (.word32 4294967295)] =
    .ok (.scalar (.nat 4294967295)) := rfl
example : Primitive.word32ToNat.eval { natBits := 31 } [.scalar (.word32 4294967295)] =
    .error (.limit .natBits) := rfl

private def same [BEq α] [BEq β] : Except α β → Except α β → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

private def unary (primitive : Primitive) (args : List Operand := [.local 0]) : Program := {
  functions := #[{ arity := 1, blocks := #[
    ⟨1, .letOp (.primitive primitive args) 1⟩,
    ⟨2, .ret (.local 1)⟩] }] }

private def rejected {α : Type} (result : Except Binary.Error α) (error : Binary.Error) : IO Unit := do
  match result with
  | .error actual => need (actual == error) s!"conversion codec rejection: {reprStr actual}"
  | .ok _ => throw (IO.userError "conversion codec accepted invalid input")

private def eval (primitive : Primitive) (bits : Nat) (args : List Value)
    (expected : Except Error Value) : IO Unit := do
  need (same (primitive.eval { natBits := bits } args) expected)
    s!"conversion evaluation differs: {reprStr primitive}, bits={bits}, args={reprStr args}"

/-- A fixed program for independent native execution and proof integration. -/
def fixture : Binary.Artifact := {
  limits := {
    functions := 1, constructors := 0, blocks := 6, locals := 6,
    operands := 2, continuations := 0, inputNodes := 8, natBits := 128,
    stringBytes := 0, byteArrayBytes := 64 }
  maxSteps := 7
  program := { functions := #[{ arity := 1, blocks := #[
    ⟨1, .letOp (.primitive .natToWord32 [.local 0]) 1⟩,
    ⟨2, .letOp (.primitive .word32ToNat [.local 1]) 2⟩,
    ⟨3, .letOp (.primitive .natAdd [.local 2, .literal (.nat 5)]) 3⟩,
    ⟨4, .letOp (.primitive .natToWord32 [.local 3]) 4⟩,
    ⟨5, .letOp (.primitive .word32ToBytes [.local 4]) 5⟩,
    ⟨6, .ret (.local 5)⟩] }] } }

def run (directory : Option System.FilePath := none) : IO Unit := do
  need (Binary.primitives.size == 47) "functional opcode inventory differs"
  need (Binary.primitiveOpcode .natToWord32 == 45 &&
    Binary.primitiveOpcode .word32ToNat == 46) "conversion opcodes differ"
  for (n, low) in #[(0, 0), (1, 1), (2 ^ 32 - 1, 4294967295), (2 ^ 32, 0),
      (2 ^ 65 + 37, 37), (2 ^ 4096 - 1, 4294967295)] do
    eval .natToWord32 4096 [.scalar (.nat n)] (.ok (.scalar (.word32 low.toUInt32)))
  for n in #[0, 1, 2 ^ 32 - 1] do
    eval .word32ToNat 32 [.scalar (.word32 n.toUInt32)] (.ok (.scalar (.nat n)))
  for bits in #[0, 1, 31, 32, 65, 128, 4096] do
    eval .natToWord32 bits [.scalar (.nat (2 ^ bits))] (.error (.limit .natBits))
    eval .natToWord32 bits [.scalar (.nat 0)] (.ok (.scalar (.word32 0)))
    eval .word32ToNat bits [.scalar (.word32 0)] (.ok (.scalar (.nat 0)))
  eval .word32ToNat 31 [.scalar (.word32 0xffffffff)] (.error (.limit .natBits))
  for primitive in #[Primitive.natToWord32, .word32ToNat] do
    eval primitive 0 [] (.error (.arityMismatch 1 0))
    -- Arity rejection precedes scalar validation.
    eval primitive 0 [.scalar (.nat 1), .erased] (.error (.arityMismatch 1 2))
    for value in #[Value.erased, .pap 0 #[], .ctor ⟨0, 0, 0⟩ #[],
        .scalar (.str ""), .scalar (.bool false), .scalar (.field 0),
        .scalar (.extField ⟨0, 0⟩), .scalar (.bytes #[])] do
      eval primitive 4096 [value] (.error (.primitiveType primitive))
    let image : Binary.Artifact := { fixture with program := unary primitive }
    let bytes ← checked (Binary.encode image |>.mapError reprStr)
    need (bytes.extract 0 12 == #[0x49, 0x58, 0x42, 0x46, 1, 0, 0, 0, 1, 0, 0, 0])
      "IXBF program header differs"
    rejected (Binary.decode (bytes.set! 8 0)) .version
    for count in #[0, 2] do
      let bad := unary primitive (List.replicate count (.local 0))
      rejected (Binary.encode { image with program := bad }) (.reference (.invalidInstruction 0 0))
      -- Serialize without the encoder's admission check to exercise decoder validation.
      let badBytes ← checked (Binary.Internal.encode
        (Binary.Internal.writeArtifact { image with program := bad }) |>.mapError reprStr)
      rejected (Binary.decode badBytes) (.reference (.invalidInstruction 0 0))
    need (!primitive.cryptoOpcode.isSome) "legacy IXBY profile admitted conversion"
  eval .natToWord32 4096 [.scalar (.word32 0)] (.error (.primitiveType .natToWord32))
  eval .word32ToNat 4096 [.scalar (.nat 0)] (.error (.primitiveType .word32ToNat))
  eval .word32ToNat 0 [.scalar (.nat 1)] (.error (.limit .natBits))
  for opcode in [47:256] do
    rejected (Binary.Internal.decode {} #[1, opcode.toUInt8, 1, 0, 0]
      (Binary.Internal.readOp {})) (.tag opcode)
  for (primitive, bytes, slot) in #[(Primitive.natToWord32, #[1, 45, 1, 0, 0], 0),
      (.word32ToNat, #[1, 46, 1, 0, 1], 1)] do
    need (same (Binary.Internal.encode (Binary.Internal.writeOp (.primitive primitive [.local slot]))) (.ok bytes))
      "conversion operation bytes differ"
    need (same (Binary.Internal.decode {} bytes (Binary.Internal.readOp {}))
      (.ok (.primitive primitive [.local slot]))) "conversion operation decoding differs"
  let input ← checked (Binary.encodeInput fixture #[.scalar (.nat (2 ^ 65 + 37))] |>.mapError reprStr)
  need (input == #[0x49, 0x58, 0x46, 0x49, 1, 0, 0, 0, 0, 0, 0, 0,
    1, 0, 0, 0xa5, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 4])
    "independent IXFI bytes differ"
  let expected : Value := .scalar (.bytes #[42, 0, 0, 0])
  let output ← checked (Binary.encodeOutput fixture expected |>.mapError reprStr)
  need (output == #[0x49, 0x58, 0x46, 0x4f, 1, 0, 0, 0, 0, 0, 0, 0, 0, 6, 4, 42, 0, 0, 0])
    "independent IXFO bytes differ"
  rejected (Binary.decodeInput fixture (input.set! 8 1)) .version
  rejected (Binary.decodeOutput fixture (output.set! 8 1)) .version
  let program ← checked (Binary.encode fixture |>.mapError reprStr)
  let independent ← checked (unhex
    "4958424601000000010000000100060602000880010040070000010100060100012d010000010200012e0100010203000100020002010005030400012d01000304050001150100040506010005")
  need (program == independent.data) "independent IXBF conversion program differs"
  let loaded ← checked (Binary.decode program |>.mapError reprStr)
  let inputs ← checked (Binary.decodeInput loaded.value input |>.mapError reprStr)
  need (same (execute loaded.value.limits loaded.value.program inputs.value loaded.value.maxSteps) (.ok expected))
    "seven-step conversion fixture differs"
  need (same (execute loaded.value.limits loaded.value.program inputs.value (loaded.value.maxSteps - 1))
    (.error .outOfFuel)) "conversion fixture accepted insufficient fuel"
  if let some directory := directory then
    IO.FS.writeBinFile (directory / "conversions.ixby") ⟨program⟩
    IO.FS.writeBinFile (directory / "conversions.ixbi") ⟨input⟩
    IO.FS.writeBinFile (directory / "conversions.ixbo") ⟨output⟩
  IO.println "conversion primitives: kernel boundaries, scalar limits, types, unary arity, 47 opcodes, exact headers/I/O and execution passed"

end CompilatrixTests.Ixby.Conversions
