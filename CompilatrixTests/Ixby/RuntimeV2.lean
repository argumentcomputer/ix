import Compilatrix.Ixby.Binary
import Compilatrix.Tools.Check

/-! Revision-two conformance against independent artifact bytes and source
sequence oracles. Builders are admitted only within reference execution. -/

namespace CompilatrixTests.Ixby.RuntimeV2

open Ix.Ixby Compilatrix.Ixby Compilatrix.Tools.Check

private def same [BEq α] [BEq β] : Except α β → Except α β → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

private def n (value : Nat) : Value := .scalar (.nat value)
private def bytes (value : Array UInt8) : Value := .scalar (.bytes value)

private def expect (op : Primitive) (args : List Value) (result : Except Error Value)
    (limits : Limits := {}) : IO Unit :=
  need (same (op.eval limits args) result) s!"runtime v2 primitive: {reprStr op}: {reprStr args}"

def firstChunk : Array UInt8 := (Array.range 31).map Nat.toUInt8
def secondChunk : Array UInt8 := (Array.range 34).map fun i => (i * 7 + 131).toUInt8

/-- Assembled independently from the upstream generator's fixed wire image. -/
def fixture : Binary.Artifact := {
  limits := {
    functions := 1, constructors := 0, blocks := 14, locals := 14,
    operands := 3, continuations := 0, inputNodes := 8, natBits := 128,
    stringBytes := 0, byteArrayBytes := 128 }
  maxSteps := 15
  program := { functions := #[{ arity := 1, blocks := #[
    ⟨1, .letOp (.primitive .arrayEmpty []) 1⟩,
    ⟨2, .letOp (.primitive .arrayPush [.local 1, .literal (.nat 37)]) 2⟩,
    ⟨3, .letOp (.primitive .arraySet [.local 0, .literal (.nat 1), .local 2]) 3⟩,
    ⟨4, .letOp (.primitive .arrayGet [.local 3, .literal (.nat 1)]) 4⟩,
    ⟨5, .letOp (.primitive .arrayLength [.local 4]) 5⟩,
    ⟨6, .letOp (.primitive .natToField [.literal (.nat (2 ^ 128 - 1))]) 6⟩,
    ⟨7, .letOp (.primitive .fieldToNat [.local 6]) 7⟩,
    ⟨8, .letOp (.primitive .byteBuilderEmpty []) 8⟩,
    ⟨9, .letOp (.primitive .byteBuilderAppend [.local 8, .literal (.bytes firstChunk)]) 9⟩,
    ⟨10, .letOp (.primitive .byteBuilderAppend [.local 9, .literal (.bytes secondChunk)]) 10⟩,
    ⟨11, .letOp (.primitive .byteBuilderLength [.local 10]) 11⟩,
    ⟨12, .letOp (.primitive .byteBuilderFreeze [.local 10]) 12⟩,
    ⟨13, .letOp (.primitive .bytesSlice [.local 12, .literal (.word32 1),
      .literal (.word32 63)]) 13⟩,
    ⟨14, .ret (.local 13)⟩] }] } }

def fixtureInput : Array Value := #[.array #[n 7, n 9]]
def fixtureOutput : Value := bytes ((firstChunk ++ secondChunk).extract 1 64)

private def independentProgram : String :=
  "49584246010000000200000001000e0e03000880010080010f00000101000e0100013100010200013502000101002502030001340300000100010002030400013302000301000104050001320100040506000130010100ffffffffffffffffffffffffffffffffffff03060700012f010006070800013600080900013702000801061f000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e090a000137020009010622838a91989fa6adb4bbc2c9d0d7dee5ecf3fa01080f161d242b323940474e555c636a0a0b00013901000a0b0c00013801000a0c0d00012a03000c01030100000001033f0000000d0e01000d"

private def rejectInternal {α : Type} (value : Except Binary.Error α) : IO Unit := do
  match value with
  | .error .internalValue => pure ()
  | _ => throw (IO.userError "serializable builder accepted or rejected for the wrong reason")

def run (directory : Option System.FilePath := none) : IO Unit := do
  need (Binary.primitives == Codec.primitives) "compiler and upstream opcode tables differ"
  for (op, opcode, arity) in #[(Primitive.fieldToNat, 47, 1), (.natToField, 48, 1),
      (.arrayEmpty, 49, 0), (.arrayLength, 50, 1), (.arrayGet, 51, 2),
      (.arraySet, 52, 3), (.arrayPush, 53, 2), (.byteBuilderEmpty, 54, 0),
      (.byteBuilderAppend, 55, 2), (.byteBuilderFreeze, 56, 1), (.byteBuilderLength, 57, 1)] do
    need (Binary.primitiveOpcode op == opcode && op.arity == arity) "runtime v2 opcode/arity"
    expect op (List.replicate (arity + 1) .erased) (.error (.arityMismatch arity (arity + 1)))
    if arity > 0 then
      expect op (List.replicate arity .erased) (.error (.primitiveType op))
  for value in #[0, 1, goldilocksModulus - 1, goldilocksModulus,
      goldilocksModulus + 1, 2 ^ 128 - 1, 2 ^ 4096 - 1] do
    expect .natToField [n value] (.ok (.scalar (.field (Goldilocks.reduce value)))) { natBits := 4096 }
  expect .natToField [n (2 ^ 128)] (.error (.limit .natBits)) { natBits := 128 }
  expect .fieldToNat [.scalar (.field (Goldilocks.reduce (goldilocksModulus - 1)))]
    (.ok (n (goldilocksModulus - 1))) { natBits := 64 }
  expect .fieldToNat [.scalar (.field (Goldilocks.reduce (goldilocksModulus - 1)))]
    (.error (.limit .natBits)) { natBits := 63 }
  expect .fieldToNat [.scalar (.field 0)] (.ok (n 0)) { natBits := 0 }
  expect .natToField [.scalar (.field 0)] (.error (.primitiveType .natToField))
  expect .fieldToNat [n 0] (.error (.primitiveType .fieldToNat))
  expect .arrayEmpty [] (.ok (.array #[]))
  let original : Array Value := #[n 7, .array #[n 9, .erased]]
  let updated : Array Value := #[n 7, .array #[n 37]]
  expect .arraySet [.array original, n 1, .array #[n 37]] (.ok (.array updated))
  expect .arrayGet [.array original, n 1] (.ok (.array #[n 9, .erased]))
  expect .arrayGet [.array updated, n 1] (.ok (.array #[n 37]))
  expect .arrayPush [.array original, .array updated] (.ok (.array (original.push (.array updated))))
  for index in #[2, 2 ^ 32, 2 ^ 128] do
    expect .arrayGet [.array original, n index] (.error (.primitiveValue .arrayGet))
      { natBits := 129 }
    expect .arraySet [.array original, n index, .erased] (.error (.primitiveValue .arraySet))
      { natBits := 129 }
  expect .arrayGet [.array original, n (2 ^ 128)] (.error (.limit .natBits)) { natBits := 128 }
  expect .arrayLength [.array original] (.error (.limit .natBits)) { natBits := 1 }
  -- Array length is independent of the operand-vector capacity.
  expect .arrayLength [.array (Array.replicate 65 .erased)] (.ok (n 65)) { operands := 1 }
  expect .byteBuilderEmpty [] (.ok (.byteBuilder #[])) { byteArrayBytes := 0 }
  let joined := firstChunk ++ secondChunk
  expect .byteBuilderAppend [.byteBuilder firstChunk, bytes secondChunk] (.ok (.byteBuilder joined))
  expect .byteBuilderAppend [.byteBuilder firstChunk, bytes #[]] (.ok (.byteBuilder firstChunk))
  expect .byteBuilderFreeze [.byteBuilder firstChunk] (.ok (bytes firstChunk))
  expect .byteBuilderFreeze [.byteBuilder joined] (.ok (bytes joined))
  expect .byteBuilderLength [.byteBuilder joined] (.ok (n 65))
  expect .byteBuilderLength [.byteBuilder joined] (.error (.limit .natBits)) { natBits := 6 }
  expect .byteBuilderAppend [.byteBuilder firstChunk, bytes secondChunk]
    (.error (.limit .byteArrayBytes)) { byteArrayBytes := 64 }
  expect .byteBuilderFreeze [.byteBuilder firstChunk]
    (.error (.limit .byteArrayBytes)) { byteArrayBytes := 30 }
  expect .byteBuilderAppend [.byteBuilder firstChunk, bytes #[]]
    (.error (.limit .byteArrayBytes)) { byteArrayBytes := 30 }
  expect .bytesSlice [bytes joined, .scalar (.word32 1), .scalar (.word32 63)] (.ok fixtureOutput)
  expect .bytesSlice [bytes joined, .scalar (.word32 0xffffffff), .scalar (.word32 2)]
    (.error (.primitiveValue .bytesSlice))
  let id : CtorId := { block := 1, member := 0, tag := 0 }
  let identity : Binary.Artifact := { fixture with
    limits := {}, maxSteps := 10,
    program := { constructors := #[⟨id, 1⟩], functions := #[
      { arity := 1, blocks := #[⟨1, .ret (.local 0)⟩] },
      { arity := 2, blocks := #[⟨2, .ret (.local 0)⟩] }] } }
  for value in #[Value.byteBuilder #[], .array #[.array #[.byteBuilder #[1]]],
      .ctor id #[.array #[.byteBuilder #[1]]], .pap 1 #[.array #[.byteBuilder #[1]]]] do
    rejectInternal (Binary.encodeInput identity #[value])
    rejectInternal (Binary.encodeOutput identity value)
  let program ← checked (Binary.encode fixture |>.mapError reprStr)
  let input ← checked (Binary.encodeInput fixture fixtureInput |>.mapError reprStr)
  let output ← checked (Binary.encodeOutput fixture fixtureOutput |>.mapError reprStr)
  need (program == (← checked (unhex independentProgram)).data) "independent runtime v2 program"
  need (input == (← checked (unhex "495846490100000002000000010402000007000009")).data)
    "independent runtime v2 input"
  need (output == (← checked (unhex
    "4958464f010000000200000000063f0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e838a91989fa6adb4bbc2c9d0d7dee5ecf3fa01080f161d242b323940474e555c63")).data)
    "independent runtime v2 output"
  let profile : Profile := { limits := fixture.limits, maxSteps := fixture.maxSteps }
  let profileBytes ← checked (Codec.encodeProfile profile |>.mapError reprStr)
  need (profileBytes.size == 184 && profileBytes.extract 0 16 ==
    #[73, 88, 70, 80, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0]) "IXFP header/size"
  let upstreamProgram ← checked (Codec.encodeProgram profile fixture.program |>.mapError reprStr)
  need (upstreamProgram == program) "compiler and upstream program bytes differ"
  let upstreamInput ← checked (Codec.encodeInput profile fixture.program fixtureInput |>.mapError reprStr)
  need (upstreamInput == input) "compiler and upstream input bytes differ"
  let upstreamOutput ← checked (Codec.encodeOutput profile fixture.program fixtureOutput |>.mapError reprStr)
  need (upstreamOutput == output) "compiler and upstream output bytes differ"
  let decoded ← checked (Binary.decode program |>.mapError reprStr)
  let loaded ← checked (Binary.decodeInput decoded.value input |>.mapError reprStr)
  need (same (execute fixture.limits decoded.value.program loaded.value 15) (.ok fixtureOutput))
    "runtime v2 fixture execution"
  need (same (execute fixture.limits decoded.value.program loaded.value 14) (.error .outOfFuel))
    "runtime v2 logical fuel"
  for old in #[0, 1] do
    need (same (Binary.decode program |>.map (·.value.maxSteps)) (.ok 15)) "current revision rejected"
    need (match Binary.decode (program.set! 8 old) with | .error .version => true | _ => false)
      "old program revision admitted"
    need (match Binary.decodeInput fixture (input.set! 8 old) with | .error .version => true | _ => false)
      "old input revision admitted"
    need (match Binary.decodeOutput fixture (output.set! 8 old) with | .error .version => true | _ => false)
      "old output revision admitted"
  if let some directory := directory then
    IO.FS.createDirAll (directory / "runtime-v2")
    for (name, data) in [("program.ixby", program), ("input.ixbi", input),
        ("output.ixbo", output), ("profile.ixfp", profileBytes)] do
      IO.FS.writeBinFile (directory / "runtime-v2" / name) ⟨data⟩
  IO.println "runtime v2: all 11 new primitives, persistent aliases, checked slices, builder rejection, independent artifacts and 15-step execution passed"

end CompilatrixTests.Ixby.RuntimeV2
