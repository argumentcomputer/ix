import Compilatrix.Ixby.Binary
import Compilatrix.Tools.Check
import CompilatrixTests.Ixby.Conversions
import CompilatrixTests.Ixby.RuntimeV2
import CompilatrixTests.Ixby.Chunked

open Compilatrix.Tools.Check Compilatrix.Ixby Ix.Ixby

private def artifact (program : Program) : Binary.Artifact :=
  { limits := { natBits := 4096, byteArrayBytes := 16777216 },
    maxSteps := 2 ^ 70 + 17, program }

private def loaded (original : Binary.Artifact) (directory : Option System.FilePath)
    (name : Nat) : IO Binary.Artifact := do
  let bytes ← checked (Binary.encode original |>.mapError reprStr)
  let decoded ← checked (Binary.decode bytes |>.mapError reprStr)
  need (decoded.value == original) "binary decoding changed the artifact"
  if let some directory := directory then
    IO.FS.writeBinFile (directory / s!"{name}.ixby") ⟨bytes⟩
  return decoded.value

private def rejects {α : Type} (result : Except Binary.Error α) (expected : Binary.Error) : IO Unit := do
  match result with
  | .ok _ => throw (IO.userError "malformed binary accepted")
  | .error actual => need (actual == expected) s!"wrong binary rejection: {reprStr actual}"

private def failed {α : Type} : Except Binary.Error α → Bool
  | .error _ => true
  | .ok _ => false

private def primArgs (p : Primitive) : List Value :=
  match p with
  | .arrayEmpty | .byteBuilderEmpty => []
  | .arrayLength => [.array #[.erased, .scalar (.nat 7)]]
  | .arrayGet => [.array #[.erased, .array #[.scalar (.nat 7)]], .scalar (.nat 1)]
  | .arraySet => [.array #[.erased], .scalar (.nat 0), .array #[.scalar (.nat 7)]]
  | .arrayPush => [.array #[], .array #[.scalar (.nat 7)]]
  | .byteBuilderAppend => [.byteBuilder #[0, 255], .scalar (.bytes #[128, 1])]
  | .byteBuilderFreeze | .byteBuilderLength => [.byteBuilder #[0, 255, 128, 1]]
  | p => (scalarArgs p).map Value.scalar
where scalarArgs (p : Primitive) : List Scalar :=
  let n := Scalar.nat (2 ^ 80 + 127)
  let w := Scalar.word32 0xfedcba98
  let f := Scalar.field (Goldilocks.reduce (goldilocksModulus - 3))
  let e := Scalar.extField ⟨Goldilocks.reduce 19, Goldilocks.reduce 23⟩
  match p with
  | .natToWord32 => [n]
  | .word32ToNat => [w]
  | .fieldToNat => [f]
  | .natToField => [n]
  | .natAdd | .natSub | .natMul | .natDiv | .natMod | .natEq | .natLt => [n, .nat 0]
  | .strAppend | .strEq => [.str "a☃é", .str "β"]
  | .strLength => [.str "a☃é"]
  | .word32ToBytes | .word32ToField => [w]
  | .bytesToWord32 => [.bytes #[0x98, 0xba, 0xdc, 0xfe]]
  | .fieldAdd | .fieldSub | .fieldMul | .fieldEq | .extPack => [f, .field 7]
  | .fieldInverse | .fieldToBytes => [f]
  | .bytesToField => [.bytes (bytesLE 8 (goldilocksModulus - 1))]
  | .extAdd | .extSub | .extMul | .extEq => [e, .extField ⟨3, 5⟩]
  | .extInverse | .extFst | .extSnd => [e]
  | .bytesLength | .blake3 => [.bytes #[0, 255, 128, 1]]
  | .bytesGet => [.bytes #[0, 255, 128, 1], .word32 2]
  | .bytesAppend | .bytesEq => [.bytes #[0, 255], .bytes #[128, 1]]
  | .bytesSlice => [.bytes #[0, 255, 128, 1], .word32 1, .word32 2]
  | _ => [w, .word32 5]

private def execute (image : Binary.Artifact) (args : Array Value) : IO Value := do
  let reference ← checked (Ix.Ixby.execute image.limits image.program args 10000 |>.mapError reprStr)
  let chunked ← checked (Runtime.Chunked.execute image.limits image.program args 10000 |>.mapError reprStr)
  need (reference == chunked) "chunked decoded artifact differs from the reference"
  return reference

private def function (arity : Nat) (blocks : Array (Nat × Instr)) : Function :=
  { arity, blocks := blocks.map fun (locals, instruction) => { locals, instruction } }

def main (args : List String) : IO UInt32 := cli "check-ixby-binary" do
  let directory ← match args with
    | [] => pure none
    | [path] => pure (some (System.FilePath.mk path))
    | _ => throw (IO.userError "usage: check-ixby-binary [export-directory]")
  if let some directory := directory then IO.FS.createDirAll directory
  CompilatrixTests.Ixby.Conversions.run directory
  CompilatrixTests.Ixby.RuntimeV2.run directory
  discard <| CompilatrixTests.Ixby.Chunked.run
  let load (name : Nat) (original : Binary.Artifact) := loaded original directory name
  let mut count := 0
  for scalar in #[Scalar.nat 0, .nat 127, .nat 128, .nat 16383, .nat 16384,
      .nat (2 ^ 80 + 17), .str "", .str "a☃é", .bool false, .bool true,
      .word32 0xffffffff, .field 0, .field (Goldilocks.reduce (goldilocksModulus - 1)),
      .extField ⟨3, 5⟩, .bytes #[], .bytes #[0, 255, 128, 1]] do
    let fn : Function := {
      arity := 0
      blocks := #[{ locals := 0, instruction := .ret (.literal scalar) }] }
    let original := artifact { functions := #[fn] }
    let decoded ← load count original
    need ((← execute decoded #[]) == .scalar scalar) "scalar execution changed"
    count := count + 1
  for primitive in Binary.primitives do
    let args := primArgs primitive
    let fn : Function := {
      arity := args.length
      blocks := #[
        { locals := args.length, instruction := .letOp
            (.primitive primitive ((List.range args.length).map Operand.local)) 1 },
        { locals := args.length + 1, instruction := .ret (.local args.length) }] }
    let original := artifact { functions := #[fn] }
    let decoded ← load count original
    let expected ← checked (primitive.eval original.limits args |>.mapError reprStr)
    need ((← execute decoded args.toArray) == expected) s!"primitive execution changed: {reprStr primitive}"
    count := count + 1
  let natCase : Function := {
    arity := 1
    blocks := #[
      { locals := 1, instruction := .caseNat (.local 0) 1 2 },
      { locals := 1, instruction := .ret (.literal (.nat 99)) },
      { locals := 2, instruction := .ret (.local 1) }] }
  let image ← load count (artifact { functions := #[natCase] })
  for (n, expected) in #[(0, 99), (1, 0), (2 ^ 80, 2 ^ 80 - 1)] do
    need ((← execute image #[.scalar (.nat n)]) == .scalar (.nat expected)) "Nat branch changed"
    count := count + 1
  let controlId : CtorId := { block := 987, member := 2 ^ 40, tag := 2 ^ 70 }
  let controls := #[
    function 2 #[
      (2, .letOp (.construct 0 [.local 0, .local 1]) 1),
      (3, .letOp (.copy (.local 2)) 2),
      (4, .letOp (.project (.local 3) 1) 3), (5, .ret (.local 4))],
    function 1 #[(1, .caseCtor (.local 0) [⟨0, 1⟩]), (3, .ret (.local 2))],
    function 3 #[(3, .branch (.local 0) 1 2), (3, .ret (.local 1)), (3, .ret (.local 2))],
    natCase,
    function 1 #[(1, .letOp (.closure 5 [.local 0]) 1), (2, .ret (.local 1))],
    function 2 #[(2, .letOp (.primitive .natAdd [.local 0, .local 1]) 1), (3, .ret (.local 2))],
    function 2 #[(2, .letOp (.closure 5 []) 1),
      (3, .letOp (.apply (.local 2) [.local 0, .local 1]) 2), (4, .ret (.local 3))],
    function 2 #[(2, .letOp (.closure 5 [.local 0]) 1), (3, .tailApply (.local 2) [.local 1])],
    function 2 #[(2, .letOp (.call 5 [.local 0, .local 1]) 1), (3, .ret (.local 2))],
    function 2 #[(2, .tailCall 5 [.local 0, .local 1])],
    function 2 #[(2, .letOp (.call 4 [.local 0]) 1),
      (3, .letOp (.apply (.local 2) [.local 1]) 2), (4, .ret (.local 3))],
    function 2 #[(2, .letOp (.closure 4 []) 1),
      (3, .letOp (.apply (.local 2) [.local 0, .local 1]) 2), (4, .ret (.local 3))],
    function 1 #[(1, .caseNat (.local 0) 1 2), (1, .ret (.literal (.nat 0))),
      (2, .letOp (.callSelf [.local 1]) 3), (3, .ret (.local 2))],
    function 1 #[(1, .caseNat (.local 0) 1 2), (1, .ret (.literal (.nat 0))),
      (2, .tailCallSelf [.local 1])],
    function 0 #[(0, .letOp (.apply .erased [.literal (.nat 17)]) 1), (1, .ret (.local 0))]]
  let n (n : Nat) := Value.scalar (.nat n)
  let samples : Array (Nat × Array Value × Value) := #[
    (0, #[n 7, n 9], n 9), (1, #[.ctor controlId #[n 7, n 9]], n 9),
    (2, #[.scalar (.bool true), n 7, n 9], n 7),
    (2, #[.scalar (.bool false), n 7, n 9], n 9),
    (3, #[n 0], n 99), (3, #[n 9], n 8),
    (4, #[n 7], .pap 5 #[n 7]),
    (5, #[n 7, n 9], n 16), (6, #[n 7, n 9], n 16), (7, #[n 7, n 9], n 16),
    (8, #[n 7, n 9], n 16), (9, #[n 7, n 9], n 16),
    (10, #[n 7, n 9], n 16), (11, #[n 7, n 9], n 16),
    (12, #[n 100], n 0), (13, #[n 100], n 0), (14, #[], .erased)]
  for (entry, args, expected) in samples do
    let image ← load count (artifact { entry, functions := controls, constructors := #[⟨controlId, 2⟩] })
    need ((← execute image args) == expected) s!"control execution changed: {entry}"
    count := count + 1
  let id : CtorId := { block := 123, member := 2 ^ 40, tag := 2 ^ 70 }
  let identity : Function := { arity := 1, blocks := #[{ locals := 1, instruction := .ret (.local 0) }] }
  let binary : Function := { arity := 2, blocks := #[{ locals := 2, instruction := .ret (.local 0) }] }
  let image ← load count (artifact { functions := #[identity, binary], constructors := #[⟨id, 2⟩] })
  let value : Value := .array #[.ctor id #[.scalar (.str "λ"),
    .pap 1 #[.array #[.scalar (.nat (2 ^ 90)), .erased]]], .erased]
  let input ← checked (Binary.encodeInput image #[value] |>.mapError reprStr)
  let inputValue ← checked (Binary.decodeInput image input |>.mapError reprStr)
  need (inputValue.value == #[value]) "structured input changed"
  let output ← execute image inputValue.value
  need (output == value) "structured execution changed"
  let encoded ← checked (Binary.encodeOutput image output |>.mapError reprStr)
  let decoded ← checked (Binary.decodeOutput image encoded |>.mapError reprStr)
  need (decoded.value == value) "structured output changed"
  if let some directory := directory then
    IO.FS.writeBinFile (directory / "identity.ixby")
      ⟨← checked (Binary.encode image |>.mapError reprStr)⟩
    IO.FS.writeBinFile (directory / "identity.ixbi") ⟨input⟩
    IO.FS.writeBinFile (directory / "identity.ixbo") ⟨encoded⟩
  rejects (Binary.decodeInput image input { valueNodes := 1 }) .nodeLimit
  rejects (Binary.decodeInput image input { valueDepth := 1 }) .depthLimit
  rejects (Binary.decodeInput image input { bytes := input.size - 1 }) .byteLimit
  rejects (Binary.decodeInput image input { integerBytes := 1 }) .integerLimit
  rejects (Binary.decodeInput image (input.push 0)) .trailing
  rejects (Binary.decodeInput image (input.set! 0 0)) .header
  rejects (Binary.decodeInput image (input.set! 4 99)) .version
  rejects (Binary.decodeInput image (input.set! 8 99)) .version
  rejects (Binary.decodeInput image (input.extract 0 12 ++ #[0x81, 0] ++ input.extract 13 input.size)) .nonCanonical
  for i in [:input.size] do
    need (failed (Binary.decodeInput image (input.extract 0 i))) "truncated input accepted"
  let boolean ← checked (Binary.encodeInput image #[.scalar (.bool true)] |>.mapError reprStr)
  rejects (Binary.decodeInput image (boolean.set! 15 2)) .nonCanonical
  rejects (Binary.decodeInput image (boolean.set! 13 255)) (.tag 255)
  rejects (Binary.decodeInput image (boolean.set! 14 255)) (.tag 255)
  let field ← checked (Binary.encodeInput image #[.scalar (.field 1)] |>.mapError reprStr)
  rejects (Binary.decodeInput image (field.extract 0 15 ++ bytesLE 8 goldilocksModulus)) .nonCanonical
  let string ← checked (Binary.encodeInput image #[.scalar (.str "a")] |>.mapError reprStr)
  rejects (Binary.decodeInput image (string.set! 16 255)) .nonCanonical
  let bytes ← checked (Binary.encode image |>.mapError reprStr)
  for i in [:bytes.size] do
    need (failed (Binary.decode (bytes.extract 0 i))) "truncated artifact accepted"
  rejects (Binary.decode (bytes.push 0)) .trailing
  rejects (Binary.decode (bytes.set! 0 0)) .header
  rejects (Binary.decode (bytes.set! 4 0)) .version
  rejects (Binary.decode (bytes.set! 8 0)) .version
  rejects (Binary.decode (bytes.set! 8 1)) .version
  rejects (Binary.Internal.decode {} #[255] (Binary.Internal.readInstr {})) (.tag 255)
  rejects (Binary.Internal.decode {} #[255] (Binary.Internal.readOp {})) (.tag 255)
  rejects (Binary.Internal.decode {} #[1, 255, 0] (Binary.Internal.readOp {})) (.tag 255)
  IO.println s!"check-ixby-binary ok: {count} decoded executions; structured values; all truncations and malformed encodings rejected"
