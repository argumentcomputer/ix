module
import Ix.Ixby
import Blake3.Rust
meta import Ix.Ixby
meta import Blake3.Rust

namespace Tests.Ixby.Codec

open Ix.Ixby
open Ix.Ixby.Codec

private def w (n : UInt32) : Value := .scalar (.word32 n)
private def g (n : Nat) : Value := .scalar (.field (Goldilocks.reduce n))
private def identity : Program := { functions := #[{
  arity := 1, blocks := #[⟨1, .ret (.local 0)⟩] }] }

private def primitiveProgram (op : Primitive) : Program := { functions := #[{
  arity := op.arity, blocks := #[
    ⟨op.arity, .letOp (.primitive op ((List.range op.arity).map Operand.local)) 1⟩,
    ⟨op.arity + 1, .ret (.local op.arity)⟩] }] }

private def pairId : CtorId := { block := 1, member := 3, tag := 2 }
private def nodeId : CtorId := { block := 2 }
private def objects : Program := {
  constructors := #[⟨pairId, 2⟩, ⟨nodeId, 1⟩]
  functions := identity.functions.push { arity := 2, blocks := #[⟨2, .ret (.local 0)⟩] }
}
private def pair : Value := .ctor pairId #[w 1, .pap 1 #[g 2]]
private def nested : Nat → Value
  | 0 => w 1
  | n + 1 => .ctor nodeId #[nested n]

private def valueCases : List Value := [
  .scalar (.bool false), .scalar (.bool true), w 0, w 0xffffffff,
  g 0, g (goldilocksModulus - 1),
  .scalar (.extField ⟨Goldilocks.reduce 7, Goldilocks.reduce (goldilocksModulus - 1)⟩),
  .scalar (.bytes #[]), .scalar (.bytes #[0, 0xc0, 0x80, 0xff]),
  .erased, .pap 0 #[], .pap 1 #[w 7], pair, nested 8]

private def bytesOf (encoded : Except Codec.Error Bytes) : Bytes :=
  match encoded with | .ok bytes => bytes | .error _ => #[]
private def isError {α : Type} : Except Codec.Error α → Bool
  | .error _ => true | .ok _ => false
private def errorIs {α : Type} (result : Except Codec.Error α) (expected : Codec.Error) : Bool :=
  match result with | .error error => error == expected | .ok _ => false

private def roundTripProgram (program : Program) (profile : Profile := {}) : Bool :=
  match encodeProgram profile program with
  | .error _ => false
  | .ok bytes => match decodeProgram profile bytes with
    | .error _ => false
    | .ok decoded => decoded.value == program

private def roundTripValue (value : Value) : Bool :=
  match encodeInput {} objects #[value], encodeOutput {} objects value with
  | .ok input, .ok output =>
    match decodeInput {} objects input, decodeOutput {} objects output with
    | .ok i, .ok o => i.value == #[value] && o.value == value
    | _, _ => false
  | _, _ => false

private def rawProgram (program : Program) : Except Codec.Error Bytes :=
  Internal.encode 16777216 0 (Internal.writeProgram {} program)

private def rejectsRaw (program : Program) : Bool :=
  match rawProgram program with
  | .ok bytes => isError (decodeProgram {} bytes)
  | .error _ => false

private def opProgram (op : Op) : Program := {
  constructors := #[⟨pairId, 2⟩]
  functions := #[{ arity := 1, blocks := #[
    ⟨1, .letOp op 1⟩, ⟨2, .ret (.local 1)⟩] }]
}

private def branchProgram : Program := { functions := #[{
  arity := 1, entry := 2, blocks := #[
    ⟨1, .ret (.literal (.word32 7))⟩,
    ⟨1, .ret (.literal (.word32 11))⟩,
    ⟨1, .branch (.local 0) 0 1⟩] }] }

private def caseProgram : Program := {
  constructors := #[⟨pairId, 2⟩]
  functions := #[{ arity := 1, blocks := #[
    ⟨1, .caseCtor (.local 0) [⟨0, 1⟩]⟩,
    ⟨3, .ret (.local 1)⟩] }]
}

-- Independently written byte vectors pin tags, order, lengths, and endian.
private def identityBytes : Bytes := #[
  0x49, 0x58, 0x42, 0x59, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
  1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
  1, 0, 0, 0, 1, 0, 0, 0, 0, 0]
private def inputBytes : Bytes := #[
  0x49, 0x58, 0x42, 0x49, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0x78, 0x56, 0x34, 0x12]
private def outputBytes : Bytes := #[
  0x49, 0x58, 0x42, 0x4f, 0, 0, 0, 0, 0, 1, 0x78, 0x56, 0x34, 0x12]

private def rawOutput (body : Bytes) : Bytes := "IXBO".toUTF8.data ++ #[0, 0, 0, 0] ++ body
private def replaceU32 (bytes : Bytes) (offset n : Nat) : Bytes :=
  bytes.extract 0 offset ++ bytesLE 4 n ++ bytes.extract (offset + 4) bytes.size

private def executeValue (program : Program) (input : Array Value) (expected : Value)
    (fuel : Nat) : Bool :=
  match encodeProgram {} program, encodeInput {} program input with
  | .ok code, .ok args => match Codec.execute {} code args fuel with
    | .ok execution => execution.output == expected &&
        execution.outputBytes == bytesOf (encodeOutput {} program expected)
    | .error _ => false
  | _, _ => false

private def profileBytes : Bytes := bytesOf (encodeProfile {})
private def primitiveBytes : Bytes := bytesOf (encodeProgram {} (primitiveProgram .word32Add))
private def nestedBytes : Bytes := bytesOf (encodeOutput {} objects (nested 4))

private def statements : Except Codec.Error Commitment.Statement :=
  Commitment.ofArtifacts {} identityBytes inputBytes outputBytes

private def checkMismatch (expected : Commitment.Statement) (domain : Commitment.Domain)
    (code := identityBytes) (input := inputBytes) (profile : Profile := {}) : Bool :=
  match Commitment.executeAndCheck profile code input 2 expected with
  | .error (.mismatch actual) => actual == domain
  | _ => false

private def checks : List (String × Bool) := [
  ("golden identity program", bytesOf (encodeProgram {} identity) == identityBytes),
  ("golden Word32 input", bytesOf (encodeInput {} identity #[w 0x12345678]) == inputBytes),
  ("golden Word32 output", bytesOf (encodeOutput {} identity (w 0x12345678)) == outputBytes),
  ("profile fixed size", profileBytes.size == 68),
  ("profile round trip", match decodeProfile profileBytes with
    | .ok decoded => decoded.value == ({} : Profile) | _ => false),
  ("all profile capacities round trip", match decodeProfile (bytesOf (encodeProfile {
      limits := {
        functions := 17, constructors := 19, blocks := 23, locals := 29,
        operands := 31, continuations := 37, inputNodes := 41, natBits := 0,
        stringBytes := 0, byteArrayBytes := 43 },
      programBytes := 47, valueBytes := 53, valueDepth := 59, maxSteps := 61 })) with
    | .ok decoded => decoded.value.parameters == #[17, 19, 23, 29, 31, 37, 41, 0, 0, 43, 47, 53, 59, 61]
    | _ => false),
  ("identity round trip", roundTripProgram identity),
  ("constructor and PAP program round trip", roundTripProgram objects),
  ("all scalar and structured values round trip", valueCases.all roundTripValue),
  ("every crypto primitive round trips", cryptoPrimitives.toList.all (roundTripProgram ∘ primitiveProgram)),
  ("every let operation round trips", [
      .copy (.local 0), .construct 0 [.local 0, .erased], .project .erased 7,
      .closure 0 [], .call 0 [.local 0], .callSelf [.local 0], .apply (.local 0) [.erased]
    ].all (fun op => roundTripProgram (opProgram op))),
  ("all tail instructions round trip", [
      .tailCall 0 [.local 0], .tailCallSelf [.local 0], .tailApply (.local 0) []
    ].all (fun instruction => roundTripProgram { functions := #[{
      arity := 1, blocks := #[⟨1, instruction⟩] }] })),
  ("nonzero block entry and Bool branches", roundTripProgram branchProgram),
  ("constructor case round trip", roundTripProgram caseProgram),
  ("nonzero program entry", roundTripProgram { branchProgram with
      entry := 1, functions := identity.functions ++ branchProgram.functions }),
  ("all strict program prefixes rejected", (List.range identityBytes.size).all
    (fun n => isError (decodeProgram {} (identityBytes.extract 0 n)))),
  ("all strict input prefixes rejected", (List.range inputBytes.size).all
    (fun n => isError (decodeInput {} identity (inputBytes.extract 0 n)))),
  ("all strict output prefixes rejected", (List.range outputBytes.size).all
    (fun n => isError (decodeOutput {} identity (outputBytes.extract 0 n)))),
  ("all strict profile prefixes rejected", (List.range profileBytes.size).all
    (fun n => isError (decodeProfile (profileBytes.extract 0 n)))),
  ("program trailing byte", errorIs (decodeProgram {} (identityBytes.push 0)) .trailing),
  ("input trailing byte", errorIs (decodeInput {} identity (inputBytes.push 0)) .trailing),
  ("output trailing byte", errorIs (decodeOutput {} identity (outputBytes.push 0)) .trailing),
  ("profile extra byte rejected", isError (decodeProfile (profileBytes.push 0))),
  ("program magic checked", errorIs (decodeProgram {} (identityBytes.set! 0 0)) .header),
  ("wire revision checked", errorIs (decodeProgram {} (identityBytes.set! 4 1)) .version),
  ("profile wire revision checked", errorIs (decodeProfile (profileBytes.set! 4 1)) .version),
  ("semantic revision checked", errorIs (decodeProfile (profileBytes.set! 8 1)) .version),
  ("profile cannot enable Nat", errorIs (decodeProfile (profileBytes.set! 40 1)) (.profile .configuration)),
  ("input/output domains cannot be swapped", errorIs (decodeOutput {} identity inputBytes) .header),
  ("Boolean 2 is not true", errorIs (decodeOutput {} identity (rawOutput #[0, 0, 2])) .nonCanonical),
  ("unknown scalar tag", errorIs (decodeOutput {} identity (rawOutput #[0, 5])) (.tag 5)),
  ("unknown value/pointer tag", errorIs (decodeOutput {} identity (rawOutput #[4])) (.tag 4)),
  ("field modulus is noncanonical", errorIs
    (decodeOutput {} identity (rawOutput (#[0, 2] ++ bytesLE 8 goldilocksModulus))) .nonCanonical),
  ("max u64 is not a field encoding", errorIs
    (decodeOutput {} identity (rawOutput (#[0, 2] ++ bytesLE 8 (2 ^ 64 - 1)))) .nonCanonical),
  ("extension second coefficient is canonical", errorIs
    (decodeOutput {} identity (rawOutput (#[0, 3] ++ bytesLE 8 0 ++ bytesLE 8 goldilocksModulus))) .nonCanonical),
  ("unknown instruction tag", errorIs (decodeProgram {} (identityBytes.set! 36 255)) (.tag 255)),
  ("unknown operand tag", errorIs (decodeProgram {} (identityBytes.set! 37 255)) (.tag 255)),
  ("unknown primitive tag", errorIs (decodeProgram {} (primitiveBytes.set! 38 255)) (.tag 255)),
  ("forward local is rejected", isError (decodeProgram {} (identityBytes.set! 38 1))),
  ("invalid program entry", isError (decodeProgram {} (identityBytes.set! 8 1))),
  ("wrong input arity", isError (encodeInput {} identity #[])),
  ("wrong decoded input arity", isError (decodeInput {} identity
    ("IXBI".toUTF8.data ++ bytesLE 4 0 ++ bytesLE 4 0))),
  ("unused invalid function rejected", rejectsRaw { identity with
    functions := identity.functions.push { arity := 0, blocks := #[⟨0, .ret (.local 0)⟩] } }),
  ("unreachable invalid block rejected", rejectsRaw { functions := #[{
    arity := 1, blocks := #[⟨1, .ret (.local 0)⟩, ⟨1, .ret (.local 2)⟩] }] }),
  ("duplicate constructor identities rejected", rejectsRaw { objects with
    constructors := objects.constructors.push ⟨pairId, 2⟩ }),
  ("duplicate case alternatives rejected", rejectsRaw { caseProgram with functions := #[{
    arity := 1, blocks := #[⟨1, .caseCtor (.local 0) [⟨0, 1⟩, ⟨0, 1⟩]⟩,
      ⟨3, .ret (.local 1)⟩] }] }),
  ("Nat programs are not encoded", isError (encodeProgram {} (primitiveProgram .natAdd))),
  ("Nat zero is not encoded as a word", isError (encodeOutput {} identity (.scalar (.nat 0)))),
  ("strings are not encoded as bytes", isError (encodeOutput {} identity (.scalar (.str "")))),
  ("unknown constructor value rejected", isError (encodeOutput {} identity pair)),
  ("saturated PAP rejected", isError (encodeOutput {} identity (.pap 0 #[w 1]))),
  ("unknown input PAP function rejected", isError (decodeOutput {} identity (rawOutput
    (#[2] ++ bytesLE 4 99 ++ bytesLE 4 0)))),
  ("constructor member cannot truncate", errorIs (encodeProgram {} { identity with
    constructors := #[⟨{ pairId with member := 2 ^ 32 }, 0⟩] }) .integerRange),
  ("constructor tag cannot truncate", errorIs (encodeProgram {} { identity with
    constructors := #[⟨{ pairId with tag := 2 ^ 32 }, 0⟩] }) .integerRange),
  ("erased projection index cannot truncate", errorIs
    (encodeProgram {} (opProgram (.project .erased (2 ^ 32)))) .integerRange),
  ("full 256-bit constructor digest survives", roundTripProgram { identity with
    constructors := #[⟨{ block := ⟨2 ^ 256 - 1, by decide⟩, member := 0xffffffff, tag := 0xffffffff }, 0⟩] }),
  ("encoder program byte limit", errorIs (encodeProgram { programBytes := 41 } identity) .byteLimit),
  ("decoder program byte limit", errorIs (decodeProgram { programBytes := 41 } identityBytes) .byteLimit),
  ("exact program byte boundary", roundTripProgram identity { programBytes := 42 }),
  ("encoder input byte limit", errorIs (encodeInput { valueBytes := 17 } identity #[w 0x12345678]) .byteLimit),
  ("decoder input byte limit", errorIs (decodeInput { valueBytes := 17 } identity inputBytes) .byteLimit),
  ("encoder output byte limit", errorIs (encodeOutput { valueBytes := 13 } identity (w 0x12345678)) .byteLimit),
  ("decoder output byte limit", errorIs (decodeOutput { valueBytes := 13 } identity outputBytes) .byteLimit),
  ("hostile vector count rejected before allocation", errorIs
    (decodeInput {} identity (replaceU32 inputBytes 8 0xffffffff)) .countLimit),
  ("hostile function count rejected before allocation", errorIs
    (decodeProgram {} (replaceU32 identityBytes 16 0xffffffff)) .countLimit),
  ("hostile byte length rejected before allocation", errorIs
    (decodeOutput {} identity (rawOutput (#[0, 4] ++ bytesLE 4 0xffffffff))) .countLimit),
  ("nested value depth enforced", errorIs (decodeOutput { valueDepth := 4 } objects nestedBytes) .depthLimit),
  ("exact value depth succeeds", (decodeOutput { valueDepth := 5 } objects nestedBytes).isOk),
  ("shared nested node budget enforced", errorIs (decodeOutput {
      limits := { natBits := 0, stringBytes := 0, inputNodes := 4 } } objects nestedBytes) .nodeLimit),
  ("shared sibling node budget enforced", errorIs (decodeOutput {
      limits := { natBits := 0, stringBytes := 0, inputNodes := 2 } } objects
      (bytesOf (encodeOutput {} objects (.ctor pairId #[w 1, w 2])))) .nodeLimit),
  ("exact node boundary succeeds", (decodeOutput {
      limits := { natBits := 0, stringBytes := 0, inputNodes := 5 } } objects nestedBytes).isOk),
  ("canonicality is checked, not assumed", errorIs
    (Internal.canonicalize (fun (_ : Unit) => .ok #[1]) #[2] ()) .nonCanonical),
  ("byte execution identity", executeValue identity #[w 0x12345678] (w 0x12345678) 2),
  ("byte execution branch true", executeValue branchProgram #[.scalar (.bool true)] (w 7) 3),
  ("byte execution branch false", executeValue branchProgram #[.scalar (.bool false)] (w 11) 3),
  ("byte execution constructor case", executeValue caseProgram #[.ctor pairId #[w 7, w 11]] (w 7) 3),
  ("byte execution primitive", executeValue (primitiveProgram .word32Add) #[w 0xffffffff, w 2] (w 1) 3),
  ("byte execution BLAKE3", executeValue (primitiveProgram .blake3) #[.scalar (.bytes "abc".toUTF8.data)]
    (.scalar (.bytes (Blake3.Rust.hash "abc".toUTF8).val.data)) 3),
  ("nonterminal byte run rejects", errorIs (Codec.execute {} identityBytes inputBytes 1)
    (.profile (.reference .outOfFuel))),
  ("byte step bound enforced", errorIs (Codec.execute { maxSteps := 1 } identityBytes inputBytes 2) (.profile .steps)),
  ("commitments match independent domain preimages", match statements with
    | .error _ => false
    | .ok s =>
      let h (tag : UInt8) (payload : Bytes) := (Blake3.Rust.hash
        ⟨"IxBy/commit/v0".toUTF8.data ++ #[0, tag] ++ payload⟩).val.data
      let p := h 0 profileBytes
      let c := h 1 (p ++ identityBytes)
      let i := h 2 (c ++ inputBytes)
      let o := h 3 (c ++ outputBytes)
      s.profile.bytes == p && s.program.bytes == c && s.input.bytes == i && s.output.bytes == o &&
        s.digest.bytes == h 4 (p ++ c ++ i ++ o)),
  ("all hash domains distinguish the same payload", let domains : List Commitment.Domain :=
      [.profile, .program, .input, .output, .statement]
    domains.all fun a => domains.all fun b =>
      a == b || (Commitment.hash a #[1, 2, 3]).bytes != (Commitment.hash b #[1, 2, 3]).bytes),
  ("reference commitment check accepts correct execution", match statements with
    | .ok s => (Commitment.executeAndCheck {} identityBytes inputBytes 2 s).isOk
    | _ => false),
  ("changed profile rejects old statement", match statements with
    | .ok s => checkMismatch s .profile (profile := { maxSteps := 999999 }) | _ => false),
  ("unused code is program-bound", match statements with
    | .ok s => checkMismatch s .program (code := bytesOf (encodeProgram {} { identity with
        functions := identity.functions.push { arity := 0, blocks := #[⟨0, .ret (.literal (.word32 7))⟩] } }))
    | _ => false),
  ("changed input rejects old statement", match statements with
    | .ok s => checkMismatch s .input (input := bytesOf (encodeInput {} identity #[w 9])) | _ => false),
  ("changed output commitment rejects", match statements with
    | .ok s => checkMismatch { s with output := Commitment.hash .output #[] } .output | _ => false),
  ("well-formed wrong output is not an execution proof", match Commitment.ofArtifacts {}
      identityBytes inputBytes (bytesOf (encodeOutput {} identity (w 9))) with
    | .ok s => checkMismatch s .output | _ => false),
  ("malformed artifacts cannot get an admitted statement", isError
    (Commitment.ofArtifacts {} (identityBytes.push 0) inputBytes outputBytes))
]

#guard checks.all (·.2)

public def suite : IO UInt32 := do
  IO.println "ixby-codec (canonical artifacts and commitments)"
  let mut failed := 0
  for (name, passed) in checks do
    if passed then IO.println s!"  ✓ {name}"
    else
      failed := failed + 1
      IO.eprintln s!"  ✗ {name}"
  IO.println s!"{checks.length - failed}/{checks.length} checks passed"
  return if failed == 0 then 0 else 1

end Tests.Ixby.Codec
