module
import Tests.Ixby.Common
import Ix.Ixby
import Blake3.Rust

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
  .scalar (.nat 0), .scalar (.nat (2 ^ 256 - 1)), .scalar (.str "λ🙂"),
  .array #[], .array #[.array #[w 7], .erased, pair],
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

-- Independent Python encoding and b3sum digest vectors, not codec output.
private def identityBytes : Bytes := #[
  73, 88, 66, 70, 1, 0, 0, 0, 2, 0, 0, 0, 128, 32, 128, 32, 128, 128, 4, 128, 32, 128, 2, 128, 128, 4, 128, 128, 4, 128, 32, 128, 128, 4, 128, 128, 4, 192, 132, 61, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0]
private def inputBytes : Bytes := #[
  73, 88, 70, 73, 1, 0, 0, 0, 2, 0, 0, 0, 1, 0, 3, 120, 86, 52, 18]
private def outputBytes : Bytes := #[
  73, 88, 70, 79, 1, 0, 0, 0, 2, 0, 0, 0, 0, 3, 120, 86, 52, 18]
private def statementBytes : Bytes := #[
  213, 229, 210, 168, 85, 2, 187, 71, 236, 7, 229, 64, 80, 107, 109, 79, 229, 24, 156, 30, 143, 83, 165, 143, 67, 64, 79, 199, 135, 166, 126, 249]

private def rawOutput (body : Bytes) : Bytes :=
  "IXFO".toUTF8.data ++ #[1, 0, 0, 0, 2, 0, 0, 0] ++ body
private def profileBytes := bytesOf (encodeProfile {})
private def nestedBytes := bytesOf (encodeOutput {} objects (nested 4))
private def executeValue (program : Program) (input : Array Value) (expected : Value)
    (fuel : Nat) : Bool :=
  match encodeProgram {} program, encodeInput {} program input with
  | .ok code, .ok args => match Codec.execute {} code args fuel with
    | .ok execution => execution.output == expected &&
        execution.outputBytes == bytesOf (encodeOutput {} program expected)
    | .error _ => false
  | _, _ => false
private def statements := Commitment.ofArtifacts {} identityBytes inputBytes outputBytes

private def checks : IO (List Check) := do
  return [
    ("golden current program", bytesOf (encodeProgram {} identity) == identityBytes),
    ("golden current input", bytesOf (encodeInput {} identity #[w 0x12345678]) == inputBytes),
    ("golden current output", bytesOf (encodeOutput {} identity (w 0x12345678)) == outputBytes),
    ("golden independent commitment", match statements with
      | .ok s => s.digest.bytes == statementBytes | _ => false),
    ("fixed profile has 184 bytes", profileBytes.size == 184),
    ("profile round trips", match decodeProfile profileBytes with
      | .ok v => v.value == ({} : Profile) | _ => false),
    ("u128 capacities and u64 fuel round trip", let p : Profile := {
        limits := { functions := 2 ^ 100 + 17, natBits := 2 ^ 120 }, maxSteps := 2 ^ 63 + 1 }
      match decodeProfile (bytesOf (encodeProfile p)) with
      | .ok v => v.value.parameters == p.parameters && v.value.maxSteps == p.maxSteps | _ => false),
    ("loader budgets are separate from semantic profile", bytesOf (encodeProfile
      { programBytes := 47, valueBytes := 53, valueDepth := 59 }) == bytesOf (encodeProfile {})),
    ("all scalar and structured values round trip", valueCases.all roundTripValue),
    ("every current primitive round trips", primitives.toList.all (roundTripProgram ∘ primitiveProgram)),
    ("every let operation round trips", [
      .copy (.local 0), .construct 0 [.local 0, .erased], .project .erased 7,
      .closure 0 [], .call 0 [.local 0], .callSelf [.local 0], .apply (.local 0) [.erased]
      ].all (fun op => roundTripProgram (opProgram op))),
    ("all tail instructions round trip", [
      .tailCall 0 [.local 0], .tailCallSelf [.local 0], .tailApply (.local 0) []
      ].all (fun instruction => roundTripProgram { functions := #[{
        arity := 1, blocks := #[⟨1, instruction⟩] }] })),
    ("Bool branches and nonzero block entry round trip", roundTripProgram branchProgram),
    ("constructor case round trip", roundTripProgram caseProgram),
    ("nonzero program entry round trip", roundTripProgram { branchProgram with
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
    ("profile trailing byte", isError (decodeProfile (profileBytes.push 0))),
    ("old program semantic revisions rejected", [0, 1].all fun n =>
      errorIs (decodeProgram {} (identityBytes.set! 8 n)) .version),
    ("old input semantic revisions rejected", [0, 1].all fun n =>
      errorIs (decodeInput {} identity (inputBytes.set! 8 n)) .version),
    ("old output semantic revisions rejected", [0, 1].all fun n =>
      errorIs (decodeOutput {} identity (outputBytes.set! 8 n)) .version),
    ("old IXBY magic rejected", errorIs (decodeProgram {} (identityBytes.set! 3 0x59)) .header),
    ("old IXBP magic rejected", errorIs (decodeProfile (profileBytes.set! 2 0x42)) .header),
    ("wire revision checked", errorIs (decodeProgram {} (identityBytes.set! 4 0)) .version),
    ("profile revision checked", errorIs (decodeProfile (profileBytes.set! 4 1)) .version),
    ("profile semantic revision checked", errorIs (decodeProfile (profileBytes.set! 12 1)) .version),
    ("program semantic limits are profile-bound", isError (decodeProgram
      { limits := { natBits := 128 } } identityBytes)),
    ("program fuel is profile-bound", isError (decodeProgram { maxSteps := 9 } identityBytes)),
    ("IO domains cannot be swapped", errorIs (decodeOutput {} identity inputBytes) .header),
    ("noncanonical boolean", errorIs (decodeOutput {} identity (rawOutput #[0, 2, 2])) .nonCanonical),
    ("unknown scalar", errorIs (decodeOutput {} identity (rawOutput #[0, 7])) (.tag 7)),
    ("unknown value", errorIs (decodeOutput {} identity (rawOutput #[5])) (.tag 5)),
    ("field modulus rejected", errorIs (decodeOutput {} identity
      (rawOutput (#[0, 4] ++ bytesLE 8 goldilocksModulus))) .nonCanonical),
    ("max u64 field rejected", errorIs (decodeOutput {} identity
      (rawOutput (#[0, 4] ++ bytesLE 8 (2 ^ 64 - 1)))) .nonCanonical),
    ("extension second coefficient checked", errorIs (decodeOutput {} identity
      (rawOutput (#[0, 5] ++ bytesLE 8 0 ++ bytesLE 8 goldilocksModulus))) .nonCanonical),
    ("overlong natural rejected", errorIs (decodeOutput {} identity (rawOutput #[0, 0, 128, 0])) .nonCanonical),
    ("invalid UTF8 rejected", errorIs (decodeOutput {} identity (rawOutput #[0, 1, 1, 255])) .nonCanonical),
    ("wide Nats retain their tag", roundTripValue (.scalar (.nat (2 ^ 256 + 37)))),
    ("wide declaration metadata round trips", roundTripProgram { identity with
      constructors := #[⟨{ pairId with member := 2 ^ 80, tag := 2 ^ 100 }, 0⟩] }),
    ("wide erased projection index round trips", roundTripProgram (opProgram (.project .erased (2 ^ 80)))),
    ("full constructor digest survives", roundTripProgram { identity with
      constructors := #[⟨{ block := ⟨2 ^ 256 - 1, by decide⟩ }, 0⟩] }),
    ("wrong input arity rejected", isError (encodeInput {} identity #[])),
    ("unused invalid function rejected", rejectsRaw { identity with
      functions := identity.functions.push { arity := 0, blocks := #[⟨0, .ret (.local 0)⟩] } }),
    ("unreachable invalid block rejected", rejectsRaw { functions := #[{
      arity := 1, blocks := #[⟨1, .ret (.local 0)⟩, ⟨1, .ret (.local 2)⟩] }] }),
    ("duplicate constructors rejected", rejectsRaw { objects with
      constructors := objects.constructors.push ⟨pairId, 2⟩ }),
    ("duplicate alternatives rejected", rejectsRaw { caseProgram with functions := #[{
      arity := 1, blocks := #[⟨1, .caseCtor (.local 0) [⟨0, 1⟩, ⟨0, 1⟩]⟩,
        ⟨3, .ret (.local 1)⟩] }] }),
    ("unknown constructor rejected", isError (encodeOutput {} identity pair)),
    ("saturated PAP rejected", isError (encodeOutput {} identity (.pap 0 #[w 1]))),
    ("internal builder must be frozen", errorIs (encodeOutput {} identity (.byteBuilder #[1])) .internalValue),
    ("nested builder must be frozen", errorIs (encodeOutput {} identity
      (.array #[.byteBuilder #[]])) .internalValue),
    ("encoder program byte limit", errorIs (encodeProgram
      { programBytes := identityBytes.size - 1 } identity) .byteLimit),
    ("decoder program byte limit", errorIs (decodeProgram
      { programBytes := identityBytes.size - 1 } identityBytes) .byteLimit),
    ("exact program byte limit", roundTripProgram identity { programBytes := identityBytes.size }),
    ("encoder value byte limit", errorIs (encodeOutput
      { valueBytes := outputBytes.size - 1 } identity (w 0x12345678)) .byteLimit),
    ("decoder value byte limit", errorIs (decodeOutput
      { valueBytes := outputBytes.size - 1 } identity outputBytes) .byteLimit),
    ("hostile byte count rejected before allocation", errorIs (decodeOutput {} identity
      (rawOutput #[0, 6, 255, 255, 255, 255, 15])) .countLimit),
    ("hostile array count rejected before allocation", errorIs (decodeOutput {} identity
      (rawOutput #[4, 255, 255, 255, 255, 15])) .countLimit),
    ("depth enforced", errorIs (decodeOutput { valueDepth := 4 } objects nestedBytes) .depthLimit),
    ("exact depth succeeds", (decodeOutput { valueDepth := 5 } objects nestedBytes).isOk),
    ("shared node budget enforced", errorIs (decodeOutput { limits := { inputNodes := 4 } }
      objects nestedBytes) .nodeLimit),
    ("shared array node budget enforced", isError (decodeOutput { limits := { inputNodes := 2 } }
      identity (bytesOf (encodeOutput {} identity (.array #[w 1, w 2]))))),
    ("canonicality checked", errorIs
      (Internal.canonicalize (fun (_ : Unit) => .ok #[1]) #[2] ()) .nonCanonical),
    ("byte identity execution", executeValue identity #[w 0x12345678] (w 0x12345678) 2),
    ("byte array identity execution", executeValue identity #[.array #[w 1]] (.array #[w 1]) 2),
    ("byte true branch", executeValue branchProgram #[.scalar (.bool true)] (w 7) 3),
    ("byte false branch", executeValue branchProgram #[.scalar (.bool false)] (w 11) 3),
    ("byte constructor case", executeValue caseProgram #[.ctor pairId #[w 7, w 11]] (w 7) 3),
    ("byte primitive", executeValue (primitiveProgram .word32Add) #[w 0xffffffff, w 2] (w 1) 3),
    ("byte zero-arity primitive", executeValue (primitiveProgram .arrayEmpty) #[] (.array #[]) 3),
    ("byte array update", executeValue (primitiveProgram .arraySet)
      #[.array #[w 1, w 2], .scalar (.nat 1), w 9] (.array #[w 1, w 9]) 3),
    ("byte BLAKE3", executeValue (primitiveProgram .blake3) #[.scalar (.bytes "abc".toUTF8.data)]
      (.scalar (.bytes (Blake3.Rust.hash "abc".toUTF8).val.data)) 3),
    ("exact fuel enforced", errorIs (Codec.execute {} identityBytes inputBytes 1)
      (.profile (.reference .outOfFuel))),
    ("correct statement accepted", match statements with
      | .ok s => (Commitment.executeAndCheck {} identityBytes inputBytes 2 s).isOk | _ => false),
    ("wrong expected output rejected", match statements with
      | .ok s => match Commitment.executeAndCheck {} identityBytes inputBytes 2
          { s with output := Commitment.hash .output #[] } with
        | .error (.mismatch .output) => true | _ => false
      | _ => false),
    ("malformed artifact cannot get an admitted statement", isError
      (Commitment.ofArtifacts {} (identityBytes.push 0) inputBytes outputBytes))
  ]

public def suite : IO UInt32 := runChecks "ixby-codec" checks
end Tests.Ixby.Codec
