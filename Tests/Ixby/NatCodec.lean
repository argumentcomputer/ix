module
import Tests.Ixby.Common
import Ix.Ixby

/-! Exact-Nat revision-1 admission and canonical byte execution. These are pure
reference/codec tests, not evidence of Nat support in native Flock constraints. -/

namespace Tests.Ixby.NatCodec

open Ix.Ixby
open Ix.Ixby.Codec

private def profile (bits : Nat := 96) : Profile := {
  revision := .cryptoNatV1
  limits := {
    functions := 2, constructors := 1, blocks := 4, locals := 4,
    operands := 2, continuations := 2, inputNodes := 8,
    natBits := bits, stringBytes := 0, byteArrayBytes := 64 }
  programBytes := 512, valueBytes := 512, valueDepth := 4, maxSteps := 8 }

private def n (value : Nat) : Value := .scalar (.nat value)
private def w (value : UInt32) : Value := .scalar (.word32 value)
private def identity : Program := { functions := #[{
  arity := 1, blocks := #[⟨1, .ret (.local 0)⟩] }] }
private def primitiveProgram (op : Primitive) : Program := { functions := #[{
  arity := op.arity, blocks := #[
    ⟨op.arity, .letOp (.primitive op ((List.range op.arity).map Operand.local)) 1⟩,
    ⟨op.arity + 1, .ret (.local op.arity)⟩] }] }
private def caseProgram : Program := { functions := #[{
  arity := 1, blocks := #[
    ⟨1, .caseNat (.local 0) 1 2⟩,
    ⟨1, .ret (.literal (.nat 9))⟩,
    ⟨2, .ret (.local 1)⟩] }] }
private def pairId : CtorId := { block := 7, member := 2, tag := 3 }
private def objects : Program := {
  constructors := #[⟨pairId, 2⟩]
  functions := identity.functions.push { arity := 2, blocks := #[⟨2, .ret (.local 0)⟩] } }
private def nested : Value := .ctor pairId #[n (2 ^ 64 + 7), .pap 1 #[n 0]]

private def bytesOf : Except Codec.Error Bytes → Bytes
  | .ok bytes => bytes
  | .error _ => #[]
private def errorIs {α : Type} (result : Except Codec.Error α) (expected : Codec.Error) : Bool :=
  match result with | .error error => error == expected | .ok _ => false
private def valueIs (result : Except Codec.Error Value) (expected : Value) : Bool :=
  match result with | .ok value => value == expected | .error _ => false
private def rawOutput (body : Bytes) : Bytes := "IXBO".toUTF8.data ++ #[1, 0, 0, 0] ++ body
private def rawNat (bytes : Bytes) : Bytes := rawOutput (#[0, 5] ++ bytesLE 4 bytes.size ++ bytes)
private def encoded (value : Value) (p : Profile := profile) : Bytes :=
  bytesOf (encodeOutput p identity value)

private def roundTripProgram (program : Program) : Bool :=
  match encodeProgram profile program with
  | .ok bytes => match decodeProgram profile bytes with
    | .ok decoded => decoded.value == program
    | _ => false
  | _ => false
private def roundTripValue (value : Value) : Bool :=
  match encodeInput profile objects #[value], encodeOutput profile objects value with
  | .ok input, .ok output => match decodeInput profile objects input, decodeOutput profile objects output with
    | .ok i, .ok o => i.value == #[value] && o.value == value
    | _, _ => false
  | _, _ => false
private def executeValue (program : Program) (input : Array Value) (p : Profile := profile) :
    Except Codec.Error Value := do
  let code ← encodeProgram p program
  let args ← encodeInput p program input
  let execution ← Codec.execute p code args 3
  return execution.output
private def agrees (op : Primitive) (a b : Nat) (expected : Value) : Bool :=
  valueIs (executeValue (primitiveProgram op) #[n a, n b]) expected

private def profileBytes : Bytes := bytesOf (encodeProfile profile)
private def addBytes : Bytes := bytesOf (encodeProgram profile (primitiveProgram .natAdd))
private def inputBytes : Bytes := bytesOf (encodeInput profile identity #[n (2 ^ 32)])
private def outputBytes : Bytes := encoded (n (2 ^ 32))

-- Exact reference semantics are kernel-checked independently of the byte tests.
example : Primitive.eval (profile 33).limits .natAdd #[n (2 ^ 32 - 1), n 1].toList =
    .ok (n (2 ^ 32)) := rfl
example : Primitive.eval (profile 32).limits .natAdd #[n (2 ^ 32 - 1), n 1].toList =
    .error (.limit .natBits) := rfl
example : Primitive.eval profile.limits .natDiv [n 17, n 0] = .ok (n 0) := rfl
example : Primitive.eval profile.limits .natMod [n 17, n 0] = .ok (n 17) := rfl

private def checks : IO (List Check) := pure [
  ("experimental IXBY profiles exclude the complete IXBF conversions",
    (Profile.primitiveOpcode {} .natToWord32).isNone &&
    (Profile.primitiveOpcode {} .word32ToNat).isNone &&
    (profile.primitiveOpcode .natToWord32).isNone &&
    (profile.primitiveOpcode .word32ToNat).isNone),
  ("Nat revision explicitly admitted", profile.validate.isOk),
  ("v0 cannot enable Nat by changing capacity", !(Profile.validate {
    limits := { natBits := 96, stringBytes := 0 } }).isOk),
  ("v1 cannot enable String by changing capacity", !({ profile with
    limits.stringBytes := 1 } : Profile).validate.isOk),
  ("profile remains exactly 68 bytes", profileBytes.size == 68),
  ("independent Nat profile wire golden", profileBytes ==
    "IXBP".toUTF8.data ++ bytesLE 4 1 ++ bytesLE 4 1 ++
      (#[2, 1, 4, 4, 2, 2, 8, 96, 0, 64, 512, 512, 4, 8].flatMap (bytesLE 4))),
  ("profile round trip preserves revision and bit bound", match decodeProfile profileBytes with
    | .ok decoded => decoded.value == profile | _ => false),
  ("mismatched semantic revision rejected", errorIs
    (decodeProfile (profileBytes.set! 8 0)) .version),
  ("unknown paired revisions rejected", errorIs
    (decodeProfile ((profileBytes.set! 4 2).set! 8 2)) .version),
  ("old 35 primitive opcode assignments preserved", cryptoPrimitives.size == 35 &&
    cryptoPrimitives.toList.all (fun op => profile.primitiveOpcode op == op.cryptoOpcode)),
  ("exact appended Nat opcode assignments", (cryptoNatPrimitives.toList.zipIdx).all
    (fun (op, i) => profile.primitiveOpcode op == some (35 + i) &&
      (bytesOf (encodeProgram profile (primitiveProgram op)))[38]? == some (35 + i).toUInt8)),
  ("all seven Nat primitives round trip", cryptoNatPrimitives.size == 7 &&
    cryptoNatPrimitives.toList.all (roundTripProgram ∘ primitiveProgram)),
  ("Nat case instruction round trips with tag 7", roundTripProgram caseProgram &&
    (bytesOf (encodeProgram profile caseProgram))[36]? == some 7),
  ("Nat literals are admitted", roundTripProgram { functions := #[{
    arity := 0, blocks := #[⟨0, .ret (.literal (.nat (2 ^ 80 + 3)))⟩] }] }),
  ("zero uses empty magnitude", encoded (n 0) == rawOutput #[0, 5, 0, 0, 0, 0]),
  ("one uses one-byte magnitude", encoded (n 1) == rawOutput #[0, 5, 1, 0, 0, 0, 1]),
  ("Nat 2^32 is not narrowed to Word32", outputBytes ==
    rawOutput #[0, 5, 5, 0, 0, 0, 0, 0, 0, 0, 1]),
  ("same numeric Nat and Word32 have distinct tags", encoded (n 7) != encoded (w 7)),
  ("Nat values and nested constructor/PAP captures round trip", [
    n 0, n 1, n 255, n 256, n (2 ^ 32), n (2 ^ 64), n (2 ^ 96 - 1), nested
    ].all roundTripValue),
  ("zero allowed with zero-bit bound", (encodeOutput (profile 0) identity (n 0)).isOk),
  ("one rejected with zero-bit bound", errorIs (encodeOutput (profile 0) identity (n 1))
    (.profile (.reference (.limit .natBits)))),
  ("exact partial-byte bound accepted", (decodeOutput (profile 9) identity (rawNat #[255, 1])).isOk),
  ("partial-byte overflow rejected", errorIs (decodeOutput (profile 9) identity (rawNat #[0, 2]))
    (.profile (.reference (.limit .natBits)))),
  ("nonempty zero magnitude rejected", errorIs (decodeOutput profile identity (rawNat #[0])) .nonCanonical),
  ("redundant high zero rejected", errorIs (decodeOutput profile identity (rawNat #[7, 0])) .nonCanonical),
  ("hostile magnitude length bounded before allocation", errorIs (decodeOutput profile identity
    (rawOutput (#[0, 5] ++ bytesLE 4 0xffffffff))) .countLimit),
  ("zero-bit decoder rejects nonempty magnitude", errorIs
    (decodeOutput (profile 0) identity (rawNat #[1])) .countLimit),
  ("unknown scalar tag still rejected", errorIs (decodeOutput profile identity (rawOutput #[0, 6])) (.tag 6)),
  ("unknown appended opcode rejected", errorIs (decodeProgram profile (addBytes.set! 38 42)) (.tag 42)),
  ("all strict profile prefixes rejected", (List.range profileBytes.size).all
    (fun size => !(decodeProfile (profileBytes.extract 0 size)).isOk)),
  ("all strict Nat program prefixes rejected", (List.range addBytes.size).all
    (fun size => !(decodeProgram profile (addBytes.extract 0 size)).isOk)),
  ("all strict Nat input prefixes rejected", (List.range inputBytes.size).all
    (fun size => !(decodeInput profile identity (inputBytes.extract 0 size)).isOk)),
  ("all strict Nat output prefixes rejected", (List.range outputBytes.size).all
    (fun size => !(decodeOutput profile identity (outputBytes.extract 0 size)).isOk)),
  ("Nat trailing byte rejected", errorIs (decodeOutput profile identity (outputBytes.push 0)) .trailing),
  ("v1 program rejected under v0", errorIs (decodeProgram {} addBytes) .version),
  ("v0 program rejected under v1", errorIs (decodeProgram profile
    (bytesOf (encodeProgram {} identity))) .version),
  ("v1 input rejected under v0", errorIs (decodeInput {} identity inputBytes) .version),
  ("v1 output rejected under v0", errorIs (decodeOutput {} identity outputBytes) .version),
  ("renaming header cannot enable Nat opcodes in v0", errorIs
    (decodeProgram {} (addBytes.set! 4 0)) (.tag 35)),
  ("renaming header cannot enable Nat scalar in v0", errorIs
    (decodeOutput {} identity (outputBytes.set! 4 0)) (.tag 5)),
  ("renaming header cannot enable Nat case in v0", errorIs (decodeProgram {}
    ((bytesOf (encodeProgram profile caseProgram)).set! 4 0)) (.tag 7)),
  ("Nat addition carries beyond 32 bits", agrees .natAdd (2 ^ 32 - 1) 1 (n (2 ^ 32))),
  ("Nat subtraction truncates at zero", agrees .natSub 3 9 (n 0)),
  ("Nat subtraction remains exact beyond 64 bits", agrees .natSub (2 ^ 80 + 9) 7 (n (2 ^ 80 + 2))),
  ("Nat multiplication carries beyond 64 bits", agrees .natMul (2 ^ 40 + 1) (2 ^ 40 + 1)
    (n (2 ^ 80 + 2 ^ 41 + 1))),
  ("Nat quotient exact", agrees .natDiv (2 ^ 80 + 7) (2 ^ 40) (n (2 ^ 40))),
  ("Nat remainder exact", agrees .natMod (2 ^ 80 + 7) (2 ^ 40) (n 7)),
  ("Nat division by zero is zero", agrees .natDiv (2 ^ 80 + 7) 0 (n 0)),
  ("Nat modulo zero is the dividend", agrees .natMod (2 ^ 80 + 7) 0 (n (2 ^ 80 + 7))),
  ("Nat equality returns Bool", agrees .natEq (2 ^ 80) (2 ^ 80) (.scalar (.bool true))),
  ("Nat inequality returns Bool", agrees .natEq (2 ^ 80) (2 ^ 80 + 1) (.scalar (.bool false))),
  ("Nat comparison exact", agrees .natLt (2 ^ 80) (2 ^ 80 + 1) (.scalar (.bool true))),
  ("Nat comparison equal is false", agrees .natLt 7 7 (.scalar (.bool false))),
  ("Nat overflow fails instead of wrapping", errorIs
    (executeValue (primitiveProgram .natAdd) #[n (2 ^ 32 - 1), n 1] (profile 32))
    (.profile (.reference (.limit .natBits)))),
  ("Nat product overflow fails", errorIs
    (executeValue (primitiveProgram .natMul) #[n (2 ^ 31), n 2] (profile 32))
    (.profile (.reference (.limit .natBits)))),
  ("Nat and Word32 cannot mix implicitly", errorIs
    (executeValue (primitiveProgram .natAdd) #[n 1, w 2]) (.profile (.reference (.primitiveType .natAdd)))),
  ("Word32 arithmetic still wraps in v1", valueIs (executeValue
    (primitiveProgram .word32Add) #[w 0xffffffff, w 1]) (w 0)),
  ("zero Nat case preserves original frame", valueIs (executeValue caseProgram #[n 0]) (n 9)),
  ("successor Nat case appends exact predecessor", valueIs (executeValue caseProgram #[n (2 ^ 64)]) (n (2 ^ 64 - 1))),
  ("Nat case does not accept Word32", errorIs (executeValue caseProgram #[w 0]) (.profile (.reference .notNat))),
  ("String scalar still excluded", !(encodeOutput profile identity (.scalar (.str ""))).isOk),
  ("String primitive still excluded", !(encodeProgram profile (primitiveProgram .strEq)).isOk),
  ("Nat input forest keeps shared node budget", !(encodeInput
    { profile with limits.inputNodes := 3 } objects #[nested]).isOk),
  ("Nat input forest keeps depth budget", !(encodeInput
    { profile with valueDepth := 2 } objects #[nested]).isOk),
  ("Nat output keeps byte budget", errorIs
    (encodeOutput { profile with valueBytes := 18 } identity (n (2 ^ 32))) .byteLimit &&
    errorIs (encodeOutput (profile 100001) identity (n (2 ^ 100000))) .byteLimit)
]

public def suite : IO UInt32 := runChecks "ixby-nat-codec" checks

end Tests.Ixby.NatCodec
