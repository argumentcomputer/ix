module
import Ix.Ixby
import Blake3.Rust
meta import Ix.Ixby
meta import Blake3.Rust

namespace Tests.Ixby.Crypto

open Ix.Ixby

private def w (n : UInt32) : Value := .scalar (.word32 n)
private def g (n : Nat) : Value := .scalar (.field (Goldilocks.reduce n))
private def e (a b : Nat) : Value :=
  .scalar (.extField ⟨Goldilocks.reduce a, Goldilocks.reduce b⟩)
private def b (bytes : Array UInt8) : Value := .scalar (.bytes bytes)
private def boolean (value : Bool) : Value := .scalar (.bool value)

private def program (op : Primitive) : Program := { functions := #[{
  arity := op.arity
  blocks := #[⟨op.arity, .letOp (.primitive op ((List.range op.arity).map Operand.local)) 1⟩,
    ⟨op.arity + 1, .ret (.local op.arity)⟩] }] }

private def accepts (op : Primitive) (args : Array Value) (expected : Value) : Bool :=
  match Profile.execute {} (program op) args 3 with
  | .ok actual => actual == expected
  | _ => false

private def rejects (op : Primitive) (args : List Value) (error : Error) : Bool :=
  match op.eval {} args with
  | .error actual => actual == error
  | _ => false

private def hashMatches (bytes : Array UInt8) : Bool :=
  Ix.Ixby.Blake3.hash bytes == (Blake3.Rust.hash ⟨bytes⟩).val.data

private def pairId : CtorId := { block := 1 }

/-- A word primitive inside functional calls and immutable constructed data.
The original local remains available after the callee returns its new value. -/
private def wordPair : Program := {
  constructors := #[⟨pairId, 2⟩]
  functions := #[
    { arity := 1, blocks := #[
      ⟨1, .letOp (.call 1 [.local 0]) 1⟩,
      ⟨2, .letOp (.construct 0 [.local 0, .local 1]) 2⟩,
      ⟨3, .ret (.local 2)⟩] },
    { arity := 1, blocks := #[
      ⟨1, .letOp (.primitive .word32Add [.local 0, .literal (.word32 1)]) 1⟩,
      ⟨2, .ret (.local 1)⟩] }]
}

theorem word_scalar_preserves_functional_locals (a : UInt32) :
    execute {} wordPair #[w a] 7 = .ok (.ctor pairId #[w a, w (a + 1)]) := by
  rfl

private def checks : List (String × Bool) := [
  ("word primitive composes with calls and immutable constructors",
    match Profile.execute {} wordPair #[w 0xffffffff] 7 with
    | .ok value => value == .ctor pairId #[w 0xffffffff, w 0]
    | _ => false),
  ("word addition wraps", accepts .word32Add #[w 0xffffffff, w 1] (w 0)),
  ("word subtraction wraps", accepts .word32Sub #[w 0, w 1] (w 0xffffffff)),
  ("word multiplication wraps", accepts .word32Mul #[w 0xffffffff, w 2] (w 0xfffffffe)),
  ("word and", accepts .word32And #[w 0xf0f0, w 0xff] (w 0xf0)),
  ("word or", accepts .word32Or #[w 0xf0, w 0x0f] (w 0xff)),
  ("word xor", accepts .word32Xor #[w 0xff, w 0x0f] (w 0xf0)),
  ("word shift left", accepts .word32Shl #[w 1, w 31] (w 0x80000000)),
  ("large shift left is zero", accepts .word32Shl #[w 1, w 32] (w 0)),
  ("word shift right", accepts .word32Shr #[w 0x80000000, w 31] (w 1)),
  ("large shift right is zero", accepts .word32Shr #[w 0xffffffff, w 0xffffffff] (w 0)),
  ("word rotate", accepts .word32Rotr #[w 1, w 1] (w 0x80000000)),
  ("word rotate modulo 32", accepts .word32Rotr #[w 1, w 33] (w 0x80000000)),
  ("word rotate by 32 is identity", accepts .word32Rotr #[w 42, w 32] (w 42)),
  ("word equality", accepts .word32Eq #[w 4, w 4] (boolean true)),
  ("word inequality", accepts .word32Eq #[w 4, w 5] (boolean false)),
  ("word comparison", accepts .word32Lt #[w 4, w 5] (boolean true)),
  ("word canonical LE bytes", accepts .word32ToBytes #[w 0x12345678] (b #[0x78, 0x56, 0x34, 0x12])),
  ("word bytes decode", accepts .bytesToWord32 #[b #[0x78, 0x56, 0x34, 0x12]] (w 0x12345678)),
  ("word bytes exact length", rejects .bytesToWord32 [b #[1, 0, 0, 0, 0]] (.primitiveValue .bytesToWord32)),
  ("word-to-field is injective", accepts .word32ToField #[w 0xffffffff] (g 0xffffffff)),
  ("field addition reduces", accepts .fieldAdd #[g (goldilocksModulus - 1), g 1] (g 0)),
  ("field subtraction reduces", accepts .fieldSub #[g 0, g 1] (g (goldilocksModulus - 1))),
  ("field product reduces before narrowing", accepts .fieldMul #[g (goldilocksModulus - 1), g (goldilocksModulus - 1)] (g 1)),
  ("field inverse zero", accepts .fieldInverse #[g 0] (g 0)),
  ("field inverse two", accepts .fieldInverse #[g 2] (g 9223372034707292161)),
  ("field equality", accepts .fieldEq #[g 9, g 9] (boolean true)),
  ("field inequality", accepts .fieldEq #[g 9, g 10] (boolean false)),
  ("field LE bytes", accepts .fieldToBytes #[g (goldilocksModulus - 1)] (b #[0, 0, 0, 0, 255, 255, 255, 255])),
  ("field bytes decode", accepts .bytesToField #[b (bytesLE 8 (goldilocksModulus - 1))] (g (goldilocksModulus - 1))),
  ("field wire p rejected", rejects .bytesToField [b (bytesLE 8 goldilocksModulus)] (.primitiveValue .bytesToField)),
  ("field wire u64 maximum rejected", rejects .bytesToField [b (bytesLE 8 (2 ^ 64 - 1))] (.primitiveValue .bytesToField)),
  ("field byte length checked", rejects .bytesToField [b #[]] (.primitiveValue .bytesToField)),
  ("extension addition", accepts .extAdd #[e 1 2, e 3 4] (e 4 6)),
  ("extension subtraction", accepts .extSub #[e 4 6, e 3 4] (e 1 2)),
  ("extension X squared is seven", accepts .extMul #[e 0 1, e 0 1] (e 7 0)),
  ("extension coefficient order", accepts .extMul #[e 1 2, e 3 4] (e 59 10)),
  ("extension inverse zero", accepts .extInverse #[e 0 0] (e 0 0)),
  ("extension inverse identity", accepts .extInverse #[e 1 0] (e 1 0)),
  ("extension equality", accepts .extEq #[e 1 2, e 1 2] (boolean true)),
  ("extension inequality", accepts .extEq #[e 1 2, e 2 1] (boolean false)),
  ("extension construction", accepts .extPack #[g 1, g 2] (e 1 2)),
  ("extension first coefficient", accepts .extFst #[e 1 2] (g 1)),
  ("extension second coefficient", accepts .extSnd #[e 1 2] (g 2)),
  ("byte length", accepts .bytesLength #[b #[3, 4, 5]] (w 3)),
  ("byte access", accepts .bytesGet #[b #[3, 255, 5], w 1] (w 255)),
  ("byte access bounds", rejects .bytesGet [b #[3], w 1] (.primitiveValue .bytesGet)),
  ("byte append", accepts .bytesAppend #[b #[1], b #[2, 3]] (b #[1, 2, 3])),
  ("byte slice", accepts .bytesSlice #[b #[1, 2, 3, 4], w 1, w 2] (b #[2, 3])),
  ("empty slice at end", accepts .bytesSlice #[b #[1, 2], w 2, w 0] (b #[])),
  ("slice cannot truncate bounds", rejects .bytesSlice [b #[1, 2], w 1, w 2] (.primitiveValue .bytesSlice)),
  ("slice addition does not wrap", rejects .bytesSlice [b #[1], w 0xffffffff, w 2] (.primitiveValue .bytesSlice)),
  ("byte equality", accepts .bytesEq #[b #[1, 2], b #[1, 2]] (boolean true)),
  ("byte inequality", accepts .bytesEq #[b #[1], b #[1, 0]] (boolean false)),
  ("Nat is not a word", rejects .word32Add [.scalar (.nat 1), w 2] (.primitiveType .word32Add)),
  ("word is not a field", rejects .fieldAdd [w 1, g 2] (.primitiveType .fieldAdd)),
  ("string is not bytes", rejects .blake3 [.scalar (.str "abc")] (.primitiveType .blake3)),
  ("hash input bound precedes computation",
    match Primitive.eval { byteArrayBytes := 1 } .blake3 [b #[1, 2]] with
    | .error (.limit .byteArrayBytes) => true | _ => false),
  ("hash output obeys byte capacity",
    match Primitive.eval { byteArrayBytes := 31 } .blake3 [b #[]] with
    | .error (.limit .byteArrayBytes) => true | _ => false),
  ("byte append output capacity",
    match Primitive.eval { byteArrayBytes := 1 } .bytesAppend [b #[1], b #[2]] with
    | .error (.limit .byteArrayBytes) => true | _ => false),
  ("profile excludes Nat operations",
    match Profile.validateProgram {} (program .natAdd) with
    | .error .unsupportedInstruction => true | _ => false),
  ("profile excludes even Nat zero inputs",
    match Profile.validateValues {} (program .word32ToBytes) #[.scalar (.nat 0)] with
    | .error .unsupportedScalar => true | _ => false),
  ("profile excludes strings",
    match Profile.validateValues {} (program .word32ToBytes) #[.scalar (.str "")] with
    | .error .unsupportedScalar => true | _ => false),
  ("profile rejects wide configuration",
    match Profile.validate { maxSteps := 2 ^ 32 } with
    | .error .configuration => true | _ => false),
  ("profile cannot enable Nat by raising capacity",
    match Profile.validate { limits := { natBits := 32, stringBytes := 0 } } with
    | .error .configuration => true | _ => false),
  ("profile step bound",
    match Profile.execute { maxSteps := 2 } (program .word32Add) #[w 1, w 2] 3 with
    | .error .steps => true | _ => false),
  ("profile depth bound",
    match Profile.validateValues { valueDepth := 0 } (program .word32ToBytes) #[w 0] with
    | .error .depth => true | _ => false),
  ("every crypto primitive has a unique round-tripping opcode",
    (cryptoPrimitives.toList.zipIdx).all (fun (op, i) => op.cryptoOpcode == some i)),
  ("all crypto primitive arities checked",
    cryptoPrimitives.toList.all (fun op => rejects op [] (.arityMismatch op.arity 0))),
  ("nontrivial extension inverses",
    (List.range 31).all fun i =>
      let a : ExtGoldilocks := ⟨Goldilocks.reduce (i + 1), Goldilocks.reduce (2 * i + 3)⟩
      a.mul a.inverse == ⟨1, 0⟩),
  ("base inverses and canonical reduction",
    (List.range 64).all fun i =>
      let a := Goldilocks.reduce (goldilocksModulus - i - 1)
      a.mul a.inverse == 1),
  ("hash primitive executes through the profile",
    accepts .blake3 #[b "abc".toUTF8.data] (b (Blake3.Rust.hash "abc".toUTF8).val.data)),
  ("BLAKE3 exhaustive short lengths",
    (List.range 130).all fun n => hashMatches ((Array.range n).map (fun i => (i % 251).toUInt8))),
  ("BLAKE3 block/chunk/tree boundaries",
    [255, 256, 257, 1023, 1024, 1025, 2047, 2048, 2049, 3072, 3073,
      4096, 5120, 6144, 7168, 8192, 8193, 16385, 65536].all fun n =>
      hashMatches ((Array.range n).map (fun i => (i % 251).toUInt8)))
]

-- FFI is an independent conformance oracle in tests only; the machine and
-- its logical execution theorem do not import it or assume its correctness.
#guard checks.all (·.2)

public def suite : IO UInt32 := do
  IO.println "ixby-crypto (reference primitives and profile)"
  let mut failed := 0
  for (name, passed) in checks do
    if passed then IO.println s!"  ✓ {name}"
    else
      failed := failed + 1
      IO.eprintln s!"  ✗ {name}"
  IO.println s!"{checks.length - failed}/{checks.length} checks passed"
  return if failed == 0 then 0 else 1

end Tests.Ixby.Crypto
