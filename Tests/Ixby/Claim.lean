module
import Tests.Ixby.Common
import Ix.Ixby.Claim.Ixon

namespace Tests.Ixby.Claim

open Ix.Ixby
open Ix.Ixby.Claim
open Codec (Bytes)

private def digest (byte : UInt8) : Commitment.Digest :=
  ⟨Array.replicate 32 byte, by simp⟩

private def statement : Commitment.Statement := ⟨digest 1, digest 2, digest 3, digest 4⟩
private def publicExpected : PublicStatement := publicStatement statement

private def execGolden : Bytes :=
  #[0x49, 0x58, 0x42, 0x45, 0, 0, 0, 0] ++
    Array.replicate 32 1 ++ Array.replicate 32 2 ++
    Array.replicate 32 3 ++ Array.replicate 32 4
private def publicGolden : Bytes :=
  #[0x49, 0x58, 0x42, 0x52, 0, 0, 0, 0] ++
    Array.replicate 32 1 ++ Array.replicate 32 2 ++ Array.replicate 32 4

private def identity : Program := { functions := #[{
  arity := 1, blocks := #[⟨1, .ret (.local 0)⟩] }] }
private def falseGuest : Program := { functions := #[{
  arity := 1, blocks := #[⟨1, .ret (.literal (.bool true))⟩] }] }
private def bytesOf (value : Except Codec.Error Bytes) : Bytes :=
  match value with | .ok bytes => bytes | .error _ => #[]
private def code : Bytes := bytesOf (Codec.encodeProgram {} identity)
private def trueCode : Bytes := bytesOf (Codec.encodeProgram {} falseGuest)
private def root (byte : UInt8) : Address := ⟨⟨Array.replicate 32 byte⟩⟩
private def claim (byte : UInt8) : Ix.Claim := .checkEnv (root byte) none
private def claimBytes (byte : UInt8) : ByteArray := Ix.Claim.ser (claim byte)
private def expected (byte : UInt8) := IxonAdapter.expected {} code (claim byte)

private def rejects {ε α : Type} (value : Except ε α) : Bool := !value.isOk

private def okIs {ε α : Type} [BEq α] (value : Except ε α) (expected : α) : Bool :=
  match value with | .ok actual => actual == expected | .error _ => false

private def different {ε : Type} (left right : Except ε PublicStatement) : Bool :=
  match left, right with
  | .ok left, .ok right => left != right && left.digest != right.digest
  | _, _ => false

private def checks : IO (List Check) := do
  return [
    ("full Exec golden wire", okIs (encodeExec statement) execGolden),
    ("public result golden wire", okIs (encodePublic publicExpected) publicGolden),
    ("full Exec size is 136", execGolden.size == execWireBytes),
    ("public result size is 104", publicGolden.size == publicWireBytes),
    ("full Exec round trip", match decodeExec execGolden with
      | .ok decoded => decoded.value == statement | _ => false),
    ("public result round trip", match decodePublic publicGolden with
      | .ok decoded => decoded.value == publicExpected | _ => false),
    ("all full Exec prefixes rejected", (List.range execGolden.size).all
      (fun size => rejects (decodeExec (execGolden.extract 0 size)))),
    ("all public result prefixes rejected", (List.range publicGolden.size).all
      (fun size => rejects (decodePublic (publicGolden.extract 0 size)))),
    ("full Exec trailing data rejected", rejects (decodeExec (execGolden.push 0))),
    ("public result trailing data rejected", rejects (decodePublic (publicGolden.push 0))),
    ("full Exec version rejected", rejects (decodeExec (execGolden.set! 4 1))),
    ("public result version rejected", rejects (decodePublic (publicGolden.set! 4 1))),
    ("full Exec wrong domain rejected", rejects (decodeExec (execGolden.set! 3 0x52))),
    ("public result wrong domain rejected", rejects (decodePublic (publicGolden.set! 3 0x45))),
    ("Exec and public codecs cannot be substituted", rejects (decodeExec publicGolden) &&
      rejects (decodePublic execGolden)),
    ("semantic profile is not a result statement", rejects
      (decodePublic (bytesOf (Codec.encodeProfile {})))),
    ("public digest uses independent domain 5 preimage", publicExpected.digest.bytes ==
      (Blake3.Rust.hash ⟨"IxBy/commit/v0".toUTF8.data ++ #[0, 5] ++
        (digest 1).bytes ++ (digest 2).bytes ++ (digest 4).bytes⟩).val.data),
    ("public and full statement digests differ", publicExpected.digest != statement.digest),
    ("projection hides only input commitment", publicStatement
      { statement with input := digest 9 } == publicExpected &&
        ({ statement with input := digest 9 } : Commitment.Statement).digest != statement.digest),
    ("projection retains every public component", [
      { statement with profile := digest 9 }, { statement with program := digest 9 },
      { statement with output := digest 9 }
      ].all (fun changed => publicStatement changed != publicExpected)),
    ("canonical closed CheckEnv golden wire", (claimBytes 7).data ==
      #[0xe5] ++ Array.replicate 32 7 ++ #[0]),
    ("canonical public claim round trip", match IxonAdapter.decodePublicClaim (claimBytes 7) with
      | .ok checked => checked.claim == claim 7 | _ => false),
    ("public claim prefixes rejected", (List.range 34).all (fun size => rejects
      (IxonAdapter.decodePublicClaim ((claimBytes 7).extract 0 size)))),
    ("public claim trailing byte rejected", rejects
      (IxonAdapter.decodePublicClaim ((claimBytes 7).push 0))),
    ("public claim wrong kind rejected", rejects
      (IxonAdapter.decodePublicClaim ⟨(claimBytes 7).data.set! 0 0xe4⟩)),
    ("public claim noncanonical assumptions tag rejected", rejects
      (IxonAdapter.decodePublicClaim ⟨(claimBytes 7).data.set! 33 2⟩)),
    ("public claim nonminimal Tag4 rejected", rejects (IxonAdapter.decodePublicClaim
      ⟨#[0xe8, 5] ++ Array.replicate 32 7 ++ #[0]⟩)),
    ("conditional CheckEnv is not coerced to a closed claim", rejects
      (IxonAdapter.expected {} code (.checkEnv (root 7) (some (root 8))))),
    ("malformed conditional addresses cannot alias a closed byte envelope", rejects
      (IxonAdapter.expected {} code
        (.checkEnv ⟨⟨Array.replicate 31 7⟩⟩ (some ⟨⟨#[0]⟩⟩)))),
    ("Check is not coerced to CheckEnv", rejects
      (IxonAdapter.expected {} code (.check (root 7) none))),
    ("short public root rejected", rejects
      (IxonAdapter.expected {} code (.checkEnv ⟨⟨Array.replicate 31 7⟩⟩ none))),
    ("long public root rejected", rejects
      (IxonAdapter.expected {} code (.checkEnv ⟨⟨Array.replicate 33 7⟩⟩ none))),
    ("public expected statement needs no private input", (expected 7).isOk),
    ("wrong public claim changes expected statement", different (expected 7) (expected 8)),
    ("wrong guest changes expected statement", different (expected 7)
      (IxonAdapter.expected {} trueCode (claim 7))),
    ("wrong profile changes expected statement", different (expected 7)
      (IxonAdapter.expected { maxSteps := 100 } code (claim 7))),
    ("malformed guest cannot produce an approved statement", rejects
      (IxonAdapter.expected {} (code.push 0) (claim 7))),
    ("Bool.true output cannot substitute for C under the same guest", match
        IxonAdapter.expected {} trueCode (claim 7) with
      | .error _ => false
      | .ok expected => match Codec.encodeInput {} falseGuest #[claimResult (claimBytes 7).data] with
        | .error _ => false
        | .ok input => match Codec.execute {} trueCode input 2 with
          | .error _ => false
          | .ok execution => match Commitment.ofExecution execution with
            | .error _ => false
            | .ok actual => publicStatement actual != expected
              && actual.output != expected.output),
    ("expected claim is exactly the committed reference result", match expected 7 with
      | .error _ => false
      | .ok expected => match Codec.encodeInput {} identity #[claimResult (claimBytes 7).data] with
        | .error _ => false
        | .ok input => match Codec.execute {} code input 2 with
          | .error _ => false
          | .ok execution => match Commitment.ofExecution execution with
            | .error _ => false
            | .ok actual => publicStatement actual == expected),
    ("terminal adapter reconstructs C rather than accepting prover statement", match expected 7 with
      | .error _ => false
      | .ok pinned =>
        let check := fun actual (_ : Unit) => actual == pinned
        okIs (IxonAdapter.verifyWith {} code check (claim 7) ()) true &&
          okIs (IxonAdapter.verifyWith {} code check (claim 8) ()) false)
  ]

public def suite : IO UInt32 := runChecks "ixby-claim" checks

end Tests.Ixby.Claim
