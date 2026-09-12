module
import Tests.Ixby.Common
import Ix.MultiStark.Verify.Codec

namespace Tests.MultiStark.Verify.Codec

open _root_.MultiStark.Verify
open _root_.MultiStark.Verify.Codec
open Tests.Ixby (Check runChecks)

private def digest : Digest := ⟨(Array.range 32).map Nat.toUInt8, by simp⟩
private def ext : Ext := ⟨Ix.Ixby.Goldilocks.reduce (Ix.Ixby.goldilocksModulus - 1), 42⟩
private def round : OpenedRound := #[#[#[ext, ⟨3, 4⟩], #[]], #[]]
private def empty : Proof := {
  active := #[], commitments := ⟨#[], #[], #[]⟩, accumulators := #[], logDegrees := #[]
  fri := ⟨#[], #[], #[], #[], #[], 0⟩
  quotient := #[], preprocessed := none, stage1 := #[], stage2 := #[]
}
private def fixture : Proof := {
  active := #[true, false, true], commitments := ⟨#[digest], #[digest, digest], #[]⟩
  accumulators := #[ext, ⟨0, 0⟩], logDegrees := #[3, 8]
  fri := {
    commits := #[#[digest], #[digest, digest]], commitPow := #[7, 8]
    inputOpenings := #[⟨#[#[#[1, 2, 3], #[]], #[#[4, 5]]], #[digest]⟩]
    commitOpenings := #[⟨1, #[#[ext], #[⟨0, 1⟩]], #[digest]⟩]
    finalPoly := #[ext, ⟨5, 6⟩], queryPow := 9
  }
  quotient := round, preprocessed := some round, stage1 := round, stage2 := round
}

private def bytesOf (result : Except DecodeError Bytes) : Bytes :=
  match result with | .ok bytes => bytes | .error _ => #[]
private def errorIs {α : Type} (result : Except DecodeError α) (expected : DecodeError) : Bool :=
  match result with | .error actual => actual == expected | .ok _ => false
private def roundTrip (proof : Proof) : Bool :=
  match encodeProof {} proof with
  | .error _ => false
  | .ok bytes => match decodeProof {} bytes with
    | .error _ => false
    | .ok checked => checked.value == proof

private def emptyBytes : Bytes := Array.replicate 121 0
private def fixtureBytes : Bytes := bytesOf (encodeProof {} fixture)

private def checks : IO (List Check) := do
  let claimBytes := bytesOf (encodeClaims {} #[#[1, 2], #[], #[3]])
  let smallClaimBytes := bytesOf (encodeClaims {} #[#[1, 2]])
  return [
    ("empty native-shaped record has the independent 121-byte golden wire",
      bytesOf (encodeProof {} empty) == emptyBytes),
    ("codec round trips all multiproof fields", roundTrip fixture),
    ("codec round trips absent preprocessed openings", roundTrip { fixture with preprocessed := none }),
    ("codec round trips present empty preprocessed openings", roundTrip
      { empty with preprocessed := some #[] }),
    ("encoding admission does not assert proof validity", roundTrip empty),
    ("all proof prefixes are rejected", (List.range fixtureBytes.size).all
      (fun size => !(decodeProof {} (fixtureBytes.extract 0 size)).isOk)),
    ("trailing proof bytes rejected", errorIs (decodeProof {} (fixtureBytes.push 0)) .trailing),
    ("noncanonical activation Boolean rejected", errorIs
      (decodeProof {} (fixtureBytes.set! 8 2)) .tag),
    ("noncanonical Option discriminator rejected", errorIs
      (decodeProof {} (emptyBytes.set! 104 2)) .tag),
    ("hostile u64 vector count rejected before allocation", errorIs
      (decodeProof {} (Array.replicate 8 255 ++ emptyBytes.extract 8 emptyBytes.size)) .vectorLimit),
    ("global nested-item budget enforced", errorIs (decodeProof { items := 3 } fixtureBytes) .itemLimit),
    ("per-vector budget enforced", errorIs (decodeProof { vector := 2 } fixtureBytes) .vectorLimit),
    ("decoder byte admission enforced", errorIs
      (decodeProof { bytes := 120 } emptyBytes) .byteLimit),
    ("encoder byte admission enforced", errorIs (encodeProof { bytes := 120 } empty) .byteLimit),
    ("encoder nested-item budget enforced", errorIs (encodeProof { items := 3 } fixture) .itemLimit),
    ("encoder vector budget enforced", errorIs (encodeProof { vector := 2 } fixture) .vectorLimit),
    ("u64 encoder cannot silently narrow", errorIs
      (Wire.encode {} (Wire.writeNat 8 (2 ^ 64))) .integerRange),
    ("canonical field endian vector", bytesOf (Wire.encode {} (Wire.writeField ext.c0)) ==
      #[0, 0, 0, 0, 255, 255, 255, 255]),
    ("modulus is rejected rather than reduced", errorIs
      (Wire.decode {} #[1, 0, 0, 0, 255, 255, 255, 255] Wire.readField) .field),
    ("maximum u64 is rejected as a field", errorIs
      (Wire.decode {} (Array.replicate 8 255) Wire.readField) .field),
    ("extension second coefficient is canonical", errorIs (Wire.decode {}
      (Array.replicate 8 0 ++ #[1, 0, 0, 0, 255, 255, 255, 255]) Wire.readExt) .field),
    ("FRI query PoW witness is a canonical field", errorIs (decodeProof {}
      (emptyBytes.extract 0 88 ++ #[1, 0, 0, 0, 255, 255, 255, 255] ++
        emptyBytes.extract 96 emptyBytes.size)) .field),
    ("canonicality evidence is checked", errorIs
      (Wire.canonicalize (fun (_ : Unit) => .ok #[1]) #[2] ()) .nonCanonical),
    ("empty native claims golden vector", bytesOf (encodeClaims {} #[]) == Array.replicate 8 0),
    ("native claims preserve outer and inner lengths", match decodeClaims {} claimBytes with
      | .ok checked => checked.value == #[#[1, 2], #[], #[3]]
      | .error _ => false),
    ("native claims trailing bytes rejected", errorIs
      (decodeClaims {} (Array.replicate 9 0)) .trailing),
    ("all small native claim prefixes rejected", (List.range smallClaimBytes.size).all
      (fun size => !(decodeClaims {} (smallClaimBytes.extract 0 size)).isOk)),
    ("native claim field words must be canonical", errorIs (decodeClaims {}
      (Wire.littleEndian 8 1 ++ Wire.littleEndian 8 1 ++ Wire.littleEndian 8 Ix.Ixby.goldilocksModulus)) .field),
    ("hostile native claim length rejected before allocation", errorIs
      (decodeClaims {} (Array.replicate 8 255)) .vectorLimit),
    ("native claims respect global item budget", errorIs
      (decodeClaims { items := 2 } (bytesOf (encodeClaims {} #[#[1, 2]]))) .itemLimit)
  ]

public def suite : IO UInt32 := runChecks "stage2-codec" checks

end Tests.MultiStark.Verify.Codec
