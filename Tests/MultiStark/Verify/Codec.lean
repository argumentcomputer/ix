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

private def wireChecks : IO (List Check) := do
  let state : Wire.ReadState := { bytes := #[99, 1, 0, 0, 0, 2, 0, 0, 0, 77], offset := 1, vectorLimit := 5, items := 7 }
  let emptyState : Wire.ReadState := { bytes := #[], vectorLimit := 3, items := 3 }
  let nested : Array Bytes := #[#[1, 2], #[3]]
  let nestedBytes := bytesOf (Wire.encode {} (Wire.writeVector (Wire.writeVector Wire.writeByte) nested))
  let large := (Array.range 100000).map Nat.toUInt8
  return [
    ("reader advances the cursor without changing bytes or budgets", match (Wire.readNat 4).run state with
      | .ok (value, final) => value == 1 && final.offset == 5 && final.bytes == state.bytes &&
        final.vectorLimit == 5 && final.items == 7
      | .error _ => false),
    ("readBytes accepts the exact remaining boundary", match (Wire.readBytes 9).run state with
      | .ok (bytes, final) => bytes == state.bytes.extract 1 10 && final.offset == 10
      | .error _ => false),
    ("readBytes rejects one byte past the boundary", errorIs ((Wire.readBytes 10).run state) .truncated),
    ("zero-width integer has exactly one admitted value", bytesOf (Wire.encode {} (Wire.writeNat 0 0)) == #[] &&
      errorIs (Wire.encode {} (Wire.writeNat 0 1)) .integerRange &&
      match Wire.decode {} #[] (Wire.readNat 0) with | .ok value => value == 0 | .error _ => false),
    ("zero count performs no element read", match (Wire.readCounted 0 Wire.readByte).run emptyState with
      | .ok (values, final) => values.isEmpty && final.offset == 0 && final.items == 3
      | .error _ => false),
    ("vector budget is checked before the first element", errorIs
      ((Wire.readCounted 4 Wire.readByte).run emptyState) .vectorLimit),
    ("item budget is checked before the first element", errorIs
      ((Wire.readCounted 3 Wire.readByte).run { emptyState with items := 2 }) .itemLimit),
    ("counted reader charges all items even for zero-byte elements", match
      (Wire.readCounted 3 (Wire.readBytes 0)).run emptyState with
      | .ok (values, final) => values == #[#[], #[], #[]] && final.items == 0 && final.offset == 0
      | .error _ => false),
    ("nested reader charges outer and inner elements exactly", match Wire.decode
      { vector := 2, items := 5 } nestedBytes (Wire.readVector (Wire.readVector Wire.readByte)) with
      | .ok values => values == nested | .error _ => false),
    ("nested reader cannot spend an outer item twice", errorIs (Wire.decode
      { vector := 2, items := 4 } nestedBytes (Wire.readVector (Wire.readVector Wire.readByte))) .itemLimit),
    ("nested writer uses the same global item accounting", errorIs (Wire.encode
      { vector := 2, items := 4 } (Wire.writeVector (Wire.writeVector Wire.writeByte) nested)) .itemLimit),
    ("Boolean grammar rejects every other byte tag", (Array.range 256).all fun tag =>
      (Wire.decode {} #[tag.toUInt8] Wire.readBool).isOk == (tag < 2)),
    ("Option grammar rejects every other byte tag", (Array.range 256).all fun tag =>
      (Wire.decode {} (#[tag.toUInt8] ++ if tag == 1 then #[99] else #[]) (Wire.readOption Wire.readByte)).isOk == (tag < 2)),
    ("large admitted vector preserves exact order with tail recursion", match Wire.decode
      { bytes := 100000, vector := 100000, items := 100000 } large (Wire.readCounted 100000 Wire.readByte) with
      | .ok values => values == large | .error _ => false)
  ]

private def checks : IO (List Check) := do
  let claimBytes := bytesOf (encodeClaims {} #[#[1, 2], #[], #[3]])
  let smallClaimBytes := bytesOf (encodeClaims {} #[#[1, 2]])
  return (← wireChecks) ++ [
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
