/-
  Serialization roundtrip and encoding tests for Ix.Claim types.
-/

module
public import Ix.Claim
public import Ix.SpecDigest
public import Tests.Gen.Claim

open LSpec SlimCheck
open Ixon (runGet)
open Ix (RevealConstructorInfo RevealRecursorRule RevealConstantInfo Claim)

/-! ## Roundtrip helper -/

def claimSerde (c : Claim) : Bool :=
  let bytes := Claim.ser c
  match runGet Claim.get bytes with
  | .ok c' => c == c'
  | .error _ => false

/-! ## Unit tests -/

private def addr1 : Address := Address.blake3 "hello".toUTF8
private def addr2 : Address := Address.blake3 "world".toUTF8
private def addr3 : Address := Address.blake3 "test".toUTF8

/-- This specification set, a stand-in binding hash, the standard axioms only.
    The same fixture as `test_ctx` in `crates/ixon/src/proof.rs`. -/
private def ctx : Ix.ClaimContext :=
  { spec := Ix.SpecDigest.specDigest.toOption.getD default
    binding := Address.blake3 "binding".toUTF8
    axioms := none }

def claimUnits : TestSeq :=
  -- Typechecking claims: both no-asm and with-asm forms.
  test "Eval no-asm roundtrip" (claimSerde (.eval ctx addr1 addr2 none))
  ++ test "Eval with-asm roundtrip"
       (claimSerde (.eval ctx addr1 addr2 (some addr3)))
  ++ test "Check no-asm roundtrip" (claimSerde (.check ctx addr1 none))
  ++ test "Check with-asm roundtrip"
       (claimSerde (.check ctx addr1 (some addr2)))
  ++ test "CheckEnv no-asm roundtrip" (claimSerde (.checkEnv ctx addr1 none))
  ++ test "CheckEnv with-asm roundtrip"
       (claimSerde (.checkEnv ctx addr1 (some addr2)))
  -- Contains
  ++ test "Contains roundtrip" (claimSerde (.contains addr1 addr2))
  -- Catalog (the first multi-byte claim tag)
  ++ test "Catalog roundtrip" (claimSerde (.catalog addr1))
  ++ test "CheckEnv under a literal class roundtrip"
       (claimSerde (.checkEnv { ctx with literalClass := true } addr1 none))
  -- Reveal claim variants (carried over from previous suite)
  ++ test "Reveal defn safety-only" (claimSerde (.reveal addr1
    (.defn none (some .safe) none none none)))
  ++ test "Reveal defn all fields" (claimSerde (.reveal addr1
    (.defn (some .defn) (some .safe) (some 3) (some addr2) (some addr3))))
  ++ test "Reveal axio with type" (claimSerde (.reveal addr1
    (.axio none none (some addr2))))
  ++ test "Reveal recr with rules" (claimSerde (.reveal addr1
    (.recr (some true) none (some 2) none none none none none
      (some #[⟨0, 3, addr2⟩]))))
  ++ test "Reveal muts with component" (claimSerde (.reveal addr1
    (.muts #[(0, .defn (some .defn) (some .safe) none none none)])))
  ++ test "Reveal cPrj" (claimSerde (.reveal addr1
    (.cPrj (some 0) (some 1) (some addr2))))
  ++ test "Reveal rPrj" (claimSerde (.reveal addr1
    (.rPrj (some 2) (some addr2))))
  ++ test "Reveal iPrj" (claimSerde (.reveal addr1
    (.iPrj (some 3) (some addr2))))
  ++ test "Reveal dPrj" (claimSerde (.reveal addr1
    (.dPrj (some 0) (some addr2))))
  ++ test "Reveal defn all none" (claimSerde (.reveal addr1
    (.defn none none none none none)))
  ++ test "Reveal quot" (claimSerde (.reveal addr1
    (.quot (some .type) (some 1) (some addr2))))

/-! ## Byte-level encoding tests

  Claim variants 3..=7 are single-byte TagN (`f = 4`) headers
  `0xE3`..`0xE7`, followed by the scope bytes (object format 4, then the
  validator). The typing claims (validator 3, erased-lean-v2) then carry
  their context: specification digest, binding hash and an axioms opt byte,
  65 bytes when there are no further axioms. Each claim has an opt byte (`0x00` for `none`,
  `0x01`+32-byte address for `some`).
-/

def claimEncodingTests : TestSeq :=
  let evalBytes := Claim.ser (.eval ctx addr1 addr2 none)
  let evalWithAsm := Claim.ser (.eval ctx addr1 addr2 (some addr3))
  let checkBytes := Claim.ser (.check ctx addr1 none)
  let checkWithAsm := Claim.ser (.check ctx addr1 (some addr2))
  let checkEnvBytes := Claim.ser (.checkEnv ctx addr1 none)
  let containsBytes := Claim.ser (.contains addr1 addr2)
  let revealSafetyOnly := Claim.ser
    (.reveal addr1 (.defn none (some .safe) none none none))
  let revealAllFields := Claim.ser (.reveal addr1
    (.defn (some .defn) (some .safe) (some 3) (some addr2) (some addr3)))
  let retiredRefused : Bool := match Claim.de (checkBytes.set! 2 1) with
    | .error e => (e.splitOn "erased-lean-v1 is retired").length > 1
    | .ok _ => false
  -- Two scope bytes follow each claim tag, then the 65-byte context.
  -- Eval = 133 bytes; with asm = 165
  test "Eval tag byte is 0xE3" (evalBytes.data[0]! == 0xE3)
  ++ test "Eval scope is object format 4, erased-lean-v2"
       (evalBytes.data[1]! == 4 && evalBytes.data[2]! == 3)
  ++ test "Eval context follows the scope"
       (evalBytes.extract 3 35 == ctx.spec.hash
         && evalBytes.extract 35 67 == ctx.binding.hash
         && evalBytes.data[67]! == 0)
  ++ test "Eval no-asm size is 133" (evalBytes.size == 133)
  ++ test "Eval with-asm size is 165" (evalWithAsm.size == 165)
  -- Check: tag + scope + context + 32 + option = 101 bytes; with asm = 133
  ++ test "Check tag byte is 0xE4" (checkBytes.data[0]! == 0xE4)
  ++ test "Check no-asm size is 101" (checkBytes.size == 101)
  ++ test "Check with-asm size is 133" (checkWithAsm.size == 133)
  -- CheckEnv: tag + scope + context + 32 + option = 101 bytes
  ++ test "CheckEnv tag byte is 0xE5" (checkEnvBytes.data[0]! == 0xE5)
  ++ test "CheckEnv no-asm size is 101" (checkEnvBytes.size == 101)
  ++ test "Check for the retired erased-lean-v1 validator is refused" retiredRefused
  ++ test "Check with an axioms commitment roundtrips"
       (claimSerde (.check { ctx with axioms := some addr3 } addr1 none))
  -- Reveal claim: 0xE6
  ++ test "Reveal tag byte is 0xE6" (revealSafetyOnly.data[0]! == 0xE6)
  -- Reveal: tag + scope + commitment + variant + mask + safety = 38
  ++ test "Reveal safety-only defn size is 38" (revealSafetyOnly.size == 38)
  ++ test "Reveal all-fields defn is larger"
       (revealAllFields.size > revealSafetyOnly.size)
  -- Contains: tag + scope + two addresses = 67
  ++ test "Contains tag byte is 0xE7" (containsBytes.data[0]! == 0xE7)
  ++ test "Contains size is 67" (containsBytes.size == 67)

/-! ## Catalog claim: wire pin + Rust digest parity

  The catalog claim is the first multi-byte claim tag (`0xE8 0x00`:
  TagN rung 2, since claim variants 0–7 fill rung 1). Its exact wire form is a
  cross-serializer commitment: `catalog_claim_wire_bytes_pinned` in
  `crates/ixon/src/proof.rs` asserts the SAME digest hex over the same
  fixture, so the two serializers cannot drift on the large-tag path
  without one of the pins going red.
-/

private def catMembers : Address := Address.blake3 "members".toUTF8

/-- Must equal the Rust pin in `proof.rs::catalog_claim_wire_bytes_pinned`. -/
private def catalogDigestPin : String :=
  "4f5686bd1a8386231370703d58223aca769c82c835964d4914ca41305a8030f3"

def catalogClaimTests : TestSeq :=
  let bytes := Claim.ser (.catalog catMembers)
  let proof : Ixon.Proof := { claim := .catalog catMembers, proof := .empty }
  let proofBytes := Ixon.Proof.ser proof
  let proofRoundtrips : Bool := match Ixon.Proof.de proofBytes with
    | .ok p => p.claim == proof.claim && p.proof == proof.proof
    | .error _ => false
  test "Catalog tag is 2 bytes 0xE8 0x00 (TagN 4 0xE 8)"
    (bytes.data[0]! == 0xE8 && bytes.data[1]! == 0x00)
  ++ test "Catalog scope is object format 4, erased-lean-v2"
       (bytes.data[2]! == 4 && bytes.data[3]! == 3)
  ++ test "Catalog is the scope and the members root, 36 bytes" (bytes.size == 4 + 32)
  ++ test "Catalog digest parity with Rust pin"
       (toString (Address.blake3 bytes) == catalogDigestPin)
  ++ test "Catalog proof wrapper tag is single-byte 0xF5"
       (proofBytes.data[0]! == 0xF5)
  ++ test "Catalog proof wrapper roundtrips" proofRoundtrips

/-- A reveal mask bit beyond the variant's fields is refused, so one claim has
one encoding. The Rust reader refuses the same bytes
(`proof.rs::reveal_mask_refuses_unknown_bits`): a Reveal claim over the zero
commitment, its variant byte, then the one-byte mask. -/
def revealMaskTests : TestSeq :=
  let header : Array UInt8 := #[0xE6, 0x04, 0x00] ++ Array.replicate 32 0
  let bytes (variant mask : UInt8) : ByteArray := ⟨header ++ #[variant, mask]⟩
  test "Reveal defn with no fields reads" (Ix.Claim.de (bytes 0 0) matches .ok _)
  ++ test "Reveal defn mask bit 5 refused" (Ix.Claim.de (bytes 0 0x20) matches .error _)
  ++ test "Reveal axio with no fields reads" (Ix.Claim.de (bytes 2 0) matches .ok _)
  ++ test "Reveal axio mask bit 3 refused" (Ix.Claim.de (bytes 2 0x08) matches .error _)
  ++ test "Reveal dprj mask bit 2 refused" (Ix.Claim.de (bytes 7 0x04) matches .error _)

/-! ## Suite -/

public def Tests.Claim.suite : List TestSeq := [
  claimUnits,
  claimEncodingTests,
  catalogClaimTests,
  revealMaskTests,
  checkIO "Claim serde roundtrips" (∀ c : Claim, claimSerde c),
]

