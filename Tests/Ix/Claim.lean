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
  match Claim.de bytes, runGet Claim.get bytes with
  | .ok c1, .ok c2 => c == c1 && c == c2
  | _, _ => false

def proofSerde (p : Ixon.Proof) : Bool :=
  let bytes := Ixon.Proof.ser p
  match Ixon.Proof.de bytes with
  | .ok p' => p'.claim == p.claim && p'.proof == p.proof
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
  -- Compile claims
  ++ test "Compile immortal roundtrip" (claimSerde (.compile
    { env := addr1, roleTable := none, target := addr2, policy := .immortal, abiArity := 2, elfHash := addr3 }))
  ++ test "Compile zeroRc roundtrip" (claimSerde (.compile
    { env := addr1, roleTable := some addr2, target := addr2, policy := .zeroRc, abiArity := 3, elfHash := addr3 }))
  ++ test "Compile plainRc roundtrip" (claimSerde (.compile
    { env := addr1, roleTable := some addr3, target := addr2, policy := .plainRc, abiArity := 1, elfHash := addr3 }))
  ++ test "Compile proof roundtrip" (proofSerde
    { claim := .compile { env := addr1, roleTable := some addr1, target := addr2, policy := .zeroRc, abiArity := 2, elfHash := addr3 }
      proof := ⟨#[0x10, 0x20, 0x30]⟩ })

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
  -- Compile: deterministic 103- and 135-byte wire vectors shared with IxCC.CompileClaim
  ++ (let envHash : Address := ⟨ByteArray.mk (Array.replicate 32 0x11)⟩
      let target : Address := ⟨ByteArray.mk (Array.replicate 32 0x22)⟩
      let elfHash : Address := ⟨ByteArray.mk (Array.replicate 32 0x33)⟩
      let cc : Ix.CompileClaim :=
        { env := envHash, roleTable := none, target := target, policy := .plainRc, abiArity := 3
          elfHash := elfHash }
      let compileBytes := Claim.ser (.compile cc)
      -- The claim names the role table (validator `07`): `00` after `env` for an
      -- environment without a role binding, `01` and the table's address otherwise.
      let boundCc : Ix.CompileClaim :=
        { cc with roleTable := some ⟨ByteArray.mk (Array.replicate 32 0x44)⟩ }
      let expectedBoundBytes : ByteArray :=
        ByteArray.mk (#[0xE8, 0x05, 0x04, 0x07]
          ++ Array.replicate 32 0x11 ++ #[0x01] ++ Array.replicate 32 0x44
          ++ Array.replicate 32 0x22 ++ #[0x02, 0x03] ++ Array.replicate 32 0x33)
      -- The former format (validator `06`, no role table) is refused.
      let formerBytes : ByteArray :=
        ByteArray.mk (#[0xE8, 0x05, 0x04, 0x06]
          ++ Array.replicate 32 0x11 ++ Array.replicate 32 0x22
          ++ #[0x02, 0x03] ++ Array.replicate 32 0x33)
      let expectedCompileBytes : ByteArray :=
        ByteArray.mk (#[0xE8, 0x05, 0x04, 0x07]
          ++ Array.replicate 32 0x11 ++ #[0x00]
          ++ Array.replicate 32 0x22
          ++ #[0x02, 0x03]
          ++ Array.replicate 32 0x33)
      -- `abiArity`'s `N0` code at its boundaries; `IxCC/IxCCTests/Pipeline/Compiler.lean`
      -- pins the same vectors for `IxCC.CompileClaim` (B4-2). `80 80` is 256.
      let arityClaimBytes (arity : List UInt8) : ByteArray :=
        ByteArray.mk (#[0xE8, 0x05, 0x04, 0x07] ++ Array.replicate 32 0x11 ++ #[0x00]
          ++ Array.replicate 32 0x22 ++ #[0x02] ++ arity.toArray ++ Array.replicate 32 0x33)
      let arityVectors : List (UInt64 × List UInt8) := [
        (0, [0x00]), (5, [0x05]), (6, [0x06]), (127, [0x7F]), (128, [0x80, 0x00]),
        (256, [0x80, 0x80]), (16511, [0xBF, 0xFF]), (16512, [0xC0, 0x00, 0x00]),
        (18446744073709551615, [0xC3, 0x7F, 0xBF, 0xFE, 0xFE, 0xFE, 0xFF, 0xFF, 0xFF])]
      let arityRejected : List (List UInt8) :=
        [[0xC4], [0xC3, 0x80, 0xBF, 0xFE, 0xFE, 0xFE, 0xFF, 0xFF, 0xFF]]
      test "Compile wire header is E8 05 04 07"
        (compileBytes.extract 0 4 == ⟨#[0xE8, 0x05, 0x04, 0x07]⟩)
      ++ test "Compile wire size is 103 without a role table" (compileBytes.size == 103)
      ++ test "Compile wire matches deterministic 103-byte vector"
           (compileBytes == expectedCompileBytes)
      ++ test "Compile with a role table matches deterministic 135-byte vector and roundtrips"
           (Claim.ser (.compile boundCc) == expectedBoundBytes &&
             (Claim.de expectedBoundBytes).toOption == some (.compile boundCc))
      ++ test "Compile former format (validator 06, no role table) is refused"
           ((Claim.de formerBytes).toOption.isNone && (Claim.de (formerBytes.set! 3 0x07)).toOption.isNone
             && (Claim.de (expectedCompileBytes.set! 3 0x06)).toOption.isNone
             && (Claim.de (expectedCompileBytes.set! 36 0x02)).toOption.isNone)
      ++ test "Compile deterministic vector roundtrips via Claim.de"
           ((Claim.de compileBytes).toOption == some (.compile cc))
      ++ test "Compile abiArity N0 vectors shared with IxCC.CompileClaim"
           (arityVectors.all fun (arity, bytes) =>
             Claim.ser (.compile { cc with abiArity := arity }) == arityClaimBytes bytes &&
               (Claim.de (arityClaimBytes bytes)).toOption == some (.compile { cc with abiArity := arity }))
      ++ test "Compile invalid and overflowing abiArity codes are refused"
           (arityRejected.all fun bytes => (Claim.de (arityClaimBytes bytes)).toOption.isNone)
      ++ test "Compile is not read under the role-binding (E8 03) or literal-class (E8 04) tags"
           ((Claim.de (compileBytes.set! 1 0x03)).toOption.isNone
             && (Claim.de (compileBytes.set! 1 0x04)).toOption.isNone)
      ++ test "Compile proof (F8 00) wraps the compile claim"
           (let proof : Ixon.Proof := { claim := .compile cc, proof := ⟨#[7]⟩ }
            let bytes := Ixon.Proof.ser proof
            bytes.extract 0 2 == ⟨#[0xF8, 0x00]⟩ &&
              (Ixon.Proof.de bytes).toOption.map (·.claim) == some (.compile cc)))

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

