/-
  Serialization roundtrip and encoding tests for Ix.Claim types.
-/

module
public import Ix.Claim
public import Ix.SpecDigest
public import Tests.Gen.Claim

open LSpec LSpec.Prop
open Ixon (runGet)
open Ix (RevealConstructorInfo RevealRecursorRule RevealConstantInfo Claim)

set_option compiler.extract_closed false

/-! ## Roundtrip helper -/

def claimSerde (c : Claim) : Bool :=
  let bytes := Claim.ser c
  match runGet Claim.get bytes with
  | .ok c' => c == c'
  | .error _ => false

/-! ## Unit tests -/

private def mkAddr1 (_ : Unit) : Address := Address.blake3 "hello".toUTF8
private def mkAddr2 (_ : Unit) : Address := Address.blake3 "world".toUTF8
private def mkAddr3 (_ : Unit) : Address := Address.blake3 "test".toUTF8

/-- This specification set, a stand-in binding hash, the standard axioms only.
    The same fixture as `test_ctx` in `crates/ixon/src/proof.rs`. -/
private def mkCtx (_ : Unit) : Ix.ClaimContext :=
  { spec := Ix.SpecDigest.specDigest.toOption.getD default
    binding := Address.blake3 "binding".toUTF8
    axioms := none }

def claimUnits : LSpec.Spec := do
  -- Typechecking claims: both no-asm and with-asm forms.
  itBool "Eval no-asm roundtrip" (claimSerde (.eval (mkCtx ()) (mkAddr1 ()) (mkAddr2 ()) none))
  itBool "Eval with-asm roundtrip"
    (claimSerde (.eval (mkCtx ()) (mkAddr1 ()) (mkAddr2 ()) (some (mkAddr3 ()))))
  itBool "Check no-asm roundtrip" (claimSerde (.check (mkCtx ()) (mkAddr1 ()) none))
  itBool "Check with-asm roundtrip"
    (claimSerde (.check (mkCtx ()) (mkAddr1 ()) (some (mkAddr2 ()))))
  itBool "CheckEnv no-asm roundtrip" (claimSerde (.checkEnv (mkCtx ()) (mkAddr1 ()) none))
  itBool "CheckEnv with-asm roundtrip"
    (claimSerde (.checkEnv (mkCtx ()) (mkAddr1 ()) (some (mkAddr2 ()))))
  -- Contains
  itBool "Contains roundtrip" (claimSerde (.contains (mkAddr1 ()) (mkAddr2 ())))
  -- Catalog (the first multi-byte claim tag)
  itBool "Catalog roundtrip" (claimSerde (.catalog (mkAddr1 ())))
  itBool "CheckEnv under a literal class roundtrip"
    (claimSerde (.checkEnv { mkCtx () with literalClass := true } (mkAddr1 ()) none))
  -- Reveal claim variants (carried over from previous suite)
  itBool "Reveal defn safety-only" (claimSerde (.reveal (mkAddr1 ())
    (.defn none (some .safe) none none none none) none))
  itBool "Reveal defn all fields" (claimSerde (.reveal (mkAddr1 ())
    (.defn (some .defn) (some .safe) (some 3) (some (mkAddr2 ())) (some (mkAddr3 ()))
      (some { alloc := .noAlloc, boundedStack := true })) (some (mkAddr3 ()))))
  itBool "Reveal axio with type" (claimSerde (.reveal (mkAddr1 ())
    (.axio none none (some (mkAddr2 ()))) none))
  itBool "Reveal recr with rules" (claimSerde (.reveal (mkAddr1 ())
    (.recr (some true) none (some 2) none none none none none
      (some #[⟨0, 3, mkAddr2 ()⟩])) none))
  itBool "Reveal muts with component" (claimSerde (.reveal (mkAddr1 ())
    (.muts #[(0, .defn (some .defn) (some .safe) none none none
      (some { alloc := .noRc, boundedStack := false }))]) none))
  itBool "Reveal muts constructor field modes" (claimSerde (.reveal (mkAddr1 ())
    (.muts #[(0, .indc none none none none none
      (some #[(0, { fieldModes := some #[.inherited, .shared] }),
              (1, { fieldModes := some #[] })]))]) (some (mkAddr2 ()))))
  itBool "Reveal cPrj" (claimSerde (.reveal (mkAddr1 ())
    (.cPrj (some 0) (some 1) (some (mkAddr2 ()))) none))
  itBool "Reveal rPrj" (claimSerde (.reveal (mkAddr1 ())
    (.rPrj (some 2) (some (mkAddr2 ()))) none))
  itBool "Reveal iPrj" (claimSerde (.reveal (mkAddr1 ())
    (.iPrj (some 3) (some (mkAddr2 ()))) none))
  itBool "Reveal dPrj" (claimSerde (.reveal (mkAddr1 ())
    (.dPrj (some 0) (some (mkAddr2 ()))) none))
  itBool "Reveal defn all none" (claimSerde (.reveal (mkAddr1 ())
    (.defn none none none none none none) none))
  itBool "Reveal quot" (claimSerde (.reveal (mkAddr1 ())
    (.quot (some .type) (some 1) (some (mkAddr2 ()))) none))

/-! ## Byte-level encoding tests

  Claim variants 3..=7 are single-byte TagN (`f = 4`) headers
  `0xE3`..`0xE7`, followed by the scope bytes (object format 4, then the
  validator). The typing claims (validator 3, erased-lean-v2) then carry
  their context: specification digest, binding hash and an axioms opt byte,
  65 bytes when there are no further axioms. Each claim has an opt byte (`0x00` for `none`,
  `0x01`+32-byte address for `some`).
-/

def claimEncodingTests : LSpec.Spec := do
  let mkEvalBytes (_ : Unit) : ByteArray := Claim.ser (.eval (mkCtx ()) (mkAddr1 ()) (mkAddr2 ()) none)
  let mkEvalWithAsm (_ : Unit) : ByteArray := Claim.ser (.eval (mkCtx ()) (mkAddr1 ()) (mkAddr2 ()) (some (mkAddr3 ())))
  let mkCheckBytes (_ : Unit) : ByteArray := Claim.ser (.check (mkCtx ()) (mkAddr1 ()) none)
  let mkCheckWithAsm (_ : Unit) : ByteArray := Claim.ser (.check (mkCtx ()) (mkAddr1 ()) (some (mkAddr2 ())))
  let mkCheckEnvBytes (_ : Unit) : ByteArray := Claim.ser (.checkEnv (mkCtx ()) (mkAddr1 ()) none)
  let mkContainsBytes (_ : Unit) : ByteArray := Claim.ser (.contains (mkAddr1 ()) (mkAddr2 ()))
  let mkRevealSafetyOnly (_ : Unit) : ByteArray := Claim.ser
    (.reveal (mkAddr1 ()) (.defn none (some .safe) none none none none) none)
  let mkRevealAllFields (_ : Unit) : ByteArray := Claim.ser (.reveal (mkAddr1 ())
    (.defn (some .defn) (some .safe) (some 3) (some (mkAddr2 ())) (some (mkAddr3 ()))
      (some { alloc := .noAlloc, boundedStack := true })) (some (mkAddr3 ())))
  -- Two scope bytes follow each claim tag, then the 65-byte context.
  -- Eval = 133 bytes; with asm = 165
  itBool "Eval tag byte is 0xE3" ((mkEvalBytes ()).get! 0 == (0xE3 : UInt8))
  it "Eval scope is object format 4, erased-lean-v2" do
    let evalBytes := mkEvalBytes ()
    expect (evalBytes.get! 1 == (4 : UInt8) && evalBytes.get! 2 == (3 : UInt8))
  it "Eval context follows the scope" do
    let ctx := mkCtx ()
    let evalBytes := Claim.ser (.eval ctx (mkAddr1 ()) (mkAddr2 ()) none)
    expect (evalBytes.extract 3 35 == ctx.spec.hash
      && evalBytes.extract 35 67 == ctx.binding.hash
      && evalBytes.get! 67 == (0 : UInt8))
  itBool "Eval no-asm size is 133" ((mkEvalBytes ()).size == 133)
  itBool "Eval with-asm size is 165" ((mkEvalWithAsm ()).size == 165)
  -- Check: tag + scope + context + 32 + option = 101 bytes; with asm = 133
  itBool "Check tag byte is 0xE4" ((mkCheckBytes ()).get! 0 == (0xE4 : UInt8))
  itBool "Check no-asm size is 101" ((mkCheckBytes ()).size == 101)
  itBool "Check with-asm size is 133" ((mkCheckWithAsm ()).size == 133)
  -- CheckEnv: tag + scope + context + 32 + option = 101 bytes
  itBool "CheckEnv tag byte is 0xE5" ((mkCheckEnvBytes ()).get! 0 == (0xE5 : UInt8))
  itBool "CheckEnv no-asm size is 101" ((mkCheckEnvBytes ()).size == 101)
  it "Check for the retired erased-lean-v1 validator is refused" do
    let checkBytes := mkCheckBytes ()
    let retiredRefused : Bool := match Claim.de (checkBytes.set! 2 1) with
      | .error e => (e.splitOn "erased-lean-v1 is retired").length > 1
      | .ok _ => false
    expect retiredRefused
  itBool "Check with an axioms commitment roundtrips"
    (claimSerde (.check { mkCtx () with axioms := some (mkAddr3 ()) } (mkAddr1 ()) none))
  -- Reveal claim: 0xE6
  itBool "Reveal tag byte is 0xE6" ((mkRevealSafetyOnly ()).get! 0 == (0xE6 : UInt8))
  -- Reveal: tag + scope + commitment + variant + mask + safety + binders(none) = 39
  itBool "Reveal safety-only defn size is 39" ((mkRevealSafetyOnly ()).size == 39)
  itBool "Reveal all-fields defn is larger"
    (decide ((mkRevealAllFields ()).size > (mkRevealSafetyOnly ()).size))
  -- Contains: tag + scope + two addresses = 67
  itBool "Contains tag byte is 0xE7" ((mkContainsBytes ()).get! 0 == (0xE7 : UInt8))
  itBool "Contains size is 67" ((mkContainsBytes ()).size == 67)

/-! ## Catalog claim: wire pin + Rust digest parity

  The catalog claim is the first multi-byte claim tag (`0xE8 0x00`:
  TagN rung 2, since claim variants 0–7 fill rung 1). Its exact wire form is a
  cross-serializer commitment: `catalog_claim_wire_bytes_pinned` in
  `crates/ixon/src/proof.rs` asserts the SAME digest hex over the same
  fixture, so the two serializers cannot drift on the large-tag path
  without one of the pins going red.
-/

private def mkCatMembers (_ : Unit) : Address := Address.blake3 "members".toUTF8

/-- Must equal the Rust pin in `proof.rs::catalog_claim_wire_bytes_pinned`. -/
private def catalogDigestPin : String :=
  "4f5686bd1a8386231370703d58223aca769c82c835964d4914ca41305a8030f3"

def catalogClaimTests : LSpec.Spec := do
  let mkBytes := fun () => Claim.ser (.catalog (mkCatMembers ()))
  it "Catalog tag is 2 bytes 0xE8 0x00 (TagN 4 0xE 8)" do
    let bytes := mkBytes ()
    expect (bytes.get! 0 == (0xE8 : UInt8) && bytes.get! 1 == (0x00 : UInt8))
  it "Catalog scope is object format 4, erased-lean-v2" do
    let bytes := mkBytes ()
    expect (bytes.get! 2 == (4 : UInt8) && bytes.get! 3 == (3 : UInt8))
  itBool "Catalog is the scope and the members root, 36 bytes" ((mkBytes ()).size == 4 + 32)
  itBool "Catalog digest parity with Rust pin"
    (toString (Address.blake3 (mkBytes ())) == catalogDigestPin)
  it "Catalog proof wrapper tag is single-byte 0xF5" do
    let proof : Ixon.Proof := { claim := .catalog (mkCatMembers ()), proof := .empty }
    let proofBytes := Ixon.Proof.ser proof
    expect (proofBytes.get! 0 == (0xF5 : UInt8))
  it "Catalog proof wrapper roundtrips" do
    let proof : Ixon.Proof := { claim := .catalog (mkCatMembers ()), proof := .empty }
    let proofBytes := Ixon.Proof.ser proof
    let proofRoundtrips : Bool := match Ixon.Proof.de proofBytes with
      | .ok p => p.claim == proof.claim && p.proof == proof.proof
      | .error _ => false
    expect proofRoundtrips

/-- A reveal mask bit beyond the variant's fields is refused, so one claim has
one encoding. The Rust reader refuses the same bytes
(`proof.rs::reveal_mask_refuses_unknown_bits`): a Reveal claim over the zero
commitment, its variant byte, the one-byte mask, then `0x00` (`binders = none`). -/
def revealMaskTests : LSpec.Spec := do
  let mkHeader (_ : Unit) : Array UInt8 := #[0xE6, 0x04, 0x00] ++ Array.replicate 32 0
  let bytes (variant mask : UInt8) : ByteArray := ⟨mkHeader () ++ #[variant, mask, 0x00]⟩
  itBool "Reveal defn with no fields reads" (Ix.Claim.de (bytes 0 0) matches .ok _)
  itBool "Reveal defn mask bit 5 reads valid DefAsserts"
    (Ix.Claim.de ⟨mkHeader () ++ #[0, 0x20, 0x06, 0x00]⟩ matches .ok _)
  itBool "Reveal defn mask bit 5 refuses alloc 3"
    (Ix.Claim.de ⟨mkHeader () ++ #[0, 0x20, 0x03, 0x00]⟩ matches .error _)
  itBool "Reveal defn mask bit 5 refuses code 8"
    (Ix.Claim.de ⟨mkHeader () ++ #[0, 0x20, 0x08, 0x00]⟩ matches .error _)
  itBool "Reveal defn mask bit 6 refused" (Ix.Claim.de (bytes 0 0x40) matches .error _)
  itBool "Reveal muts ctor mask bit 6 reads fieldModes"
    (Ix.Claim.de ⟨mkHeader () ++ #[8, 1, 1, 0, 1, 0x20, 1, 0, 0x40, 2, 0, 1, 0x00]⟩ matches .ok _)
  itBool "Reveal muts ctor fieldMode 2 refused"
    (Ix.Claim.de ⟨mkHeader () ++ #[8, 1, 1, 0, 1, 0x20, 1, 0, 0x40, 2, 0, 2, 0x00]⟩ matches .error _)
  itBool "Reveal muts ctor mask bit 7 refused"
    (Ix.Claim.de ⟨mkHeader () ++ #[8, 1, 1, 0, 1, 0x20, 1, 0, 0x80, 0x00, 0x00]⟩ matches .error _)
  itBool "Reveal binders opt tag 2 refused"
    (Ix.Claim.de ⟨mkHeader () ++ #[0, 0, 0x02]⟩ matches .error _)
  itBool "Reveal axio with no fields reads" (Ix.Claim.de (bytes 2 0) matches .ok _)
  itBool "Reveal axio mask bit 3 refused" (Ix.Claim.de (bytes 2 0x08) matches .error _)
  itBool "Reveal dprj mask bit 2 refused" (Ix.Claim.de (bytes 7 0x04) matches .error _)

/-! ## Suite -/

public def Tests.Claim.suite : LSpec.Spec := do
  claimUnits
  claimEncodingTests
  catalogClaimTests
  revealMaskTests
  prop "Claim serde roundtrips" fun (c : Claim) => claimSerde c
