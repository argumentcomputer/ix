/-
  Serialization roundtrip and encoding tests for Ix.Claim types.
-/

module
public import Ix.Claim
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

def claimUnits : TestSeq :=
  -- Typechecking claims: both no-asm and with-asm forms.
  test "Eval no-asm roundtrip" (claimSerde (.eval addr1 addr2 none))
  ++ test "Eval with-asm roundtrip"
       (claimSerde (.eval addr1 addr2 (some addr3)))
  ++ test "Check no-asm roundtrip" (claimSerde (.check addr1 none))
  ++ test "Check with-asm roundtrip"
       (claimSerde (.check addr1 (some addr2)))
  ++ test "CheckEnv no-asm roundtrip" (claimSerde (.checkEnv addr1 none))
  ++ test "CheckEnv with-asm roundtrip"
       (claimSerde (.checkEnv addr1 (some addr2)))
  -- Contains
  ++ test "Contains roundtrip" (claimSerde (.contains addr1 addr2))
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

  All claim variants are at Tag4 sizes 3..=7 (single-byte tags
  `0xE3`..`0xE7`). Each claim has an opt byte (`0x00` for `none`,
  `0x01`+32-byte address for `some`).
-/

def claimEncodingTests : TestSeq :=
  let evalBytes := Claim.ser (.eval addr1 addr2 none)
  let evalWithAsm := Claim.ser (.eval addr1 addr2 (some addr3))
  let checkBytes := Claim.ser (.check addr1 none)
  let checkWithAsm := Claim.ser (.check addr1 (some addr2))
  let checkEnvBytes := Claim.ser (.checkEnv addr1 none)
  let containsBytes := Claim.ser (.contains addr1 addr2)
  let revealSafetyOnly := Claim.ser
    (.reveal addr1 (.defn none (some .safe) none none none))
  let revealAllFields := Claim.ser (.reveal addr1
    (.defn (some .defn) (some .safe) (some 3) (some addr2) (some addr3)))
  -- Eval claim: 0xE3 + 64 + 1 (opt) = 66 bytes; with asm = 98
  test "Eval tag byte is 0xE3" (evalBytes.data[0]! == 0xE3)
  ++ test "Eval no-asm size is 66" (evalBytes.size == 66)
  ++ test "Eval with-asm size is 98" (evalWithAsm.size == 98)
  -- Check claim: 0xE4 + 32 + 1 = 34 bytes; with asm = 66
  ++ test "Check tag byte is 0xE4" (checkBytes.data[0]! == 0xE4)
  ++ test "Check no-asm size is 34" (checkBytes.size == 34)
  ++ test "Check with-asm size is 66" (checkWithAsm.size == 66)
  -- CheckEnv claim: 0xE5 + 32 + 1 = 34 bytes
  ++ test "CheckEnv tag byte is 0xE5" (checkEnvBytes.data[0]! == 0xE5)
  ++ test "CheckEnv no-asm size is 34" (checkEnvBytes.size == 34)
  -- Reveal claim: 0xE6
  ++ test "Reveal tag byte is 0xE6" (revealSafetyOnly.data[0]! == 0xE6)
  -- Reveal safety-only defn: 1 (tag) + 32 (comm) + 1 (variant) + 1 (mask) + 1 (safety) = 36
  ++ test "Reveal safety-only defn size is 36" (revealSafetyOnly.size == 36)
  ++ test "Reveal all-fields defn is larger"
       (revealAllFields.size > revealSafetyOnly.size)
  -- Contains claim: 0xE7 + 64 = 65
  ++ test "Contains tag byte is 0xE7" (containsBytes.data[0]! == 0xE7)
  ++ test "Contains size is 65" (containsBytes.size == 65)

/-! ## Suite -/

public def Tests.Claim.suite : List TestSeq := [
  claimUnits,
  claimEncodingTests,
  checkIO "Claim serde roundtrips" (∀ c : Claim, claimSerde c),
]
