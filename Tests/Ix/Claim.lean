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
  -- EvalClaim
  test "EvalClaim roundtrip" (claimSerde (.eval addr1 addr2))
  -- CheckClaim
  ++ test "CheckClaim roundtrip" (claimSerde (.check addr1))
  -- RevealClaim with defn revealing only safety
  ++ test "RevealClaim defn safety-only" (claimSerde (.reveal addr1
    (.defn none (some .safe) none none none)))
  -- RevealClaim with defn revealing all fields
  ++ test "RevealClaim defn all fields" (claimSerde (.reveal addr1
    (.defn (some .defn) (some .safe) (some 3) (some addr2) (some addr3))))
  -- RevealClaim with axio revealing type
  ++ test "RevealClaim axio with type" (claimSerde (.reveal addr1
    (.axio none none (some addr2))))
  -- RevealClaim with recr with rules
  ++ test "RevealClaim recr with rules" (claimSerde (.reveal addr1
    (.recr (some true) none (some 2) none none none none none
      (some #[⟨0, 3, addr2⟩]))))
  -- RevealClaim with muts with component
  ++ test "RevealClaim muts with component" (claimSerde (.reveal addr1
    (.muts #[(0, .defn (some .defn) (some .safe) none none none)])))
  -- Projection variants
  ++ test "RevealClaim cPrj" (claimSerde (.reveal addr1
    (.cPrj (some 0) (some 1) (some addr2))))
  ++ test "RevealClaim rPrj" (claimSerde (.reveal addr1
    (.rPrj (some 2) (some addr2))))
  ++ test "RevealClaim iPrj" (claimSerde (.reveal addr1
    (.iPrj (some 3) (some addr2))))
  ++ test "RevealClaim dPrj" (claimSerde (.reveal addr1
    (.dPrj (some 0) (some addr2))))
  -- Empty fields
  ++ test "RevealClaim defn all none" (claimSerde (.reveal addr1
    (.defn none none none none none)))
  -- Quot variant
  ++ test "RevealClaim quot" (claimSerde (.reveal addr1
    (.quot (some .type) (some 1) (some addr2))))

/-! ## Byte-level encoding tests -/

def claimEncodingTests : TestSeq :=
  let evalBytes := Claim.ser (.eval addr1 addr2)
  let checkBytes := Claim.ser (.check addr1)
  let revealSafetyOnly := Claim.ser (.reveal addr1 (.defn none (some .safe) none none none))
  let revealAllFields := Claim.ser (.reveal addr1
    (.defn (some .defn) (some .safe) (some 3) (some addr2) (some addr3)))
  -- EvalClaim: starts with 0xE4, total 65 bytes (1 tag + 32 + 32)
  test "EvalClaim tag byte is 0xE4" (evalBytes.data[0]! == 0xE4)
  ++ test "EvalClaim size is 65" (evalBytes.size == 65)
  -- CheckClaim: starts with 0xE3, total 33 bytes (1 tag + 32)
  ++ test "CheckClaim tag byte is 0xE3" (checkBytes.data[0]! == 0xE3)
  ++ test "CheckClaim size is 33" (checkBytes.size == 33)
  -- RevealClaim: starts with 0xE6
  ++ test "RevealClaim tag byte is 0xE6" (revealSafetyOnly.data[0]! == 0xE6)
  -- RevealClaim safety-only defn: 36 bytes (1 tag + 32 comm + 1 variant + 1 mask + 1 safety)
  ++ test "RevealClaim safety-only defn size is 36" (revealSafetyOnly.size == 36)
  -- RevealClaim with all defn fields should be larger
  ++ test "RevealClaim all-fields defn is larger" (revealAllFields.size > revealSafetyOnly.size)

/-! ## Suite -/

public def Tests.Claim.suite : List TestSeq := [
  claimUnits,
  claimEncodingTests,
  checkIO "Claim serde roundtrips" (∀ c : Claim, claimSerde c),
]
