/-
  Tests for the commitment pipeline and claim construction.
-/

module
public import LSpec
public import Ix.Commit

open LSpec
open Ixon (Comm runGet serCommTagged)
open Ix (Claim RevealConstantInfo)

/-! ## Test addresses -/

private def payload1 : Address := Address.blake3 "payload1".toUTF8
private def payload2 : Address := Address.blake3 "payload2".toUTF8
private def secret1 : Address := Address.blake3 "secret1".toUTF8
private def secret2 : Address := Address.blake3 "secret2".toUTF8

/-! ## Comm.commit determinism tests -/

def commDeterminismTests : TestSeq :=
  let comm1 := Comm.mk secret1 payload1
  let comm2 := Comm.mk secret1 payload1
  -- Same comm → same address
  test "Comm.commit deterministic" (Comm.commit comm1 == Comm.commit comm2)
  -- Different secrets → different addresses
  ++ test "Different secrets produce different commit addresses"
    (Comm.commit (Comm.mk secret1 payload1) != Comm.commit (Comm.mk secret2 payload1))
  -- Different payloads → different addresses
  ++ test "Different payloads produce different commit addresses"
    (Comm.commit (Comm.mk secret1 payload1) != Comm.commit (Comm.mk secret1 payload2))
  -- Verify commitment format: tagged serialization starts with 0xE5 and is 65 bytes
  ++ test "serCommTagged starts with 0xE5"
    ((serCommTagged comm1).data[0]! == 0xE5)
  ++ test "serCommTagged is 65 bytes"
    ((serCommTagged comm1).size == 65)

/-! ## Claim.commit tests -/

def claimCommitTests : TestSeq :=
  let evalClaim := Claim.eval payload1 payload2
  let checkClaim := Claim.check payload1
  let revealSafety := Claim.reveal payload1 (.defn none (some .safe) none none none)
  let revealKind := Claim.reveal payload1 (.defn (some .defn) none none none none)
  let revealBoth := Claim.reveal payload1 (.defn (some .defn) (some .safe) none none none)
  -- Claim.commit is deterministic
  test "Claim.commit deterministic" (Claim.commit evalClaim == Claim.commit evalClaim)
  -- Different claim types → different addresses
  ++ test "eval and check have different commit addresses"
    (Claim.commit evalClaim != Claim.commit checkClaim)
  -- Different reveal fields → different addresses
  ++ test "Reveal safety-only differs from kind-only"
    (Claim.commit revealSafety != Claim.commit revealKind)
  ++ test "Reveal kind-only differs from kind+safety"
    (Claim.commit revealKind != Claim.commit revealBoth)
  ++ test "Reveal safety-only differs from kind+safety"
    (Claim.commit revealSafety != Claim.commit revealBoth)

/-! ## RevealClaim field combination tests -/

private def claimRoundtrips (c : Claim) : Bool :=
  let bytes := Claim.ser c
  match runGet Claim.get bytes with
  | .ok c' => c' == c
  | .error _ => false

private def allNoneClaim : Claim :=
  Claim.reveal payload1 (.defn none none none none none)

private def allFieldsClaim : Claim :=
  Claim.reveal payload1
    (.defn (some .defn) (some .safe) (some 3) (some payload2) (some payload1))

private def singleFieldAddrsDistinct : Bool :=
  let comm := payload1
  let addrK := Claim.commit (.reveal comm (.defn (some .defn) none none none none))
  let addrS := Claim.commit (.reveal comm (.defn none (some .safe) none none none))
  let addrL := Claim.commit (.reveal comm (.defn none none (some 1) none none))
  let addrT := Claim.commit (.reveal comm (.defn none none none (some payload2) none))
  let addrV := Claim.commit (.reveal comm (.defn none none none none (some payload2)))
  addrK != addrS && addrK != addrL && addrK != addrT && addrK != addrV &&
  addrS != addrL && addrS != addrT && addrS != addrV &&
  addrL != addrT && addrL != addrV &&
  addrT != addrV

def fieldCombinationTests : TestSeq :=
  -- All-none fields still produce a valid claim
  test "All-none defn serialization roundtrips" (claimRoundtrips allNoneClaim)
  -- All fields present still produce a valid claim
  ++ test "All-fields defn serialization roundtrips" (claimRoundtrips allFieldsClaim)
  -- Each single field produces a distinct commit address
  ++ test "Single-field reveals have distinct commit addresses" singleFieldAddrsDistinct

/-! ## compileDef determinism tests -/

private def emptyCompileEnv : Ix.CompileM.CompileEnv :=
  Ix.CompileM.CompileEnv.new { consts := {} }

-- def anon : Type := Prop
private def simpleType : Lean.Expr := Lean.mkSort (.succ .zero)
private def simpleValue : Lean.Expr := Lean.mkSort .zero

-- def anon : Type 1 := Type
private def simpleType2 : Lean.Expr := Lean.mkSort (.succ (.succ .zero))
private def simpleValue2 : Lean.Expr := Lean.mkSort (.succ .zero)

private def compileDefSucceeds : Bool :=
  match Ix.Commit.compileDef emptyCompileEnv [] simpleType simpleValue with
  | .ok _ => true
  | .error _ => false

private def compileDefDeterministic : Bool :=
  match Ix.Commit.compileDef emptyCompileEnv [] simpleType simpleValue,
        Ix.Commit.compileDef emptyCompileEnv [] simpleType simpleValue with
  | .ok (addr1, _), .ok (addr2, _) => addr1 == addr2
  | _, _ => false

private def compileDefDifferentValueDifferentAddr : Bool :=
  match Ix.Commit.compileDef emptyCompileEnv [] simpleType simpleValue,
        Ix.Commit.compileDef emptyCompileEnv [] simpleType2 simpleValue2 with
  | .ok (addr1, _), .ok (addr2, _) => addr1 != addr2
  | _, _ => false

-- Alpha-invariance: constant name must not affect the content address
private def compileDefAlphaConstName : Bool :=
  match Ix.Commit.compileDef emptyCompileEnv [] simpleType simpleValue (name := .anonymous),
        Ix.Commit.compileDef emptyCompileEnv [] simpleType simpleValue (name := .str .anonymous "Foo") with
  | .ok (addr1, _), .ok (addr2, _) => addr1 == addr2
  | _, _ => false

-- Alpha-invariance: binder names must not affect the content address
-- fun (x : Prop) => x  vs  fun (y : Prop) => y
private def propExpr : Lean.Expr := Lean.mkSort .zero
private def binderType1 : Lean.Expr := Lean.mkForall `x .default propExpr propExpr
private def binderValue1 : Lean.Expr := Lean.mkLambda `x .default propExpr (Lean.mkBVar 0)
private def binderType2 : Lean.Expr := Lean.mkForall `y .default propExpr propExpr
private def binderValue2 : Lean.Expr := Lean.mkLambda `y .default propExpr (Lean.mkBVar 0)

private def compileDefAlphaBinderNames : Bool :=
  match Ix.Commit.compileDef emptyCompileEnv [] binderType1 binderValue1,
        Ix.Commit.compileDef emptyCompileEnv [] binderType2 binderValue2 with
  | .ok (addr1, _), .ok (addr2, _) => addr1 == addr2
  | _, _ => false

-- Alpha-invariance: level parameter names must not affect the content address
-- def _.{u} : Sort (u+1) := Sort u  vs  def _.{v} : Sort (v+1) := Sort v
private def compileDefAlphaLevelNames : Bool :=
  let typ1 := Lean.mkSort (.succ (.param `u))
  let val1 := Lean.mkSort (.param `u)
  let typ2 := Lean.mkSort (.succ (.param `v))
  let val2 := Lean.mkSort (.param `v)
  match Ix.Commit.compileDef emptyCompileEnv [`u] typ1 val1,
        Ix.Commit.compileDef emptyCompileEnv [`v] typ2 val2 with
  | .ok (addr1, _), .ok (addr2, _) => addr1 == addr2
  | _, _ => false

def compileDefTests : TestSeq :=
  test "compileDef succeeds on simple def" compileDefSucceeds
  ++ test "compileDef produces same address for same inputs" compileDefDeterministic
  ++ test "compileDef produces different address for different inputs" compileDefDifferentValueDifferentAddr
  ++ test "alpha-invariance: constant name does not affect address" compileDefAlphaConstName
  ++ test "alpha-invariance: binder names do not affect address" compileDefAlphaBinderNames
  ++ test "alpha-invariance: level param names do not affect address" compileDefAlphaLevelNames

/-! ## checkClaim and revealClaim tests -/

private def checkClaimSucceeds : Bool :=
  match Ix.Commit.checkClaim emptyCompileEnv [] simpleType simpleValue with
  | .ok (.check _) => true
  | _ => false

private def checkClaimMatchesCompileDef : Bool :=
  match Ix.Commit.compileDef emptyCompileEnv [] simpleType simpleValue,
        Ix.Commit.checkClaim emptyCompileEnv [] simpleType simpleValue with
  | .ok (addr, _), .ok (.check claimAddr) => addr == claimAddr
  | _, _ => false

private def openConstantInfoDefn : Bool :=
  match Ix.Commit.compileDef emptyCompileEnv [] simpleType simpleValue with
  | .ok (_, env') =>
    -- Look up the compiled constant via the anonymous name
    let (ixName, _) := (Ix.CanonM.canonName .anonymous).run {}
    match env'.nameToNamed.get? ixName with
    | some named =>
      match env'.constants.get? named.addr with
      | some constant =>
        let info := Ix.Commit.openConstantInfo constant.info
        -- Should be a defn variant with all fields some
        match info with
        | .defn (some _) (some .safe) (some _) (some _) (some _) => true
        | _ => false
      | none => false
    | none => false
  | .error _ => false

private def openConstantInfoRoundtrips : Bool :=
  match Ix.Commit.compileDef emptyCompileEnv [] simpleType simpleValue with
  | .ok (_, env') =>
    let (ixName, _) := (Ix.CanonM.canonName .anonymous).run {}
    match env'.nameToNamed.get? ixName with
    | some named =>
      match env'.constants.get? named.addr with
      | some constant =>
        let info := Ix.Commit.openConstantInfo constant.info
        -- The fully-revealed RevealConstantInfo should serde roundtrip
        claimRoundtrips (.reveal payload1 info)
      | none => false
    | none => false
  | .error _ => false

private def revealClaimWrapper : Bool :=
  let info : RevealConstantInfo := .defn (some .defn) none none none none
  let claim := Ix.Commit.revealClaim payload1 info
  claim == Claim.reveal payload1 info

def claimConstructorTests : TestSeq :=
  test "checkClaim succeeds" checkClaimSucceeds
  ++ test "checkClaim address matches compileDef" checkClaimMatchesCompileDef
  ++ test "openConstantInfo produces defn with all fields" openConstantInfoDefn
  ++ test "openConstantInfo result serde roundtrips" openConstantInfoRoundtrips
  ++ test "revealClaim wraps correctly" revealClaimWrapper

/-! ## IO tests for commitConst -/

def commitConstIOTest : TestSeq :=
  .individualIO "commitConst: different random secrets produce different addresses" none (do
    let payload := Address.blake3 "test-payload".toUTF8
    let (_, commitAddr1) ← Ix.Commit.commitConst payload
    let (_, commitAddr2) ← Ix.Commit.commitConst payload
    return (commitAddr1 != commitAddr2, 0, 0, none)) .done

/-! ## Suite registration -/

public def Tests.Commit.suite : List TestSeq := [
  commDeterminismTests,
  claimCommitTests,
  fieldCombinationTests,
  compileDefTests,
  claimConstructorTests,
]

public def Tests.Commit.suiteIO : List TestSeq := [
  commitConstIOTest,
]
