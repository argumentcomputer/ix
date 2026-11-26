/-
  Tests for the commitment pipeline and claim construction.
-/

module
public import LSpec
public import Ix.Commit

open LSpec
open Ixon (Comm runGet serCommTagged)
open Ix (Claim RevealConstantInfo)

set_option compiler.extract_closed false

/-! ## Test addresses -/

private def mkPayload1 (_ : Unit) : Address := Address.blake3 "payload1".toUTF8
private def mkPayload2 (_ : Unit) : Address := Address.blake3 "payload2".toUTF8
private def mkSecret1 (_ : Unit) : Address := Address.blake3 "secret1".toUTF8
private def mkSecret2 (_ : Unit) : Address := Address.blake3 "secret2".toUTF8

/-! ## Comm.commit determinism tests -/

def commDeterminismTests : LSpec.Spec := do
  it "Comm.commit deterministic" do
    let comm1 := Comm.mk (mkSecret1 ()) (mkPayload1 ())
    let comm2 := Comm.mk (mkSecret1 ()) (mkPayload1 ())
    expect (Comm.commit comm1 == Comm.commit comm2)
  it "Different secrets produce different commit addresses" do
    expect (Comm.commit (Comm.mk (mkSecret1 ()) (mkPayload1 ())) !=
      Comm.commit (Comm.mk (mkSecret2 ()) (mkPayload1 ())))
  it "Different payloads produce different commit addresses" do
    expect (Comm.commit (Comm.mk (mkSecret1 ()) (mkPayload1 ())) !=
      Comm.commit (Comm.mk (mkSecret1 ()) (mkPayload2 ())))
  it "serCommTagged starts with 0xE1" do
    let comm1 := Comm.mk (mkSecret1 ()) (mkPayload1 ())
    expect ((serCommTagged comm1).data[0]! == 0xE1)
  it "serCommTagged is 65 bytes" do
    let comm1 := Comm.mk (mkSecret1 ()) (mkPayload1 ())
    expect ((serCommTagged comm1).size == 65)

/-! ## Claim.commit tests -/

/-- A stand-in claim context. -/
private def mkCtx (_ : Unit) : Ix.ClaimContext :=
  { spec := Address.blake3 "commit-test-spec".toUTF8
    binding := Address.blake3 "commit-test-binding".toUTF8
    axioms := none }

def claimCommitTests : LSpec.Spec := do
  it "Claim.commit deterministic" do
    let evalClaim := Claim.eval (mkCtx ()) (mkPayload1 ()) (mkPayload2 ()) none
    expect (Claim.commit evalClaim == Claim.commit evalClaim)
  it "eval and check have different commit addresses" do
    let ctx := mkCtx ()
    let evalClaim := Claim.eval ctx (mkPayload1 ()) (mkPayload2 ()) none
    let checkClaim := Claim.check ctx (mkPayload1 ()) none
    expect (Claim.commit evalClaim != Claim.commit checkClaim)
  it "Reveal safety-only differs from kind-only" do
    let p1 := mkPayload1 ()
    let revealSafety := Claim.reveal p1 (.defn none (some .safe) none none none none) none
    let revealKind := Claim.reveal p1 (.defn (some .defn) none none none none none) none
    expect (Claim.commit revealSafety != Claim.commit revealKind)
  it "Reveal kind-only differs from kind+safety" do
    let p1 := mkPayload1 ()
    let revealKind := Claim.reveal p1 (.defn (some .defn) none none none none none) none
    let revealBoth := Claim.reveal p1 (.defn (some .defn) (some .safe) none none none none) none
    expect (Claim.commit revealKind != Claim.commit revealBoth)
  it "Reveal safety-only differs from kind+safety" do
    let p1 := mkPayload1 ()
    let revealSafety := Claim.reveal p1 (.defn none (some .safe) none none none none) none
    let revealBoth := Claim.reveal p1 (.defn (some .defn) (some .safe) none none none none) none
    expect (Claim.commit revealSafety != Claim.commit revealBoth)

/-! ## RevealClaim field combination tests -/

private def claimRoundtrips (c : Claim) : Bool :=
  let bytes := Claim.ser c
  match runGet Claim.get bytes with
  | .ok c' => c' == c
  | .error _ => false

private def mkAllNoneClaim (_ : Unit) : Claim :=
  Claim.reveal (mkPayload1 ()) (.defn none none none none none none) none

private def mkAllFieldsClaim (_ : Unit) : Claim :=
  Claim.reveal (mkPayload1 ())
    (.defn (some .defn) (some .safe) (some 3) (some (mkPayload2 ())) (some (mkPayload1 ()))
      (some { alloc := .noAlloc, boundedStack := true }))
    (some (mkSecret1 ()))

private def singleFieldAddrsDistinct (_ : Unit) : Bool :=
  let comm := mkPayload1 ()
  let p2 := mkPayload2 ()
  let addrK := Claim.commit (.reveal comm (.defn (some .defn) none none none none none) none)
  let addrS := Claim.commit (.reveal comm (.defn none (some .safe) none none none none) none)
  let addrL := Claim.commit (.reveal comm (.defn none none (some 1) none none none) none)
  let addrT := Claim.commit (.reveal comm (.defn none none none (some p2) none none) none)
  let addrV := Claim.commit (.reveal comm (.defn none none none none (some p2) none) none)
  let addrA := Claim.commit (.reveal comm (.defn none none none none none
    (some { alloc := .noRc, boundedStack := false })) none)
  let addrB := Claim.commit (.reveal comm (.defn none none none none none none) (some p2))
  let addrs := #[addrK, addrS, addrL, addrT, addrV, addrA, addrB]
  (List.range addrs.size).all fun i =>
    (List.range addrs.size).all fun j =>
      i == j || addrs[i]! != addrs[j]!

def fieldCombinationTests : LSpec.Spec := do
  -- All-none fields still produce a valid claim
  itBool "All-none defn serialization roundtrips" (claimRoundtrips (mkAllNoneClaim ()))
  -- All fields present still produce a valid claim
  itBool "All-fields defn serialization roundtrips" (claimRoundtrips (mkAllFieldsClaim ()))
  -- Each single field produces a distinct commit address
  itBool "Single-field reveals have distinct commit addresses" (singleFieldAddrsDistinct ())

/-! ## compileDef determinism tests -/

private def mkEmptyCompileEnv (_ : Unit) : Ix.CompileM.CompileEnv :=
  Ix.CompileM.CompileEnv.new { consts := {} }

-- def anon : Type := Prop
private def simpleType : Lean.Expr := Lean.mkSort (.succ .zero)
private def simpleValue : Lean.Expr := Lean.mkSort .zero

-- def anon : Type 1 := Type
private def simpleType2 : Lean.Expr := Lean.mkSort (.succ (.succ .zero))
private def simpleValue2 : Lean.Expr := Lean.mkSort (.succ .zero)

private def compileDefSucceeds (_ : Unit) : Bool :=
  match Ix.Commit.compileDef (mkEmptyCompileEnv ()) [] simpleType simpleValue with
  | .ok _ => true
  | .error _ => false

private def compileDefDeterministic (_ : Unit) : Bool :=
  let env := mkEmptyCompileEnv ()
  match Ix.Commit.compileDef env [] simpleType simpleValue,
        Ix.Commit.compileDef env [] simpleType simpleValue with
  | .ok (addr1, _), .ok (addr2, _) => addr1 == addr2
  | _, _ => false

private def compileDefDifferentValueDifferentAddr (_ : Unit) : Bool :=
  let env := mkEmptyCompileEnv ()
  match Ix.Commit.compileDef env [] simpleType simpleValue,
        Ix.Commit.compileDef env [] simpleType2 simpleValue2 with
  | .ok (addr1, _), .ok (addr2, _) => addr1 != addr2
  | _, _ => false

-- Alpha-invariance: constant name must not affect the content address
private def compileDefAlphaConstName (_ : Unit) : Bool :=
  let env := mkEmptyCompileEnv ()
  match Ix.Commit.compileDef env [] simpleType simpleValue (name := .anonymous),
        Ix.Commit.compileDef env [] simpleType simpleValue (name := .str .anonymous "Foo") with
  | .ok (addr1, _), .ok (addr2, _) => addr1 == addr2
  | _, _ => false

-- Alpha-invariance: binder names must not affect the content address
-- fun (x : Prop) => x  vs  fun (y : Prop) => y
private def propExpr : Lean.Expr := Lean.mkSort .zero
private def binderType1 : Lean.Expr := Lean.mkForall `x .default propExpr propExpr
private def binderValue1 : Lean.Expr := Lean.mkLambda `x .default propExpr (Lean.mkBVar 0)
private def binderType2 : Lean.Expr := Lean.mkForall `y .default propExpr propExpr
private def binderValue2 : Lean.Expr := Lean.mkLambda `y .default propExpr (Lean.mkBVar 0)

private def compileDefAlphaBinderNames (_ : Unit) : Bool :=
  let env := mkEmptyCompileEnv ()
  match Ix.Commit.compileDef env [] binderType1 binderValue1,
        Ix.Commit.compileDef env [] binderType2 binderValue2 with
  | .ok (addr1, _), .ok (addr2, _) => addr1 == addr2
  | _, _ => false

-- Alpha-invariance: level parameter names must not affect the content address
-- def _.{u} : Sort (u+1) := Sort u  vs  def _.{v} : Sort (v+1) := Sort v
private def compileDefAlphaLevelNames (_ : Unit) : Bool :=
  let env := mkEmptyCompileEnv ()
  let typ1 := Lean.mkSort (.succ (.param `u))
  let val1 := Lean.mkSort (.param `u)
  let typ2 := Lean.mkSort (.succ (.param `v))
  let val2 := Lean.mkSort (.param `v)
  match Ix.Commit.compileDef env [`u] typ1 val1,
        Ix.Commit.compileDef env [`v] typ2 val2 with
  | .ok (addr1, _), .ok (addr2, _) => addr1 == addr2
  | _, _ => false

def compileDefTests : LSpec.Spec := do
  itBool "compileDef succeeds on simple def" (compileDefSucceeds ())
  itBool "compileDef produces same address for same inputs" (compileDefDeterministic ())
  itBool "compileDef produces different address for different inputs" (compileDefDifferentValueDifferentAddr ())
  itBool "alpha-invariance: constant name does not affect address" (compileDefAlphaConstName ())
  itBool "alpha-invariance: binder names do not affect address" (compileDefAlphaBinderNames ())
  itBool "alpha-invariance: level param names do not affect address" (compileDefAlphaLevelNames ())

/-! ## checkClaim and revealClaim tests -/

private def checkClaimSucceeds (_ : Unit) : Bool :=
  match Ix.Commit.checkClaim (mkCtx ()) (mkEmptyCompileEnv ()) [] simpleType simpleValue with
  | .ok (.check _ _ _) => true
  | _ => false

private def checkClaimMatchesCompileDef (_ : Unit) : Bool :=
  let env := mkEmptyCompileEnv ()
  match Ix.Commit.compileDef env [] simpleType simpleValue,
        Ix.Commit.checkClaim (mkCtx ()) env [] simpleType simpleValue with
  | .ok (addr, _), .ok (.check _ claimAddr _) => addr == claimAddr
  | _, _ => false

private def openConstantInfoDefn (_ : Unit) : Bool :=
  match Ix.Commit.compileDef (mkEmptyCompileEnv ()) [] simpleType simpleValue with
  | .ok (_, env') =>
    -- Look up the compiled constant via the anonymous name
    let (ixName, _) := (Ix.CanonM.canonName .anonymous).run {}
    match env'.nameToNamed.get? ixName with
    | some named =>
      match env'.constants.get? named.addr with
      | some bytes =>
        match Ixon.deConstantAt bytes 0 bytes.size with
        | .ok constant =>
          let info := Ix.Commit.openConstantInfo constant.info
          -- Should be a defn variant with all fields some
          match info with
          | .defn (some _) (some .safe) (some _) (some _) (some _) (some _) => true
          | _ => false
        | .error _ => false
      | none => false
    | none => false
  | .error _ => false

private def openConstantInfoRoundtrips (_ : Unit) : Bool :=
  match Ix.Commit.compileDef (mkEmptyCompileEnv ()) [] simpleType simpleValue with
  | .ok (_, env') =>
    let (ixName, _) := (Ix.CanonM.canonName .anonymous).run {}
    match env'.nameToNamed.get? ixName with
    | some named =>
      match env'.constants.get? named.addr with
      | some bytes =>
        match Ixon.deConstantAt bytes 0 bytes.size with
        | .ok constant =>
          let info := Ix.Commit.openConstantInfo constant.info
          let bAddr := Ix.Commit.sectionAddr constant.binders
          -- The fully-revealed RevealConstantInfo and sectionAddr should serde roundtrip
          claimRoundtrips (.reveal (mkPayload1 ()) info (some bAddr))
        | .error _ => false
      | none => false
    | none => false
  | .error _ => false

private def revealClaimWrapper (_ : Unit) : Bool :=
  let p1 := mkPayload1 ()
  let p2 := mkPayload2 ()
  let info : RevealConstantInfo := .defn (some .defn) none none none none none
  let claim := Ix.Commit.revealClaim p1 info
  let claimWithBinders := Ix.Commit.revealClaim p1 info (some p2)
  claim == Claim.reveal p1 info none &&
    claimWithBinders == Claim.reveal p1 info (some p2)

def claimConstructorTests : LSpec.Spec := do
  itBool "checkClaim succeeds" (checkClaimSucceeds ())
  itBool "checkClaim address matches compileDef" (checkClaimMatchesCompileDef ())
  itBool "openConstantInfo produces defn with all fields" (openConstantInfoDefn ())
  itBool "openConstantInfo result serde roundtrips" (openConstantInfoRoundtrips ())
  itBool "revealClaim wraps correctly" (revealClaimWrapper ())

/-! ## IO tests for commitConst -/

def commitConstIOTest : LSpec.Spec := do
  it "commitConst: different random secrets produce different addresses" do
    let payload := Address.blake3 "test-payload".toUTF8
    let (_, commitAddr1) ← Ix.Commit.commitConst payload
    let (_, commitAddr2) ← Ix.Commit.commitConst payload
    expect (commitAddr1 != commitAddr2)

/-! ## Suite registration -/

public def Tests.Commit.suite : LSpec.Spec := do
  commDeterminismTests
  claimCommitTests
  fieldCombinationTests
  compileDefTests
  claimConstructorTests

public def Tests.Commit.suiteIO : LSpec.Spec := do
  commitConstIOTest
