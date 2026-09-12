module
import Tests.Aggr
import Ix.MultiStark.Stage2

/-! Opt-in real native proof of the existing test stand-in's 18-word aggregate
claim layout. This tests protocol verification and every public-claim binding,
NOT the truth of an Ixon CheckEnv claim: the stand-in is not a production
aggregate program and must never be approved as one. -/

namespace Tests.MultiStark.Verify.Wrapper

open LSpec Aiur
open _root_.MultiStark.Verify

public def suite : IO UInt32 := do
  let compiled ← match Tests.Aggr.childProgram.compile with
    | .error error => IO.eprintln s!"wrapper stand-in compile: {error}"; return 1
    | .ok compiled => pure compiled
  let some aggregateEntry := compiled.getFuncIdx `fake_aggr
    | IO.eprintln "missing fake_aggr entry"; return 1
  let some verifyClaimEntry := compiled.getFuncIdx `fake_verify_claim
    | IO.eprintln "missing fake_verify_claim entry"; return 1
  let system := AiurSystem.build compiled.bytecode Tests.MultiStark.recCommitParams Tests.MultiStark.innerFri
  let keyBytes := system.vkBytes
  let publicClaim : ClosedCheckEnv := ⟨⟨Array.replicate 31 7 ++ #[1], by simp⟩⟩
  let typedClaim : Ix.Claim := .checkEnv ⟨⟨publicClaim.root.bytes⟩⟩ none
  let config : SourceConfig := { aggregate := {
    ixvmKey := keyBytes.data, verifyClaimEntry := Ix.Ixby.Goldilocks.reduce verifyClaimEntry
    aggregateKey := keyBytes.data, aggregateEntry := Ix.Ixby.Goldilocks.reduce aggregateEntry } }
  let allowed := Aggr.allowedBlob keyBytes verifyClaimEntry keyBytes aggregateEntry
  let inputs := Aggr.pubInput allowed (Ix.Claim.ser typedClaim)
  let (nativeClaim, nativeProof, _) ← match system.prove aggregateEntry inputs default with
    | .error error => IO.eprintln s!"wrapper stand-in prove: {error}"; return 1
    | .ok result => pure result
  let proofBytes ← match system.proofToAdviceBytes nativeClaim nativeProof with
    | .error error => IO.eprintln s!"wrapper stand-in native verify: {error}"; return 1
    | .ok bytes => pure bytes
  let result := checkClaim config publicClaim proofBytes.data
  let wrongClaim : ClosedCheckEnv := ⟨⟨Array.replicate 32 8, by simp⟩⟩
  let wrongAggregate := { config with
    aggregate := { config.aggregate with aggregateEntry := config.aggregate.aggregateEntry.add 1 } }
  let wrongIxvm := { config with
    aggregate := { config.aggregate with verifyClaimEntry := config.aggregate.verifyClaimEntry.add 1 } }
  let wrongChildKey := { config with
    aggregate := { config.aggregate with ixvmKey := config.aggregate.ixvmKey.push 0 } }
  let malformedKey := { config with
    aggregate := { config.aggregate with aggregateKey := config.aggregate.aggregateKey.push 0 } }
  let otherSystem := AiurSystem.build compiled.bytecode Tests.MultiStark.recCommitParams
    { Tests.MultiStark.innerFri with numQueries := 4 }
  let wrongVerifierKey := { config with
    aggregate := { config.aggregate with aggregateKey := otherSystem.vkBytes.data } }
  let conditionalAlias : Ix.Claim := .checkEnv ⟨⟨Array.replicate 31 7⟩⟩ (some ⟨⟨#[0]⟩⟩)
  let checks :=
    test "stand-in proof native claim matches pure public-claim adapter"
      (nativeClaim.map (·.n) == (config.aggregate.expectedClaim publicClaim).map (·.val)) ++
    test s!"complete pure claim-bound verification ({repr result})" result.isOk ++
    test "typed wrapper returns exactly the supplied canonical claim"
      (claimWrapper config publicClaim proofBytes.data == some publicClaim) ++
    test "byte wrapper returns exactly the supplied canonical bytes"
      (claimBytesWrapper config publicClaim.bytes proofBytes.data == some publicClaim.bytes) ++
    test "public Ix.Claim adapter verifies the same proof"
      (_root_.MultiStark.Stage2.stage2Verify config typedClaim proofBytes) ++
    test "wrong public root rejected" (!stage2Verify config wrongClaim proofBytes.data) ++
    test "wrong aggregate entry rejected" (!stage2Verify wrongAggregate publicClaim proofBytes.data) ++
    test "wrong IxVM entry rejected" (!stage2Verify wrongIxvm publicClaim proofBytes.data) ++
    test "wrong allowed child key rejected" (!stage2Verify wrongChildKey publicClaim proofBytes.data) ++
    test "noncanonical aggregate key rejected" (!stage2Verify malformedKey publicClaim proofBytes.data) ++
    test "another canonical aggregate verifier key rejected" (!stage2Verify wrongVerifierKey publicClaim proofBytes.data) ++
    test "trailing private proof byte rejected" (!stage2Verify config publicClaim (proofBytes.data.push 0)) ++
    test "trailing public claim byte rejected" (!stage2VerifyBytes config (publicClaim.bytes.push 0) proofBytes.data) ++
    test "another typed claim kind rejected" (!_root_.MultiStark.Stage2.stage2Verify config
      (.check ⟨⟨publicClaim.root.bytes⟩⟩ none) proofBytes) ++
    test "conditional root rejected" (!_root_.MultiStark.Stage2.stage2Verify config
      (.checkEnv ⟨⟨publicClaim.root.bytes⟩⟩ (some ⟨⟨publicClaim.root.bytes⟩⟩)) proofBytes) ++
    test "malformed conditional value really has identical bytes"
      (Ix.Claim.ser conditionalAlias == Ix.Claim.ser typedClaim) ++
    test "typed adapter rejects conditional alias even with a valid closed-claim proof"
      (!_root_.MultiStark.Stage2.stage2Verify config conditionalAlias proofBytes) ++
    test "explicit sampling exhaustion rejects"
      (!stage2Verify { config with verifier := { transcript := { sampleAttempts := 0 } } } publicClaim proofBytes.data) ++
    test "explicit proof decoding byte limit rejects"
      (!stage2Verify { config with decode := { bytes := 1 } } publicClaim proofBytes.data)
  IO.println s!"Stand-in aggregate-layout binding proof: {proofBytes.size} bytes (not production Ixon validity)"
  lspecIO (.ofList [("stage2-wrapper-real", [checks])]) []

end Tests.MultiStark.Verify.Wrapper
