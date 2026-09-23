module

public import Tests.Aggr

/-!
A current-format proof round trip through the production `ix_aggr` circuit.
The child is a small stand-in for IxVM; both systems use one query and no PoW
to keep this explicit integration gate tractable. These are test parameters,
not the production security configuration.
-/

public section

namespace Tests.Aggr

def proofRoundTrip : IO UInt32 := do
  let commitment : Aiur.CommitmentParameters := { logBlowup := 1, capHeight := 0 }
  let fri : Aiur.FriParameters := {
    logFinalPolyLen := 0, maxLogArity := 1, numQueries := 1
    commitProofOfWorkBits := 0, queryProofOfWorkBits := 0 }
  let child ← IO.ofExcept childProgram.compile
  let childIdx := child.getFuncIdx `fake_verify_claim |>.get!
  let childSystem := Aiur.AiurSystem.build child.bytecode commitment fri
  let top ← IO.ofExcept <| Aggr.ixAggr.mapError (fun e => s!"{e}")
  let compiled ← IO.ofExcept <| top.compileWithGroups Aggr.functionGroups
  let idx := compiled.getFuncIdx `ix_aggr |>.get!
  let system := Aiur.AiurSystem.build compiled.bytecode commitment fri
  let childVk := childSystem.vkBytes
  let selfVk := system.vkBytes
  let allowed := Aggr.allowedBlob childVk childIdx selfVk idx
  let statement : Aggr.CheckEnvTrees := {
    subjects := (Ix.AssumptionTree.canonical #[Address.blake3 "proof-round-trip".toUTF8]).get!
    assumptions := none }
  let bytes := Ix.Claim.ser statement.claim
  let (childClaim, childProof, _) ← IO.ofExcept <|
    childSystem.prove childIdx (MultiStark.digestGs bytes) default
  let childAdvice ← IO.ofExcept <| childSystem.proofToAdviceBytes childClaim childProof
  let claims := MultiStark.serializeClaims #[childClaim]
  IO.println "Proving the production ix_aggr wrap with one-query test parameters…"
  let (claim, proof) ← IO.ofExcept <| system.proveIxAggr idx
    (Aggr.pubInput allowed bytes) 0 childAdvice ByteArray.empty childVk selfVk
    claims ByteArray.empty bytes allowed
    (Aggr.preimagesBlob #[]) (Aggr.treesBlob #[]) (Aggr.pathsBlob #[])
  let expected := Aiur.buildClaim idx (Aggr.pubInput allowed bytes) #[]
  let decoded := Aiur.Proof.ofBytesChecked proof.toBytes
  let tampered := expected.set! 2 ((expected[2]?).getD 0 + 1)
  LSpec.lspecIO (.ofList [("aggregate-proof", [
    LSpec.test "production aggregation returns the exact outer claim" (claim == expected),
    Tests.ProofHelpers.expectOk "production aggregate proof verifies" (system.verify expected proof),
    Tests.ProofHelpers.expectOk "current proof bytes decode and verify"
      (decoded.bind (system.verify expected)),
    Tests.ProofHelpers.expectErr "aggregate proof rejects a changed outer claim"
      (system.verify tampered proof)
  ])]) []

end Tests.Aggr
end
