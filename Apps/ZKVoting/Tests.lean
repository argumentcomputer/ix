module
public import Apps.ZKVoting.Election
public import LSpec

public section
namespace ZKVoting.Tests
open ZKVoting LSpec

private def execution (vm : Aiur.CompiledToplevel) (env : Ixon.Env)
    (claim : Ix.Claim) (accept : Bool) (label : String) : IO TestSeq := do
  let witness ← IO.ofExcept (IxVM.ClaimHarness.buildClaimWitness env claim)
  let idx := vm.getFuncIdx `verify_claim |>.get!
  let bytecode := vm.bytecode.execute idx witness.input witness.inputIOBuffer
  let native := vm.bytecode.executeIxVM idx witness.input witness.inputIOBuffer
  let expected := fun result => match result with
    | .ok (out, io, _) => accept && out.isEmpty && io == witness.inputIOBuffer
    | .error _ => !accept
  return test s!"Voting bytecode: {label}" (expected bytecode = true)
    ++ test s!"Voting generated backend: {label}" (expected native = true)

def tests (leanEnv : Lean.Environment) (vm : Aiur.CompiledToplevel) : IO TestSeq := do
  let phases ← compileElection leanEnv
  let base := Ix.Commit.mkCompileEnv phases
  let mut cache := base
  let mut receipts := #[]
  for (salt, choice) in [(1001, Candidate.alice), (1002, .alice), (1003, .bob)] do
    let (receipt, next) ← IO.ofExcept (Ix.Commit.compileDef cache []
      (Lean.mkConst ``Ballot) (Lean.toExpr (Ballot.mk salt choice)))
    cache := next
    receipts := receipts.push (toString receipt)
  let board : Board := { receipts, tally := ⟨2, 1, 0⟩ }
  let (claim, finalCache) ← IO.ofExcept (expectedClaim cache board)
  let env ← IO.ofExcept (materialize phases.compileEnv finalCache)
  let mut seq := test "Voting: equal choices with different salts have distinct receipts"
    (receipts[0]! != receipts[1]!)
  seq := seq ++ test "Voting: verifier reconstructs the claim without private ballots"
    ((checkStatement base board claim receipts).toOption.isSome)
  seq := seq ++ (← execution vm env claim true "three ballots tally to 2/1/0")
  let wrongTally := { board with tally := ⟨1, 2, 0⟩ }
  let (wrongClaim, wrongCache) ← IO.ofExcept (expectedClaim finalCache wrongTally)
  let wrongEnv ← IO.ofExcept (materialize env wrongCache)
  seq := seq ++ (← execution vm wrongEnv wrongClaim false "wrong tally with the same total")
  let other := toString (Address.blake3 "unlisted receipt".toUTF8)
  for (label, altered) in [
      ("changed tally", wrongTally),
      ("substituted receipt", { board with receipts := receipts.set! 0 other }),
      ("omission with adjusted total", { board with receipts := receipts.pop, tally := ⟨2, 0, 0⟩ }),
      ("duplicate with adjusted total", { board with receipts := receipts.push receipts[0]!, tally := ⟨3, 1, 0⟩ }),
      ("reordered list", { board with receipts := receipts.reverse }),
      ("malformed receipt", { board with receipts := receipts.set! 0 "not-a-hash" }),
      ("unsupported format", { board with format := 2 }),
      ("empty election", { board with receipts := #[], tally := ⟨0, 0, 0⟩ })] do
    seq := seq ++ test s!"Voting rejects {label}" ((checkStatement base altered claim).toOption.isNone)
  seq := seq ++ test "Voting rejects a missing voter receipt"
    ((checkStatement base board claim #[other]).toOption.isNone)
  let .eval input output _ := claim | throw <| IO.userError "expected eval claim"
  seq := seq ++ test "Voting rejects typing assumptions"
    ((checkStatement base board (.eval input output (some input))).toOption.isNone)
  let (fakeInput, _) ← IO.ofExcept (Ix.Commit.compileDef base []
    (Lean.mkConst ``Result) (Lean.toExpr board.tally))
  seq := seq ++ test "Voting rejects a different program returning the same tally"
    ((checkStatement base board (.eval fakeInput output none)).toOption.isNone)
  -- Try to replace a ballot's body while retaining its public receipt key.
  let witness ← IO.ofExcept (IxVM.ClaimHarness.buildClaimWitness env claim)
  let a ← IO.ofExcept (parseReceipt receipts[0]!)
  let b ← IO.ofExcept (parseReceipt receipts[2]!)
  let bytes := env.getConst? b |>.map Ixon.ser |>.get!
  let forgedIO := witness.inputIOBuffer.extend 2 (a.hash.data.map Aiur.G.ofUInt8)
    (bytes.data.map Aiur.G.ofUInt8)
  let idx := vm.getFuncIdx `verify_claim |>.get!
  seq := seq ++ test "Voting authenticates private ballot bytes (bytecode)"
    ((vm.bytecode.execute idx witness.input forgedIO).toOption.isNone)
    ++ test "Voting authenticates private ballot bytes (generated)"
    ((vm.bytecode.executeIxVM idx witness.input forgedIO).toOption.isNone)
  let system := buildSystem vm
  seq := seq ++ test "Voting rejects missing proof bytes"
    ((verifyProof system vm base board { claim, proof := .empty }).toOption.isNone)
  let (charlie, charlieCache) ← IO.ofExcept (Ix.Commit.compileDef finalCache []
    (Lean.mkConst ``Ballot) (Lean.toExpr (Ballot.mk 1004 .charlie)))
  let charlieBoard : Board := { receipts := #[toString charlie], tally := ⟨0, 0, 1⟩ }
  let (charlieClaim, charlieCache) ← IO.ofExcept (expectedClaim charlieCache charlieBoard)
  seq := seq ++ (← execution vm (← IO.ofExcept (materialize env charlieCache))
    charlieClaim true "single Charlie ballot")
  -- Exercise the cryptographic boundary too: rewriting the wrapper claim to
  -- agree with a forged board must not make an old proof verify.
  let (_, proof, _) ← IO.ofExcept (system.proveIxVM idx witness.input witness.inputIOBuffer)
  let wrapper : Ixon.Proof := { claim, proof := proof.toBytes }
  seq := seq ++ test "Voting verifies a real proof using only the public board"
    ((verifyProof system vm base board wrapper receipts).toOption.isSome)
    ++ test "Voting rejects a valid proof attached to a rewritten tally claim"
      ((verifyProof system vm base wrongTally { wrapper with claim := wrongClaim }).toOption.isNone)
    ++ test "Voting rejects a valid proof attached to a different ballot list"
      ((verifyProof system vm base charlieBoard { wrapper with claim := charlieClaim }).toOption.isNone)
    ++ test "Voting rejects truncated proof bytes"
      ((verifyProof system vm base board
        { wrapper with proof := wrapper.proof.extract 0 (wrapper.proof.size / 2) }).toOption.isNone)
  return seq

end ZKVoting.Tests

def main : IO UInt32 := do
  let seq ← ZKVoting.Tests.tests (← get_env!) (← ZKVoting.compileVM)
  LSpec.lspecIO (.ofList [("voting", [seq])]) []
