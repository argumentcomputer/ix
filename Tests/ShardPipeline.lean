module

import Ix.Cli.CheckCmd
import Ix.Cli.ShardProofIndex

/-!
Opt-in integration test using the real IxVM and recursion systems. Tiny FRI
parameters keep the fixture smaller; this still constructs recursive proofs
and must run separately from measurements. All writes stay in a temporary
directory. Production parameters are untouched.
-/

namespace Tests.ShardPipeline

private def ensure (ok : Bool) (message : String) : IO Unit := do
  unless ok do throw (IO.userError message)

private def fixture : Ixon.Env × Array Address := Id.run do
  let a : Ixon.Constant := ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[.succ .zero]⟩
  let d : Ixon.Constant := ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[.succ (.succ .zero)]⟩
  let aa := Address.blake3 (Ixon.serConstant a)
  let da := Address.blake3 (Ixon.serConstant d)
  let b : Ixon.Constant := ⟨.axio ⟨false, 0, .ref 0 #[]⟩, #[], #[aa], #[]⟩
  let c : Ixon.Constant := ⟨.axio ⟨false, 0, .ref 0 #[]⟩, #[], #[da], #[]⟩
  let ba := Address.blake3 (Ixon.serConstant b)
  let ca := Address.blake3 (Ixon.serConstant c)
  let env := ({} : Ixon.Env).storeConst aa a |>.storeConst ba b
    |>.storeConst ca c |>.storeConst da d
  return (env, #[aa, ba, ca, da])

private def objectPath (dir : System.FilePath) (address : Address) : System.FilePath :=
  let s := (toString address).toSlice
  dir / (s.take 2).toString / (s.drop 2 |>.take 2).toString /
    (s.drop 4 |>.take 2).toString / (s.drop 6).toString

private def indexed (dir : System.FilePath) (claim : Ix.Claim) : IO Address := do
  let some address ← Ix.Cli.ShardProofIndex.readAddress dir (Address.blake3 (Ix.Claim.ser claim))
    | throw (IO.userError "missing shard proof index entry")
  return address

private def smoke : IO Unit := do
  let (env, addresses) := fixture
  let a := addresses[0]!
  let b := addresses[1]!
  let c := addresses[2]!
  let d := addresses[3]!
  let claimOf (owned : Array Address) :=
    IxVM.ClaimHarness.shardCheckEnvClaimTrees env owned |>.map (·.1)
  let original ← IO.ofExcept (claimOf #[a, b, c])
  let ab ← IO.ofExcept (claimOf #[a, b])
  let ca ← IO.ofExcept (claimOf #[a])
  let top ← IO.ofExcept (IxVM.ixVM.mapError (fun e => s!"{e}"))
  let compiled ← IO.ofExcept (top.compile.mapError (fun e => s!"{e}"))
  let verifyIdx := compiled.getFuncIdx `verify_claim |>.get!
  let cp : Aiur.CommitmentParameters := { logBlowup := 1, capHeight := 0 }
  let fp : Aiur.FriParameters :=
    { logFinalPolyLen := 0, maxLogArity := 1, numQueries := 4,
      commitProofOfWorkBits := 0, queryProofOfWorkBits := 0 }
  let ixvm := Aiur.AiurSystem.build compiled.bytecode cp fp
  let recursion ← IO.ofExcept (Ix.Cli.ShardProofIndex.buildRecursionBackend ixvm verifyIdx
    { commitment := cp, fri := fp })
  let handle ← IO.ofExcept (Aiur.EnvHandle.fromBytes (← IO.ofExcept (Ixon.serEnv env)))
  let dir ← IO.FS.createTempDir
  IO.println s!"shard-pipeline smoke artifacts: {dir}"
  let storeDir := dir / "store"
  let indexDir := dir / "index"
  let planDir := dir / "splits"
  IO.FS.createDirAll planDir
  let maxRam := 128 * 1024 * 1024 * 1024
  -- Recreate two validated journals from an interrupted run. This forces
  -- nested healing without a production-only fault-injection switch.
  let journal (claim : Ix.Claim) (parts : Array (Array Address)) : IO Unit := do
    let key := "ix-shard-splits-v2".toUTF8 ++ recursion.allowed ++
      maxRam.toUInt64.toLEBytes ++ Ix.Claim.ser claim
    let path := planDir / s!"{Address.blake3 key}.json"
    IO.FS.writeFile path (Lean.toJson (parts.map (fun p => p.map toString))).compress
  journal original #[#[a, b], #[c]]
  journal ab #[#[a], #[b]]
  let blocks := Ix.Cli.CheckCmd.addrListsBlob #[#[a, b, c], #[d]]
  let run (lookahead : Bool) : IO String := do
    IO.ofExcept (← Aiur.shardPipeline ixvm recursion.system handle blocks blocks "0\n1"
      verifyIdx recursion.aggrIdx maxRam storeDir.toString indexDir.toString
      planDir.toString lookahead true false)
  let verifyOriginal : IO Address := do
    let address ← indexed indexDir original
    let bytes ← IO.FS.readBinFile (objectPath storeDir address)
    ensure (Address.blake3 bytes == address) "stored wrapper hash changed"
    let wrapper ← IO.ofExcept (Ixon.Proof.de bytes)
    ensure (Ix.Claim.ser wrapper.claim == Ix.Claim.ser original) "healing changed the original claim bytes"
    let proof ← IO.ofExcept (Aiur.Proof.ofBytesChecked wrapper.proof)
    IO.ofExcept (Ix.Cli.ShardProofIndex.verifyProof ixvm verifyIdx original proof (some recursion))
    let rawClaim := Aiur.buildClaim verifyIdx
      (IxVM.ClaimHarness.packedDigestKey (Address.blake3 (Ix.Claim.ser original))) #[]
    ensure (!((ixvm.verify rawClaim proof).toBool)) "split root should be a recursion proof"
    return address
  let first ← run true
  IO.println first
  -- The summary is one segment per in-process NUMA lane (`a | b | …`), so
  -- counts are summed over segments: a lane holding a single shard has
  -- nothing to overlap, and cached proofs are reported per lane.
  let countOf (summary label : String) : Nat :=
    (summary.splitOn label).dropLast.foldl (fun acc piece =>
      acc + (((piece.trimRight.splitOn " ").getLast?.bind String.toNat?).getD 0)) 0
  ensure (countOf first " preparation overlap(s)" > 0) "lookahead did not overlap any preparation"
  let firstAddress ← verifyOriginal
  let resumed ← run false
  ensure (countOf resumed " cached proof(s)" == 2) "resume did not reuse both original proofs"
  ensure ((← verifyOriginal) == firstAddress) "resume replaced an already verified original proof"
  -- Remove completed parents and corrupt one persisted child. The journal
  -- must resume through verified siblings and replace the rejected child.
  IO.FS.removeFile (indexDir / toString (Address.blake3 (Ix.Claim.ser original)))
  IO.FS.removeFile (indexDir / toString (Address.blake3 (Ix.Claim.ser ab)))
  let childAddress ← indexed indexDir ca
  IO.FS.writeBinFile (objectPath storeDir childAddress) "corrupt child".toUTF8
  IO.println (← run false)
  let _ ← verifyOriginal
  IO.println "shard-pipeline: nested healing, unchanged claim, overlap, verified resume and corrupt-child recovery passed"

public def suite : IO UInt32 := do
  try
    smoke
    return 0
  catch e =>
    IO.eprintln s!"shard-pipeline: {e}"
    return 1

end Tests.ShardPipeline
