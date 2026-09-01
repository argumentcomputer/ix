module

public import Ix.Aiur.Hypercube
public import Ix.Aiur.Compiler
public import Ix.IxVM.ClaimHarness
public import Ix.IxVM.Toplevel

/-!
Head-to-head: the IxVM kernel proving `Claim.check` for a constant on both
backends — multi-stark over Goldilocks (the production pipeline, default
parameters) and SP1 Hypercube over KoalaBear (the `koalaBearProfile`
kernel, default `ProverParams`). Reports prove/verify wall time and proof
size. The two backends interpret the same claim witness; only the digest
packing differs (4-byte vs 2-byte words), per the width profiles.
-/

public section

open IxVM.ClaimHarness

namespace Tests.Ix.IxVM.Hypercube

private def ms (a b : Nat) : String := s!"{b - a} ms"

def benchConst (name : Lean.Name) (env : Lean.Environment) : IO UInt32 := do
  IO.println s!"hypercube-bench: {name}"
  let ixonEnv ← loadIxonEnv name env
  let target ← lookupAddr ixonEnv name
  let claim := Ix.Claim.check target none

  -- ── multi-stark / Goldilocks ───────────────────────────────────────────
  let goldTop ← IO.ofExcept <| IxVM.ixVM.mapError toString
  let goldCompiled ← IO.ofExcept goldTop.compile
  let some goldIdx := goldCompiled.getFuncIdx `verify_claim
    | IO.eprintln "verify_claim not found (goldilocks)"; return 1
  let goldSys := Aiur.AiurSystem.build goldCompiled.bytecode
    Aiur.defaultCommitmentParameters Aiur.defaultFriParameters
  let wG ← IO.ofExcept <| buildClaimWitness ixonEnv claim {}
  let t0 ← IO.monoMsNow
  let (claimG, proofG, _) ← IO.ofExcept <|
    goldSys.prove goldIdx wG.input wG.inputIOBuffer
  let t1 ← IO.monoMsNow
  IO.ofExcept <| goldSys.verify claimG proofG
  let t2 ← IO.monoMsNow
  let sizeG := proofG.toBytes.size

  -- ── Hypercube / KoalaBear ──────────────────────────────────────────────
  let kbTop ← IO.ofExcept <| (do
    let p ← IxVM.koalaBearProfile
    let f ← IxVM.ixVMFullOver p
    pure (f.prune [`verify_claim])).mapError toString
  let kbCompiled ← IO.ofExcept kbTop.compile
  let some kbIdx := kbCompiled.getFuncIdx `verify_claim
    | IO.eprintln "verify_claim not found (koalabear)"; return 1
  let t3 ← IO.monoMsNow
  let kbSys ← IO.ofExcept <|
    Aiur.HypercubeSystem.build kbCompiled.bytecode kbIdx
  let t4 ← IO.monoMsNow
  let wKB ← IO.ofExcept <|
    buildClaimWitness ixonEnv claim {} (profile := koalaBearWitnessProfile)
  let t5 ← IO.monoMsNow
  let (claimKB, blob) ← IO.ofExcept <|
    kbSys.prove wKB.input wKB.inputIOBuffer
  let t6 ← IO.monoMsNow
  IO.ofExcept <| Aiur.HypercubeSystem.verify kbSys claimKB blob
  let t7 ← IO.monoMsNow

  -- claim sanity: [functionChannel, funIdx] ++ input (unit output)
  let expectedKB := #[Aiur.G.ofNat 0, Aiur.G.ofNat kbIdx] ++ wKB.input
  let claimOk := claimKB == expectedKB

  IO.println "── results ─────────────────────────────────────────────"
  IO.println s!"multi-stark (Goldilocks, logBlowup 2, 100 queries, 20 PoW bits):"
  IO.println s!"  prove   {ms t0 t1}"
  IO.println s!"  verify  {ms t1 t2}"
  IO.println s!"  proof   {sizeG} bytes"
  IO.println s!"hypercube (KoalaBear, blowup 1, 100 queries + PoW/grinding defaults):"
  IO.println s!"  build   {ms t3 t4}  (machine synthesis + setup structures)"
  IO.println s!"  prove   {ms t5 t6}"
  IO.println s!"  verify  {ms t6 t7}"
  IO.println s!"  blob    {blob.size} bytes  (vk + proof, bincode)"
  IO.println s!"  claim   {claimKB.size} elements, matches expected: {claimOk}"
  pure (if claimOk then 0 else 1)

def benchNatAddComm (env : Lean.Environment) : IO UInt32 :=
  benchConst ``Nat.add_comm env

/-- Print the multi-stark verifying key's serialized size for the production
kernel system (no proving). -/
def vkSizes (_env : Lean.Environment) : IO UInt32 := do
  let goldTop ← IO.ofExcept <| IxVM.ixVM.mapError toString
  let goldCompiled ← IO.ofExcept goldTop.compile
  let goldSys := Aiur.AiurSystem.build goldCompiled.bytecode
    Aiur.defaultCommitmentParameters Aiur.defaultFriParameters
  IO.println s!"multi-stark kernel vk: {goldSys.vkBytes.size} bytes"
  pure 0

end Tests.Ix.IxVM.Hypercube
