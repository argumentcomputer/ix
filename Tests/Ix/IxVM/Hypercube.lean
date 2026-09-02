module

public import Ix.Aiur.Hypercube
public import Ix.Aiur.Compiler
public import Ix.Aiur.Statistics
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

/-- Execute the same `Claim.check` on both kernels and print the FFT-cost
model's statistics (heights, widths, per-circuit cost) side by side. The
KoalaBear bytecode's constants all fit under the Goldilocks modulus, so the
multi-stark system (whose shapes feed the model) builds for it too — the
model then says what multi-stark WOULD pay for the narrow-field circuits,
a like-for-like circuit-complexity comparison. -/
def kernelStats (name : Lean.Name) (env : Lean.Environment) : IO UInt32 := do
  IO.println s!"kernel-stats: {name}"
  let ixonEnv ← loadIxonEnv name env
  let target ← lookupAddr ixonEnv name
  let claim := Ix.Claim.check target none
  let kbTopE : Except String Aiur.Source.Toplevel := (do
    let p ← IxVM.koalaBearProfile
    let f ← IxVM.ixVMFullOver p
    pure (f.prune [`verify_claim])).mapError toString
  let cases : List (String × Except String Aiur.Source.Toplevel × WitnessProfile) :=
    [("goldilocks", IxVM.ixVM.mapError toString, goldilocksWitnessProfile),
     ("koalabear ", kbTopE, koalaBearWitnessProfile)]
  for (label, topE, profile) in cases do
    let top ← IO.ofExcept topE
    let compiled ← IO.ofExcept top.compile
    let some idx := compiled.getFuncIdx `verify_claim
      | IO.eprintln s!"{label}: verify_claim not found"; return 1
    let sys := Aiur.AiurSystem.build compiled.bytecode
      Aiur.defaultCommitmentParameters Aiur.defaultFriParameters
    let w ← IO.ofExcept <| buildClaimWitness ixonEnv claim {} (profile := profile)
    match compiled.bytecode.execute idx w.input w.inputIOBuffer with
    | .error e => IO.eprintln s!"{label}: execute failed: {e}"; return 1
    | .ok (_, _, queryCounts) =>
      let stats := Aiur.computeStats compiled queryCounts sys.circuitShapes
      let live := stats.circuits.filter (·.height > 0)
      let pow2 (n : Nat) : Nat := if n ≤ 1 then n else Nat.nextPowerOfTwo n
      let area := live.foldl (fun a c => a + c.width * pow2 c.height) 0
      let tallest := live.foldl (fun a c => max a c.height) 0
      IO.println s!"{label}: totalFftCost {stats.totalFftCost}, live circuits {live.size},         Σ width·2^⌈h⌉ = {area}, tallest height {tallest}"
      let top := (live.qsort (fun a b => a.fftCost > b.fftCost)).extract 0 8
      for c in top do
        IO.println s!"    {c.name}: w {c.width}, h {c.height}, fft {c.fftCost}"
  pure 0

def kernelStatsNatAddComm (env : Lean.Environment) : IO UInt32 :=
  kernelStats ``Nat.add_comm env

/-- Print the multi-stark verifying key's serialized size for the production
kernel system (no proving). -/
def vkSizes (_env : Lean.Environment) : IO UInt32 := do
  let goldTop ← IO.ofExcept <| IxVM.ixVM.mapError toString
  let goldCompiled ← IO.ofExcept goldTop.compile
  let goldSys := Aiur.AiurSystem.build goldCompiled.bytecode
    Aiur.defaultCommitmentParameters Aiur.defaultFriParameters
  IO.println s!"multi-stark kernel vk: {goldSys.vkBytes.size} bytes"
  let stats (label : String) (t : Aiur.Bytecode.Toplevel) : IO Unit := do
    let fns := t.functions.filter (·.constrained)
    let widths := fns.foldl (fun a f => a + f.layout.width) 0
    let lookups := fns.foldl (fun a f => a + f.layout.lookups) 0
    IO.println s!"{label}: {fns.size} constrained fns, Σwidth {widths}, Σlookup slots {lookups}"
  stats "goldilocks kernel" goldCompiled.bytecode
  let kbTop ← IO.ofExcept <| (do
    let p ← IxVM.koalaBearProfile
    let f ← IxVM.ixVMFullOver p
    pure (f.prune [`verify_claim])).mapError toString
  let kbCompiled ← IO.ofExcept kbTop.compile
  stats "koalabear kernel " kbCompiled.bytecode
  pure 0

end Tests.Ix.IxVM.Hypercube
