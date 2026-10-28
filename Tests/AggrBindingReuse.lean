module

public import LSpec
public import Ix.IxVM.ClaimHarness

/-!
# One binding proof, two aggregates

End to end through the `ix` binary. The `binding` claim for the default role
table is proven once (`ix prove-binding`), from an environment that carries
the roles and their evidence. Two other environments with that binding, each
a different claim set and carrying only the binding's section, are sharded
(`ix shard`) and their shards proven assuming the binding (`ix prove
--assume-binding`). Each is then aggregated with the same proof file (`ix
aggregate --binding-proof`), and its root verifies as the claim an aggregate
that validates its binding states (`ix verify --aggregate --ixe --ixes`).
The shard proofs alone compose only with the proof file (`ix verify --ixes
--binding-proof`); they do not compose without it, with a proof of another
claim in its place, or with the proof file corrupted, and without it the
aggregate refuses them.

The two aggregates take minutes of recursion and about 190 GB, so `run`
(`aggregate-binding-reuse`) is a manual runner. `cli` (`binding-proof-cli`)
is the same flow without the two aggregates and their verification: the
binding proof, the shard proofs, their composition with the binding proof and
every refusal, in about a minute. Both need `.lake/build/bin/ix` (`lake build
ix`) and keep the store and caches in a temporary `HOME`.
-/

public section

namespace Tests.Aggr.BindingReuse

/-- The closures of `names` and of the constants the kernel fabricates
    during reduction, compiled, with the default role binding's section and
    nothing else: no role records or evidence, which a claim that assumes
    its binding never reads. -/
private def boundClosure (leanEnv : Lean.Environment) (names : Array Lean.Name) :
    IO Ixon.Env := do
  let mut seen : Lean.NameSet := {}
  let mut deduped : Array (Lean.Name × Lean.ConstantInfo) := #[]
  for n in names do
    unless leanEnv.constants.contains n do
      throw (IO.userError s!"{n} is not in the test environment")
  for n in names ++ IxVM.ClaimHarness.synthesizedPrimNames do
    if leanEnv.constants.contains n then
      for entry in Lean.collectDependencies n leanEnv.constants do
        if !seen.contains entry.fst then
          seen := seen.insert entry.fst
          deduped := deduped.push entry
  let raw ← Ix.CompileM.rsCompileEnvFFI deduped.toList
  let bytes ← IO.ofExcept Ix.Kernel.Reader.defaultTableBytes
  let address ← IO.ofExcept Ix.Kernel.Reader.defaultTableAddress
  pure { raw.toEnv with roleBinding := some { address, bytes } }

private def isAddressHex (s : String) : Bool :=
  s.length == 64 && s.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

private def lines (s : String) : List String :=
  (s.splitOn "\n").map (·.trimAscii.toString) |>.filter (!·.isEmpty)

/-- Where `ix` keeps the object at `hex` in the store under `home`
    (`Ix.Store.storePath`). -/
private def storeFile (home : System.FilePath) (hex : String) : System.FilePath :=
  home / ".ix" / "store" / (hex.take 2).toString / ((hex.drop 2).take 2).toString /
    ((hex.drop 4).take 2).toString / (hex.drop 6).toString

/-- Run `ix` with `HOME` set to `home`, logging the command, its exit code
    and time, and on failure the end of its output. -/
private def ix (exe : String) (home : System.FilePath) (args : Array String) :
    IO IO.Process.Output := do
  IO.eprintln s!"[binding-reuse] ix {" ".intercalate args.toList}"
  let started ← IO.monoMsNow
  let out ← IO.Process.output { cmd := "env", args := #[s!"HOME={home}", exe] ++ args }
  IO.eprintln s!"[binding-reuse]   exit {out.exitCode} in {(← IO.monoMsNow) - started} ms"
  if out.exitCode != 0 then
    IO.eprintln s!"{(out.stdout.takeEnd 1500).toString}\n{(out.stderr.takeEnd 1500).toString}"
  pure out

/-- One claim set: shard it, prove its shards assuming the binding, check
    their composition with the binding proof, and without it, with a shard
    proof (a proof of another claim) in its place and with it corrupted;
    check that the aggregate refuses them without it; with `aggregate`,
    aggregate them with it and verify the root against the environment. -/
private def claimSet (exe : String) (home dir : System.FilePath) (label : String)
    (env : Ixon.Env) (shards : Nat) (bindingProof : System.FilePath) (aggregate : Bool) :
    IO (Array (String × Bool)) := do
  let ixe := dir / s!"{label}.ixe"
  let ixes := dir / s!"{label}.ixes"
  IO.FS.writeBinFile ixe (← IO.ofExcept (Ixon.serEnv env))
  let sharded ← ix exe home #["shard", ixe.toString, "--shards", toString shards,
    "--out", ixes.toString]
  if sharded.exitCode != 0 then return #[(s!"{label}: ix shard", false)]
  let proved ← ix exe home #["prove", "--ixe", ixe.toString, "--ixes", ixes.toString,
    "--assume-binding"]
  let proofs := (lines proved.stdout).filter isAddressHex
  if proved.exitCode != 0 || proofs.isEmpty then
    return #[(s!"{label}: ix prove --assume-binding", false)]
  let envArgs := #["--ixe", ixe.toString, "--ixes", ixes.toString]
  let composed ← ix exe home (#["verify"] ++ envArgs ++ proofs.toArray ++
    #["--binding-proof", bindingProof.toString])
  let unbound ← ix exe home (#["verify"] ++ envArgs ++ proofs.toArray)
  -- a proof of another claim (the first shard's) in the binding proof's place
  let otherClaim := dir / s!"{label}-shard-claim.proof"
  IO.FS.writeBinFile otherClaim (← IO.FS.readBinFile (storeFile home proofs.head!))
  let wrongClaim ← ix exe home (#["verify"] ++ envArgs ++ proofs.toArray ++
    #["--binding-proof", otherClaim.toString])
  -- the binding proof with its last byte, in the STARK proof's bytes, changed
  let good ← IO.FS.readBinFile bindingProof
  let corrupt := dir / s!"{label}-corrupt-binding.proof"
  IO.FS.writeBinFile corrupt (good.set! (good.size - 1) (good.get! (good.size - 1) ^^^ 1))
  let corrupted ← ix exe home (#["verify"] ++ envArgs ++ proofs.toArray ++
    #["--binding-proof", corrupt.toString])
  let refused ← ix exe home (#["aggregate"] ++ envArgs ++ proofs.toArray ++ #["--no-write"])
  let refusals := #[
    (s!"{label}: {proofs.length} shard proofs that assume the binding compose with the binding proof",
      composed.exitCode == 0),
    (s!"{label}: without the binding proof they do not compose", unbound.exitCode != 0),
    (s!"{label}: with a shard proof in the binding proof's place they do not compose",
      wrongClaim.exitCode != 0),
    (s!"{label}: with the binding proof corrupted they do not compose", corrupted.exitCode != 0),
    (s!"{label}: without the binding proof the aggregate refuses them", refused.exitCode != 0)]
  unless aggregate do return refusals
  let aggregated ← ix exe home (#["aggregate"] ++ envArgs ++ proofs.toArray ++
    #["--binding-proof", bindingProof.toString])
  let root := (lines aggregated.stdout).getLast?.getD ""
  let verified ← if aggregated.exitCode == 0 && isAddressHex root then
      (·.exitCode == 0) <$> ix exe home (#["verify", "--aggregate", root] ++ envArgs)
    else pure false
  return refusals ++ #[
    (s!"{label}: the aggregate with the binding proof file succeeds",
      aggregated.exitCode == 0 && isAddressHex root),
    (s!"{label}: its root verifies as the environment's claim validating its binding",
      verified)]

/-- The flow, with the two aggregates and their verification when `aggregate`;
    `name` labels the report. -/
def runWith (name : String) (aggregate : Bool) (leanEnv : Lean.Environment) : IO UInt32 := do
  let ixExe : System.FilePath := ".lake" / "build" / "bin" / "ix"
  unless (← ixExe.pathExists) do
    IO.eprintln s!"{ixExe} missing — run `lake build ix` first"
    return 1
  let exe := (← IO.FS.realPath ixExe).toString
  let home ← IO.FS.createTempDir
  let dir ← IO.FS.createTempDir
  try
    -- The binding proof, from an environment that carries the roles and the
    -- records they are validated against.
    let roles ← IxVM.ClaimHarness.loadSharedIxonEnv #[] leanEnv
    let rolesIxe := dir / "roles.ixe"
    IO.FS.writeBinFile rolesIxe (← IO.ofExcept (Ixon.serEnv roles))
    let bindingProof := dir / "binding.proof"
    let proved ← ix exe home #["prove-binding", rolesIxe.toString,
      "--out", bindingProof.toString]
    unless proved.exitCode == 0 && (← bindingProof.pathExists) do
      IO.eprintln "ix prove-binding failed"
      return 1
    -- Two claim sets over that binding, both with the constants the kernel
    -- fabricates: `id` in one shard, and a theorem whose proof reduces
    -- through a bound operation in two.
    let left ← claimSet exe home dir "left" (← boundClosure leanEnv #[``id]) 1
      bindingProof aggregate
    let right ← claimSet exe home dir "right"
      (← boundClosure leanEnv #[``Nat.add_zero]) 2 bindingProof aggregate
    LSpec.lspecIO (.ofList [(name,
      (left ++ right).toList.map fun (label, ok) => LSpec.test label ok)]) []
  finally
    IO.FS.removeDirAll home
    IO.FS.removeDirAll dir

/-- `aggregate-binding-reuse`: the whole flow, with both aggregates. -/
def run (leanEnv : Lean.Environment) : IO UInt32 := runWith "aggregate-binding-reuse" true leanEnv

/-- `binding-proof-cli`: the flow without the aggregates. -/
def cli (leanEnv : Lean.Environment) : IO UInt32 := runWith "binding-proof-cli" false leanEnv

end Tests.Aggr.BindingReuse

end
