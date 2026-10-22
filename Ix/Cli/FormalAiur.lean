module
public import Cli
public import Ix.Check
public import Ix.Shard.Check
public import Ix.Store
public import Ix.Aggr.Reference
public import Ix.Cli.ShardProofIndex

/-! Application bridge to the separate Aiur/IxVM packages. This module reuses
Ix's claim and witness construction, not the legacy evaluator or compiler.
Compilation runs in the standalone exporter and is cached by its contents.
The generic Aiur Lean library does not acquire application-specific FFI. -/
public section
namespace Ix.Cli.FormalAiur
open Lean LegacyIxVM.ClaimHarness

def selected (p : Cli.Parsed) : Bool := p.hasFlag "formal"

def command (cmd : String) (args : Array String) : IO Unit := do
  (← IO.getStdout).flush
  let child ← IO.Process.spawn { cmd, args, stdout := .inherit, stderr := .inherit }
  let code ← child.wait
  unless code == 0 do throw (IO.userError s!"{cmd} failed with status {code}")

def compiledArtifact (p : Cli.Parsed) (flag env exporterPath target sourcePath mode : String)
    (extra : Array String := #[]) : IO String := do
  if let some path := p.flag? flag then return path.as! String
  if let some path ← IO.getEnv env then return path
  let exporter := System.FilePath.mk exporterPath
  command "lake" #["-q", "build", target]
  let source ← IO.FS.readBinFile sourcePath
  let compiler ← IO.FS.readBinFile exporter
  let digest := Address.blake3 ((Address.blake3 compiler).hash ++ source)
  let directory := System.FilePath.mk ".lake/aiur"
  IO.FS.createDirAll directory
  let path := directory / s!"{target}-{digest}.json"
  unless ← path.pathExists do
    let pid ← IO.Process.getPID
    let stamp ← IO.monoNanosNow
    let tmp := directory / s!"{target}-{digest}.tmp.{pid}.{stamp}"
    try
      command "lake" (#["env", exporter.toString, mode, tmp.toString] ++ extra)
      IO.FS.rename tmp path
    finally
      if ← tmp.pathExists then IO.FS.removeFile tmp
  return path.toString

def artifact (p : Cli.Parsed) : IO String :=
  compiledArtifact p "aiur-artifact" "IX_AIUR_ARTIFACT" "IxVM/.lake/build/bin/ixvm"
    "ixvm" "IxVM/IxVM/Program.aiur" "export-claim-trace"

def host : IO String := do
  if let some path ← IO.getEnv "IX_AIUR_HOST" then return path
  let path := System.FilePath.mk "target/release/ixvm-proof"
  unless ← path.pathExists do
    command "cargo" #["build", "--release", "--locked", "-p", "ixvm", "--bin", "ixvm-proof", "--features", "parallel"]
  return path.toString

/-- Stream metadata is small; each byte payload is transported exactly once.
The Rust host turns these into immutable vectors captured by hint closures. -/
def invocation (input : Array LegacyAiur.G) (buffer : LegacyAiur.IOBuffer)
    (entry : String := "IxVM::verify_claim") : Json :=
  Json.mkObj [("entry", toJson entry), ("args", toJson (input.map (·.n))),
    ("streams", toJson (buffer.map.toArray.map fun ((channel, key), info) =>
      Json.mkObj [("channel", toJson channel.n), ("key", toJson (key.map LegacyAiur.G.n)),
        ("values", toJson ((buffer.data.getD channel #[]).extract info.idx (info.idx + info.len) |>.map LegacyAiur.G.n))]))]

def invoke (artifactPath mode : String) (input : Json) (proofPath : String)
    (rows : Nat) (retention : String := "regenerate") : IO Unit :=
  IO.FS.withTempFile fun handle path => do
    handle.putStr input.compress
    handle.flush
    command (← host) #[mode, artifactPath, path.toString, proofPath, toString rows, retention]

def rejectFlags (p : Cli.Parsed) (flags : Array String) : IO Unit := do
  for flag in flags do
    if p.hasFlag flag then
      throw (IO.userError s!"--{flag} is currently supported by the legacy backend only; omit --formal to use it")

def retention (p : Cli.Parsed) : IO String := do
  let value := ((p.flag? "retention").map (·.as! String)).getD "regenerate"
  unless value == "regenerate" || value == "retain" do
    throw (IO.userError "formal retention must be retain or regenerate; automatic RAM planning remains in the legacy backend")
  return value

def rows (p : Cli.Parsed) : IO Nat := do
  let n := ((p.flag? "shard-rows").map (·.as! Nat)).getD 65536
  unless n > 0 && (n &&& (n - 1)) == 0 do
    throw (IO.userError "--shard-rows must be a positive power of two")
  return n

def verifyWrapper (artifactPath : String) (wrapper : Ixon.Proof) : IO Unit := do
  let digest := Address.blake3 (Ix.Claim.ser wrapper.claim)
  IO.FS.withTempFile fun _ path => do
    IO.FS.writeBinFile path wrapper.proof
    invoke artifactPath "verify" (invocation (packedDigestKey digest) default) path.toString 65536

def shardIndex : IO System.FilePath := StoreIO.toIO (Store.cacheDir "formal-shard-proofs")

private def one (p : Cli.Parsed) (artifactPath : String) (prove : Bool) (rows : Nat) (retain : String)
    (claim : Ix.Claim) (_ : Option LegacyAiur.EnvHandle) (target : Ix.Check.Target)
    (label : String) : IO UInt32 := do
  try
    let .leanW witness := target | throw (IO.userError "formal backend needs a stream witness")
    let digest := Address.blake3 (Ix.Claim.ser claim)
    if prove && p.hasFlag "skip-proven" && !p.hasFlag "no-index" then
      if let some addr ← ShardProofIndex.readAddress (← shardIndex) digest then
        try
          let wrapper ← IO.ofExcept (Ixon.Proof.de (← StoreIO.toIO (Store.read addr)))
          unless wrapper.claim == claim do throw (IO.userError "cached claim mismatch")
          verifyWrapper artifactPath wrapper
          IO.println s!"reused {addr}"
          return 0
        catch e => IO.eprintln s!"ignored cached proof {addr}: {e}"
    IO.println s!"{if prove then "Proving" else "Checking"} {label} with formal Aiur"
    let input := invocation witness.input witness.inputIOBuffer
    if !prove then
      invoke artifactPath "execute" input "" rows
      return 0
    IO.FS.withTempFile fun _ path => do
      invoke artifactPath "prove" input path.toString rows retain
      let proof ← IO.FS.readBinFile path
      let keyPath := path.toString ++ ".vk"
      let claimsPath := path.toString ++ ".claims"
      let key ← IO.FS.readBinFile keyPath
      let keyAddr ← StoreIO.toIO (Store.write key)
      IO.FS.removeFile keyPath
      IO.FS.removeFile claimsPath
      let _ ← StoreIO.toIO (Store.write (Ix.Claim.ser claim))
      let wrapper : Ixon.Proof := { claim, proof }
      let proofAddr ← StoreIO.toIO (Store.write (Ixon.Proof.ser wrapper))
      unless p.hasFlag "no-index" do
        ShardProofIndex.writeAddress (← shardIndex) digest proofAddr
      IO.println s!"verifying-key {keyAddr}"
      IO.println (toString proofAddr)
      return 0
  catch e =>
    IO.eprintln s!"{label}: {e}"
    return 1

def run (p : Cli.Parsed) (prove : Bool) : IO UInt32 := do
  rejectFlags p #["interp", "stats-out", "json", "json-name", "ram-budget", "out-ixes",
    "shards", "report", "distributed", "cells", "lanes", "exec-jobs", "plan-only", "max-ram", "texray"]
  let rowLimit ← rows p
  let retain ← retention p
  let artifactPath ← artifact p
  let runOne := one p artifactPath (prove && !p.hasFlag "exec-only") rowLimit retain
  let ixe := (p.flag? "ixe").map (·.as! String)
  let manifest := (p.flag? "ixes").map (·.as! String)
  match ixe, manifest, (p.flag? "shard").map (·.as! Nat) with
  | some ixe, some manifest, some k =>
    Ix.Shard.Check.runShardCheckManifest manifest ixe k (fun c w l => runOne c none (.leanW w) l)
  | some ixe, some manifest, none =>
    Ix.Shard.Check.runShardCheckAll manifest ixe ((p.flag? "jobs").map (·.as! Nat))
      (fun c w l => runOne c none (.leanW w) l)
  | _, some _, _ => IO.eprintln "--ixes requires --ixe"; return 1
  | _, none, some _ => IO.eprintln "--shard requires --ixes"; return 1
  | _, none, none =>
    if p.hasFlag "jobs" then throw (IO.userError "formal --jobs currently requires --ixe and --ixes")
    Ix.Check.forEachClaim ixe ((p.flag? "claim").map (·.as! String))
      (p.variableArgsAs! String).toList (p.hasFlag "keep-going") "formal-aiur" true runOne

def verify (p : Cli.Parsed) : IO UInt32 := do
  rejectFlags p #["aggregate", "structural-above"]
  let artifactPath ← artifact p
  let proofs := p.variableArgsAs! String
  let ixe := (p.flag? "ixe").map (·.as! String)
  let manifest := (p.flag? "ixes").map (·.as! String)
  let shard := (p.flag? "shard").map (·.as! Nat)
  let mut expected : Array Ix.Claim := #[]
  match ixe, manifest with
  | some ixe, some manifest =>
    let env ← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile ixe))
    let view ← IO.ofExcept (Ix.Shard.parseIxesManifest (← IO.FS.readBinFile manifest))
    if !(← Ix.Shard.shardsCover env view.shards) then return 1
    match shard with
    | some k =>
      let some blocks := view.shards[k]? | throw (IO.userError "shard index out of range")
      let prepared ← IO.ofExcept (Aggr.Reference.prepareShards env #[blocks])
      expected := prepared.map (·.claim)
    | none =>
      let (view, _) ← IO.ofExcept (view.pruneEmpty env)
      let prepared ← IO.ofExcept (Aggr.Reference.prepareShards env view.shards)
      expected := prepared.map (·.claim)
  | none, none =>
    if shard.isSome || p.hasFlag "record" then throw (IO.userError "--shard/--record requires --ixe and --ixes")
  | _, _ => throw (IO.userError "formal partition verification requires both --ixe and --ixes")
  if proofs.isEmpty then
    if expected.isEmpty then IO.eprintln "expected a proof address"; return 1
    for claim in expected do IO.println s!"CheckEnv claim digest: {Address.blake3 (Ix.Claim.ser claim)}"
    return 0
  let mut result := 0
  let mut covered : Array Ix.Claim := #[]
  for hex in proofs do
    try
      let some addr := Address.fromString hex | throw (IO.userError "invalid proof address")
      let wrapper ← IO.ofExcept (Ixon.Proof.de (← StoreIO.toIO (Store.read addr)))
      unless expected.isEmpty || expected.contains wrapper.claim do
        throw (IO.userError "proof does not match a requested manifest shard")
      if covered.contains wrapper.claim then throw (IO.userError "duplicate shard proof")
      let digest := Address.blake3 (Ix.Claim.ser wrapper.claim)
      verifyWrapper artifactPath wrapper
      covered := covered.push wrapper.claim
      if p.hasFlag "record" then ShardProofIndex.writeAddress (← shardIndex) digest addr
      IO.println s!"ok: proof {addr} verifies claim {digest}"
    catch e => IO.eprintln s!"{hex}: {e}"; result := 1
  unless expected.all covered.contains do
    IO.eprintln "proofs do not cover every requested nonempty shard"
    return 1
  return result

end Ix.Cli.FormalAiur
end
