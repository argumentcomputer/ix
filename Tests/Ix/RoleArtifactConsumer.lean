module

public import Tests.Ix.RoleGeneration
public import Ix.Cli.CheckLeanCmd

namespace Tests.Ix.RoleArtifactConsumer

open Ixon
open _root_.Ix.RoleBinding.Artifact
open _root_.Ix.Cli.CheckLeanCmd

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def checked (result : Except DriverError α) : IO α :=
  IO.ofExcept (result.mapError DriverError.message)

private def insert (env : Env) (record : Constant) : Env × Address :=
  let address := Address.admissionHash (serConstant record)
  ({ env with consts := env.consts.insert address (LazyConstant.ofConstant record) }, address)

/-- A real theorem body becomes a partial definition in a mutual owner and its
projection. Both remain actual authenticated input records at the tier entry. -/
private def withTier (env : Env) (proof : Constant) : Except String (Env × Address × Address) := do
  let .defn definition := proof.info | throw "fixture proof is not a definition record"
  let tier := { proof with info := .muts #[.defn { definition with kind := .defn, safety := .part }] }
  let (env, owner) := insert env tier
  let projection : Constant := { refs := #[], sharing := #[], univs := #[], info := .dPrj { idx := 0, block := owner } }
  let (env, address) := insert env projection
  return (env, owner, address)

private def checks : IO Nat := do
  let (env, generated) ← IO.ofExcept (Tests.Ix.RoleGeneration.completeArtifact .natDiv)
  let some (proofAddress, proof) := generated.evidence[0]?
    | throw (IO.userError "fixture has no proof")
  let (tierEnv, tierOwner, tierAddress) ← IO.ofExcept (withTier env proof)
  let receipt ← IO.ofExcept ((checkTiered tierEnv artifactLimits).mapError toString)
  ensure (!receipt.logical.consts.isEmpty && receipt.tier.length == 1)
    "the actual logical/tier fold did not accept the nonempty fixture"
  ensure (receipt.prepared.records.length == tierEnv.consts.size &&
    receipt.prepared.binding.bytes == generated.table.toBytes)
    "tier receipt changed the actual binding or original raw batch"
  ensure (!(check tierEnv artifactLimits).isOk) "logical-only entry accepted a partial definition"
  let input ← IO.ofExcept ((prepareRecords tierEnv artifactLimits).mapError toString)
  let (logical, tier) := _root_.Ix.Kernel.Admission.partitionTier input.constants
  let keys := logical.map (·.1) ++ tier.toList.map (fun (_, a, _) => a)
  ensure (keys.length == input.constants.length && keys.eraseDups.length == keys.length &&
    input.constants.all (fun (a, _) => keys.contains a)) "partition lost or duplicated an original record"
  ensure (tier.size == 2 && tier.any (fun (_, a, _) => a == tierOwner) &&
    tier.any (fun (_, a, _) => a == tierAddress)) "tier projection was not partitioned with its owner"
  ensure (!(receipt.prepared.preludeFor { generated.table with bound := #[] }).isOk)
    "tier prelude accepted a different canonical table"
  let some tierRaw := tierEnv.consts[tierOwner]? | throw (IO.userError "tier owner missing")
  let badRaw := { tierRaw with buf := ByteArray.mk #[0], off := 0, len := 1 }
  ensure (match checkTiered { tierEnv with consts := tierEnv.consts.insert tierOwner badRaw } artifactLimits with
    | .error (.preparation (.bytes (.mismatch _ _ _))) => true | _ => false)
    "tier bytes escaped the authentication of the complete input"
  ensure (match checkTiered { tierEnv with consts := tierEnv.consts.erase proofAddress } artifactLimits with
    | .error (.preparation (.coverage _)) => true | _ => false)
    "missing proof was supplied by a default evidence store"
  let .defn definition := proof.info | throw (IO.userError "proof kind changed")
  let fenced : Constant := { proof with
    refs := proof.refs.push tierAddress
    info := .defn { definition with kind := .defn, value := .ref proof.refs.size.toUInt64 #[] } }
  let (fencedEnv, _) := insert tierEnv fenced
  ensure (match checkTiered fencedEnv artifactLimits with
    | .error (.admission (.fence _ _)) => true | _ => false) "logical reference to tier escaped the fence"

  let cfg : CheckCfg := { silent := true, progressMs := 0, slowMs := 0 }
  let bytes ← IO.ofExcept (serEnv env)
  let tierBytes ← IO.ofExcept (serEnv tierEnv)
  for anon in [false, true] do
    let p ← checked (← prepareInput bytes anon)
    let logical ← checked (← runPrepared p cfg .all)
    ensure (logical.failures.isEmpty && logical.artifactAdmission == some (.logical env.consts.size))
      "bound whole check did not run the actual logical entry"
    ensure (logical.hostStatement.any (·.kind == .logical))
      "bound whole check omitted its receipt-derived host statement"
    let selected := if anon then toString (generated.table.addressOf? .natDiv).get! else "Nat.div"
    let selected ← checked (← runPrepared p cfg (.only #[selected]))
    ensure (selected.failures.isEmpty && selected.artifactAdmission.isNone && selected.hostStatement.isNone)
      "selected proof-backed operation lost actual evidence or claimed whole admission"
    let capped ← checked (← runPrepared p cfg .all (some 1))
    ensure (capped.artifactAdmission.isNone && capped.hostStatement.isNone)
      "capped checking claimed complete artifact admission"
    let tp ← checked (← prepareInput tierBytes anon)
    let tr ← checked (← runPrepared tp cfg .all)
    ensure (tr.failures.isEmpty && tr.artifactAdmission == some (.tiered tierEnv.consts.size 1))
      "bound whole check did not run the actual tiered entry"
    ensure (tr.hostStatement.any (fun s => match s.kind with | .tiered .. => true | _ => false))
      "bound tier check omitted its receipt-derived partition commitments"
    let thin := { env with assumptions := ({} : Std.HashSet Address).insert tierAddress }
    let thin ← IO.ofExcept (serEnv thin)
    let thin ← checked (← prepareInput thin anon)
    ensure (match checkWhole thin .all none with
      | .error (.artifact message) => message.contains "thin artifact" | _ => false)
      "unresolved thin input obtained a whole receipt"

  -- An unnamed bad theorem is absent from the meta inventory. Whole checking
  -- must still refuse it through the exact full artifact entry.
  let badProof := { proof with info := .defn { definition with value := .var 0 } }
  let (badEnv, _) := insert env badProof
  let badBytes ← IO.ofExcept (serEnv badEnv)
  let bad ← checked (← prepareInput badBytes)
  ensure (match ← runPrepared bad cfg .all with | .error (.artifact _) => true | _ => false)
    "an unnamed invalid record escaped bound whole checking"
  let ix ← IO.FS.realPath ".lake/build/bin/ix"
  let dir ← IO.FS.createTempDir
  try
    let path := dir / "bound.ixe"
    let tierPath := dir / "tier.ixe"
    let badPath := dir / "invalid.ixe"
    IO.FS.writeBinFile path bytes
    IO.FS.writeBinFile tierPath tierBytes
    IO.FS.writeBinFile badPath badBytes
    let vars := #[("IX_KERNEL_CHECK_PROGRESS_MS", some "0"), ("IX_KERNEL_CHECK_SLOW_MS", some "0")]
    for (file, args, code, text) in [
        (path, #[], 0, "whole artifact: logical entry accepted"),
        (tierPath, #["--anon"], 0, "tier constants typed only"),
        (path, #["--consts", "Nat.div"], 0, "selected checking only"),
        (badPath, #[], 3, "artifact")] do
      let out ← IO.Process.output { cmd := ix.toString, args := #["check-lean", file.toString] ++ args, env := vars }
      ensure (out.exitCode == code && (out.stdout ++ out.stderr).contains text)
        s!"bound CLI control failed: {out.exitCode}\n{out.stdout}\n{out.stderr}"
    let failures := dir / "aggregate-failures.txt"
    let out ← IO.Process.output {
      cmd := ix.toString
      args := #["check-lean", badPath.toString, "--fail-out", failures.toString]
      env := vars }
    ensure (out.exitCode == 3 && out.stderr.contains "artifact") "aggregate refusal exit changed"
    let lines := (← IO.FS.readFile failures).splitOn "\n" |>.map (·.trimAscii.toString)
    ensure (lines.any (·.contains "artifact") && lines.all (fun line => line.isEmpty || line.startsWith "#"))
      "aggregate refusal wrote a fabricated declaration selector"
    let kernel ← IO.FS.realPath ".lake/build/bin/kernel-check-ixe"
    let neutral := #["CHECK_IXE_ROOTS", "CHECK_IXE_SKIP", "CHECK_IXE_READ_CACHE"].map (·, none)
    let mut previous : Option (Array (String × String × String)) := none
    for mode in ["stream", "eager"] do
      let rowsPath := dir / s!"{mode}.jsonl"
      let result ← IO.Process.output {
        cmd := kernel.toString
        args := #[path.toString, rowsPath.toString, "--load", mode, "--jobs", "2"]
        env := neutral }
      ensure (result.exitCode == 0) s!"bound diagnostic {mode} failed: {result.stdout}\n{result.stderr}"
      let mut rows : Array (String × String × String) := #[]
      for line in (← IO.FS.readFile rowsPath).splitOn "\n" do
        if line.isEmpty then continue
        let row ← IO.ofExcept (Lean.Json.parse line)
        rows := rows.push (← IO.ofExcept (row.getObjValAs? String "address"),
          ← IO.ofExcept (row.getObjValAs? String "outcome"), ← IO.ofExcept (row.getObjValAs? String "reason"))
      ensure (!rows.isEmpty && rows.all (·.2.1 == "accept")) "actual bound proof/operation records were refused"
      for (address, lazy) in env.consts.toList do
        let record ← IO.ofExcept lazy.get
        let owner := toString (Ixon.CheckOrder.owner address record)
        ensure (rows.any (·.1 == owner)) s!"bound diagnostic omitted owner {owner}"
      let sorted := rows.qsort (fun a b => a.1 < b.1)
      if let some earlier := previous then ensure (earlier == sorted) "stream/eager bound diagnostic rows differ"
      previous := some sorted
    return 7
  finally
    IO.FS.removeDirAll dir

public def units : LSpec.TestSeq :=
  .individualIO "bound artifact consumers: whole logical/tier entries and actual CLI routing" none (do
    let count ← checks
    return (true, count, 0, none)) .done

end Tests.Ix.RoleArtifactConsumer
