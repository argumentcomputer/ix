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

/-- Publish `name` at `address`. -/
private def publish (env : Env) (name : String) (address : Address) : Env :=
  let n := _root_.Ix.Name.mkStr _root_.Ix.Name.mkAnon name
  { env with named := env.named.insert n { addr := address }, names := RawEnv.addNameComponents env.names n }

/-- `axiom cheat : False` and `theorem useCheat : False := cheat`, both published:
a user axiom, which strict checking declines, and a constant that depends on it. -/
private def withCheat (env : Env) (falseAddress : Address) : Env × Address × Address :=
  let cheat : Constant := {
    info := .axio ⟨false, 0, .ref 0 #[]⟩, sharing := #[], refs := #[falseAddress], univs := #[] }
  let (env, cheatAddress) := insert env cheat
  let useCheat : Constant := {
    info := .defn ⟨.thm, .safe, {}, 0, .ref 0 #[], .ref 1 #[]⟩, sharing := #[]
    refs := #[falseAddress, cheatAddress], univs := #[] }
  let (env, useAddress) := insert env useCheat
  (publish (publish env "cheat" cheatAddress) "useCheat" useAddress, cheatAddress, useAddress)

/-- `axiom badCheat : False False`, published: a user axiom that reads, but
whose type does not check (`False` is not a function). -/
private def withBadCheat (env : Env) (falseAddress : Address) : Env × Address :=
  let bad : Constant := {
    info := .axio ⟨false, 0, .app (.ref 0 #[]) (.ref 0 #[])⟩, sharing := #[], refs := #[falseAddress]
    univs := #[] }
  let (env, address) := insert env bad
  (publish env "badCheat" address, address)

private structure Fixture where
  env : Env
  tierEnv : Env
  badEnv : Env
  cheatEnv : Env
  tierCheatEnv : Env
  badCheatEnv : Env
  generated : _root_.Ix.RoleBinding.Generated
  proofAddress : Address
  proof : Constant
  tierOwner : Address
  tierAddress : Address
  cheatAddress : Address
  useAddress : Address
  badAddress : Address
  bytes : ByteArray
  tierBytes : ByteArray
  badBytes : ByteArray
  cheatBytes : ByteArray
  badCheatBytes : ByteArray
  tierCheatBytes : ByteArray
  noSorry : ByteArray
  ix : System.FilePath
  kernel : System.FilePath
  dir : System.FilePath
  path : System.FilePath
  tierPath : System.FilePath
  badPath : System.FilePath
  cheatPath : System.FilePath
  tierCheatPath : System.FilePath
  noSorryPath : System.FilePath
  boundPath : System.FilePath

private def buildFixture : IO Fixture := do
  let (env, generated) ← IO.ofExcept (Tests.Ix.RoleGeneration.completeArtifact .natDiv)
  let some (proofAddress, proof) := generated.evidence[0]?
    | throw (IO.userError "fixture has no proof")
  let (tierEnv, tierOwner, tierAddress) ← IO.ofExcept (withTier env proof)
  let .defn definition := proof.info | throw (IO.userError "proof kind changed")
  let badProof := { proof with info := .defn { definition with value := .var 0 } }
  let (badEnv, _) := insert env badProof
  let some falseAddress := generated.table.addressOf? .false | throw (IO.userError "fixture has no False")
  let (cheatEnv, cheatAddress, useAddress) := withCheat env falseAddress
  let (tierCheatEnv, _, _) := withCheat tierEnv falseAddress
  let (badCheatEnv, badAddress) := withBadCheat cheatEnv falseAddress
  let table := generated.table
  let noSorryTable : _root_.Ix.Kernel.RoleTable :=
    { table with bound := table.bound.filter (·.1 != _root_.Ix.Kernel.Role.sorryAx) }
  let noSorryBytes := noSorryTable.toBytes
  let noSorryEnv := { cheatEnv with roleBinding := some ⟨Address.admissionHash noSorryBytes, noSorryBytes⟩ }
  let bytes ← IO.ofExcept (serEnv env)
  let tierBytes ← IO.ofExcept (serEnv tierEnv)
  let badBytes ← IO.ofExcept (serEnv badEnv)
  let cheatBytes ← IO.ofExcept (serEnv cheatEnv)
  let badCheatBytes ← IO.ofExcept (serEnv badCheatEnv)
  let tierCheatBytes ← IO.ofExcept (serEnv tierCheatEnv)
  let noSorry ← IO.ofExcept (serEnv noSorryEnv)
  let ix ← IO.FS.realPath ".lake/build/bin/ix"
  let kernel ← IO.FS.realPath ".lake/build/bin/kernel-check-ixe"
  let dir ← IO.FS.createTempDir
  let path := dir / "bound.ixe"
  let tierPath := dir / "tier.ixe"
  let badPath := dir / "invalid.ixe"
  let cheatPath := dir / "cheat.ixe"
  let tierCheatPath := dir / "tier-cheat.ixe"
  let noSorryPath := dir / "no-sorry.ixe"
  let boundPath := dir / "bound-axioms.ixe"
  IO.FS.writeBinFile path bytes
  IO.FS.writeBinFile tierPath tierBytes
  IO.FS.writeBinFile badPath badBytes
  IO.FS.writeBinFile cheatPath cheatBytes
  IO.FS.writeBinFile tierCheatPath tierCheatBytes
  IO.FS.writeBinFile noSorryPath noSorry
  IO.FS.writeBinFile boundPath bytes
  return {
    env, tierEnv, badEnv, cheatEnv, tierCheatEnv, badCheatEnv, generated,
    proofAddress, proof, tierOwner, tierAddress, cheatAddress, useAddress, badAddress,
    bytes, tierBytes, badBytes, cheatBytes, badCheatBytes, tierCheatBytes, noSorry,
    ix, kernel, dir, path, tierPath, badPath, cheatPath, tierCheatPath, noSorryPath, boundPath
  }

private def rowsOf (rowsPath : System.FilePath) : IO (Std.HashMap String String) := do
  let mut rows : Std.HashMap String String := {}
  for line in (← IO.FS.readFile rowsPath).splitOn "\n" do
    if line.isEmpty then continue
    let row ← IO.ofExcept (Lean.Json.parse line)
    rows := rows.insert (← IO.ofExcept (row.getObjValAs? String "address"))
      (← IO.ofExcept (row.getObjValAs? String "outcome"))
  return rows

private def checkKernelIxeUserAxioms (fx : Fixture) (args : Array String)
    (cache? : Option System.FilePath) (allow : Bool) (outName : String) : IO Unit := do
  let rowsPath := fx.dir / outName
  let result ← IO.Process.output {
    cmd := fx.kernel.toString
    args := #[fx.cheatPath.toString, rowsPath.toString] ++ args ++ (if allow then #["--allow-user-axioms"] else #[])
    env := #[("CHECK_IXE_ROOTS", none), ("CHECK_IXE_SKIP", none),
      ("CHECK_IXE_READ_CACHE", cache?.map (·.toString))] }
  let rows ← rowsOf rowsPath
  let label := s!"kernel-check-ixe {args} allow={allow}"
  ensure (result.exitCode == 0 && rows.contains (toString fx.cheatAddress) && rows.contains (toString fx.useAddress))
    s!"{label} failed: {result.exitCode}\n{result.stderr}"
  if allow then
    ensure (rows.toList.all (·.2 == "accept") &&
      result.stderr.contains s!"CONDITIONAL on 1 user axioms:\n  {fx.cheatAddress}")
      s!"{label} did not admit and list the user axiom\n{result.stderr}"
  else
    ensure (rows[toString fx.cheatAddress]? != some "accept" && rows[toString fx.useAddress]? != some "accept" &&
      !result.stderr.contains "CONDITIONAL")
      s!"{label} admitted a user axiom while strict\n{result.stderr}"

private def orderedChecks (env tierEnv badEnv : Env) : IO Unit := do
  let prepared ← IO.ofExcept ((prepareRecords env artifactLimits).mapError toString)
  let order := (prepared.prepared.records.map Prod.fst).toArray
  let ordinary ← IO.ofExcept ((check env artifactLimits).mapError toString)
  let ordered ← IO.ofExcept ((checkAt env artifactLimits order).mapError toString)
  ensure (ordered.prepared.records == prepared.prepared.records &&
    ordered.target.consts.map (·.name) == ordinary.target.consts.map (·.name))
    "explicit logical order changed raw rows or accepted declaration sequence"
  let tierInput ← IO.ofExcept ((prepareRecords tierEnv artifactLimits).mapError toString)
  let tierOrder := (tierInput.prepared.records.map Prod.fst).toArray
  let defaultTier ← IO.ofExcept ((checkTiered tierEnv artifactLimits).mapError toString)
  let orderedTier ← IO.ofExcept ((checkTieredAt tierEnv artifactLimits tierOrder).mapError toString)
  ensure (orderedTier.prepared.records == tierInput.prepared.records &&
    orderedTier.logical.consts.map (·.name) == defaultTier.logical.consts.map (·.name) &&
    orderedTier.tier.length == defaultTier.tier.length)
    "explicit tier order changed raw rows, logical declarations or tier census"
  ensure (!(checkAt tierEnv artifactLimits tierOrder).isOk)
    "explicit logical entry retried partial input through the tier"
  for (artifact, actualOrder) in [(env, order), (tierEnv, tierOrder)] do
    ensure (actualOrder.size > 1) "ordered fixture is unexpectedly small"
    let missing := Address.admissionHash "ordered-entry-absent-record".toUTF8
    ensure (!artifact.consts.contains missing) "missing-order control names an existing record"
    let duplicate := actualOrder.set! 0 actualOrder[1]!
    let unknown := actualOrder.set! 0 missing
    for invalid in [actualOrder.pop, duplicate, unknown] do
      ensure (match prepareRecordsAt artifact artifactLimits invalid with
        | .error (.coverage _) => true | _ => false)
        "explicit order admitted incomplete, duplicated or foreign records"
      ensure (!(checkAt artifact artifactLimits invalid).isOk &&
        !(checkTieredAt artifact artifactLimits invalid).isOk)
        "an actual entry bypassed explicit-order coverage guards"
  let badInput ← IO.ofExcept ((prepareRecords badEnv artifactLimits).mapError toString)
  let badOrder := (badInput.prepared.records.map Prod.fst).toArray
  ensure (!(checkAt badEnv artifactLimits badOrder).isOk &&
    !(checkTieredAt badEnv artifactLimits badOrder).isOk)
    "explicit-order admission accepted an invalid logical theorem"

private def tierFenceChecks (fx : Fixture) : IO Unit := do
  let receipt ← IO.ofExcept ((checkTiered fx.tierEnv artifactLimits).mapError toString)
  ensure (!receipt.logical.consts.isEmpty && receipt.tier.length == 1)
    "the actual logical/tier fold did not accept the nonempty fixture"
  ensure (receipt.prepared.records.length == fx.tierEnv.consts.size &&
    receipt.prepared.binding.bytes == fx.generated.table.toBytes)
    "tier receipt changed the actual binding or original raw batch"
  ensure (!(check fx.tierEnv artifactLimits).isOk) "logical-only entry accepted a partial definition"
  let input ← IO.ofExcept ((prepareRecords fx.tierEnv artifactLimits).mapError toString)
  let (logical, tier) := _root_.Ix.Kernel.Admission.partitionTier input.constants
  let keys := logical.map (·.1) ++ tier.toList.map (fun (_, a, _) => a)
  ensure (keys.length == input.constants.length && keys.eraseDups.length == keys.length &&
    input.constants.all (fun (a, _) => keys.contains a)) "partition lost or duplicated an original record"
  ensure (tier.size == 2 && tier.any (fun (_, a, _) => a == fx.tierOwner) &&
    tier.any (fun (_, a, _) => a == fx.tierAddress)) "tier projection was not partitioned with its owner"
  ensure (!(receipt.prepared.preludeFor { fx.generated.table with bound := #[] }).isOk)
    "tier prelude accepted a different canonical table"
  let some tierRaw := fx.tierEnv.consts[fx.tierOwner]? | throw (IO.userError "tier owner missing")
  let badRaw := { tierRaw with buf := ByteArray.mk #[0], off := 0, len := 1 }
  ensure (match checkTiered { fx.tierEnv with consts := fx.tierEnv.consts.insert fx.tierOwner badRaw } artifactLimits with
    | .error (.preparation (.bytes (.mismatch _ _ _))) => true | _ => false)
    "tier bytes escaped the authentication of the complete input"
  ensure (match checkTiered { fx.tierEnv with consts := fx.tierEnv.consts.erase fx.proofAddress } artifactLimits with
    | .error (.preparation (.coverage _)) => true | _ => false)
    "missing proof was supplied by a default evidence store"
  let .defn definition := fx.proof.info | throw (IO.userError "proof kind changed")
  let fenced : Constant := { fx.proof with
    refs := fx.proof.refs.push fx.tierAddress
    info := .defn { definition with kind := .defn, value := .ref fx.proof.refs.size.toUInt64 #[] } }
  let (fencedEnv, _) := insert fx.tierEnv fenced
  ensure (match checkTiered fencedEnv artifactLimits with
    | .error (.admission (.fence _ _)) => true | _ => false) "logical reference to tier escaped the fence"

private def inProcessWholeCheck (fx : Fixture) (anon : Bool) : IO Unit := do
  let cfg : CheckCfg := { silent := true, progressMs := 0, slowMs := 0 }
  let p ← checked (← prepareInput fx.bytes anon)
  let logical ← checked (← runPrepared p cfg .all)
  ensure (logical.failures.isEmpty && logical.artifactAdmission == some (.logical fx.env.consts.size))
    "bound whole check did not run the actual logical entry"
  ensure (logical.hostStatement.any (·.kind == .logical))
    "bound whole check omitted its receipt-derived host statement"
  ensure (logical.rows.isEmpty && logical.execution == .serial)
    "default quiet whole check did not take the single-pass checkWhole fast path"
  let logicalFull ← checked (← runPrepared p { cfg with perRecord := true } .all)
  ensure (logical.artifactAdmission == logicalFull.artifactAdmission &&
    logical.hostStatement == logicalFull.hostStatement &&
    logical.passed == logicalFull.passed && logical.typed == logicalFull.typed &&
    logical.targetsCovered == logicalFull.targetsCovered &&
    logical.roles == logicalFull.roles && !logicalFull.rows.isEmpty)
    "single-pass whole check disagreed with per-record pool check"
  let selected := if anon then toString (fx.generated.table.addressOf? .natDiv).get! else "Nat.div"
  let selected ← checked (← runPrepared p cfg (.only #[selected]))
  ensure (selected.failures.isEmpty && selected.artifactAdmission.isNone && selected.hostStatement.isNone)
    "selected proof-backed operation lost actual evidence or claimed whole admission"
  let capped ← checked (← runPrepared p cfg .all (some 1))
  ensure (capped.artifactAdmission.isNone && capped.hostStatement.isNone)
    "capped checking claimed complete artifact admission"
  let tp ← checked (← prepareInput fx.tierBytes anon)
  let tr ← checked (← runPrepared tp cfg .all)
  ensure (tr.failures.isEmpty && tr.artifactAdmission == some (.tiered fx.tierEnv.consts.size 1))
    "bound whole check did not run the actual tiered entry"
  ensure (tr.hostStatement.any (fun s => match s.kind with | .tiered .. => true | _ => false))
    "bound tier check omitted its receipt-derived partition commitments"
  let thin := { fx.env with assumptions := ({} : Std.HashSet Address).insert fx.tierAddress }
  let thin ← IO.ofExcept (serEnv thin)
  let thin ← checked (← prepareInput thin anon)
  ensure (match checkWhole thin .all none with
    | .error (.artifact message) => message.contains "thin artifact" | _ => false)
    "unresolved thin input obtained a whole receipt"

private def inProcessUserAxiomCheck (fx : Fixture) (anon : Bool) : IO Unit := do
  let cfg : CheckCfg := { silent := true, progressMs := 0, slowMs := 0 }
  let strict ← checked (← prepareInput fx.cheatBytes anon)
  let r ← checked (← runPrepared strict cfg .all)
  ensure (!r.failures.isEmpty && r.artifactAdmission.isNone && r.conditionalOn.isEmpty &&
    runExit r true == _root_.Ix.Benchmark.Results.exitRejected)
    "strict checking admitted a user axiom"
  let p ← checked (← prepareInput fx.cheatBytes anon (allowUserAxioms := true))
  let r ← checked (← runPrepared p cfg .all)
  ensure (r.failures.isEmpty && r.hostStatement.isNone &&
    r.artifactAdmission == some (.conditional fx.cheatEnv.consts.size none #[fx.cheatAddress]) &&
    runExit r true == exitConditional && runExit r true true == _root_.Ix.Benchmark.Results.exitUsage &&
    runStatus r true == "conditional")
    s!"the conditional whole run is not reported as conditional on cheat: {repr r.artifactAdmission}"
  let r ← checked (← runPrepared p cfg (.only #[if anon then toString fx.useAddress else "useCheat"]))
  ensure (r.failures.isEmpty && r.userAxioms == #[fx.cheatAddress] && runExit r false == exitConditional &&
    runStatus r false == "conditional")
    "a selected run through a user axiom is not conditional on it"
  let pBad ← checked (← prepareInput fx.badCheatBytes anon (allowUserAxioms := true))
  let r ← checked (← runPrepared pBad cfg (.only (if anon then #[toString fx.useAddress, toString fx.badAddress]
    else #["useCheat", "badCheat"])))
  let bad := r.targets.filter (·.target.address == fx.badAddress)
  ensure (bad.size == 1 && bad.all (fun t => t.outcome == "reject" && !t.reason.startsWith "reader:") &&
    r.failures.size == 1 && r.userAxioms == #[fx.cheatAddress] && runStatus r false == "rejected")
    s!"a rejected user axiom was listed as admitted: {r.userAxioms}, {bad.map (·.reason)}"
  let natDiv := if anon then toString (fx.generated.table.addressOf? .natDiv).get! else "Nat.div"
  let r ← checked (← runPrepared p cfg (.only #[natDiv]))
  ensure (r.failures.isEmpty && r.userAxioms.isEmpty && runExit r false == 0)
    "a selected run that reads no user axiom became conditional"
  let strict ← checked (← runPrepared (← checked (← prepareInput fx.bytes anon)) cfg .all)
  let p ← checked (← prepareInput fx.bytes anon (allowUserAxioms := true))
  let r ← checked (← runPrepared p cfg .all)
  ensure (r.artifactAdmission == some (.logical fx.env.consts.size) && r.hostStatement.isSome &&
    r.hostStatement == strict.hostStatement && r.artifactAdmission == strict.artifactAdmission &&
    runExit r true true == 0) "the flag replaced the certified entry on an artifact without user axioms"
  match ← prepareInput fx.noSorry anon (allowUserAxioms := true) with
  | .error (.artifact message) =>
    ensure (message.contains "leaves sorryAx unbound") s!"wrong refusal: {message}"
  | _ => throw (IO.userError "a binding without sorryAx admitted user axioms")

private def inProcessTierUserAxiomChecks (fx : Fixture) : IO Unit := do
  let cfg : CheckCfg := { silent := true, progressMs := 0, slowMs := 0 }
  let p ← checked (← prepareInput fx.tierCheatBytes true (allowUserAxioms := true))
  let r ← checked (← runPrepared p cfg .all)
  ensure (r.artifactAdmission == some (.conditional fx.tierCheatEnv.consts.size (some 1) #[fx.cheatAddress]))
    s!"the tiered conditional entry did not run: {repr r.artifactAdmission}"
  let strict ← checked (← runPrepared (← checked (← prepareInput fx.tierBytes true)) cfg .all)
  let r ← checked (← runPrepared (← checked (← prepareInput fx.tierBytes true (allowUserAxioms := true))) cfg .all)
  ensure (r.artifactAdmission == some (.tiered fx.tierEnv.consts.size 1) &&
      r.artifactAdmission == strict.artifactAdmission && r.hostStatement.isSome &&
      r.hostStatement == strict.hostStatement)
    s!"the flag replaced the certified tiered entry: {repr r.artifactAdmission} vs {repr strict.artifactAdmission}"
  match ← prepareInput fx.noSorry with
  | .error (.artifact message) =>
    ensure (message.contains "role binding") s!"wrong meta refusal: {message}"
  | _ => throw (IO.userError "a published sorryAx left unbound passed meta preparation")

open LSpec in
public def units : LSpec.Spec :=
  LSpec.beforeAll buildFixture (fun fx => IO.FS.removeDirAll fx.dir) "role artifact consumer fixtures" fun getFx => do
    let vars := #[("IX_KERNEL_CHECK_PROGRESS_MS", some "0"), ("IX_KERNEL_CHECK_SLOW_MS", some "0")]
    it "bound artifact consumers: tier partition and fence checks" do
      tierFenceChecks (← getFx)
    it "bound artifact consumers: in-process whole checks (meta)" do
      inProcessWholeCheck (← getFx) false
    it "bound artifact consumers: in-process whole checks (anon)" do
      inProcessWholeCheck (← getFx) true
    it "bound artifact consumers: unnamed invalid record and ordered checks" do
      let fx ← getFx
      let cfg : CheckCfg := { silent := true, progressMs := 0, slowMs := 0 }
      let bad ← checked (← prepareInput fx.badBytes)
      ensure (match ← runPrepared bad cfg .all with | .error (.artifact _) => true | _ => false)
        "an unnamed invalid record escaped bound whole checking"
      orderedChecks fx.env fx.tierEnv fx.badEnv
    it "bound artifact consumers: in-process user-axiom checks (meta)" do
      inProcessUserAxiomCheck (← getFx) false
    it "bound artifact consumers: in-process user-axiom checks (anon)" do
      inProcessUserAxiomCheck (← getFx) true
    it "bound artifact consumers: in-process tiered user-axiom checks" do
      inProcessTierUserAxiomChecks (← getFx)
    for (label, pickFile, args, code, text) in [
        ("whole logical CLI", (fun (fx : Fixture) => fx.path), #[], 0, "whole artifact: logical entry accepted"),
        ("tier anon CLI", (fun (fx : Fixture) => fx.tierPath), #["--anon"], 0, "tier constants typed only"),
        ("selected consts CLI", (fun (fx : Fixture) => fx.path), #["--consts", "Nat.div"], 0, "selected checking only"),
        ("invalid artifact CLI", (fun (fx : Fixture) => fx.badPath), #[], 3, "artifact")] do
      it s!"bound artifact consumers: ix check-lean {label}" do
        let fx ← getFx
        let out ← IO.Process.output { cmd := fx.ix.toString, args := #["check-lean", (pickFile fx).toString] ++ args, env := vars }
        ensure (out.exitCode == code && (out.stdout ++ out.stderr).contains text)
          s!"bound CLI control failed: {out.exitCode}\n{out.stdout}\n{out.stderr}"
    it "bound artifact consumers: ix check-lean aggregate fail-out" do
      let fx ← getFx
      let failures := fx.dir / "aggregate-failures.txt"
      let out ← IO.Process.output {
        cmd := fx.ix.toString
        args := #["check-lean", fx.badPath.toString, "--fail-out", failures.toString]
        env := vars }
      ensure (out.exitCode == 3 && out.stderr.contains "artifact") "aggregate refusal exit changed"
      let lines := (← IO.FS.readFile failures).splitOn "\n" |>.map (·.trimAscii.toString)
      ensure (lines.any (·.contains "artifact") && lines.all (fun line => line.isEmpty || line.startsWith "#"))
        "aggregate refusal wrote a fabricated declaration selector"
    it "bound artifact consumers: kernel-check-ixe stream vs eager parity" do
      let fx ← getFx
      let neutral := #["CHECK_IXE_ROOTS", "CHECK_IXE_SKIP", "CHECK_IXE_READ_CACHE"].map (·, none)
      let mut previous : Option (Array (String × String × String)) := none
      for mode in ["stream", "eager"] do
        let rowsPath := fx.dir / s!"{mode}.jsonl"
        let result ← IO.Process.output {
          cmd := fx.kernel.toString
          args := #[fx.path.toString, rowsPath.toString, "--load", mode, "--jobs", "2"]
          env := neutral }
        ensure (result.exitCode == 0) s!"bound diagnostic {mode} failed: {result.stdout}\n{result.stderr}"
        let mut rows : Array (String × String × String) := #[]
        for line in (← IO.FS.readFile rowsPath).splitOn "\n" do
          if line.isEmpty then continue
          let row ← IO.ofExcept (Lean.Json.parse line)
          rows := rows.push (← IO.ofExcept (row.getObjValAs? String "address"),
            ← IO.ofExcept (row.getObjValAs? String "outcome"), ← IO.ofExcept (row.getObjValAs? String "reason"))
        ensure (!rows.isEmpty && rows.all (·.2.1 == "accept")) "actual bound proof/operation records were refused"
        for (address, lazy) in fx.env.consts.toList do
          let record ← IO.ofExcept lazy.get
          let owner := toString (Ixon.CheckOrder.owner address record)
          ensure (rows.any (·.1 == owner)) s!"bound diagnostic omitted owner {owner}"
        let sorted := rows.qsort (fun a b => a.1 < b.1)
        if let some earlier := previous then ensure (earlier == sorted) "stream/eager bound diagnostic rows differ"
        previous := some sorted
    for (label, pickFile, args, code, mkTexts) in [
        ("strict meta", (fun (fx : Fixture) => fx.cheatPath), #[], 3, fun (_ : Fixture) => #[]),
        ("strict anon", (fun (fx : Fixture) => fx.cheatPath), #["--anon"], 3, fun (_ : Fixture) => #[]),
        ("conditional meta", (fun (fx : Fixture) => fx.cheatPath), #["--allow-user-axioms"], exitConditional,
          fun (fx : Fixture) => #["whole artifact: CONDITIONAL on 1 user axioms:", s!"[check-lean]   {fx.cheatAddress} cheat", "no host statement"]),
        ("conditional anon", (fun (fx : Fixture) => fx.cheatPath), #["--anon", "--allow-user-axioms"], exitConditional,
          fun (fx : Fixture) => #["whole artifact: CONDITIONAL on 1 user axioms:", s!"[check-lean]   {fx.cheatAddress}"]),
        ("conditional selected", (fun (fx : Fixture) => fx.cheatPath), #["--allow-user-axioms", "--consts", "useCheat"], exitConditional,
          fun (fx : Fixture) => #["selected checking: CONDITIONAL on 1 user axioms:", s!"[check-lean]   {fx.cheatAddress} cheat"]),
        ("conditional tiered", (fun (fx : Fixture) => fx.tierCheatPath), #["--anon", "--allow-user-axioms"], exitConditional,
          fun (_ : Fixture) => #["whole artifact: CONDITIONAL on 1 user axioms:", "conditional logical entry and typing tier"]),
        ("clean artifact with flag", (fun (fx : Fixture) => fx.boundPath), #["--allow-user-axioms"], 0,
          fun (_ : Fixture) => #["whole artifact: logical entry accepted all"]),
        ("no-sorry anon", (fun (fx : Fixture) => fx.noSorryPath), #["--anon", "--allow-user-axioms"], 3,
          fun (_ : Fixture) => #["leaves sorryAx unbound"]),
        ("no-sorry meta", (fun (fx : Fixture) => fx.noSorryPath), #[], 3,
          fun (_ : Fixture) => #["role binding"])] do
      it s!"bound artifact consumers: user-axiom CLI ({label})" do
        let fx ← getFx
        let out ← IO.Process.output { cmd := fx.ix.toString, args := #["check-lean", (pickFile fx).toString] ++ args, env := vars }
        let text := out.stdout ++ out.stderr
        ensure (out.exitCode == code && (mkTexts fx).all (fun t => text.contains t) &&
          (code == 0 || !out.stdout.contains "accepted all"))
          s!"user-axiom CLI control {args} failed: {out.exitCode}\n{out.stdout}\n{out.stderr}"
    it "bound artifact consumers: user-axiom CLI rejects --host-out" do
      let fx ← getFx
      let unused := fx.dir / "conditional.ixhc"
      let out ← IO.Process.output {
        cmd := fx.ix.toString
        args := #["check-lean", fx.cheatPath.toString, "--allow-user-axioms", "--host-out", unused.toString]
        env := vars }
      let text := out.stdout ++ out.stderr
      ensure (out.exitCode == 2 && text.contains "CONDITIONAL on 1 user axioms and issues no host statement" &&
        !out.stdout.contains "accepted all")
        s!"user-axiom CLI --host-out control failed: {out.exitCode}\n{out.stdout}\n{out.stderr}"
      ensure (!(← unused.pathExists)) "a conditional run wrote a host statement"
    for (tag, args) in [("stream", #["--load", "stream"]), ("eager-j2", #["--load", "eager", "--jobs", "2"])] do
      for allow in [true, false] do
        it s!"bound artifact consumers: kernel-check-ixe uncached {tag} allow={allow}" do
          let fx ← getFx
          checkKernelIxeUserAxioms fx args none allow s!"cheat-{tag}-{allow}.jsonl"
    it "bound artifact consumers: kernel-check-ixe read-cache paths" do
      let fx ← getFx
      let cache := fx.dir / "read-cache"
      for (tag, args) in [("j2", #["--jobs", "2"]), ("default", #[]), ("eager", #["--load", "eager"])] do
        for allow in [true, false] do
          checkKernelIxeUserAxioms fx args (some cache) allow s!"cheat-cache-{tag}-{allow}.jsonl"
      ensure (← cache.pathExists) "the read cache was never written"
    it "bound artifact consumers: kernel-check-ixe refuses no-sorry" do
      let fx ← getFx
      let refused ← IO.Process.output {
        cmd := fx.kernel.toString
        args := #[fx.noSorryPath.toString, (fx.dir / "no-sorry.jsonl").toString, "--allow-user-axioms"] }
      ensure (refused.exitCode == 2 && refused.stderr.contains "leaves sorryAx unbound")
        s!"kernel-check-ixe admitted user axioms under a binding without sorryAx\n{refused.stderr}"

end Tests.Ix.RoleArtifactConsumer
