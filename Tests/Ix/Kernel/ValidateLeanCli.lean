import LSpec
import Ix.Cli.ValidateLeanCmd
import Tests.Ix.Kernel.ReaderRoundtrip

namespace Tests.Ix.Kernel.ValidateLeanCli

open LSpec _root_.Ix.Cli.ValidateLeanCmd
open Tests.Ix.Kernel.EgressFidelity

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def phase (report : Lean.Json) (index : Nat) : IO (String × String × String) := do
  let rows ← IO.ofExcept (report.getObjValAs? (Array Lean.Json) "phases")
  ensure (rows.size == 5) "validate-lean omitted a phase row"
  let some row := rows[index - 1]? | throw (IO.userError "phase index missing")
  return (← IO.ofExcept (row.getObjValAs? String "name"),
    ← IO.ofExcept (row.getObjValAs? String "result"),
    ← IO.ofExcept (row.getObjValAs? String "detail"))

private def check : IO Nat := do
  let (_, inp) ← Tests.Ix.Kernel.ReaderRoundtrip.input
  let baseline := projections inp.store inp.ixon.blobs.toList
  ensure (baseline.blocks > 0 && baseline.compiled > 0 && baseline.matched == baseline.compiled &&
    baseline.problems.isEmpty && baseline.orderProblems.isEmpty && !baseline.motiveOrdered.isEmpty)
    "positive fixture has no complete projection/order coverage"
  ensure (Ixon.Env.envelopeVersion inp.ixon == 5 && !inp.ixon.originals.isEmpty)
    "positive fixture must exercise real compiled v5 originals"
  let bytes5 ← IO.ofExcept (Ixon.serEnv inp.ixon)
  let base := { inp.ixon with named := {}, originals := {}, originalHintOverrides := {} }
  let bytes4 ← IO.ofExcept (Ixon.serEnv base)
  ensure (bytes4.data[0]? == some 0xE4 && bytes5.data[0]? == some 0xE5) "envelope fixture versions changed"
  let parts4 ← IO.ofExcept (Ixon.deEnvVerifiedLazy bytes4)
  let parts5 ← IO.ofExcept (Ixon.deEnvVerifiedLazy bytes5)
  let some (projection, pc) := inp.store.toArray.find? (fun (_, c) => c.info matches .cPrj _)
    | throw (IO.userError "fixture has no constructor projection")
  let owner := Ixon.CheckOrder.owner projection pc
  let missing ← IO.ofExcept (Ixon.serEnv { base with
    consts := base.consts.erase projection, anonHints := base.anonHints.erase projection })
  let orphan ← IO.ofExcept (Ixon.serEnv { base with
    consts := base.consts.erase owner, anonHints := base.anonHints.erase owner })
  let block := baseline.motiveOrdered[0]!
  let bc := inp.store[block]!
  let .muts members := bc.info | throw (IO.userError "motive-order fixture is not a block")
  let swapped := { bc with info := .muts (members.swapIfInBounds 0 1) }
  let swappedAddress := Address.blake3 (Ixon.serConstant swapped)
  ensure (!base.consts.contains swappedAddress) "swapped block already exists"
  let written ← IO.ofExcept <| (Ixon.Authenticated.reconstruct maxProjections [(swappedAddress, swapped)]).mapError reprStr
  let wrongOrder := written.foldl (fun e (a, c) => e.storeConst a c) base
  let wrongBytes ← IO.ofExcept (Ixon.serEnv wrongOrder)
  let wrongReport ← IO.ofExcept <| projectionsAccess
    (_root_.Ix.KernelFidelity.RecordAccess.ofParts (← IO.ofExcept (Ixon.deEnvVerifiedLazy wrongBytes)))
  ensure (wrongReport.problems.isEmpty && wrongReport.matched == wrongReport.compiled &&
    !wrongReport.orderProblems.isEmpty) "order control must fail only the order predicate"
  let constWindow := parts4.env.consts[projection]!
  let corrupt4 := bytes4.set! constWindow.off (bytes4[constWindow.off]! ^^^ 1)
  let (_, originalWindow) := parts5.env.originals.toArray[0]!
  let corrupt5 := bytes5.set! originalWindow.off (bytes5[originalWindow.off]! ^^^ 1)
  ensure ((projectionResult { baseline with matched := baseline.compiled - 1 } 0).isFailure)
    "CLI dropped the matched/compiled coverage check"
  ensure ((projectionResult { baseline with problems := #["planted"] } 0).isFailure)
    "CLI dropped explicit fidelity problems"
  ensure ((projectionResult wrongReport 0).isFailure) "CLI dropped order refusals"
  let ix ← IO.FS.realPath ".lake/build/bin/ix"
  let dir ← IO.FS.createTempDir
  try
    let neutral : Array (String × Option String) :=
      #["IX_ANON_CAP", "IX_ANON_STAGE", "IX_ANON_SEQ", "IX_ANON_HOLD", "IX_META_EAGER",
        "IX_SHARING_LIMITS", "LD_LIBRARY_PATH"].map (·, none) ++ #[("IX_SKIP_PHASES", some "5")]
    let calls ← IO.mkRef 0
    let call := fun (label : String) (bytes : ByteArray) (code : UInt32) (failures : Nat)
        (vars : Array (String × Option String)) => do
      calls.modify (· + 1)
      let path := dir / s!"{label}.ixe"
      let reportPath := dir / s!"{label}.json"
      IO.FS.writeBinFile path bytes
      let out ← IO.Process.output {
        cmd := ix.toString, args := #["validate-lean", "--ixe", path.toString, "--report", reportPath.toString],
        env := neutral ++ vars }
      IO.FS.writeFile (dir / s!"{label}.log") (out.stdout ++ out.stderr)
      ensure (out.exitCode == code) s!"{label}: expected exit {code}, got {out.exitCode}; logs in {dir}"
      let report ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile reportPath))
      ensure ((← IO.ofExcept (report.getObjValAs? Nat "schemaVersion")) == 1 &&
        (← IO.ofExcept (report.getObjValAs? String "tool")) == "validate-lean" &&
        (← IO.ofExcept (report.getObjValAs? String "input")) == path.toString &&
        (← IO.ofExcept (report.getObjVal? "ns")) == .null) s!"{label}: report schema changed"
      for key in ["ixVersion", "leanToolchain"] do
        ensure (!(← IO.ofExcept (report.getObjValAs? String key)).isEmpty) s!"{label}: missing {key}"
      ensure ((← IO.ofExcept (report.getObjValAs? Nat "totalFailures")) == failures &&
        (← IO.ofExcept (report.getObjValAs? Bool "passed")) == (failures == 0)) s!"{label}: verdict changed"
      for i in [1, 4] do
        ensure ((← phase report i).2.1 == "skip") s!"{label}: source-only phase ran"
      for i in [1:6] do
        let (name, _, detail) ← phase report i
        ensure (name.startsWith s!"{i}." && !detail.isEmpty) s!"{label}: phase schema changed"
      return report
    for (label, bytes) in [("v4", bytes4), ("v5", bytes5)] do
      let report ← call label bytes 0 0 #[]
      ensure ((← phase report 2).2.1 == "pass") s!"{label}: serde did not pass"
      let (name, verdict, detail) ← phase report 3
      ensure (name == "3. Projection/block-order fidelity" && verdict == "pass" &&
        detail.startsWith baseline.summary) s!"{label}: projection report lost a field or changed its scope"
      ensure ((← phase report 5).2.1 == "skip") "phase-5 skip was lost"
    for (label, bytes, needle) in [("missing", missing, "not a compiler record"),
        ("orphan", orphan, "not written by its block"), ("order", wrongBytes, "blocks refused")] do
      let report ← call label bytes 1 1 #[]
      ensure ((← phase report 2).2.1 == "pass") s!"{label}: failed before fidelity"
      let (_, verdict, detail) ← phase report 3
      ensure (verdict == "fail" && detail.contains needle) s!"{label}: fidelity failure was hidden"
    for (label, bytes) in [("corrupt-v4", corrupt4), ("corrupt-v5-original", corrupt5)] do
      let report ← call label bytes 1 1 #[]
      let (_, verdict, detail) ← phase report 2
      ensure (verdict == "fail" && detail.contains "hash mismatch" &&
        (← phase report 3).2.1 == "skip" && (← phase report 5).2.1 == "skip")
        s!"{label}: authentication failure did not gate downstream phases"
    for key in ["IX_ANON_CAP", "IX_ANON_STAGE", "IX_ANON_SEQ", "IX_ANON_HOLD"] do
      let report ← call key bytes4 1 1 #[(key, some "0")]
      let (_, verdict, detail) ← phase report 3
      ensure (verdict == "fail" && detail.contains key && detail.contains "retired")
        s!"{key}: retired diagnostic was silently ignored"
    let skipped ← call "skipped" bytes4 0 0
      #[("IX_ANON_CAP", some "1"), ("IX_SKIP_PHASES", some "3,5")]
    ensure ((← phase skipped 3).2.1 == "skip") "explicit phase-3 skip did not win over retired flags"
    let decompiled ← call "v5-decompile" bytes5 0 0 #[("IX_SKIP_PHASES", none)]
    ensure ((← phase decompiled 3).2.1 == "pass" && (← phase decompiled 5).2.1 == "pass" &&
      (← phase decompiled 5).2.2.contains "oracle-free") "kernel-free phase 5 changed"
    let n ← calls.get
    ensure (n == 13) s!"expected 13 CLI controls, ran {n}"
    IO.println s!"validate-lean fidelity CLI: {n} processes, {baseline.blocks} blocks, \
      {baseline.compiled} projections, v4/v5/authentication/refusal/report controls"
    IO.FS.removeDirAll dir
    return n
  catch e =>
    IO.eprintln s!"validate-lean CLI failure artifacts retained in {dir}"
    throw e

def suite : List TestSeq := [
  .individualIO "validate-lean uses checked lazy projection/order fidelity" none (do
    let n ← check
    return (true, n, 0, none)) .done]

end Tests.Ix.Kernel.ValidateLeanCli
