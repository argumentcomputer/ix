import LSpec
import Ix.Cli.ValidateLeanCmd
import Tests.Ix.Kernel.ReaderRoundtrip

namespace Tests.Ix.Kernel.ValidateReaderCli

open LSpec _root_.Ix.Cli.ValidateLeanCmd
open Tests.Ix.Kernel.ReaderFidelity Tests.Ix.Kernel.ReaderRoundtrip

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def rowDetail (result : PhaseResult) (failure : Bool) : IO String := do
  let detail ← match result, failure with
    | .passed d, false | .failed d, true => pure d
    | _, _ => throw (IO.userError s!"wrong phase verdict: {result.render}")
  let rows ← IO.ofExcept (phaseRows #[ ("4. Source/reader fidelity", result) ]).getArr?
  ensure (rows.size == 1) "phase row disappeared"
  let row := rows[0]!
  ensure ((← IO.ofExcept (row.getObjValAs? String "name")) == "4. Source/reader fidelity" &&
    (← IO.ofExcept (row.getObjValAs? String "result")) == (if failure then "fail" else "pass") &&
    (← IO.ofExcept (row.getObjValAs? String "detail")) == detail) "failed/successful report row changed"
  return detail

private def phase (report : Lean.Json) (index : Nat) : IO (String × String × String) := do
  let rows ← IO.ofExcept (report.getObjValAs? (Array Lean.Json) "phases")
  ensure (rows.size == 5) "CLI omitted a phase"
  let row := rows[index - 1]!
  return (← IO.ofExcept (row.getObjValAs? String "name"),
    ← IO.ofExcept (row.getObjValAs? String "result"),
    ← IO.ofExcept (row.getObjValAs? String "detail"))

/-- Normalize measured durations only, retaining labels, counts and order. -/
private def stable (detail : String) : IO String := do
  let mut lines := #[]
  let mut slow := false
  for line in detail.splitOn "\n" do
    let mut line := line
    if line.startsWith "records read:" then
      let [counts, times] := line.splitOn "; read " | throw (IO.userError "missing reader timing")
      let [read, compared] := times.splitOn " ms, compared " | throw (IO.userError "missing comparison timing")
      let [comparison, ""] := compared.splitOn " ms" | throw (IO.userError "bad comparison timing")
      ensure (read.toNat?.isSome && comparison.toNat?.isSome) "non-numeric timing"
      line := counts ++ "; read 0 ms, compared 0 ms"
    else if line.startsWith "(" && line.endsWith "ms)" then
      ensure ((line.drop 1 |>.dropEnd 3 |>.toString).toNat?.isSome) "bad phase duration"
      line := "(0ms)"
    else if slow && line.startsWith "  " && line.endsWith " ms" then
      let words := line.splitOn " "
      ensure ((words[words.length - 2]?).bind String.toNat?).isSome "bad slow-record duration"
      line := String.intercalate " " (words.take (words.length - 2)) ++ " 0 ms"
    if line.startsWith "slow comparisons:" then slow := true
    if line.startsWith "unexplained:" then slow := false
    lines := lines.push line
  return String.intercalate "\n" lines.toList

private def check : IO Nat := do
  let (lean, inp) ← input
  let bytes ← IO.ofExcept (Ixon.serEnv inp.ixon)
  let parts ← IO.ofExcept (Ixon.deEnvVerifiedLazy bytes)
  let access ← IO.ofExcept (InputAccess.ofParts lean parts)
  let report ← runAccess access (keep := fun _ => true)
  ensure (report.constants == access.names.size && report.constants > 0 && report.readFailures > 0 &&
    report.count "declined: partial definition" > 0 && report.count "declined: unsafe definition" > 0)
    "real fixture lacks complete source coverage or expected declines"
  let some (_, pair) := report.pairs.toArray[0]? | throw (IO.userError "no compared pair")
  for (r, expected, failed) in [
      (report, access.names.size, false),
      ({ report with problems := #["planted problem"] }, access.names.size, true),
      ({ report with unexplained := #[(defs "twice", "planted difference")] }, access.names.size, true),
      ({ report with unmatched := #[pair.1.name] }, access.names.size, true),
      (report, access.names.size + 1, true)] do
    let detail ← rowDetail (readerResult r expected 0) failed
    ensure (detail.startsWith r.summary && detail.contains s!"source coverage: {r.constants}/{expected}")
      "phase predicate discarded summary fields or coverage"
  let twice := (access.address (_root_.Ix.Name.fromLeanName (defs "twice"))).get!
  let absent := { access with records := { access.records with
    get := fun a => if a == twice then .error "planted missing body" else access.records.get a } }
  let brokenMetadata := { access with metadata := fun _ => .error "planted metadata failure" }
  let faults : List (IO InputAccess × String) := [
    (throw (IO.userError "planted IO failure"), "planted IO failure"),
    (IO.ofExcept (.error "planted construction failure"), "planted construction failure"),
    (pure absent, "planted missing body"), (pure brokenMetadata, "planted metadata failure")]
  for (action, message) in faults do
    let detail ← rowDetail (← readerPhase action) true
    ensure (detail.contains message) "access/IO failure did not reach the phase report"
  let _ ← rowDetail (← readerPhase (pure access)) false
  let ix ← IO.FS.realPath ".lake/build/bin/ix"
  let file ← IO.FS.realPath "Tests/Ix/Kernel/ReaderFidelityDefs.lean"
  let dir ← IO.FS.createTempDir
  IO.println s!"validate-lean source CLI artifacts: {dir}"
  let neutral : Array (String × Option String) :=
    #["IX_ANON_CAP", "IX_ANON_STAGE", "IX_ANON_SEQ", "IX_ANON_HOLD", "IX_META_EAGER",
      "IX_SHARING_LIMITS", "LD_LIBRARY_PATH"].map (·, none) ++ #[("IX_SKIP_PHASES", some "5")]
  let mut details := #[]
  for eager in [false, true] do
    let label := if eager then "eager" else "lazy"
    let path := dir / s!"{label}.json"
    let out ← IO.Process.output {
      cmd := ix.toString, args := #["validate-lean", file.toString, "--ns", toString defsModule,
        "--workers", "1", "--report", path.toString],
      env := neutral ++ (if eager then #[("IX_META_EAGER", some "1")] else #[]) }
    IO.FS.writeFile (dir / s!"{label}.log") (out.stdout ++ out.stderr)
    ensure (out.exitCode == 0) s!"{label} source CLI failed; artifacts: {dir}"
    let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile path))
    ensure ((← IO.ofExcept (json.getObjValAs? Nat "schemaVersion")) == 1 &&
      (← IO.ofExcept (json.getObjValAs? String "tool")) == "validate-lean" &&
      (← IO.ofExcept (json.getObjValAs? String "input")) == file.toString &&
      (← IO.ofExcept (json.getObjValAs? String "ns")) == toString defsModule &&
      (← IO.ofExcept (json.getObjValAs? Nat "totalFailures")) == 0 &&
      (← IO.ofExcept (json.getObjValAs? Bool "passed"))) "source CLI report schema/verdict changed"
    for key in ["ixVersion", "leanToolchain"] do
      ensure (!(← IO.ofExcept (json.getObjValAs? String key)).isEmpty) s!"missing {key}"
    for i in [1:5] do ensure ((← phase json i).2.1 == "pass") s!"phase {i} failed"
    ensure ((← phase json 5).2.1 == "skip") "phase-5 skip changed"
    let (name, _, detail) ← phase json 4
    ensure (name == "4. Source/reader fidelity" && detail.contains "declined: partial definition" &&
      detail.contains "declined: unsafe definition" && detail.contains "source coverage:") "fidelity/decline scope hidden"
    let some coverage := (detail.splitOn "\n").find? (·.startsWith "source coverage:")
      | throw (IO.userError "missing coverage")
    let [a, b] := ((coverage.splitOn " ")[2]!).splitOn "/" | throw (IO.userError "bad coverage")
    ensure (a.toNat?.any (· > 0) && a == b) "incomplete source coverage passed CLI"
    ensure (out.stdout.contains (if eager then "eager diagnostic" else "source/reader fidelity (lazy)"))
      "CLI did not select the requested access mode"
    details := details.push (← stable detail)
  ensure (details.size == 2 && details[0]! == details[1]!) "eager diagnostic changed the full report"
  IO.println s!"validate-lean source fidelity: 2 actual lazy/eager CLI processes; 10 phase/JSON controls; \
    {report.constants} direct source comparisons and visible expected declines"
  return 12

def suite : List TestSeq := [
  .individualIO "validate-lean source fidelity keeps coverage, declines, failures and lazy/eager reports" none (do
    let n ← check
    return (true, n, 0, none)) .done]

end Tests.Ix.Kernel.ValidateReaderCli
