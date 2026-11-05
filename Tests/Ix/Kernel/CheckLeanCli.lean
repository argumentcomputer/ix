import LSpec
import Ix.Cli.CheckLeanCmd
import Tests.Ix.Kernel.ReaderRoundtrip
import Tests.Ix.Kernel.Pins

namespace Tests.Ix.Kernel.CheckLeanCli

open LSpec
open _root_.Ix.Cli.CheckLeanCmd

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)
private def checked (result : Except DriverError α) : IO α :=
  IO.ofExcept (result.mapError DriverError.message)
private def fixtureName (s : String) : _root_.Ix.Name :=
  _root_.Ix.Name.fromLeanName (Tests.Ix.Kernel.ReaderRoundtrip.defs s)
private def named (env : Ixon.Env) (s : String) : IO Ixon.Named :=
  match env.named[fixtureName s]? with
  | some n => pure n | none => throw (IO.userError s!"fixture name missing: {s}")
private def addNamed (env : Ixon.Env) (s : String) (entry : Ixon.Named) : Ixon.Env :=
  let n := _root_.Ix.Name.mkStr _root_.Ix.Name.mkAnon s
  { env.registerName n entry with names := Ixon.RawEnv.addNameComponents env.names n }

private def check : IO Nat := do
  let (_, inp) ← Tests.Ix.Kernel.ReaderRoundtrip.input
  let twice ← named inp.ixon "twice"
  let ax ← named inp.ixon "fidelityAxiom"
  let mut env := inp.ixon
  let aliases := (Array.range 5).map fun i => s!"CliAlias{i}"
  for n in aliases do env := addNamed env n twice
  let original ← IO.ofExcept ((env.consts[twice.addr]?).get!.get)
  let .defn definition := original.info | throw (IO.userError "twice is not a definition")
  let bad : Ixon.Constant := { original with info := .defn { definition with value := definition.typ } }
  let badAddress := Address.blake3 (Ixon.serConstant bad)
  env := { env with consts := env.consts.insert badAddress (Ixon.LazyConstant.ofConstant bad) }
  env := addNamed env "RejectedSubject" { twice with addr := badAddress }
  let badAliases := (Array.range 5).map fun i => s!"CliBadAlias{i}"
  for n in badAliases do env := addNamed env n { twice with addr := badAddress }
  let blocked : Ixon.Constant := { original with
    refs := original.refs.push ax.addr
    info := .defn { definition with value := .ref original.refs.size.toUInt64 #[] } }
  let blockedAddress := Address.blake3 (Ixon.serConstant blocked)
  env := { env with consts := env.consts.insert blockedAddress (Ixon.LazyConstant.ofConstant blocked) }
  env := addNamed env "BlockedSubject" { twice with addr := blockedAddress }
  let bytes ← IO.ofExcept (Ixon.serEnv env)
  let cfg : CheckCfg := { workers := 3, silent := true, progressMs := 0, slowMs := 0 }
  let prepared ← checked (← prepareInput bytes)
  let anonPrepared ← checked (← prepareInput bytes true)
  -- Repeated prepared runs use fresh observations/checker state, and never
  -- enter the permanent-marking pool path even when several workers were requested.
  for _ in [:3] do
    let r ← checked (← runPrepared prepared cfg (.only aliases))
    ensure (r.targetsCovered == 5 && r.passed == 5 && r.targets.map (·.target.address) == Array.replicate 5 twice.addr)
      "prepared aliases lost exact coverage"
    ensure (r.execution == .serialTier (some 3) && r.execution.workers == 1) "effective serial execution hidden"
    let a ← checked (← runPrepared anonPrepared cfg (.only #[toString twice.addr]))
    ensure (a.passed == 1 && a.targetsCovered == 1) "prepared anonymous target failed"
  let label (s : String) := toString (fixtureName s)
  for (subject, expected) in [(label "fidelityAxiom", "decline"), ("RejectedSubject", "reject"),
      ("BlockedSubject", "blocked"), (label "spin._unsafe_rec", "typed")] do
    let r ← checked (← runPrepared prepared cfg (.only #[subject]))
    ensure (r.targets.size == 1 && r.targets.all (·.outcome == expected))
      s!"{subject}: expected {expected}, got {r.targets.map (·.outcome)}"
  -- Keep the actual pin adapter's fresh-run/timing path executable on a small
  -- fixture; the historical corpus pin labels and budgets stay unchanged.
  let pin ← Tests.Tc.Pins.checkPin prepared { label := "CliAlias0", budgetMs := 60000 }
  ensure ((← lspecIO (.ofList [("pin-adapter", [pin])]) []) == 0) "pin adapter failed"
  let window := prepared.parts.env.consts[twice.addr]!
  let tampered := bytes.set! window.off (bytes[window.off]! ^^^ 1)
  for anon in [false, true] do
    match ← prepareInput tampered anon with
    | .error (.infrastructure e) => ensure (e.contains "hash mismatch") "wrong authentication failure"
    | _ => throw (IO.userError "tampered bytes reached a checker")
  let ix ← IO.FS.realPath ".lake/build/bin/ix"
  let dir ← IO.FS.createTempDir
  try
    let path := dir / "subjects.ixe"
    let corrupt := dir / "corrupt.ixe"
    let failures := dir / "failures.txt"
    let empty := dir / "empty.txt"
    IO.FS.writeBinFile path bytes
    IO.FS.writeBinFile corrupt tampered
    IO.FS.writeFile empty "# only comments\n"
    let neutral : Array (String × Option String) :=
      #[("IX_PROGRESS_MS", none), ("IX_KERNEL_CHECK_PROGRESS_MS", some "0"), ("IX_KERNEL_CHECK_SLOW_MS", some "0")]
    let calls ← IO.mkRef 0
    let call := fun (args : Array String) (vars : Array (String × Option String)) => do
      calls.modify (· + 1)
      IO.Process.output { cmd := ix.toString, args := #["check-lean", path.toString] ++ args, env := neutral ++ vars }
    let expect := fun (out : IO.Process.Output) (code : UInt32) =>
      ensure (out.exitCode == code) s!"expected exit {code}, got {out.exitCode}\n{out.stdout}\n{out.stderr}"
    let row := fun (out : IO.Process.Output) =>
      ((out.stdout.splitOn "\n").find? (·.startsWith "##check-lean## ")).map (·.splitOn " ")
    let checkRow := fun out passed failed covered => do
      let some fields := row out | throw (IO.userError s!"missing machine row: {out.stdout}")
      ensure (fields.length == 5 && fields[2]? == some (toString passed) &&
        fields[3]? == some (toString failed) && fields[4]? == some (toString covered)) s!"machine row changed: {fields}"
    let ok ← call #["--consts", String.intercalate "," (aliases.toList ++ [label "Color"]), "--max", "1", "--workers", "3", "--verbose"] #[]
    expect ok 0
    checkRow ok (5 : Nat) (0 : Nat) (5 : Nat)
    ensure (ok.stdout.contains "meta mode" && ok.stderr.contains "workers requested 3, effective 1") "mode/execution report changed"
    let typed ← call #["--consts", label "spin._unsafe_rec"] #[]
    expect typed 0
    checkRow typed (1 : Nat) (0 : Nat) (1 : Nat)
    ensure (typed.stdout.contains "1 typed only") "typed was hidden as logical acceptance"
    for (subject, verdict) in [(label "fidelityAxiom", "decline"), ("RejectedSubject", "reject"), ("BlockedSubject", "blocked")] do
      let out ← call #["--consts", subject, "--fail-out", failures.toString] #[]
      expect out 3
      checkRow out (0 : Nat) (1 : Nat) (1 : Nat)
      let text ← IO.FS.readFile failures
      ensure (text.contains verdict && _root_.Ix.Cli.ConstsFile.parseLines text == #[subject]) "named fail-out did not roundtrip"
    let aliasFailures ← call #["--consts", String.intercalate "," badAliases.toList, "--fail-out", failures.toString] #[]
    expect aliasFailures 3
    checkRow aliasFailures (0 : Nat) (5 : Nat) (5 : Nat)
    ensure ((← _root_.Ix.Cli.ConstsFile.read failures.toString) == badAliases) "failing alias stream lost order or coverage"
    let failed ← call #["--anon", "--consts", s!"#{ax.addr}", "--fail-out", failures.toString] #[]
    expect failed 3
    ensure (failed.stdout.contains "anon mode" && (← _root_.Ix.Cli.ConstsFile.read failures.toString) == #[toString ax.addr])
      "anonymous fail-out was swallowed as a comment"
    let replay ← call #["--anon", "--consts-file", failures.toString] #[]
    expect replay 3
    checkRow replay (0 : Nat) (1 : Nat) (1 : Nat)
    for args in [#["--consts", "missing"], #["--consts", ""], #["--consts-file", empty.toString],
        #["--max", "0"], #["--workers", "0"]] do
      expect (← call args #[]) 2
    for name in ["IX_KERNEL_CHECK_PROGRESS_MS", "IX_KERNEL_CHECK_SLOW_MS"] do
      let out ← call #["--consts", "CliAlias0"] #[(name, some "bad")]
      expect out 2
      ensure (out.stderr.contains name) s!"malformed setting {name} was silently ignored"
    for mode in [#[], #["--anon"]] do
      calls.modify (· + 1)
      let args := #["check-lean", corrupt.toString] ++ mode
      let out ← IO.Process.output { cmd := ix.toString, args, env := neutral }
      expect out 1
      ensure (out.stderr.contains "hash mismatch") "CLI skipped byte authentication"
    -- A whole-artifact run of an artifact with no role binding: the per-declaration
    -- checks run, the whole-artifact admission cannot, and the run says so. With a
    -- failing declaration the refusal (3) decides the exit; with none, the partial
    -- check (4) does.
    let whole ← call #[] #[]
    expect whole 3
    ensure (whole.stdout.contains "partial check: the artifact carries no role binding")
      s!"unbound whole run hid its partial coverage\n{whole.stdout}"
    let wholeReport ← checked (← runPrepared prepared cfg .all)
    let failing : Std.HashSet String := wholeReport.failures.foldl (fun s (l, _) => s.insert l) {}
    let mut clean := env
    for (n, _) in env.named.toList do
      if failing.contains (toString n) then clean := { clean with named := clean.named.erase n }
    let cleanPath := dir / "clean.ixe"
    IO.FS.writeBinFile cleanPath (← IO.ofExcept (Ixon.serEnv clean))
    calls.modify (· + 1)
    let partialRun ← IO.Process.output { cmd := ix.toString, args := #["check-lean", cleanPath.toString], env := neutral }
    expect partialRun exitPartial
    ensure (partialRun.stdout.contains "partial check: the artifact carries no role binding")
      "partial whole run did not say so"
    ensure (runExit { wholeReport with targets := #[] } true == exitPartial &&
      runExit { wholeReport with targets := #[] } false == 0 &&
      (coverageNotice { wholeReport with targets := #[] } false).any (·.contains "selected checking only"))
      "partial-check exit or notice changed"
    -- `--json`, `--json-name` and `--per-const`. A whole run writes one results row,
    -- keyed by --json-name, and the per-record CSV, and exits as the same run
    -- without --json does: 3 with a failing subject, `exitPartial` for the clean
    -- unbound artifact.
    let results := dir / "results.json"
    let csv := dir / "perconst.csv"
    let row := fun (key : String) => do
      let rows ← _root_.Ix.Benchmark.Results.readRows results.toString
      return (rows.getObjVal? key).toOption
    let status := fun (key : String) => do
      return (← row key).bind fun r => (r.getObjValAs? String "status").toOption
    let constants := fun (key : String) => do
      return (← row key).bind fun r => (r.getObjValAs? Nat "constants").toOption
    let reset := fun () => do
      if ← results.pathExists then IO.FS.removeFile results
      if ← csv.pathExists then IO.FS.removeFile csv
    let csvRows := fun () => do
      let lines := ((← IO.FS.readFile csv).splitOn "\n").filter (!·.isEmpty)
      ensure (lines.head? == some "name,addr,consts,nanos,heartbeats,subst,whnf,def_eq,nat_arith,intern,cost")
        s!"per-const CSV header changed: {lines.head?}"
      return lines.length - 1
    reset ()
    let jsonWhole ← call #["--json", results.toString, "--json-name", "fixture", "--per-const", csv.toString] #[]
    expect jsonWhole 3
    ensure ((← status "fixture") == some "rejected" && (← row "env").isNone &&
      (← constants "fixture") == some wholeReport.records)
      s!"whole --json row lost its key, status or record count: {← IO.FS.readFile results}"
    ensure ((← csvRows ()) == wholeReport.rows.size) "whole --per-const CSV is not one row per record"
    reset ()
    calls.modify (· + 1)
    let partialJson ← IO.Process.output {
      cmd := ix.toString, args := #["check-lean", cleanPath.toString, "--json", results.toString], env := neutral }
    expect partialJson exitPartial
    ensure ((← status "env") == some "ok") "unbound whole --json row missing"
    -- One full-closure row per selected name, keyed after `<json-name>/`, and one
    -- CSV over every per-name run; --json-name and --per-const are honoured.
    reset ()
    let names := dir / "names.txt"
    IO.FS.writeFile names "CliAlias0\nRejectedSubject\n"
    let perName ← call #["--consts-file", names.toString, "--json", results.toString, "--json-name", "fx",
      "--per-const", csv.toString] #[]
    expect perName 3
    ensure ((← status "fx/CliAlias0") == some "ok" && (← status "fx/RejectedSubject") == some "rejected" &&
      (← row "CliAlias0").isNone && (← row "fx").isNone && ((← constants "fx/CliAlias0").getD 0) > 0)
      s!"per-name rows lost their keys or statuses: {← IO.FS.readFile results}"
    ensure ((← csvRows ()) > 0) "per-name --per-const CSV is empty"
    ensure (perName.stdout.contains "1/2 subjects passed") s!"per-name summary changed\n{perName.stdout}"
    -- An anonymous run resolves Lean names too; a name that resolves to nothing is
    -- reported and the others still run, with the usage exit.
    reset ()
    let anonRows ← call #["--anon", "--consts", "CliAlias0,missing", "--json", results.toString] #[]
    expect anonRows 2
    ensure ((← status "CliAlias0") == some "ok" && (← row "missing").isNone &&
      anonRows.stderr.contains "missing: unresolved")
      s!"unresolved name aborted the per-name rows\n{anonRows.stderr}"
    expect (← call #["--consts", "CliAlias0", "--json", results.toString, "--fail-out", failures.toString] #[]) 2
    let count ← calls.get
    IO.println s!"check-lean CLI: {count} process controls; modes, exact aliases/cap, all five outcomes, fail-out, usage/infra exits, --json/--json-name/--per-const rows passed"
    return count
  finally
    IO.FS.removeDirAll dir

def suite : List TestSeq := [
  .individualIO "authenticated IxC CLI and repeatable prepared callers" none (do
    let n ← check
    return (true, n, 0, none)) .done]

end Tests.Ix.Kernel.CheckLeanCli
