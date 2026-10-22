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
      #["IX_TC_DEBUG_CONST", "IX_TC_STEP_TRACE", "IX_TC_STATS", "IX_TC_NO_ACCEL", "IX_MAX_REC_FUEL",
        "IX_KERNEL_CHECK_ACTIVE_SLOW_MS", "IX_PROGRESS_MS"].map (·, none) ++
        #[("IX_KERNEL_CHECK_PROGRESS_MS", some "0"), ("IX_KERNEL_CHECK_SLOW_MS", some "0")]
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
        #["--max", "0"], #["--workers", "0"], #["--no-verify"], #["--clear-every", "1"]] do
      expect (← call args #[]) 2
    for (name, value) in [("IX_TC_DEBUG_CONST", "x"), ("IX_TC_STEP_TRACE", "1"), ("IX_TC_STATS", "1"),
        ("IX_TC_NO_ACCEL", "1"), ("IX_MAX_REC_FUEL", "0"), ("IX_KERNEL_CHECK_ACTIVE_SLOW_MS", "1"),
        ("IX_TC_STATS", "bad"), ("IX_KERNEL_CHECK_PROGRESS_MS", "bad")] do
      let out ← call #["--consts", "CliAlias0"] #[(name, some value)]
      expect out 2
      ensure (out.stderr.contains name) s!"unsupported setting {name} was silently ignored"
    expect (← call #["--consts", "CliAlias0", "--clear-every", "0"]
      #[("IX_TC_STEP_TRACE", some "0"), ("IX_TC_STATS", some "0"), ("IX_TC_NO_ACCEL", some "0"),
        ("IX_KERNEL_CHECK_ACTIVE_SLOW_MS", some "0")]) 0
    for mode in [#[], #["--anon"]] do
      calls.modify (· + 1)
      let args := #["check-lean", corrupt.toString] ++ mode
      let out ← IO.Process.output { cmd := ix.toString, args, env := neutral }
      expect out 1
      ensure (out.stderr.contains "hash mismatch") "CLI skipped byte authentication"
    let count ← calls.get
    IO.println s!"check-lean CLI: {count} process controls; modes, exact aliases/cap, all five outcomes, fail-out, usage/infra exits and diagnostic flags passed"
    return count
  finally
    IO.FS.removeDirAll dir

def suite : List TestSeq := [
  .individualIO "authenticated IxC CLI and repeatable prepared callers" none (do
    let n ← check
    return (true, n, 0, none)) .done]

end Tests.Ix.Kernel.CheckLeanCli
