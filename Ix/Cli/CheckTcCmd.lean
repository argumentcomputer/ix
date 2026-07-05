/-
  `ix check-tc <path.ixe>`: typecheck a serialized `.ixe` environment
  through the pure-Lean `Ix.Tc` kernel (anon mode).

  The reference-kernel counterpart of `ix check-rs --anon`: every
  kernel-checkable address (every constant except Muts blocks and
  projections — projections are covered by their parent block) is
  checked, sequentially, with lazy on-demand ingress and per-constant
  blake3 integrity verification. Correctness-first: expect minutes at
  Init scale where the Rust kernel takes seconds.

  Flags:
  - `--fail-out <path>`: stream failing addresses (one `#<hex> <err>`
    line each) for bisect loops.
  - `--max N`: stop after N work items (smoke runs).
  - `--clear-every N`: clear reduction-memo caches every N work items
    (0 disables; default 50).
  - `--no-verify`: skip the blake3 integrity check at constant
    materialization (soundness-critical; only for timing comparisons).
  - `--verbose`: log every work item as it is checked.
-/
module
public import Cli
public import Ix.Common
public import Ix.Tc

public section

namespace Ix.Cli.CheckTcCmd

open Ix.Tc

def runCheckTcCmd (p : Cli.Parsed) : IO UInt32 := do
  let some pathArg := p.positionalArg? "path"
    | p.printError "error: must specify <path> to a .ixe file"
      return 1
  let envPath := pathArg.as! String
  let verbose := p.flag? "verbose" |>.isSome
  let verify := (p.flag? "no-verify").isNone
  let clearEvery := ((p.flag? "clear-every").map (·.as! Nat)).getD 50
  let max? := (p.flag? "max").map (·.as! Nat)
  let failOutPath := ((p.flag? "fail-out").map (·.as! String)).getD ""

  IO.println s!"Running Ix.Tc kernel check (anon mode) on {envPath}"
  let bytes ← IO.FS.readBinFile envPath
  let ixonEnv ← match Ixon.deEnvAnon bytes with
    | .ok env => pure env
    | .error e =>
      IO.eprintln s!"[check-tc] deserialize failed: {e}"
      return 1
  let work ← match buildAnonWork ixonEnv with
    | .ok work => pure work
    | .error e =>
      IO.eprintln s!"[check-tc] work discovery failed: {e}"
      return 1
  let workN := match max? with
    | some n => min n work.size
    | none => work.size
  IO.println s!"[check-tc] {work.size} work item(s) discovered{if workN < work.size then s!", checking first {workN}" else ""}"

  let failOut? ← if failOutPath.isEmpty then pure none
    else pure (some (← IO.FS.Handle.mk failOutPath .write))

  let start ← IO.monoMsNow
  let mut st := TcState.newLazyAnon ixonEnv verify
  let mut passed := 0
  let mut targetsCovered := 0
  let mut failures : Array (String × String) := #[]
  let mut sinceClear := 0
  for i in [0:workN] do
    let item := work[i]!
    let primary : KId .anon := ⟨item.primary, ()⟩
    let label := s!"#{item.primary}"
    if verbose then
      IO.println s!"[check-tc] [{i+1}/{workN}] {label}"
    let (err?, st') := match (TcM.checkConst primary).run st with
      | .ok () s => ((none : Option String), s)
      | .error e s => (some (toString e), s)
    st := st'
    targetsCovered := targetsCovered + item.targets.size
    match err? with
    | none => passed := passed + item.targets.size
    | some msg =>
      for target in item.targets do
        failures := failures.push (s!"#{target}", msg)
      if let some h := failOut? then
        h.putStrLn s!"{label} {msg}"
        h.flush
    sinceClear := sinceClear + 1
    if clearEvery != 0 && sinceClear ≥ clearEvery then
      st := { st with env := st.env.clearReductionCaches }
      sinceClear := 0
  let elapsed := (← IO.monoMsNow) - start

  IO.println s!"[check-tc] checked {targetsCovered} constants ({workN} work items) in {elapsed}ms"
  IO.println s!"[check-tc] {passed}/{targetsCovered} passed"
  if !failures.isEmpty then
    -- Best-effort addr → name labels from the (anon-ignored) meta
    -- sections, so failures are greppable by Lean name.
    let addrToName : Std.HashMap String String :=
      match Ixon.deEnv bytes with
      | .ok fullEnv => fullEnv.addrToName.fold
          (fun acc addr name => acc.insert (toString addr) (toString name)) {}
      | .error _ => {}
    IO.println s!"[check-tc] {failures.size} failure(s):"
    let shown := min 30 failures.size
    for (label, msg) in failures.toSubarray 0 shown do
      let named := match addrToName[(label.drop 1).toString]? with
        | some n => s!"{label} ({n})"
        | none => label
      IO.println s!"  ✗ {named}: {msg}"
    if failures.size > shown then
      IO.println s!"  … ({failures.size - shown} more failures suppressed)"
  if !failOutPath.isEmpty then
    IO.println s!"[check-tc] streamed {failures.size} failure(s) to {failOutPath}"
  IO.println s!"##check-tc## {elapsed} {passed} {failures.size} {targetsCovered}"
  return if failures.isEmpty then 0 else 1

end Ix.Cli.CheckTcCmd

open Ix.Cli.CheckTcCmd in
def checkTcCmd : Cli.Cmd := `[Cli|
  "check-tc" VIA runCheckTcCmd;
  "Typecheck a `.ixe` through the pure-Lean Ix.Tc kernel (anon mode)"

  FLAGS:
    "fail-out"    : String; "Write failing constants to this path"
    max           : Nat;    "Check only the first N work items"
    "clear-every" : Nat;    "Clear reduction caches every N work items (0 disables; default 50)"
    "no-verify";            "Skip blake3 integrity verification at constant materialization"
    verbose;                "Log every work item on its own line (default: quiet)"

  ARGS:
    path : String; "Path to a serialized .ixe environment"
]

end
