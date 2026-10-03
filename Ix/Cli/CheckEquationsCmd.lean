/-
  `ix check-equations SIDECAR CLOSURE`: re-verify, from a closure (`.ixe`) and
  its equation sidecar, the `(definition, equation)` pairs through which
  resource admission checked a definition (`Ix.Compile.CheckEquations`). A
  consumer that runs exactly those definitions by their bound equations can
  call this, or reimplement it, as its "run exactly the checked pairs"
  obligation.
-/
module
public import Cli
public import Ix.Compile.CheckEquations

public section

namespace Ix.Cli.CheckEquationsCmd

def runCheckEquationsCmd (p : Cli.Parsed) : IO UInt32 := do
  let some sidecarArg := p.positionalArg? "sidecar"
    | p.printError "error: must specify <sidecar>"; return 1
  let some closureArg := p.positionalArg? "closure"
    | p.printError "error: must specify <closure>"; return 1
  let sidecarPath := sidecarArg.as! String
  let closurePath := closureArg.as! String
  let sidecar ← match Lean.Json.parse (← IO.FS.readFile sidecarPath) with
    | .ok json => pure json
    | .error e => IO.eprintln s!"error: {sidecarPath}: {e}"; return 1
  let bytes ← IO.FS.readBinFile closurePath
  let env ← match Ixon.runGetExact Ixon.Env.getEnv bytes with
    | .ok env => pure env
    | .error e => IO.eprintln s!"error: {closurePath}: {e}"; return 1
  match Ix.Compile.CheckEquations.verify env sidecar with
  | .error e =>
    IO.eprintln s!"error: {e}"
    return 1
  | .ok report =>
    IO.println s!"check-equations: resource claim (root {report.root}, profile {report.profile}) holds"
    for e in report.entries do
      IO.println s!"  {e.definition} {e.definitionAddress} ↦ {e.equation} {e.equationAddress}"
    IO.println s!"check-equations: {report.entries.size} checked pair(s) verified"
    return 0

end Ix.Cli.CheckEquationsCmd

open Ix.Cli.CheckEquationsCmd in
def checkEquationsCmd : Cli.Cmd := `[Cli|
  "check-equations" VIA runCheckEquationsCmd;
  "Re-verify the resource-checked unfolding equations an `ix compile` sidecar lists against the closure"

  ARGS:
    sidecar : String; "The equation sidecar (`ix/compile-equations/1`) written by `ix compile` under resource admission."
    closure : String; "The `.ixe` closure the sidecar describes."
]

end
