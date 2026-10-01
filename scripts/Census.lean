import Compilatrix.Tools.Census

open Lean Compilatrix.Ixon Compilatrix.Tools.Check Compilatrix.Tools.Census

/-- Addresses named by a K1-style `equations.json`, when one is given. -/
def namesFile (path : Option String) : IO (Std.HashMap Address String) := do
  let some path := path | return {}
  Compilatrix.Tools.Census.names (← readJson path)

def main (args : List String) : IO UInt32 := cli "census failed" do
  let path :: rest := args
    | throw (IO.userError "usage: census ENV.ixe [--names equations.json] [--out census.json]")
  let args ← checked (parseArgs ["--names", "--out"] rest)
  let report := Compilatrix.Tools.Census.report (← IO.FS.readBinFile path) (← namesFile (optional args "--names"))
  let text := report.pretty ++ "\n"
  match optional args "--out" with
  | some out => IO.FS.writeFile out text
  | none => IO.print text
  IO.eprintln s!"census: {(report.getObjValD "constants").compress} constants; \
    reached {(report.getObjValD "reached").compress}; rejected {(report.getObjValD "rejected_at").compress}"
