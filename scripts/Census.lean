import Compilatrix.Tools.Census

open Lean Compilatrix.Ixon Compilatrix.Tools.Check Compilatrix.Tools.Census

/-- Addresses named by a K1-style `equations.json` (roots, definitions and
their unfolding equations), for readable reports. Names are diagnostic only. -/
def names (path : Option String) : IO (Std.HashMap Address String) := do
  let some path := path | return {}
  let pack ← readJson path
  let mut map : Std.HashMap Address String := {}
  let decode (hex : String) : IO Address := do
    present (Address.ofBytes? (← checked (unhex hex))) s!"invalid address {hex}"
  for root in ← arrField pack "roots" do
    map := map.insert (← decode (← strField root "address")) (← strField root "name")
  for pair in ← arrField pack "equations" do
    map := map.insert (← decode (← strField pair "definition_address")) (← strField pair "definition")
    map := map.insert (← decode (← strField pair "equation_address")) (← strField pair "equation")
  return map

def main (args : List String) : IO UInt32 := cli "census failed" do
  let path :: rest := args
    | throw (IO.userError "usage: census ENV.ixe [--names equations.json] [--out census.json]")
  let args ← checked (parseArgs ["--names", "--out"] rest)
  let report := Compilatrix.Tools.Census.report (← IO.FS.readBinFile path) (← names (optional args "--names"))
  let text := report.pretty ++ "\n"
  match optional args "--out" with
  | some out => IO.FS.writeFile out text
  | none => IO.print text
  IO.eprintln s!"census: {(report.getObjValD "constants").compress} constants; \
    reached {(report.getObjValD "reached").compress}; rejected {(report.getObjValD "rejected_at").compress}"
