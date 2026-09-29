import Compilatrix.Tools.BuildGraph

open Lean Compilatrix.Tools.Check Compilatrix.Tools.BuildGraph

/-- Runtime suites whose `Run` failure assertions form the coverage inventory. -/
def runtimeSuites : List String := ["IxonV3", "Aiur"]

def main (args : List String) : IO UInt32 := cli "build-graph check failed" do
  match args with
  | ["--write"] =>
    IO.FS.createDirAll "nix"
    IO.FS.writeFile "nix/lean-modules.json" ((← manifest ".").pretty ++ "\n")
    IO.println "wrote nix/lean-modules.json"
  | ["--write-coverage", baseline] =>
    let inventory ← coverage "." (← manifest ".") baseline runtimeSuites
    IO.FS.writeFile "nix/ci-coverage.json" (inventory.pretty ++ "\n")
    IO.println "wrote nix/ci-coverage.json; review it before committing"
  | [] => check "."
  | ["--root", root] => check root
  | _ => throw (IO.userError
      "usage: check-build-graph [--write | --write-coverage BASELINE | --root PATH]")
