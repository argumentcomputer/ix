import Compilatrix.Tools.BuildGraph

open Lean Compilatrix.Tools.Check Compilatrix.Tools.BuildGraph

def main (args : List String) : IO UInt32 := cli "build-graph check failed" do
  match args with
  | ["--write"] =>
    IO.FS.createDirAll "nix"
    IO.FS.writeFile "nix/lean-modules.json" ((← manifest ".").pretty ++ "\n")
    IO.println "wrote nix/lean-modules.json"
  | [] => check "."
  | ["--root", root] => check root
  | _ => throw (IO.userError "usage: check-build-graph [--write | --root PATH]")
