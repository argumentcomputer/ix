import Compilatrix.Tools.AiurCheck

open Compilatrix.Tools.Check

def main (args : List String) : IO UInt32 := cli "Aiur check failed" do
  let parsed ← checked (parseArgs ["--root"] args)
  Compilatrix.Tools.AiurCheck.run (option parsed "--root" ".")
