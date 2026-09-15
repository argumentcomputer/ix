import Compilatrix.Tools.AiurCheck
import Compilatrix.Tools.AiurWireCheck

open Compilatrix.Tools.Check

def main (args : List String) : IO UInt32 := cli "Aiur check failed" do
  let parsed ← checked (parseArgs ["--root", "--bytecode", "--expect-root", "--output"] args)
  if let some input := optional parsed "--bytecode" then
    need ((optional parsed "--root").isNone) "--root cannot be combined with --bytecode"
    let expected ← present (optional parsed "--expect-root") "--bytecode requires --expect-root"
    let result ← Compilatrix.Tools.AiurWireCheck.replay input expected
      ((optional parsed "--output").map System.FilePath.mk)
    IO.println result.compress
  else
    need ((optional parsed "--expect-root").isNone && (optional parsed "--output").isNone)
      "--expect-root and --output require --bytecode"
    let root := option parsed "--root" "."
    Compilatrix.Tools.AiurCheck.run root
    Compilatrix.Tools.AiurWireCheck.verifyFixtures root
