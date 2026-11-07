import IxCC.Tools.AiurCheck
import IxCC.Tools.AiurWireCheck
import IxCC.Tools.AiurMemoryCheck
import IxCC.Tools.AiurRankCheck

open IxCC.Tools.Check

def main (args : List String) : IO UInt32 := cli "Aiur check failed" do
  let parsed ← checked (parseArgs ["--root", "--bytecode", "--expect-root", "--output", "--dump-memory-air", "--dump-rank-air"] args)
  if let some output := optional parsed "--dump-memory-air" then
    need (parsed.length == 1) "--dump-memory-air cannot be combined with other options"
    IxCC.Tools.AiurMemoryCheck.emit output
  else if let some output := optional parsed "--dump-rank-air" then
    need (parsed.length == 1) "--dump-rank-air cannot be combined with other options"
    IxCC.Tools.AiurRankCheck.emit output
  else if let some input := optional parsed "--bytecode" then
    need ((optional parsed "--root").isNone) "--root cannot be combined with --bytecode"
    let expected ← present (optional parsed "--expect-root") "--bytecode requires --expect-root"
    let result ← IxCC.Tools.AiurWireCheck.replay input expected
      ((optional parsed "--output").map System.FilePath.mk)
    IO.println result.compress
  else
    need ((optional parsed "--expect-root").isNone && (optional parsed "--output").isNone)
      "--expect-root and --output require --bytecode"
    let root := option parsed "--root" "."
    IxCC.Tools.AiurCheck.run root
    IxCC.Tools.AiurWireCheck.verifyFixtures root
    IxCC.Tools.AiurMemoryCheck.verifyFixtures root
    IxCC.Tools.AiurRankCheck.verifyFixtures root
