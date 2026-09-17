import Ix.Ixby.Codec

open Ix.Ixby

/-- Compare an independently encoded fixture with the reference byte executor. -/
def main (args : List String) : IO UInt32 := do
  let [directory] := args | throw (IO.userError "usage: Fixture.lean DIRECTORY")
  let path : System.FilePath := directory
  let profileBytes ← IO.FS.readBinFile (path / "profile.ixfp")
  let program ← IO.FS.readBinFile (path / "program.ixby")
  let input ← IO.FS.readBinFile (path / "input.ixbi")
  let expected ← IO.FS.readBinFile (path / "output.ixbo")
  let profile ← match Codec.decodeProfile profileBytes.data with
    | .ok decoded => pure decoded.value
    | .error error => throw (IO.userError s!"profile decode: {repr error}")
  match Codec.execute profile program.data input.data profile.maxSteps with
  | .error error => throw (IO.userError s!"execution: {repr error}")
  | .ok execution =>
    unless execution.outputBytes == expected.data do
      throw (IO.userError "reference output differs from independent fixture")
    IO.println s!"Reference execution matched {expected.size} canonical output bytes."
    return 0
