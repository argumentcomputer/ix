import Ix.Ixby.Codec
import Compilatrix.Tools.Check

/-! Standalone canonical reference runner. Does not import the compiler. -/

open Compilatrix.Tools.Check

private def readBounded (path : System.FilePath) (limit : Nat) : IO (Array UInt8) := do
  need ((← path.metadata).byteSize.toNat ≤ limit) s!"Ixby file size limit: {path}"
  let bytes ← IO.FS.readBinFile path
  need (bytes.size ≤ limit) s!"Ixby file changed beyond size limit: {path}"
  return bytes.data

def main (args : List String) : IO UInt32 := cli "ixby-run" do
  let [profilePath, programPath, inputPath, outputPath, steps] := args |
    throw (IO.userError "usage: ixby-run <profile.ixfp> <program.ixby> <input.ixbi> <new-output.ixbo> <fuel>")
  let some fuel := steps.toNat? | throw (IO.userError "invalid Ixby fuel")
  need (!(← (System.FilePath.mk outputPath).pathExists)) "Ixby runner requires a new output file"
  let profile ← checked ((Ix.Ixby.Codec.decodeProfile (← readBounded profilePath 184)).mapError reprStr)
  -- Host read caps remain independent of the policy claimed by a profile file.
  let program ← readBounded programPath (min profile.value.programBytes 16777216)
  let input ← readBounded inputPath (min profile.value.valueBytes 16777216)
  let execution ← checked ((Ix.Ixby.Codec.execute profile.value program input fuel).mapError reprStr)
  IO.FS.writeBinFile outputPath ⟨execution.outputBytes⟩
  IO.println s!"ixby-run ok: {execution.outputBytes.size} output bytes"
