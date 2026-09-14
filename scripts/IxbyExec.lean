import Compilatrix.Ixby.Runtime.Run
import Compilatrix.Tools.Check

open Compilatrix.Tools.Check Compilatrix.Ixby Lean

def main (args : List String) : IO UInt32 := cli "ixby-exec" do
  let (programPath, inputPath, outputPath, reportPath) ← match args with
    | [program, input, output] => pure (program, input, output, none)
    | [program, input, output, report] => pure (program, input, output, some report)
    | _ => throw (IO.userError "usage: ixby-exec <program.ixby> <input.ixbi> <output.ixbo> [execution.json]")
  let artifact ← checked (Binary.decode (← IO.FS.readBinFile programPath).data |>.mapError reprStr)
  let input ← checked (Binary.decodeInput artifact.value (← IO.FS.readBinFile inputPath).data |>.mapError reprStr)
  let (output, steps) ← Runtime.runArtifact artifact.value input.value
  let bytes ← checked (Binary.encodeOutput artifact.value output |>.mapError reprStr)
  IO.FS.writeBinFile outputPath ⟨bytes⟩
  if let some path := reportPath then
    IO.FS.writeFile path ((Json.mkObj [("reference_transitions", toJson steps),
      ("output_bytes", toJson bytes.size)]).pretty ++ "\n")
  IO.println s!"ixby-exec ok: {steps} reference transitions; {bytes.size} output bytes"
