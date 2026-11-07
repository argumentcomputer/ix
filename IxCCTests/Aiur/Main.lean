import IxCCTests.Aiur.Run
import IxCCTests.Aiur.WireRun
import IxCCTests.Aiur.Execution.Run
import IxCCTests.Aiur.Static.Run
import IxCCTests.Aiur.MemoryAIR.Run
import IxCCTests.Aiur.RankAIR.Run

def main (args : List String) : IO Unit := do
  match args with
  | [] =>
      IxCCTests.Aiur.run
      IxCCTests.Aiur.WireRun.run
      IxCCTests.Aiur.Execution.run
      IxCCTests.Aiur.Static.run
      IxCCTests.Aiur.MemoryAIR.run
      IxCCTests.Aiur.RankAIR.run
  | ["--emit-wire", directory] => IxCCTests.Aiur.WireRun.emit directory
  | _ => throw (IO.userError "usage: tests-aiur [--emit-wire DIRECTORY]")
