import CompilatrixTests.Aiur.Run
import CompilatrixTests.Aiur.WireRun
import CompilatrixTests.Aiur.Execution.Run
import CompilatrixTests.Aiur.Static.Run
import CompilatrixTests.Aiur.MemoryAIR.Run
import CompilatrixTests.Aiur.RankAIR.Run

def main (args : List String) : IO Unit := do
  match args with
  | [] =>
      CompilatrixTests.Aiur.run
      CompilatrixTests.Aiur.WireRun.run
      CompilatrixTests.Aiur.Execution.run
      CompilatrixTests.Aiur.Static.run
      CompilatrixTests.Aiur.MemoryAIR.run
      CompilatrixTests.Aiur.RankAIR.run
  | ["--emit-wire", directory] => CompilatrixTests.Aiur.WireRun.emit directory
  | _ => throw (IO.userError "usage: tests-aiur [--emit-wire DIRECTORY]")
