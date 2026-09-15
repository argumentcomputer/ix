import CompilatrixTests.Aiur.Run
import CompilatrixTests.Aiur.WireRun

def main (args : List String) : IO Unit := do
  match args with
  | [] =>
      CompilatrixTests.Aiur.run
      CompilatrixTests.Aiur.WireRun.run
  | ["--emit-wire", directory] => CompilatrixTests.Aiur.WireRun.emit directory
  | _ => throw (IO.userError "usage: tests-aiur [--emit-wire DIRECTORY]")
