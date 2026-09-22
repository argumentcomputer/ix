import Ix.Cli.CodegenCmd
import Tests.Aiur.TracePlan

def main (args : List String) : IO UInt32 :=
  match args with
  | ["test"] =>
    LSpec.lspecIO (.ofList [("aiur-trace-plan", [AiurTests.TracePlan.tests])]) []
  | _ => codegenCmd.validate args
