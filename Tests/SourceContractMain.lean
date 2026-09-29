import Tests.Ix.SourceContract
import Tests.Ix.SourceContract.ImportCheck
import Tests.Ix.SourceContract.SyntaxCheck
import Tests.Ix.SourceContract.Driver

def main (args : List String) : IO UInt32 :=
  LSpec.lspecIO (.ofList [("source-contract",
    Tests.Ix.SourceContract.suite ++ Tests.Ix.SourceContract.Driver.suite)]) args
