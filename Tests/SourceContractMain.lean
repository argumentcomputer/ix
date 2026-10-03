import Tests.Ix.SourceContract
import Tests.Ix.SourceContract.ImportCheck
import Tests.Ix.SourceContract.SyntaxCheck
import Tests.Ix.SourceContract.Driver
import Tests.Ix.SourceContract.CopyCheck
import Tests.Ix.SourceContract.EquationCheck
import Tests.Ix.SourceContract.ReviewFixture
import Tests.Ix.SourceContract.Review

def main (args : List String) : IO UInt32 :=
  LSpec.lspecIO (.ofList [("source-contract",
    Tests.Ix.SourceContract.suite ++ Tests.Ix.SourceContract.Driver.suite ++
      Tests.Ix.SourceContract.Review.suite)]) args
