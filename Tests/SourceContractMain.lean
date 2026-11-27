import Tests.Ix.SourceContract
import Tests.Ix.SourceContract.ImportCheck
import Tests.Ix.SourceContract.SyntaxCheck
import Tests.Ix.SourceContract.Driver

def main (args : List String) : IO UInt32 :=
  LSpec.lspecMain (LSpec.describe "source-contract" do
    Tests.Ix.SourceContract.suite
    Tests.Ix.SourceContract.Driver.suite) args
