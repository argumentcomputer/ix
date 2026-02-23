import Tests.Aiur.Common
import Ix.IxVM

def Tests.IxVM.suite := [
  mkAiurTests IxVM.ixVM []
]

def main (args : List String) : IO UInt32 := do
  LSpec.lspecIO (.ofList [("ixvm", Tests.IxVM.suite)]) args
