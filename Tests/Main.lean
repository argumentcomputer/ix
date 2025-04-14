import Tests.ArithExpr
import Tests.Binius
import Tests.Boundary
import Tests.ByteArray
import Tests.Unsigned
import Tests.Ix
import Tests.Ix.Compile
import Tests.Keccak

def main (args: List String) : IO UInt32 := do
  if args.contains "compile"
  then LSpec.lspecEachIO Tests.Ix.Compile.suiteIO id
  else
    LSpec.lspecIO (.ofList [
      ("arith-expr", Tests.ArithExpr.suite),
      ("boundary", Tests.Boundary.suite),
      ("binius-bindings", Tests.Binius.bindingsSuite),
      ("binius-witness", Tests.Binius.witnessSuite),
      ("binius-transparent", Tests.Binius.transparentSuite),
      ("byte-array", Tests.ByteArray.suite),
      ("unsigned", Tests.Unsigned.suite),
      ("ix", Tests.Ix.suite),
      ("keccak", Tests.Keccak.suite),
    ]) args
