import Tests.ArithExpr
import Tests.Binius
import Tests.Boundary
import Tests.ByteArray
import Tests.Unsigned
import Tests.Ix
import Tests.Iroh

def main := LSpec.lspecIO (.ofList [
    ("arith-expr", Tests.ArithExpr.suite),
    ("boundary", Tests.Boundary.suite),
    ("binius-bindings", Tests.Binius.bindingsSuite),
    ("binius-witness", Tests.Binius.witnessSuite),
    ("binius-transparent", Tests.Binius.transparentSuite),
    ("byte-array", Tests.ByteArray.suite),
    ("unsigned", Tests.Unsigned.suite),
    ("ix", Tests.Ix.suite),
    ("iroh", Tests.Iroh.suite),
  ])
