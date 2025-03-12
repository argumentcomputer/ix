import Tests.ArithExpr
import Tests.Binius
import Tests.Boundary
import Tests.ByteArray
import Tests.Ix

def main := LSpec.lspecIO (.ofList [
    ("arith-expr", Tests.ArithExpr.suite),
    ("boundary", Tests.Boundary.suite),
    ("binius-bindings", Tests.Binius.bindingsSuite),
    ("binius-witness", Tests.Binius.witnessSuite),
    ("byte-array", Tests.ByteArray.suite),
    ("ix", Tests.Ix.suite),
  ])
