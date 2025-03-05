import Tests.ArithExpr
import Tests.Binius
import Tests.ByteArray
import Tests.Ix

def main := do
  let _ <- LSpec.lspecIO (.ofList [
    ("arith-expr", Tests.ArithExpr.suite),
    ("binius",     Tests.Binius.suite),
    ("byte-array", Tests.ByteArray.suite),
    ("ix", Tests.Ix.suite),
  ]) []
  dbg

