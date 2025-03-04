import Tests.ArithExpr
import Tests.Binius
import Tests.ByteArray
import Tests.Ixon

def main := LSpec.lspecIO $ .ofList [
    ("arith-expr", Tests.ArithExpr.suite),
    ("binius",     Tests.Binius.suite),
    ("byte-array", Tests.ByteArray.suite),
    ("ixon", Tests.Ixon.suite),
  ]
