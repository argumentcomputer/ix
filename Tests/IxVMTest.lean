import Tests.IxVM

def testSuite : Std.HashMap String (List LSpec.TestSeq) := .ofList [
  ("ixvm", Tests.IxVM.suite),
]

def main (args : List String) : IO UInt32 := do
  LSpec.lspecIO testSuite args
