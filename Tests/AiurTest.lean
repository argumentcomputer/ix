import Tests.Aiur

def testSuite : Std.HashMap String (List LSpec.TestSeq) := .ofList [
  ("aiur", Tests.Aiur.suite),
]

def main (args : List String) : IO UInt32 := do
  LSpec.lspecIO testSuite args
