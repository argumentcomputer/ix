import Std.Data.HashMap.Basic
import Tests.ArithExpr
import Tests.Binius
import Tests.ByteArray

open Std (HashMap)

def map := HashMap.ofList [
    ("arith-expr", Tests.ArithExpr.suite),
    ("binius",     Tests.Binius.suite),
    ("byte-array", Tests.ByteArray.suite),
  ]

def main (args : List String) : IO UInt32 := do
  -- Compute the filtered map containing the test suites to run
  let filteredMap :=
    if args.isEmpty then map
    else Id.run do
      let mut acc := .empty
      for arg in args do
        for (key, tSeq) in map do
          if key.startsWith arg then
            acc := acc.insert key tSeq
      pure acc

  -- Accumulate error messages
  let mut testsWithErrors : HashMap String (Array String) := .empty
  for (key, tSeqs) in filteredMap do
    IO.println key
    for tSeq in tSeqs do
      let (success, msg) := tSeq.run (indent := 2)
      if success then IO.println msg
      else
        IO.eprintln msg
        if let some msgs := testsWithErrors[key]? then
          testsWithErrors := testsWithErrors.insert key $ msgs.push msg
        else
          testsWithErrors := testsWithErrors.insert key #[msg]

  if testsWithErrors.isEmpty then return 0

  -- Print error messages and then return 1
  IO.eprintln "-------------------------------- Failing tests ---------------------------------"
  for (key, msgs) in testsWithErrors do
    IO.eprintln key
    for msg in msgs do
      IO.eprintln msg
  return 1
