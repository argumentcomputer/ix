import Tests.FormalChecks.Common

/-!
# `formal-checks ranges`

The range split of a one-shard proof (`stark-verifier ranges PROOF DIR 1` in
`check-formal.sh`): one leaf, `[0, 1)`, with no children, and its statement is
the 65-byte range statement (`Aggr.rangeStatement`).
-/

namespace Tests.FormalChecks.Ranges

open Lean System Tests.FormalChecks

def main (argv : List String) : IO UInt32 := do
  let [dir] := argv
    | IO.eprintln "usage: formal-checks ranges DIR (the directory holding ranges/)"; return 2
  let dir : FilePath := dir
  let ranges ← readJson (dir / "ranges" / "ranges.json")
  let expected := Json.arr #[Json.mkObj [("lo", 0), ("hi", 1), ("children", Json.arr #[])]]
  unless ranges == expected do
    fail s!"ranges.json is {ranges.compress}, expected {expected.compress}"
  let statement ← IO.FS.readBinFile (dir / "ranges" / "0.statement")
  unless statement.size == 65 do
    fail s!"0.statement has {statement.size} bytes, expected 65"
  return 0

end Tests.FormalChecks.Ranges
