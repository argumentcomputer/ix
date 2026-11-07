import IxCCTests.IxonV3.Run

/-- `tests-ixon-v3` runs the suite. `tests-ixon-v3 write-chunked-catalog FAT OUT`
writes the chunked reference catalog from the fat one (a refreeze step,
`docs/corpus.md`). -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [] => return if ← IxCCTests.IxonV3.run then 0 else 1
  | ["write-chunked-catalog", fat, out] =>
    IxCCTests.IxonV3.CatalogFixtures.writeChunked fat out
    return 0
  | _ =>
    IO.eprintln "usage: tests-ixon-v3 [write-chunked-catalog FAT.ixc OUT.ixc]"
    return 2
