/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Tests.Certified.Fidelity

def main (args : List String) : IO UInt32 := do
  if args.length > 1 then
    IO.eprintln "usage: certified-fidelity-tests [OUTPUT_DIRECTORY]"
    return 2
  Tests.Certified.Fidelity.run (args.head?.map System.FilePath.mk)
  return 0
