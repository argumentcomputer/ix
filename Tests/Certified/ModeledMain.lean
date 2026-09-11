/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Tests.Certified.ModeledAdversarial

def main (args : List String) : IO Unit := do
  let directory := (args.head?).map System.FilePath.mk
  Tests.Certified.Modeled.run directory
  Tests.Certified.ModeledAdversarial.run directory
