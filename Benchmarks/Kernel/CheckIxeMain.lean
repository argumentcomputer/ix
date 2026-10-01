/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Benchmarks.Kernel.CheckIxe
import Benchmarks.Kernel.CheckIxeFold

/-! Entry point of `kernel-check-ixe`, the certified checker's environment check:
con-leche through the Ixon reader; see `Benchmarks.Kernel.CheckIxe`. With `--fold` first, the batch fold
over the records the environment check accepts (`Benchmarks.Kernel.CheckIxeFold`). -/

def main : List String → IO UInt32
  | "--fold" :: args => Benchmarks.Kernel.CheckIxeFold.run args
  | args => Benchmarks.Kernel.CheckIxe.run args
