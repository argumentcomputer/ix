/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Benchmarks.Kernel.ConLecheCensus
import Benchmarks.Kernel.ConLecheFold

/-! Entry point of `kernel-census`, the certified checker's census from L5
(plan v4): con-leche through the Ixon reader, the same driver as
`kernel-census-cl`; see `Benchmarks.Kernel.ConLecheCensus`. With `--fold`
first, the batch fold over the records the census accepts
(`Benchmarks.Kernel.ConLecheFold`). The intrinsic reference kernel's census
(`kernel-census-intrinsic`) was retired at L6. -/

def main : List String → IO UInt32
  | "--fold" :: args => Benchmarks.Kernel.ConLecheFold.run args
  | args => Benchmarks.Kernel.ConLecheCensus.run args
