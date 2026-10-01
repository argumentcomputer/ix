/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Benchmarks.Kernel.ConLecheCensus

/-! Entry point of `kernel-census`, the certified checker's census from L5
(plan v4): con-leche through the Ixon reader, the same driver as
`kernel-census-cl`; see `Benchmarks.Kernel.ConLecheCensus`. The intrinsic
reference kernel's census is `kernel-census-intrinsic`. -/

def main (args : List String) : IO UInt32 := Benchmarks.Kernel.ConLecheCensus.run args
