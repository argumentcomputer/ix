/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Benchmarks.Kernel.ConLecheCensus

/-! Entry point of `kernel-census-cl`; see `Benchmarks.Kernel.ConLecheCensus`. -/

def main (args : List String) : IO UInt32 := Benchmarks.Kernel.ConLecheCensus.run args
