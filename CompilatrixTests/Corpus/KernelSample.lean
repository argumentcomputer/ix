import CompilatrixTests.Corpus.Kernel.Tuple
import CompilatrixTests.Corpus.Kernel.EvenOdd
import CompilatrixTests.Corpus.Kernel.StrictAnd
import CompilatrixTests.Corpus.Kernel.NatShiftr

/-! # The corpus's kernel-recheck sample (MT.2, manual)

The whole `Recheck.run` by `decide +kernel` on four corpus roots beyond K1:
`bench-k1/even-odd` (mutual recursion), `phase1-scalar/tuple` (an allocated
3-tuple), `natShiftr` (shifts, 171 constants) and `strictAndOr`'s
`entryStrictAnd` (a `Bool` result). Each takes 20–24 s to build and about
4 GB (2026-10-01). Built by hand, like `CompilatrixTests.Recheck.KernelSlow`:
`lake build CompilatrixTests.Corpus.KernelSample`; nothing in the default
build or the programs derivation imports it. `lake exe corpus
kernel-artifacts --check` compares the artifacts with a fresh run. -/
