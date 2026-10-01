import CompilatrixTests.Corpus.Build
import CompilatrixTests.Corpus.KernelGen

/-! Thin root of the `corpus` executable (MT.1): `check`, `rebuild`, and
`kernel-artifacts [--check]` (the kernel-recheck sample's modules). -/

def main (args : List String) : IO UInt32 :=
  match args with
  | ["kernel-artifacts"] => CompilatrixTests.Corpus.KernelGen.main false
  | ["kernel-artifacts", "--check"] => CompilatrixTests.Corpus.KernelGen.main true
  | _ => CompilatrixTests.Corpus.main args
