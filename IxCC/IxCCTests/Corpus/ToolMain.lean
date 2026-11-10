import IxCCTests.Corpus.Build
import IxCCTests.Corpus.KernelGen

/-! Thin root of the `corpus` executable: `check`, `rebuild`, and
`kernel-artifacts [--check]` (the kernel-recheck sample's modules). -/

def main (args : List String) : IO UInt32 :=
  match args with
  | ["kernel-artifacts"] => IxCCTests.Corpus.KernelGen.main false
  | ["kernel-artifacts", "--check"] => IxCCTests.Corpus.KernelGen.main true
  | _ => IxCCTests.Corpus.toolMain args
