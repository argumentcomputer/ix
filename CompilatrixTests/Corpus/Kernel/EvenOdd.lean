import CompilatrixTests.Corpus.Artifacts.EvenOdd
import CompilatrixTests.Recheck.Kernel.Support

/-! The whole recheck path on a corpus closure in the kernel (MT.2): on the
program, configuration and certificate of
`CompilatrixTests.Corpus.Artifacts.EvenOdd`, `Recheck.run` gives the object's
bytes the native run writes (`corpus kernel-artifacts --check` recomputes
them). Manual: `lake build CompilatrixTests.Corpus.KernelSample`. -/

namespace CompilatrixTests.Corpus.Kernel.EvenOdd

open Compilatrix CompilatrixTests.Recheck.Artifacts.CorpusEvenOdd

set_option maxRecDepth 1000000

example : (Recheck.run cfg program cert).map Recheck.Artifact.bytes = .ok object := by decide +kernel

end CompilatrixTests.Corpus.Kernel.EvenOdd
