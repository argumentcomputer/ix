import IxCCTests.Corpus.Artifacts.EvenOdd
import IxCCTests.Recheck.Kernel.Support

/-! The whole recheck path on a corpus closure in the kernel: on the
program, configuration and certificate of
`IxCCTests.Corpus.Artifacts.EvenOdd`, `Recheck.run` gives the object's
bytes the native run writes (`corpus kernel-artifacts --check` recomputes
them). Manual: `lake build IxCCTests.Corpus.KernelSample`. -/

namespace IxCCTests.Corpus.Kernel.EvenOdd

open IxCC IxCCTests.Recheck.Artifacts.CorpusEvenOdd

set_option maxRecDepth 1000000

example : (Recheck.run cfg program cert).map Recheck.Artifact.bytes = .ok object := by decide +kernel

end IxCCTests.Corpus.Kernel.EvenOdd
