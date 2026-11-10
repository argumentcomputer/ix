import IxCCTests.Corpus.Artifacts.Tuple
import IxCCTests.Recheck.Kernel.Support

/-! The whole recheck path on a corpus closure in the kernel: on the
program, configuration and certificate of
`IxCCTests.Corpus.Artifacts.Tuple`, `Recheck.run` gives the object's
bytes the native run writes (`corpus kernel-artifacts --check` recomputes
them). Manual: `lake build IxCCTests.Corpus.KernelSample`. -/

namespace IxCCTests.Corpus.Kernel.Tuple

open IxCC IxCCTests.Recheck.Artifacts.CorpusTuple

set_option maxRecDepth 1000000

example : (Recheck.run cfg program cert).map Recheck.Artifact.bytes = .ok object := by decide +kernel

end IxCCTests.Corpus.Kernel.Tuple
