import IxCCTests.Corpus.Artifacts.NatShiftr
import IxCCTests.Recheck.Kernel.Support

/-! The whole recheck path on a corpus closure in the kernel (MT.2): on the
program, configuration and certificate of
`IxCCTests.Corpus.Artifacts.NatShiftr`, `Recheck.run` gives the object's
bytes the native run writes (`corpus kernel-artifacts --check` recomputes
them). Manual: `lake build IxCCTests.Corpus.KernelSample`. -/

namespace IxCCTests.Corpus.Kernel.NatShiftr

open IxCC IxCCTests.Recheck.Artifacts.CorpusNatShiftr

set_option maxRecDepth 1000000

example : (Recheck.run cfg program cert).map Recheck.Artifact.bytes = .ok object := by decide +kernel

end IxCCTests.Corpus.Kernel.NatShiftr
