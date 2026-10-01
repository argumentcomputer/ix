import CompilatrixTests.Corpus.Artifacts.Tuple
import CompilatrixTests.Recheck.Kernel.Support

/-! The whole recheck path on a corpus closure in the kernel (MT.2): on the
program, configuration and certificate of
`CompilatrixTests.Corpus.Artifacts.Tuple`, `Recheck.run` gives the object's
bytes the native run writes (`corpus kernel-artifacts --check` recomputes
them). Manual: `lake build CompilatrixTests.Corpus.KernelSample`. -/

namespace CompilatrixTests.Corpus.Kernel.Tuple

open Compilatrix CompilatrixTests.Recheck.Artifacts.CorpusTuple

set_option maxRecDepth 1000000

example : (Recheck.run cfg program cert).map Recheck.Artifact.bytes = .ok object := by decide +kernel

end CompilatrixTests.Corpus.Kernel.Tuple
