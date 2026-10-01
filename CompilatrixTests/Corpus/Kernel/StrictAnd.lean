import CompilatrixTests.Corpus.Artifacts.StrictAnd
import CompilatrixTests.Recheck.Kernel.Support

/-! The whole recheck path on a corpus closure in the kernel (MT.2): on the
program, configuration and certificate of
`CompilatrixTests.Corpus.Artifacts.StrictAnd`, `Recheck.run` gives the object's
bytes the native run writes (`corpus kernel-artifacts --check` recomputes
them). Manual: `lake build CompilatrixTests.Corpus.KernelSample`. -/

namespace CompilatrixTests.Corpus.Kernel.StrictAnd

open Compilatrix CompilatrixTests.Recheck.Artifacts.CorpusStrictAnd

set_option maxRecDepth 1000000

example : (Recheck.run cfg program cert).map Recheck.Artifact.bytes = .ok object := by decide +kernel

end CompilatrixTests.Corpus.Kernel.StrictAnd
