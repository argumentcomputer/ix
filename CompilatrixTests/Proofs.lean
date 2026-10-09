import Compilatrix.Ixon.Serialize
import Compilatrix.Ixon.Uses
import Compilatrix.Ixon.Address
import Compilatrix.Ixon.Univ
import Compilatrix.Ixon.Kinds
import Compilatrix.Ixon.Hash
import Compilatrix.Ixon.Merkle
import Compilatrix.IxIR.Encoding
import Compilatrix.IxIR.Decode
import Compilatrix.X86.Basic
import Compilatrix.X86.Eval
import Compilatrix.X86.EvalExamples
import Compilatrix.X86.Encode
import Compilatrix.X86.EncodeExamples
import Compilatrix.X86.ByteExamples
import Compilatrix.X86.StreamExamples
import Compilatrix.X86.ELF
import Compilatrix.X86.ELFExamples
import Compilatrix.Ixon.V3.Resource.StateProofs
import CompilatrixTests.Aiur.Proofs
import CompilatrixTests.Aiur.WireProofs
import CompilatrixTests.Aiur.Execution.Proofs
import CompilatrixTests.Aiur.Static.Proofs
import CompilatrixTests.Aiur.CounterAnalysis.Proofs
import CompilatrixTests.Aiur.MemoryAIR.Proofs
import CompilatrixTests.Aiur.RankAIR.Proofs
import CompilatrixTests.Sem.Toy.Cases
import CompilatrixTests.Sem.Toy.IO.Cases
import CompilatrixTests.Fences
import CompilatrixTests.Own.Plain.Suite
import CompilatrixTests.Cfg.Rc.Proofs

/-! Complete proof and fence collection: elaboration-time proofs of the kept
foundations and every exact axiom fence. Built explicitly; the production
library does not import it. -/
