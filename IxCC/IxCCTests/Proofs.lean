import IxCC.Ixon.Serialize
import IxCC.Ixon.Uses
import IxCC.Ixon.Address
import IxCC.Ixon.Univ
import IxCC.Ixon.Kinds
import IxCC.Ixon.Hash
import IxCC.Ixon.Merkle
import IxCC.IxIR.Encoding
import IxCC.IxIR.Decode
import IxCC.X86.Basic
import IxCC.X86.Eval
import IxCC.X86.EvalExamples
import IxCC.X86.Encode
import IxCC.X86.EncodeExamples
import IxCC.X86.ByteExamples
import IxCC.X86.StreamExamples
import IxCC.X86.ELF
import IxCC.X86.ELFExamples
import IxCCTests.Sem.Toy.Cases
import IxCCTests.Sem.Toy.IO.Cases
import IxCCTests.Fences
import IxCCTests.Fences.BigNat
import IxCCTests.Fences.ArrayElf
import IxCCTests.Fences.ArrayReadback
import IxCCTests.Fences.ArrayRt
import IxCCTests.Fences.ArraySpec
import IxCCTests.Fences.RtRcInline
import IxCCTests.Fences.OwnBorrow
import IxCCTests.Fences.OwnReuse
import IxCCTests.Fences.RtRcScalarTail
import IxCCTests.Fences.BigNatWire
import IxCCTests.Fences.LirOpt
import IxCCTests.Own.Plain.Suite
import IxCCTests.Cfg.Rc.Proofs

/-! Complete proof and fence collection: elaboration-time proofs of the kept
foundations and every exact axiom fence. Built explicitly; the production
library does not import it. -/
