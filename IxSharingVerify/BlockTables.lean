import Ix.CompileM
import IxC.Ixon.Verify.Basic

/-!
# The block state's primary tables on the wire

`BlockWireTablesWF`: the compiler's primary reference and universe tables
are representable by the constant wire format. The sharing builder's output
theorems (`Ix.Sharing.Verify.Builder`) take it as a hypothesis, and the
table interners keep it (`Ix.CompileCert.WireTables`); it lives here, apart
from the builder, so that the interner proofs need not import the sharing
construction's proofs.
-/

namespace Ix.Sharing.Verify

/-- The primary reference and universe tables in a production block state are
representable by the constant wire format. -/
structure BlockWireTablesWF (state : Ix.CompileM.BlockState) : Prop where
  refsCount : state.refs.size < UInt64.size
  refs : ∀ ref ∈ state.refs, ref.hash.size = 32
  univsCount : state.univs.size < UInt64.size
  univs : ∀ univ ∈ state.univs, Ixon.Verify.Codec.Univ.WireWF univ

end Ix.Sharing.Verify
