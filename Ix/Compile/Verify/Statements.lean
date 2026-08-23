import Ix.Compile.Verify.IxonValue
import Ix.Compile.Verify.Reference
import Ix.Compile.Verify.SourceValue

/-!
# Public compiler-verification frontier

The first slice exports a direct, table-aware Ixon-to-Lean4Lean relation, the
constructive theorem that v2 binder modes do not change the related Theory
value, a total ordinary-fragment reference compiler, and proofs that its
universe values are preserved and its expression outputs inhabit the
conservative `.many`/`.shared` format. The source/target value-preservation
theorem closes this square under explicit finite-table coherence.
`KernelSourceWitness` is the sole
upstream source-semantics boundary; later compiler-preservation slices take it
as an explicit hypothesis until Lean4Lean can construct it for a replayed Lean
environment.
-/
