import Ix.Compile.Verify.IxonValue
import Ix.Compile.Verify.Catalog
import Ix.Compile.Verify.CompileState
import Ix.Compile.Verify.CompileUniv
import Ix.Compile.Verify.CompileExpr
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
The same frontier now includes a finite immutable catalog with explicit
digest-key faithfulness, well-addressed v2 expression tables and constants,
and refinement proofs for the production reference/universe interning
operations through `CompileM.run`. Production `compileUniv` is structurally
total and refines the reference compiler while preserving both memo-cache
soundness and the independent Lean4Lean universe value. In surgery-free
environments, production `compileExpr` now selects a kernel-visible total
path; its recursive structural fragment refines `compileExprRef`, preserves a
sound collision-disciplined expression cache, retains flattened App-spine
semantics, and composes with the independent Lean4Lean expression value.
`KernelSourceWitness` is the sole
upstream source-semantics boundary; later compiler-preservation slices take it
as an explicit hypothesis until Lean4Lean can construct it for a replayed Lean
environment.
-/
