import Ix.Compile.Verify.IxonValue
import Ix.Compile.Verify.Catalog
import Ix.Compile.Verify.Codec
import Ix.Compile.Verify.CompileState
import Ix.Compile.Verify.CompileUniv
import Ix.Compile.Verify.CompileMeta
import Ix.Compile.Verify.CompileMetaStore
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
semantics, and composes with the independent Lean4Lean expression value. A
frozen-preseed state relation now closes the complete ordinary-expression
tree through the actual production dispatcher, including arbitrary-universe
local and external constants, recursive projections, and their Lean4Lean
value corollary. The strengthened theorem also exposes a structural
`ArenaRel` for the returned metadata root, preserves every warm-cache root
under append-only growth, and makes the `UInt64` arena-capacity boundary
explicit. Expression metadata now has a total KV-map reference compiler for
strings, booleans, names, naturals, integers, and recursive syntax values.
Production syntax serialization is kernel-visible and structurally total;
production metadata compilation implements the exact recursive encoding while
changing only name/blob presentation stores, and the complete ordinary
expression theorem accepts arbitrary nonempty metadata maps.  A separate
finite run support now scopes name and blob collision faithfulness; under
strict preseed integrity, syntax, data-value, and KV-map compilation preserve
all old lookups and establish exact recovery for every traversed name,
ancestor name component, and blob payload.
The v2 universe writer and reader are now kernel-visible total definitions;
an exact-consumption runner rejects trailing bytes, and the one-byte `Tag2`
domain has a proved production serializer/decoder inverse.  In particular,
the `Sort 1` universe required by the first declaration fixture is covered.
`KernelSourceWitness` is the sole
upstream source-semantics boundary; later compiler-preservation slices take it
as an explicit hypothesis until Lean4Lean can construct it for a replayed Lean
environment.
-/
