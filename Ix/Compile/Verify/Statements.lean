import Ix.Compile.Verify.IxonValue
import Ix.Compile.Verify.Catalog
import Ix.Compile.Verify.Codec
import Ix.Compile.Verify.ExprCodec
import Ix.Compile.Verify.ExprSpineCodec
import Ix.Compile.Verify.MutualConstantCodec
import Ix.Compile.Verify.CompileState
import Ix.Compile.Verify.CompileUniv
import Ix.Compile.Verify.CompileMeta
import Ix.Compile.Verify.CompileMetaStore
import Ix.Compile.Verify.CompileExpr
import Ix.Compile.Verify.CompileExprCodec
import Ix.Compile.Verify.CompileConstantCodec
import Ix.Compile.Verify.CompilePreseed
import Ix.Compile.Verify.Sharing
import Ix.Compile.Verify.CompileSharingCodec
import Ix.Compile.Verify.CompileAxiomCodec
import Ix.Compile.Verify.CompileDefinitionCodec
import Ix.Compile.Verify.CompileDefinitionDataCodec
import Ix.Compile.Verify.CompileQuotientCodec
import Ix.Compile.Verify.CompileRecursorCodec
import Ix.Compile.Verify.CompileInductiveCodec
import Ix.Compile.Verify.CompileMutualCodec
import Ix.Compile.Verify.Reference
import Ix.Compile.Verify.SourceValue

/-!
# Public compiler-verification frontier

The first slice exports a direct, table-aware Ixon-to-Lean4Lean relation, the
constructive theorem that v2 binder modes do not change the related Theory
value, a total ordinary-fragment reference compiler, and proofs that its
universe values are preserved and its expression outputs inhabit the
conservative `.many`/`.shared` format. Its source-side wire bound tracks the
three metadata-transparent spine lengths and universe-vector size, proving
that every successful bounded reference compilation is accepted by the
expression serializer's public `wireWF` domain. The production ordinary
compiler inherits that guarantee through its complete refinement theorem.
A separate compiler/codec bridge composes the production run with the exact
`deExpr`/`serExpr` inverse, so every successfully compiled bounded ordinary
expression survives production serialization. The source/target value-preservation
theorem closes this square under explicit finite-table coherence.
At the next declaration boundary, `BlockWireTablesWF` records the exact
reference-address and universe-table conditions required by the constant
wire. Frozen table views transport it across compilation, and the one-root
axiom and sequential two-root definition phases now assemble unshared
constants that round-trip through `serConstant`/`deConstant`. Production
`buildConstantWithSharing` is connected on its exact no-sharing branch: for
both axiom and definition roots, the actual builder equals the verified
unshared assembly, and `BlockResult.mk'` stores bytes that decode back to its
block. The production sharing pipeline is now proof-visible from recursive
Merkle analysis through usage propagation and nonempty table construction.
Analysis retains only wire-safe representatives, rewriting cannot increase
application, lambda, or forall spine counts, and `applySharing` preserves the
expression wire domain for every rewritten root and emitted sharing entry.
An explicit overflow fallback makes its sharing count unconditionally
representable by `UInt64`, closing the complete axiom and definition builders
against the constant codec. Pointwise recursor-rule and constructor updaters,
together with a verified heterogeneous mutual-member fold, preserve all
nested wire conditions and counted child arrays. Quotient, standalone
recursor, mutual-block, and all four projection variants are consolidated by
one arbitrary-`ConstantInfo` production-builder theorem. Every wire-safe info
value and wire-safe root array therefore yields a wire-safe constant and
round-trips through `BlockResult.mk'` with empty or nonempty sharing.
The six singleton declaration branches now share a proof-visible production
tail that derives its root array canonically from the compiled `ConstantInfo`;
payload wire safety proves every extracted root safe, the tail leaves the
final block state unchanged, and its returned `BlockResult` satisfies a named
wire/codec postcondition without a separate root-ordering hypothesis.
For singleton axioms, the production driver is further decomposed into its
context/state reset, ordinary type compilation, metadata/name finalizer,
canonical sharing tail, and exact `compileConstantInfo` dispatch. The
finalizer preserves primary tables, the surgery-free declaration audit is
proved read-only and successful, and the resulting block satisfies the codec
postcondition. The table preseeding transition is now decomposed into a total
structural collector, canonicalization, and sorted unique commits while its
stack-safe loops remain the runtime implementation. Canonicalization has an
exact list refinement; the collector succeeds constructively for ready
ordinary syntax while preserving its framed state, payload wire safety, and
structural source-count bounds. A collision-disciplined active-ancestor
invariant now proves that digest/context seen-set hits preserve coverage of
every reference and universe leaf. Both commit phases are unconditionally
executable; the source bounds discharge table capacity, while the commits
preserve both lookup maps, establish collected-index completeness, retain name
resolution, and prove codec safety. The whole singleton preseed run is now
constructed from source readiness with wire-safe primary tables and with its
expression cache, canonical-universe cache, arena, and finalization flag proved
sound. Consequently the default-state axiom driver derives the production
preseed execution, frozen expression state, source-reference compilation, and
final block codec postcondition without any raw execution or post-state
coverage hypothesis. The same construction now spans the exact two-root
definition preseed: the first collection is reframed for the second root,
their structural bounds jointly discharge both table capacities, and the
committed indexes recover frozen references for the type and value. The
production definition driver then compiles those roots sequentially, preserves
the shared frozen tables across the metadata reset, runs the common sharing
tail, and proves the default singleton `compileConstantInfo` definition branch
ends in a codec-safe block. That sequential proof is also factored over the
compiler's common `Def` representation. The theorem and opaque source
conversions retain their declaration kind, safety, reducibility hints, and
name metadata, so their default singleton `compileConstantInfo` branches now
derive the same codec-safe postcondition from the shared two-root readiness
interface. The one-root construction now similarly exposes its frozen
reference target as a reusable postcondition. Quotient compilation preserves
its exact four-way kind discriminator and quotient metadata through the
ordinary expression phase and common sharing tail, closing the default
singleton quotient dispatch as well.
Consequently, ordinary production expression compilation followed by sharing
round-trips exactly for axiom, definition, theorem, opaque, quotient, and
standalone recursor declarations as well. Recursor preseeding follows the
nonempty production root list (type followed by rule RHSs); its recursive rule
fold preserves the shared frozen tables, appends one wire-safe rule per source
rule, and carries the exact rule count through the metadata finalizer and
singleton driver.
Standalone inductive families now use the same nonempty root-list preseed
boundary. The inductive type's metadata is captured before an ordered
constructor fold gives each constructor an independent arena; every round
retains the frozen primary tables and appends one wire-safe constructor and
sharing root. Ordered environment lookup reconstructs the constructor array,
the full family mutual context controls compilation, and the resulting
one-member mutual block plus inductive/constructor projections is codec-safe
through both the `inductInfo` and `ctorInfo` singleton dispatches.
The true mutual path now exposes the same proof-visible member machinery.
Mutual `Ind` values reuse the standalone metadata drain and constructor fold;
definition, inductive, and recursor members discharge one common frozen-state
contract. Recursive class folds compile every alpha-equivalent member for
metadata while retaining exactly one payload/root representative per nonempty
class. The resulting representative count, mutual payload, standalone-collapse
branch, general mutual wrapper, projection construction, sharing pass, and
serialized block are all codec-safe. The exact production driver is closed
first from a named heterogeneous-preseed snapshot boundary and then directly
from source readiness. Heterogeneous collection resets the universe memo for
each member context, retains a context-independent frame, sums structural
capacity costs, and recovers every frozen target after the canonical commits.
Its shared digest/context seen set has one explicit collision-safety premise.
Together with constructor-context agreement and the residual wire/count
bounds, this closes the surgery-free audit, mutual-context installation, and
complete production mutual driver without a raw execution hypothesis. A
uniform member-level universe-parameter condition now constructively
discharges that shared-seen premise, including constructor-owned contexts.
The non-singleton named compiler entry is decomposed into recursive SCC member
lookup, canonical classification, and mutual compilation. Environment and
constructor lookup evidence constructs the first phase without a raw run.
The classifier is a total, fuel-bounded refinement with an isolated comparison
cache: source readiness constructs every expression/constant comparison,
monadic run formation and merging preserve the exact member count, grouping
produces only nonempty classes, and every recursive round strictly increases
the class count. The source-member bound therefore rules out fuel exhaustion.
Erased membership tags and explicit final guards additionally prove that every
result contains only collected sources and has at most one representative
class per source. Consequently the top-level codec-safe `compileConstant`
theorem constructs `sortConsts` itself; it takes the source comparison domain,
uniform downstream partition obligations, member wire bounds, and the
`UInt64` count bound, with no raw collection, sorting, or compilation run
hypothesis.
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
an exact-consumption runner rejects trailing bytes, trimmed little-endian
integers and both `Tag2` forms have proved production inverses, and every
universe whose compressed successor counts fit `UInt64` has an exact
serializer/decoder inverse.  In particular, the `Sort 1` universe required by
the first declaration fixture is covered. The v2 expression writer and reader
are also kernel-visible total definitions, `deExpr` now requires full-buffer
consumption, and all twelve constructors round-trip exactly throughout the
compiler-facing wire domain, including arbitrary canonical application,
lambda, and forall spines. Reference and recursive-reference instantiations
may carry arbitrary wire-sized universe-index vectors. That domain includes
the `A` type and both the type and value shapes of `idA`, with unrestricted
`UInt64` fields backed by complete `Tag0` and `Tag4` inverse laws.
The declaration layer now composes those results through production definition
and axiom payloads, their `ConstantInfo` discriminants, and the top-level
`serConstant`/`deConstant` pair with arbitrary wire-representable sharing,
reference, and universe tables. The catalog's public `Constant.wireWF`
invariant is proved equivalent to the codec's compositional domain and feeds
the round-trip theorem directly. It exposes all necessary table conditions:
count conversion is lossless, every address payload is exactly 32 bytes, and
every compressed universe successor count is representable. The verified
`ConstantInfo` domain now also includes quotient
declarations and constructor, recursor, inductive, and definition projections;
production recursor payloads are covered through their counted rule arrays,
packed flags, arity fields, and expression bodies. Thus every standalone
`ConstantInfo` variant round-trips. Constructor arrays, inductive payloads,
all three `MutConst` member tags, and counted mutual blocks complete the
production `ConstantInfo` grammar, yielding a top-level constant round trip
for every variant in the explicit wire domain, with arbitrary canonical
application, lambda, and forall spines in every expression payload.
`KernelSourceWitness` is the sole
upstream source-semantics boundary; later compiler-preservation slices take it
as an explicit hypothesis until Lean4Lean can construct it for a replayed Lean
environment.
-/
