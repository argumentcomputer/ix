# Canonical sharing

Status: layer 1 and share-elimination theorem complete; collision-safe v2
compressor, exact byte audit, and recompression recognizer implemented. The
validated public API has inline-recovery and canonical-fixpoint theorems, and
raw construction plus audit recovery is proved. Public compressor totality is
proved through a certified identity fallback. Canonical inlined identity now
corresponds to address identity on the exact wire-representable domain under an
explicit pairwise BLAKE3 no-collision premise. Successful evaluation is also
proved invariant under full inlining for layer-1-valid stores and constants.
The pinned ix Lean/Rust corpus, intentional local-policy deltas, external exact-
image recognizer, and both policy identifiers are frozen. Corpus-facing checks
have structural work budgets. Last reviewed 2026-08-25.

Ixon addresses compressed constants, not fully unfolded expression trees.
That is coherent only if accepted sharing tables cannot arbitrarily change the
compressed spelling of one term. The implementation therefore separates a
cheap decoder invariant from the more expensive canonical-compressor check.

## Layer 1: decoder-enforced structure

[`Compilatrix/Ixon/Sharing/Basic.lean`](../Compilatrix/Ixon/Sharing/Basic.lean)
implements four rules:

1. every `.share i` in a constant body is in bounds;
2. table entry `i` may reference only entries `< i`;
3. a table entry may not itself be a bare `.share` alias;
4. every entry is referenced at least twice across later entries and all
   constant bodies.

Rules 1–3 reject out-of-bounds references, forward edges, self-cycles, longer
cycles, and aliases. Rule 4 rejects dead and singleton entries: inlining either
strictly shrinks the encoding, so a deterministic compressor never emits
them. `ConstantInfo.exprs` in
[`Const.lean`](../Compilatrix/Ixon/Const.lean) is the authoritative enumeration
of every expression-bearing payload, including all mutual-block members,
constructors, and recursor rules.

The local constant decoder fails closed on each rule. Positive and negative
guards cover nested backward references, body overflow, self-reference,
forward reference, bare aliases, dead entries, and singleton entries. Raw
`Constant` values remain constructible so those rejection fixtures can be
serialized; accordingly, the local constant roundtrip obligation is
restricted to `Constant.sharingWF` values.

`Sharing.structuralWF` names rules 1–3 without the direct-use profitability
rule. The pinned ix compressor can retain a nested entry with one direct use
after sharing its parent, so external catalog parsing uses this common safety
core and then requires exact upstream recompression. It does not weaken
`layer1WF` or make structural well-formedness alone an identity predicate.

## Inlining

The same module provides total `substShares`, `inlineTable`, `inlineExpr`, and
`shareFree` functions. `inlineTable` proceeds left-to-right, so layer-1's
backward-edge rule resolves nested entries in one pass. The implementation is
factored through structural list recursion, and proves table-length
preservation, share-freedom of every inlined entry, and the general theorem

```text
layer1WF table bodies = true
→ body ∈ bodies
→ shareFree (inlineExpr table body) = true
```

as `shareFree_inlineExpr_of_layer1`. The stronger
`shareFree_inlineExpr_of_tableWF` shows that the first three structural rules
plus the body's bounds are sufficient; the ≥2-use profitability condition is
not part of semantic share elimination. `inlineBodies_shareFree` packages the
result at the complete-constant boundary.

## Evaluator coherence

[`Compilatrix/Ixon/Sharing/Eval.lean`](../Compilatrix/Ixon/Sharing/Eval.lean)
defines full-inlining views of evaluator frames, resolution contexts, heads,
and recursive values. Its well-formedness predicates track layer-1 tables and
the expression roots captured by closures and recursor heads. A single fuel
induction proves forward coherence for all six mutually recursive evaluator
functions: `eval`, `evalRef`, `apply`, `applyMany`, `saturate`, and `fire`.
Concretely, every successful well-formed run at a given fuel remains successful
at the same fuel after its store, frame, environment, and expression are fully
inlined, and its result is exactly `Value.inlineSharing` of the original value.

`evalClosed_inlineSharing` packages the expression boundary, and
`evalConst_inlineSharing` packages definition-constant evaluation, including
recursive reference resolution and recursor rule dispatch. These theorems need
only decoder-level sharing well-formedness, not layer-2 compressor canonicality:
canonical spelling determines identity, while layer 1 is enough to preserve
semantics. The inlined context retains the configured quotient identity map;
configured quotient heads are structurally unchanged, and a saturated
`quotV` recursively inlines its stored representative. Erasure composition
reuses this result with the existing share-free
simulation instead of adding `.share` to `PErase`. It is implemented by
`erasure_sim_inlineSharing`; sharing-aware executable
certificates check the original eraser output against the inlined relation.

## Address boundary

[`Compilatrix/Ixon/Sharing.lean`](../Compilatrix/Ixon/Sharing.lean) exposes
`Constant.address?`, which now refuses anything outside the exact layer-2
recompression image. Layer-1 constants remain serializable and decodable for
cheap ingress validation, but do not acquire semantic addresses. A bare
expression exposes only `Expr.serializedHash` from `Hash.lean`: expression
table indices have meaning inside a constant frame, so that hash is explicitly
a local cache key rather than a semantic object address.

`address?` is the transparent theorem-facing predicate for Compilatrix's local
policy. Constructed local values at an executable trust boundary use
`Constant.addressChecked` or `addressCheckedWith`: wire and local checks run
first, then the fully inlined compressor-input size is computed from backward
table-entry sizes without allocating that expansion. Only admitted values
enter exact local recompression and BLAKE3. Failures distinguish wire, local-
semantic, structural-resource, and noncanonical-sharing cases. The exact
counters and defaults live in the [structural budget policy](resource-budgets.md);
`Constant.addressCheckedWith_sound` proves that every success is wire-valid,
locally accepted, locally canonically shared, and exactly BLAKE3 of `ser`.

Production ix catalogs use the parallel
`Constant.addressIxonV2Checked[With]` boundary. It preserves the stored address
only after wire/local validation and exact recompression by the pinned ix
policy. Its soundness theorem yields `Sharing.ixonV2Canonical` rather than the
stronger local `Constant.canonicalSharing`; no normalization or whole-store
readdressing occurs.

Layer 1 is necessary but not sufficient for canonical term identity. Two
different, profitable, acyclic tables can still inline to the same bodies.

## Layer 2: exact compressor image

[`Sharing/Compress.lean`](../Compilatrix/Ixon/Sharing/Compress.lean) implements
the deterministic compressor and defines:

```text
canonical constant := compress (inline constant) == constant
```

The v2 capture baseline is ix commit
`6f18ea907b78d06f7dc0917c43beb385561c35f4`, `Ix/Sharing.lean`. Four directed
cases agree exactly. Two reviewed local strictness deltas remain: structural
rather than pointer keys plus the telescope-maximal filter and final
exact-byte audit remove nested entries that ix retains.
[`sharing-policy.md`](sharing-policy.md) records the clean-archive Lean/Rust
capture, literal constant and six-case byte vectors, the two reviewed deltas,
and policy fingerprint
`19aa227e6be89cbabef37366bdc3a48fcf1d8f856892054511ae6b6fcf1db4ce` under
policy id `compilatrix/ixon-v2-sharing/1`.

The port uses structural representatives as analysis keys; BLAKE3 affects only
ordering, and equal digests fall back to canonical expression bytes. Thus a
collision cannot authorize substitution. Its v2 node preimages include
`Uses`/`Owned` mode bytes. Candidate selection follows ix's decreasing gross
benefit policy, excludes positions that split maximal app/lam/all encodings,
and uses deterministic leaves-first structural postorder. Entries and bodies
are rewritten against structural representatives, so every table reference is
backward by construction.

A final audit prices the table header, entries, and bodies with the real v2
serializer. It removes the first entry whose deletion does not increase bytes,
then restarts until a fixpoint. `deletionLocalOptimal` is checked by
`compress?`, alongside layer 1. Runtime fixtures pin exact compression,
mode-hash discrimination, nested-candidate removal, inline recovery,
determinism, and exact recompression over a varied structural corpus.

`canonical bodies table` inlines, recompresses, and requires exact body/table
equality. `Constant.canonicalSharing` applies that definition to the frozen
`ConstantInfo.exprs` order. `Constant.address?` additionally requires
`DecodeCheck.checkedWF`, so exact sharing alone cannot give a malformed or
wire-truncating constructed value an identity.

The raw `compress?`/`canonical` definitions remain the proof surface.
`compressWithLimit` caps stored compressor input units, while `canonicalWith`
first caps the quadratic layer-1 charge and the computed fully expanded input.
Its default 4096-unit compressor cap is intentionally much tighter than the
wire sequence limit because candidate discovery, structural deduplication,
ordering, rewriting, and the deletion audit repeatedly compare syntax.
Compiled regressions pin exact-boundary acceptance and one-below rejection,
including a linear stored sharing chain with exponentially growing expansion.

`canonical_components` exposes the exact successful compressor result hidden
inside that boolean recognizer. From it,
`canonical_eq_of_expanded_eq` proves that two canonical body/table pairs with
the same expansion have identical bodies and identical tables. This is the
collision-independent uniqueness result for the sharing layer itself.

### Pinned ix exact-image recognizer

External catalog identity uses a second deterministic construction, identified
as
`ix/ixon-v2-sharing@6f18ea907b78d06f7dc0917c43beb385561c35f4`.
`decideIxonV2Sharing` reproduces upstream's candidate rule, including its
per-AST-node effective-size estimate (which overestimates flattened
application/lambda/forall spines), with neither the local maximal-telescope
filter nor the deletion audit. `compressIxonV2?` certifies structural safety
and exact inline recovery; `ixonV2Canonical` accepts only its exact body/table
image.

The construction still keys representatives structurally and uses canonical
expression bytes to break digest ties, so a BLAKE3 collision does not authorize
an expression substitution. Exact-image recognition, rather than the weaker
direct-use condition, prevents alternate acyclic sharing spellings from
minting addresses. All six clean-archive vectors match the captured ix output,
and the bounded Std fixture exercises the path over 54 production constants.
See [`sharing-policy.md`](sharing-policy.md) and
[`corpus-contact.md`](corpus-contact.md).

## Canonical semantic identity

`ConstantInfo.identityShape` replaces every embedded expression root with a
fixed placeholder while preserving the variant, every scalar field, array
shape, mutual-member kind, rule field count, and constructor metadata.
`Constant.InlinedView` combines that shape with the authoritative fully
inlined body array, reference table, and universe table. A proved restoration
left inverse establishes that `identityShape` plus the original expression
enumeration uniquely determines `ConstantInfo`.

These pieces yield two constant-level results:

- `Constant.eq_of_inlinedView_eq_of_canonicalSharing`: two layer-2-canonical
  constants with equal `InlinedView`s are equal as raw constants. This direction
  requires no hash assumption.
- `Constant.inlinedView_eq_iff_address?_eq`: for two `Constant.Addressable`
  values—defined as exact canonical sharing plus the checked writer's
  wire-representability and local-semantic domain—inlined-view equality is
  equivalent to equality of `address?` results, provided
  `Address.Blake3NoCollision (ser left) (ser right)`.

`Blake3NoCollision` is deliberately pair-specific: it says only that equality
of the two actual digests implies equality of those two preimages. It is an
explicit theorem premise, not a new axiom and not the impossible claim that a
fixed 256-bit digest is globally injective. The reverse direction then uses
the proved conditional `Constant.roundtripLaw`; `checkedWF` supplies
`wireWF`, while canonical sharing itself implies the decoder-enforced
`sharingWF` premise.

`compress?` is a proof-producing validation boundary: after running the raw
heuristic it checks layer 1, deletion-local optimality, and propositional
equality between the input and the inlined output. The kernel theorems
`inlineCompressLaw` and `compressCanonicalLaw` discharge the public
`InlineCompressLaw` and `CompressCanonicalLaw` contracts. The latter follows
because recovery rewrites recompression back to the same deterministic call.
The proof path computationally depends on the ledgered native BLAKE3 function
used for ordering, but it assumes no collision resistance or injectivity;
structural representatives authorize every rewrite. Axiom audit separates the
layers: structural rewrite/table and audit-preservation lemmas use only
`propext`/`Quot.sound`; theorems whose types include candidate selection also
record `Classical.choice` and the existing ledgered native hash axiom.

The raw mechanism proof is also compositional. `substSharesList_rewriteWith`
proves structural rewrite/substitution identity; `inlineTable_buildTable` and
`inline_buildCompression` lift it through incremental backward table
construction; each audit deletion carries a checked expansion equality, and
`audit_expanded` composes those equalities. Consequently
`uncheckedInlineLaw` discharges `UncheckedInlineLaw` for every share-free input
whose generated table indices fit `UInt64`. The explicit bound closes an
otherwise hidden Nat→wire-index truncation hole.

The audit has two deliberately separate postconditions. `audit_fixpoint`
proves that the finite deletion search terminates with no semantically
validated non-paying deletion; every accepted deletion is proved to remove one
entry, preserve expansion, and never increase final table size.
`allEntriesPay` is the stronger diagnostic that prices every syntactically
available deletion; the runtime corpus requires it for heuristic outputs.

`compressCertified` retains the audited heuristic whenever layer 1 validates.
If that internal optimization invariant fails, it returns the original
share-free bodies with an empty table. `layer1WF_empty_of_shareFree`, identity
inlining, audit fixpoint, and table-size monotonicity prove this fallback safe.
`compressTotalLaw` therefore discharges `CompressTotalLaw` universally for
share-free, UInt64-index-feasible inputs. Corpus tests compare the public result
to `compressUnchecked` and fail if the fallback activates, so total correctness
does not silently count as ix policy parity. A universal theorem that the
heuristic itself never needs fallback is desirable but is no longer on the
trusted correctness path.

## Proof ladder

| Stage | Obligation | Status |
| --- | --- | --- |
| S1 | decoder enforces layer 1 | implemented and guard-tested |
| S2 | inlining is total/share-free on layer 1 | proved; constant-level corollary included |
| S2a | evaluator commutes with full inlining on successful layer-1-valid runs | proved for all six mutual functions, closed evaluation, and definition constants |
| S2b | sharing factors through the share-free erasure simulation | proved for general and closed evaluation; exact-output program/expression certificates included |
| S3 | deterministic v2 compressor + exact deletion audit | done: recovery, audit fixpoint, index bound, certified totality, ix vectors, reviewed v2 deltas, and policy fingerprint |
| S3x | exact pinned-ix external compressor image | done: structural recovery theorems, effective-size parity, six exact vectors, and 54-constant production contact |
| S4 | checked inline recovery and exact `canonical` recognizer | public recovery, idempotence, and totality theorems proved |
| S5 | canonical inlined equality corresponds to address equality, modulo BLAKE3 assumptions | proved for `Constant.Addressable`, with an explicit pairwise `Blake3NoCollision` premise |

Reference/universe/self-member table-index validation remains separate from
sharing. It is implemented by `DecodeCheck.decodeChecked` for local-policy
bytes and `decodeIxonV2Checked` for pinned-ix bytes; both address gates require
their corresponding local checker. Sharing structure itself closes cycles; an
exact policy image closes sharing-based address splitting, and neither claims
that every other table index is semantically well-formed. Cross-constant
member metadata belongs to store ingestion.

One proof-surface distinction remains explicit. Existing evaluator/inlining
and erasure theorems consume the stronger local `sharingWF`, so an externally
loaded constant that is only `structuralWF` does not automatically inhabit
those theorem APIs even though the executable pipeline can safely resolve its
backward table. Bridging those proofs to the common structural invariant, or
proving an address-preserving whole-store policy conversion, is separate work;
catalog ingress does not claim it by fiat.
