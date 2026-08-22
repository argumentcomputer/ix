# Canonical sharing

Status: layer 1 and share-elimination theorem complete; collision-safe v2
compressor, exact byte audit, and recompression recognizer implemented. The
validated public API has inline-recovery and canonical-fixpoint theorems, and
raw construction plus audit recovery is proved. Public compressor totality is
proved through a certified identity fallback. Canonical inlined identity now
corresponds to address identity on the exact wire-representable domain under an
explicit pairwise BLAKE3 no-collision premise. Successful evaluation is also
proved invariant under full inlining for layer-1-valid stores and constants.
The pinned ix Lean/Rust corpus, intentional v2 deltas, and policy fingerprint
are frozen. Last reviewed 2026-08-14.

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

The constant decoder fails closed on each rule. Positive and negative guards
cover nested backward references, body overflow, self-reference, forward
reference, bare aliases, dead entries, and singleton entries. Raw `Constant`
values remain constructible so those rejection fixtures can be serialized;
accordingly, the constant roundtrip obligation is restricted to
`Constant.sharingWF` values.

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
semantics. Erasure composition reuses this result with the existing share-free
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

Layer 1 is necessary but not sufficient for canonical term identity. Two
different, profitable, acyclic tables can still inline to the same bodies.

## Layer 2: exact compressor image

[`Sharing/Compress.lean`](../Compilatrix/Ixon/Sharing/Compress.lean) implements
the deterministic compressor and defines:

```text
canonical constant := compress (inline constant) == constant
```

The parity baseline inspected for this port is ix commit
`c98bb74106017e518c705b2567f022e89f732393`, `Ix/Sharing.lean`. Deliberate v2
deltas are the mode-bearing node preimages, structural rather than pointer
keys, the telescope-maximal filter, and the final exact-byte audit.
[`sharing-policy.md`](sharing-policy.md) records the reproducible upstream
runner, exact six-case vectors, the two reviewed deltas, and policy fingerprint
`8c712eab0db958befe94bda3a40998debe172243dd5771f62d0cd915074f5097` under
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
`ConstantInfo.exprs` order, and `Constant.address?` is gated by it.

`canonical_components` exposes the exact successful compressor result hidden
inside that boolean recognizer. From it,
`canonical_eq_of_expanded_eq` proves that two canonical body/table pairs with
the same expansion have identical bodies and identical tables. This is the
collision-independent uniqueness result for the sharing layer itself.

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
  values—defined as `wireWF` plus exact canonical sharing—inlined-view equality
  is equivalent to equality of `address?` results, provided
  `Address.Blake3NoCollision (ser left) (ser right)`.

`Blake3NoCollision` is deliberately pair-specific: it says only that equality
of the two actual digests implies equality of those two preimages. It is an
explicit theorem premise, not a new axiom and not the impossible claim that a
fixed 256-bit digest is globally injective. The reverse direction then uses
the proved conditional `Constant.roundtripLaw`; canonical sharing itself
implies the decoder-enforced `sharingWF` premise.

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
| S4 | checked inline recovery and exact `canonical` recognizer | public recovery, idempotence, and totality theorems proved |
| S5 | canonical inlined equality corresponds to address equality, modulo BLAKE3 assumptions | proved for `Constant.Addressable`, with an explicit pairwise `Blake3NoCollision` premise |

Reference/universe/self-member table-index validation is a separate decoder
robustness item. Layer 1 closes sharing cycles and sharing-based address
splitting; it does not claim that every other table index is semantically
well-formed.
