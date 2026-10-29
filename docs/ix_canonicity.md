# Anonymous content and source order in Ix

Ix compiles Lean's declarations in their source-defined block layout. Mutual
members and constructors retain their positions; Lean-generated auxiliaries
are compiled from their stored declarations. Anonymous content still uses
positional variables, normalized universe expressions and canonical sharing.
Whole constants can share an address when their anonymous encodings agree.

This page describes those representation rules. The compiler theorem and its
premises are in [kernel.md](kernel.md#relation-to-compiler-certification);
the byte grammar is in [Ixon.md](Ixon.md). The implementation entry points are
[CompileM](../Ix/CompileM.lean), [CompileDriver](../Ix/CompileDriver.lean) and
the [Rust compiler](../crates/compile/src/compile.rs).

## What determines an address

A constant's address is BLAKE3 of its serialized `Ixon.Constant`: its
declaration payload, sharing table, reference table and universe table.
The representation of sharing is therefore part of the address, even when
two sharing layouts expand to the same expression.

| Source or representation choice | Treatment |
| --- | --- |
| Bound-variable names and ordinary Lean binder annotations | Recorded in expression metadata; anonymous variables are positional |
| Presentation metadata | Kept in the metadata arena where supported; it does not choose anonymous content |
| Semantic source contracts | Resolved before compilation and lowered into anonymous binder, arrow and let fields; changing them can change the address |
| Declared universe parameters | Referred to by position; parameter order remains meaningful |
| Universe-expression spelling | Normalized by `canonUniv`; occurrence patches retain the source spelling |
| Mutual-member and constructor order | Preserved in the block and its indices |
| Existing in-memory DAG sharing | Expanded and normalized by the canonical sharing construction |
| Global references | Lowered to the referenced constants' content addresses |

Whole-constant alpha collapse is retained: names can be aliases of one
anonymous constant. This does not merge positions inside a mutual block.
It also does not make content addressing a decision procedure for mathematical
equivalence or arbitrary definitional equality. Distinct encodings can denote
the same value; equality of hashes alone is not a proof of byte equality.

Reordering a mutual declaration can change member indices, block bytes and
projection addresses. The current compiler makes no invariance claim under
such a permutation. Determinism concerns the same source-defined layout and
compiler configuration, rather than a canonical permutation of isomorphic
blocks.

<a id="60-what-lives-in-each-ixon-block"></a>
## Block contents (canonicity §6.0)

The reference graph and its condensation determine dependency scheduling.
[`sourceMembers`](../Ix/CompileM.lean) and Rust `source_members` order the
members of each block from Lean's metadata:

- An inductive uses its position in Lean's `all` array.
- A definition-like member uses its position in its Lean `all` array.
- A recursor uses its declared family position: the member's `.rec` first,
  then the family's nested `.rec_N` positions.

Names provide the structural tie-break, and the input position breaks an
otherwise exact tie. Hash-map iteration is not the member-order rule.
Constructors retain the order in the source inductive's constructor array.
[`Ix.Cert.LeanOrder`](../Ix/Cert/LeanOrder.lean) proves the ordering facts.

The compiler represents these members as a flat `List MutConst` in Lean and
a flat vector of member references in Rust. Each member contributes one
payload and its metadata. There is no representative/equivalent-member fold.

| Compiled content | Record layout |
| --- | --- |
| A standalone definition, theorem or opaque | A definition record with its kind |
| A standalone recursor | A recursor record |
| An inductive family, including a single inductive | A mutual wrapper containing its inductive payloads |
| A block of several definition-like members or recursors | A mutual wrapper containing every member in source order |
| A member of a mutual wrapper | A definition, inductive or recursor projection at that member's index |
| A constructor | A constructor projection at its owning member's index and its constructor position |

For `n` ordered members, [`MutConst.ctx`](../Ix/Mutual.lean) assigns member
slots `0` through `n - 1`. Constructor slots follow all member slots, in
member order and then constructor order. A definition or recursor contributes
no constructor slots. The context, payload and projection proofs use this
same flat sequence:

- [context lookups](../Ix/CompileCert/Canon/Ctx.lean);
- [payload counts and shapes](../Ix/CompileCert/ProjectionLayout.lean);
- [projection rows and resolution](../Ix/CompileCert/MutualProjections.lean);
- [the complete mutual artifact](../Ix/CompileCert/MutualArtifact.lean).

For example, if `A` has two constructors and `B` has one, in that member order:

| Source | Mutual-context slot | Projection coordinates |
| --- | ---: | --- |
| `A` | 0 | member 0 |
| `B` | 1 | member 1 |
| `A.mk0` | 2 | member 0, constructor 0 |
| `A.mk1` | 3 | member 0, constructor 1 |
| `B.mk` | 4 | member 1, constructor 0 |

The serialized metadata retains its existing grouped shape. The compiler
writes one singleton name group per ordered member in `Muts.all` and the
block-name registration. That encoding boundary does not introduce member
equivalence classes. Members with equal anonymous payloads still occupy
separate positions within the block.

Lean's recursors and auxiliary definitions, including nested-family
declarations, are compiled as inputs. The compiler does not regenerate an
auxiliary family or rewrite its callers to a different block layout. Source
contract resolution, universe normalization and expression sharing are
separate representation operations and remain part of compilation.

## The compilation paths

`ix compile` and `ix compile-lean` use
[`Ix.CompileM.compileCertified`](../Ix/CompileCertified.lean) by default:

1. Prepare the selected source declarations and resolve semantic contracts.
2. Convert them to the canonical `Ix.Environment` representation with
   `Ix.CanonM`.
3. Run `Ix.Cert.compileReport`, including its report checks, at the default
   sharing limits.
4. Check failure accounting and, for contract-bearing input, resource
   validation.
5. Add the role-support closure, certificates and binding with `finalize`,
   then check the finalized artifact before writing it.

`--streamed` selects the checked streamed Lean comparison path. `ix compile
--rust` selects the uncertified Rust compiler; `ix compile-lean --rust-check`
compares its serialized result with the selected Lean path. Rust/Lean byte
parity is differential evidence, not a universal refinement theorem.

Name-only `prove`, `check` and `addr-of` use
`Ix.Check.loadNamedIxonEnv`, whose Lean path is the checked streamed loader
`compileLeanConstsValidated`. Supplying a `.ixe` uses that artifact instead.
These commands do not acquire direct `compileReport` coverage merely by
using the Lean loader. The precise boundary is described in
[the compiler theorem's scope](kernel.md#relation-to-compiler-certification).

## Canonical sharing (§6.7)

<a id="67-canonical-sharing"></a>
Every compiled block is built with
`Ix.Sharing.Exact.canonicalSharingTiered .tagN`, mirrored by Rust's
`canonical_sharing_tiered`. Its roots are the payload expressions in the
order specified by `constantInfoRootExprs`. Existing `Share` occurrences are
expanded before the construction chooses its representation.

The production rule is `sharing-k16-greedy-v1`. Structural subterm identities,
component choices, table order and tie-breaks determine the output. Pointer
caches and hashes accelerate discovery; they do not establish structural
identity. Presentation metadata does not choose sharing, while semantic
contracts already lowered into anonymous expressions remain inputs to it.
Sharing-table entries refer only backward, and the output's expansion
reproduces the input roots' meaning.

The proofs distinguish the production family from the retained exact
reference search. They cover input expansion, output meaning, wire format,
serialized length, representation congruence and conditional idempotence.
On the stated totality domain, a sufficient budget prevents refusal and the
output expands again. [`IxSharingVerify.SufficientBudget`](../IxSharingVerify/SufficientBudget.lean)
provides a polynomial budget in the written input size for backward-referencing
input tables. Larger budgets do not change an already successful result.
This is not a global byte-minimum theorem or a Rust-refinement theorem.

The default compiler fixes its sharing limits. A limit failure refuses the
block; it does not choose another sharing family or publish an intermediate
candidate. See [the format's proof inventory](Ixon.md#what-is-proved-and-what-is-not)
and [sharing integration](sharing-minimum-integration.md) for the exact domains
and repeat-normalization conditions.

## Metadata and decompilation

Metadata carries the presentation needed by the source readers: binder names,
ordinary binder annotations, reference spellings, declaration and family
names, constructor names and level-spelling patches. It is outside a
constant's content hash; metadata fidelity is outside the compiler
correctness theorem. Environment bookkeeping, including the published address map and
anonymous reducibility hints, still has the separate invariants checked by
`compileReport` and `checkFinalized`.

The [Lean decompiler](../Ix/DecompileDriver.lean) selects stored source records
through `originalView`, decodes them, and recomputes inductive flags from the
decoded declarations. The Rust decompiler follows the same source-record
approach. A missing source record is an error; decompilation does not create
a replacement declaration by kernel regeneration. Tests state their fidelity
criteria explicitly. There is no unrestricted compile/decompile bijection or
total byte-fixed-point theorem for arbitrary metadata and artifacts.

### Auxiliary-layout metadata (§10.2)

The `Muts` metadata codec retains its optional `AuxLayout` field. The current
source-order compiler emits `none`. Its existence in the format is not an
instruction to canonicalize or regenerate a block. The `metaSharing` and
`metaRefs` extension tables also retain readers, but the current compiler
does not populate them. `metaUnivs` and `univPatches` are active, as described
below. The [format reference](Ixon.md) specifies their wire domains.

### Decompiler scope (§17.3)

The decompiler reads the stored declaration's own names, members and metadata.
Its reconstruction scope must not substitute a different source declaration
merely because that declaration has the same anonymous address. This is
especially important for alias-specific names and universe spellings.

<a id="106-universe-level-canonicalization-live"></a>
## Universe-level canonicalization (canonicity §10.6)

This is the universe contract cited as **canonicity §10.6** in compiler,
codec, ingress and decompiler comments.

[`Ixon.canonUniv`](../Ix/IxonUniv.lean), mirrored in
[`crates/ixon/src/canon_univ.rs`](../crates/ixon/src/canon_univ.rs), is the
deterministic composition `linearize ∘ subsumption ∘ normalizeAux` on
positional Ixon universes. It normalizes the spelling inside a universe
expression. It does not reorder a declaration's universe-parameter list or
renumber its parameters.

The intermediate representation maps sorted parameter paths to constant and
parameter-offset contributions. A path describes the nonzero parameter
conditions under which its contributions apply. Linearization reconstructs a
level from that ordered representation. Its gate-removal rule requires the
remaining gates to retain their absorber witnesses; dropping that condition
can change a level's value.

The unconditional Lean theorem is value preservation:
[`CanonUnivEmit.canonUniv_eval`](../Ix/CompileCert/CanonUnivEmit.lean) proves
that `canonUniv u` and `u` evaluate equally at every parameter valuation.
[Scope proofs](../Ix/CompileCert/CanonUnivScope.lean) retain the parameter
bounds required by compilation. These theorems do not assert that all
semantically equal universes receive the same bytes. Fixed-point and
absorption properties have their own tested domains; subsumption leftovers
must not be silently treated as an unconditional idempotence or complete
semantic-quotient proof.

### Primary universe tables

Before compiling a block's members, both compilers collect its universe
expressions, apply `canonUniv`, sort by serialized key and deduplicate. The
expression compiler lowers and normalizes each later occurrence through the
same operation and interns its result in that primary table.

The table is marked final after preseeding. A later insertion that would grow
it is a compile error: growth would shift the virtual metadata indices
already issued. [`FinalUniverses`](../Ix/CompileCert/FinalUniverses.lean) and
the preseed proofs cover this boundary. Applying a normalizer while producing
the table is distinct from the decoder's framing and wire-validity checks.

### Restoring the source spelling

When a source occurrence's universe list differs from the normalized list,
the compiler records a patch at that occurrence's metadata-arena index:

```text
UnivPatch = { arenaIdx : UInt64, univIdxs : Array UInt64 }
```

Patch indices use the virtual table `univs ++ metaUnivs`: an index below
`univs.size` names a primary entry; a larger index names the corresponding
entry of `metaUnivs`. The primary table must stay fixed while these indices
are in use.

A patch belongs to an occurrence, not to a canonical table entry. Two source
spellings can normalize to the same entry while needing different restored
syntax. Exact expression/cache keys and separate arena positions preserve
that distinction. Patches for `sort`, external references and recursive
references are consumed by the decompiler and metadata reconstruction path.
Anonymous admission and checking do not read them, so a patch cannot change
the anonymous declaration being checked.

Metadata-mode Rust ingress carries the spelling as an expression decoration
and egress replays it. The decoration participates in metadata expression
identity, rather than the semantic universe-node identity; otherwise an
interned shared universe could overwrite another occurrence's spelling.
Patchless readers retain the documented reconstruction fallback. Fidelity
tests compare the reconstructed syntax under their stated policies.

### Universe regression controls (§17.9)

[`Tests/Ix/IxonUniverse.lean`](../Tests/Ix/IxonUniverse.lean) and the Rust
universe tests cover explicit witnesses, bounded exhaustive inputs, seeded
inputs, normalization properties and mirror parity. The
[level-spelling fixtures](../Tests/Ix/Compile/LevelSpellings.lean) exercise
occurrence restoration through compilation and reconstruction.
The unconditional value theorem remains separate from those finite tests.

## Verification boundaries

The compiler theorem relates the actual `compileReport` result to accepted
quotient Source, under its artifact and role-evidence premises. It includes
the installed environment's syntactic renaming relation and the value
statement quantified over every strong model. It does not add model existence,
total compilation, fixed-fuel checker success, metadata fidelity, general
permutation invariance or universal Rust parity to its conclusion.

The compiler tests cover same-input Lean/Rust parity, schedule independence,
source-order mutual blocks, refusal behavior and reconstruction cases.
[CI tiers](ci.md#test-tiers) identify the suites; exact corpus digests,
timings and final integration receipts belong with the corresponding test
run and release review, not in this representation contract.
