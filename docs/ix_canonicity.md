# Anonymous Canonicity in Ix

This guide states the canonicity target, the source-recovery contract and the
worked layouts. Its implementation baseline is `8bac9c61` (Lean 4.34.1), reviewed
on 2026-10-09. The full compiler theorem remains open. A passing fixture, library
byte comparison or proof audit establishes only its stated result.

Use the [pass and output-contract guide](compiler-passes.md) for the current
pipeline, [certification guide](compiler-certification.md) for checked meaning
claims and their hypotheses, [gate guide](compiler-gates.md) for validation, and
[Ixon](Ixon.md) for the binary representation. Historical section numbers remain
where source comments cite them; implementation recipes live in those guides.

## 1. The Property

Anonymous canonicity requires equivalent presentations to produce the same
canonical content and hence the same content address. The intended quotient
removes:

- Bound-variable and declaration names, through the prescribed reference map.
- Binder information, ordinary expression metadata and other presentation data.
- Source member order within mutual blocks and the resulting source auxiliary
  numbering, through the corresponding canonical classes and positions.
- Non-canonical universe-level spellings under the specified level quotient.
- Expression sharing in memory, allocation order and compiler scheduling.

In the original address notation, the target is

```text
addr(c₁) = addr(c₂)  ⇔  c₁ and c₂ have the same anonymous canonical content.
```

This specifies a structural quotient. The quotient does not identify arbitrary
mathematically equivalent programs or arbitrary theorem proofs. The ordered
universe parameters and de Bruijn indices still distinguish their respective
roles. Type and value structure, constructor structure and computationally
relevant flags remain subject to the declared format and comparison contracts.
Semantic-contract metadata has its own lowering into primary content and is
excluded from this presentation erasure. The hashing and reference hypotheses
of individual proofs remain explicit.

**Faithfulness comes first.** A transformation must preserve the source name's
specified kind, type and value contract. If a canonical presentation cannot be
produced by a supported faithful transformation, the compiler keeps the faithful
baseline and records its reason, or refuses the block when it cannot produce
that baseline. A retained baseline need not share the address of a canonical
form. Proof-justified forms at `c._ix` coexist with the source name's baseline;
they do not license changing every caller to `_ix`.

These qualifications describe the current implementation without replacing the
full target by the passing fixtures. The required general result still includes
representative independence, total generators and image construction on the
original `Dom`, every source name's faithfulness, and model pull-back through the
complete production driver. The
[remaining compiler proof obligations](compiler-certification.md#17-remaining-general-compiler-proof-obligations)
state those endpoints.

## 2. Why It Matters

A proof about a compiled declaration is tied to its content address. If two
presentations covered by the structural quotient produce different canonical
content, their proofs cannot be reused at the same address.

For example, reordering the declarations of a mutually recursive `Tree` and
`Forest` should preserve the canonical classes, the corresponding member
addresses and the canonical recursor layout. The source member order and Lean's
auxiliary suffixes remain recoverable separately. This needs a correspondence
for every affected constructor, recursor, image and user, as well as equal
primary inductive bytes.

## 3. The Epimorphism / Isomorphism Pair

The design has two complementary maps:

```text
Source ──compile──→ Canonical content
Source ──compile──→ Canonical content + source-recovery information
```

The first is many-to-one and is onto its image: alpha-equivalent declarations
can share canonical content. The second aims to recover the original supported
`ConstantInfo` presentation. Its recovery data includes metadata, the original
address-and-metadata pairs in `Named.original`, and source occurrences retained
by Pass 3. An original address is provenance; its declaration blob need not be
stored. Recovery can therefore require regeneration as well as metadata replay.

Source recovery is a stronger requirement than equality of one block address.
It must preserve the source names, kind, telescope, binders, metadata, universe
spellings and auxiliary numbering covered by the output contract. Source ranges
and editor hygiene traces are outside that presentation contract. Docstring
persistence is still separate work (§17.5); it is not already supplied by a
`ConstantInfo` roundtrip.

Changed blocks make the two readings visible: canonical recursors can coexist
with source-named image definitions. Source recovery uses the recorded source
provenance and recovery paths; transformation checking must also inspect the
transformed stored term.
The complete general inverse/faithfulness theorem is not established by this
design diagram or by one successful roundtrip.

## 4. Four Operational Invariants

### 4.1 Content-address invariance under declaration permutation

Corresponding members of structurally equivalent blocks must receive the same
canonical addresses under the prescribed member/reference correspondence.
Source-first member names, source `_N` positions and source-order motives or
minors must not determine the canonical payload.

### 4.2 Canonical round-trip fixed point

The canonical reading, recompiled under its intended input/name convention,
must reproduce the same canonical content. Source-faithful materialization has
a separate source-projection roundtrip: an artifact may also expose reserved
canonical declarations that were never source inputs. Passing all materialized
names back as fresh source can correctly trigger the `_ix` input refusal.
[ImportIxe](../Tests/Ix/ImportIxe.lean) exercises this distinction, source-root
stability and certified canonical recursors.

### 4.3 Lean-visible `_N` numbering stability

Lean's source `_N` suffixes identify positions chosen by its source expansion.
Canonical expansion can reorder or merge those positions. Decompilation must
retain the source correspondence so downstream source declarations resolve the
same recursors and auxiliary families (§6.4).

### 4.4 Kernel-side canonicity validation

The executable checkers validate stored canonical order independently of source
metadata. Their fast adjacent-member check accepts strong strict `Less`, rejects
strong `Greater` and uncollapsed `Equal`, and falls back to full refinement on
**either** weak `Less` or weak `Greater`. The fallback must recover the same
ordered singleton classes. The distinction matters when mutual references
supply a provisional comparison.

Nested auxiliaries are rediscovered from canonical members in discovery order,
with no auxiliary sort. Stored recursors are checked at the corresponding flat
positions. This validation is distinct from proving that compiling every source
block preserves its meaning. See the [kernel guide](kernel.md),
[Lean implementation](../Ix/Tc/CanonicalCheck.lean) and
[Rust implementation](../crates/kernel/src/canonical_check.rs).

## 5. What Is Erased vs. What Is Preserved

| Data | Canonical content / source recovery |
| --- | --- |
| Binder names and `BinderInfo` | Erased from primary expressions; retained in metadata. |
| Ordinary `Expr.mdata` | Erased from primary expressions; its supported KV data survives in metadata. Semantic-contract metadata has a separate lowering into primary content. |
| Reference names and source member order | Content references use the compiled mapping; source spelling and class/member metadata retain the presentation. |
| Universe expressions | `canonUniv` selects primary levels; occurrence patches retain non-canonical spellings. Universe parameter positions remain structural. |
| Source auxiliary suffixes | Canonical flat positions determine the generated layout; persisted source layout supports recovery. |
| Reducibility hints | Exact per-name hints are retained in `Named.hints`, alongside the environment's merged anonymous hints. |
| Rewritten source forms | `Named.original` retains source-form address and metadata, without requiring its blob to be stored; Pass 3 inline records retain rewritten source occurrences. |
| In-memory DAG sharing | Rebuilt by canonical sharing; memory identity does not define the canonical layout. |

Free and metavariable nodes in a declaration's serialized body are refused,
rather than erased. Safety/recursion flags are not decorative names. The
[output contract](compiler-passes.md#11-the-output-contract) gives the precise
kind/type/value and failure behavior, including the separately documented
promotion-path exception at this baseline.

## 6. The Canonical Block Layout

### 6.0 What lives in each Ixon block

For `n` primary equivalence classes and `m` canonical nested auxiliaries:

```text
primary inductive block: Muts([Indc(rep₀), …, Indc(repₙ₋₁)])
recursor block:          Muts([Recr(primary₀), …, Recr(primaryₙ₋₁),
                              Recr(aux₀), …, Recr(auxₘ₋₁)])
```

Constructors are embedded in each `Indc`. Nested auxiliary inductives are
transient inputs to generation; they are **not** extra primary `Indc` members.
Their recursors occupy the auxiliary segment of the recursor block.

The Prop-level `below` inductives and their `below.rec` recursors have their own
family blocks. Other auxiliaries (`casesOn`, `recOn`, Type-level `below`,
`brecOn`, `.go`, `.eq`) are emitted by strongly connected component: a singleton
is its own constant, and a genuine cycle is a block. There is no universal
per-kind block containing every auxiliary.

### 6.1 User-class ordering

Structural comparison and refinement determine primary classes and their
canonical order. Names select representatives within equal classes under the
specified tie-break. A name tie-break is not a substitute for proving that the
emitted declaration is independent of that representative. Aliases retain their
own source-recovery information while sharing the appropriate canonical member.

### 6.2 Nested-aux section ordering

Canonical expansion walks canonical representatives and their constructors,
opens external groups in their compiled class order, and uses a FIFO queue for
newly discovered auxiliaries. Repeated matching occurrences reuse an auxiliary.
**The auxiliary order is this canonical discovery order.** No subsequent
structural/content-hash sort is run under `Rules.compiler`.

The source walk may discover a different order; §6.4 records its correspondence.
The historical function name `sort_aux_by_partition_refinement` does not imply
that the production canonical walk sorts its auxiliary segment. See
[the Pass 1 expansion](../Ix/Compile/Canon/Nested.lean) and the
[nested layout contract](compiler-passes.md#25-nested-auxiliaries-in-discovery-order-def-25-d2).

Discovery and ownership theorems describe successful expansion under their
stated hypotheses. General paired expansion, representative independence and
production refinement must still be supplied where the full compiler proof
needs them; discovery order alone does not discharge those obligations.

### 6.3 Recursor binder layout

```text
∀ parameters, motives, minors, indices, major, target motive …
motives: primary classes, then canonical-discovery auxiliary positions
minors:  constructors of those primary classes, then of those auxiliaries
rules:   this recursor's own flat member's constructors, in their order
```

Each rule selects the corresponding minor from the global minor band.
Dependent binder indices and recursive arguments must follow that layout.
Permutation of a list of names alone does not establish recursor correctness.

### 6.4 The `rec_N` / `below_N` / `brecOn_N` name mapping

The source layout records `perm[source_j] = canonical_i`. Several source
positions can reach one canonical auxiliary after collapse. Source-facing names
retain their Lean positions, while canonical display declarations use the
canonical layout. Recursors and the applicable `below`/`brecOn` families must
use the same correspondence; one family's successful lookup is insufficient.
Out-of-component positions use an explicit sentinel and cannot be indexed as
members of this canonical block.

### 6.5 Evaporated auxiliaries

Splitting Lean's original mutual group into canonical SCCs can move an auxiliary
outside a component or change whether it must be generated there. The mapping,
absence and evaporation flags must reflect that relationship. An absent position
is not permission to substitute a similarly named recursor. The
[nested specification](../Ix/CompileCert/Canon/NestedCanon.lean) and name-map clauses
retain their matching, bound and ownership hypotheses.

For example:

```lean
mutual
  inductive A | mk : List B → List C → A
  inductive B | leaf : B
  inductive C | leaf : C
end
```

The dependency graph splits into `{A}`, `{B}` and `{C}`. In A's canonical
component, `List B` and `List C` no longer contain a member of that component,
so those fields do not require its nested auxiliaries. The original mutual
group's source recursors still need faithful Pass 3 images and source-layout
recovery. Evaporation does not authorize changing their telescopes by aliasing
them to the new component's recursors. The
[evaporation contract](compiler-passes.md#26-evaporation)
lists the complete conditions.

### 6.6 The content-address recipe

A block's ordered members, references, canonical universe table and canonical
sharing representation determine its serialized payload. The source auxiliary
permutation and presentation metadata do not enter that payload. Any declaration
that changes the actual source unit, type or value must be assessed under the
[output contract](compiler-passes.md#114-identity-requirements-a-checker-may-rely-on),
rather than assumed to be a cosmetic change.

### 6.7 Canonical sharing

Both compilers reconstruct the sharing representation from expanded expression
roots in their fixed order. Structural IDs determine identity; hashed lookup
and pointer caches accelerate discovery. The selected stored set, topological
order and index widths have deterministic tie-breaks, and stored references
point backwards.

The checked sharing results concern runs on the canonical DAG: phase-1
minimality, subsequent phase specifications, serialized length and wire validity.
Idempotence retains its output-expands-to-input hypothesis. The input-to-DAG
bridge and Rust implementation agreement are separately tested; a global byte
minimum is not claimed. These boundaries and the exact theorems are in
[Ixon's sharing specification](Ixon.md#sharing-system) and its
[proof-status section](Ixon.md#what-is-proved-and-what-is-not).
A failed sharing construction is a block error, with no resource-dependent
alternative encoding.

## 7. The Compile Pipeline

Both compilers use Pass 1 canonicalization, Pass 2 generators and Pass 3's
faithful image rewrite, optimizations and clique handling. The current order,
recognizers, faithful fallbacks and emission rules are maintained in
[compiler-passes.md](compiler-passes.md); backend ownership is in
[compiler-rust.md](compiler-rust.md). These stages' general proof obligations are
not replaced by their implementation descriptions.

## 8. Call-Site Surgery (history)

The legacy call-site surgery was deleted from both compilers. The format still
reads its historical `CallSite`/`EtaCallSite` metadata; current compilation writes
Pass 3 source-occurrence records. The former algorithm is available in version
history and is not a second supported compiler mode.

## 9. The Decompile Pipeline

Source recovery and reading the transformed/canonical declaration serve different
purposes. Evaluating the reconstructed source value does not independently test
the transformed value. The validation guide keeps these checks separate.

### 9.2 The `Named.original` field

`Named.addr` identifies the stored compiled declaration. For an image or promoted
regenerated auxiliary, `Named.original` carries the independently compiled source
form's address and metadata. It is source-name-specific: an alias cannot borrow
a different declaration's original merely because both compiled addresses agree.
The original declaration blob need not be stored: original-form compilation of
regenerated auxiliaries deliberately omits it. The decompiler handles that case
through regeneration and the recorded metadata, rather than assuming the address
can always be dereferenced to source bytes.
Pass 3's `_ix.inline` and `_ix.inline_meta` additionally preserve rewritten source
occurrences through `metaSharing`. See
[the actual record contract](compiler-passes.md#113-the-records-the-output-carries).

### 9.3 Mutual-block reconstruction

Reconstruction needs the source `all` lists, original forms, canonical block
membership and persisted nested layout. It must preserve the declared names and
source kinds while handling additional reserved canonical declarations. A
successful check of one reconstructed constant is not the full block roundtrip.
The [materialization tests](../Tests/Ix/ImportIxe.lean) cover collapsed and
non-collapsed neighbours; broader generator and decompiler correspondence remains
part of the general work in §17.

## 10. Metadata Required for Round-trip

The [Ixon format](Ixon.md) is the field/encoding reference. Metadata does not
justify a transformed term's typing or meaning; the checker must validate the
relevant actual content.

### 10.2 Aux layout persistence

`ConstantMetaInfo::Muts.aux_layout` holds the optional `AuxLayout`, including
source-position permutation and source constructor counts. The decompiler
rehydrates this source/canonical correspondence into its lookup. Its source
auxiliary recovery path nevertheless passes no layout override to recursor
generation, preserving source-walk order; §17.2 records the remaining distinction.
The
out-of-SCC sentinel stays distinct from a valid canonical index. This persisted
relationship is why source suffixes survive a canonical reorder or collapse.
See [metadata types](../crates/ixon/src/metadata.rs).

### 10.5 Metadata name canonicalization at alias occurrences

Canonical content can merge equal subterms or declarations while their source
occurrences retain different reference names. Metadata remains aligned to the
expanded occurrence tree; a sharing reference is transparent to that alignment.
When a rewritten occurrence has a source ancestor, its spelling comes from that
ancestor, not from a hash-table entry's arbitrary alias. Synthesis-created
references with no source ancestor, such as primitives and generated-family
references, use the algorithm's prescribed names. The metadata/original/inline
controls in the gate guide exercise this boundary.

### 10.6 Universe-level canonicalization

The intended universe quotient is kernel semantic equality of levels with
parameter positions fixed. The current normalizers have known subsumption
leftovers: for example, `max (v+1) (imax (imax 2 u) v)` retains a redundant
constant at `[u, v]`. General fixed-point and class-independence claims therefore
remain obligations. The [Rust property checks](../crates/ixon/src/canon_univ.rs)
and [Lean property checks](../Tests/Ix/Tc/Unit.lean) qualify their idempotence,
roundtrip, class-stability and absorption checks by absence of these leftovers;
they do not narrow the full compiler theorem's original domain.

`canonUniv` selects the primary universe spelling. `metaUnivs` and arena-indexed
`univPatches` retain non-canonical source spellings at each occurrence; a constant
occurrence's patch carries its entire universe-argument list. Two occurrences
sharing a primary table entry can therefore recover different source spellings.
The ordered universe parameters keep their roles, as the examples below show.

## 11. Sort Algorithms

[Pass 1's specification](compiler-passes.md#2-canonical-form-defined) owns the
comparator, refinement and tie-break details. Canonical nested auxiliaries use
§6.2's discovery walk. Updating a comparator requires the relevant Lean/Rust,
refinement, kernel, parity and library-byte checks; a library observation alone
does not prove comparator equivalence on arbitrary inputs.

## 12. Worked Examples — Single Constants

### 12.1 α-rename

```lean
def f₁ : Nat → Nat := fun x => x + 1
def f₂ : Nat → Nat := fun y => y + 1
```

Schematic compiled expression (elaborated implicit/type/instance arguments
omitted):

```
Ixon Expr for both:
  Lam( Ref(idx=Nat), App(App(Ref(idx=HAdd.hAdd), Var(0)), Nat(1)) )
```

The binder names `x` and `y` live in
`meta.arena[Binder { name: Address(x|y), info, … }]` — separate arena
entries, distinct addresses — but both addresses are outside the hash
input. `addr(f₁) == addr(f₂)`.

### 12.2 mdata strip

Construct two input expression trees with Lean's metaprogramming API:

```lean
def plain : Lean.Expr := .lit (.natVal 7)
def decorated : Lean.Expr :=
  .mdata (({} : Lean.KVMap).insert `displayNote (.ofString "example")) plain
```

Used as values of otherwise identical input declarations, these trees produce
the same primary expression. The ordinary `displayNote` wrapper survives in
source metadata. This example concerns those constructed trees, rather than
compiling the metaprogramming definitions above as declarations about `Lean.Expr`.
Semantic-contract metadata follows its separate lowering and cannot be dropped
under this rule.

### 12.3 Universe permutation (non-equal)

```lean
def h₁.{u, v} : Sort u → Sort v → Sort (max u v) := …
def h₂.{u, v} : Sort v → Sort u → Sort (max u v) := …
```

With the displayed parameter lists fixed, their binder domains refer to
different parameter positions. Those positions are part of the structural
signature; this example does not permit a permutation of them. Canonicity isn't
"equal up to any renaming" — it's equal up to the *specific*
equivalences in §1.

Universe normalization (§10.6) keeps this boundary: the parameter *list*
order stays structural even as spellings *inside* level expressions
(`max u v` vs `max v u` at an occurrence) are quotiented.

### 12.4 Level-spelling twins (equal content, patched presentation)

```lean
axiom twin₁.{u, v} : Sort ((max u v) + 1)      -- succ-lifted spelling
axiom twin₂.{u, v} : Sort (max (u+1) (v+1))    -- Géran-canonical form
```

These spellings have the same canonical level (§10.6): `canonUniv` maps both spellings to
`max (u+1) (v+1)` — the Géran linearization distributes `succ` into
`max`, the opposite direction from the kernel's `mk*` constructors —
so otherwise matching declarations intern the same primary `univs` entry and
`addr(twin₁) = addr(twin₂)`. Presentation survives in metadata only:
`twin₁`'s meta carries `metaUnivs = [(max u v) + 1]` and a
`univPatches` entry keying its `sort` occurrence's arena root to
virtual index `univs.size + 0`, while `twin₂` (already canonical)
carries neither. Decompile replays the patch and reconstructs each
source spelling exactly (strict phase-5/7b gates); anonymous ingress
never reads it, so checking and hashing see one level.

The same shape covers `const` level args (`@f.{(max u v) + 1}` — the
patch then carries the FULL argument list, canonical entries riding
along positionally) and the commuted twins (`max v u` → `max u v`).
A constant containing BOTH a weird spelling and its canonical form is
exactly why patches key on arena occurrences rather than table
entries: the two occurrences share one (deduped) table entry but keep
distinct arena roots.

## 13. Worked Examples — Mutual Blocks

The fixtures in [Mutual.lean](../Tests/Ix/Compile/Mutual.lean) exercise the cases
below. Unless otherwise noted, every example declares the same block
twice in different order; the assertion is that **both declarations
hash to the same block address**.

### 13.1 `AlphaCollapse` — isomorphic mutual recursion

```lean
mutual
  inductive A | a : B → A
  inductive B | b : A → B
end
```

`A` and `B` are structurally identical: each has one constructor
taking the *other* inductive as its single field. `sort_consts`
reports a single equivalence class `[A, B]`; the canonical block
contains exactly one `Inductive` member (the class representative),
and both names `A` and `B` resolve to `IndcProj { block, idx: 0 }`.
`addr(A) == addr(B)`.

### 13.2 `OverMerge` — SCC with non-equivalent members

```lean
mutual
  inductive A | a : B → A
  inductive B | b : A → A → B      -- two A fields; structurally distinct from A
  inductive C | c : A → B → C      -- external: references both
end
```

`A` and `B` are in one SCC but **not** alpha-equivalent (`B` has an
extra field). `sort_consts` produces two classes `[A]` and `[B]`;
`C` lives in a separate SCC. The block stores both members;
`addr(A) ≠ addr(B)`.

### 13.3 `OverMerge.reordered` — permutation invariance

```lean
mutual
  inductive B2 | b : A2 → A2 → B2
  inductive C2 | c : A2 → B2 → C2
  inductive A2 | a : B2 → A2
end
```

Same structure as `OverMerge` above, declared in a different source
order. `sort_consts` sees the same SCC and structural classes.
`addr(A2) == addr(A)` after alpha-collapse on the alias map.

### 13.4 `AlphaCollapse3` — longer cycles

```lean
mutual
  inductive A | a : B → A
  inductive B | b : C → B
  inductive C | c : A → C
end
```

All three are alpha-equivalent (cycle of length 3). `sort_consts`
collapses them to one class `[A, B, C]` with one representative.
`addr(A) == addr(B) == addr(C)`. The length-4 cycle `AlphaCollapse4`
(`W→X→Y→Z→W`) is the same shape.

### 13.5 `AlphaCollapse` with recursive-self collapse

```lean
mutual
  inductive A  | a  : B  → A
  inductive B  | b  : A  → B
end

mutual
  inductive A' | a' : A' → A'   -- self-ref, same shape under collapse
end
```

The self-referential `A'` has the **same** canonical form as the
mutual pair — because under alpha-collapse, both `A` and `A'` compile
to `Inductive with one ctor of domain (Rec 0)`. The test verifies
`addr(A) == addr(A')`.

## 14. Worked Examples — Nested Inductives

These diagrams distinguish the primary stored block from the transient flat
expansion used to generate recursors. Auxiliary suffixes below are illustrative
source/display names; the structural positions are what the layout specifies.
The fixtures are in [Mutual.lean](../Tests/Ix/Compile/Mutual.lean).

### 14.1 `NestedSimple` — single inductive nesting

```lean
inductive Tree where
  | leaf : Nat → Tree
  | node : List Tree → Tree
```

The flat expansion has `Tree` and one `List Tree` auxiliary:

```text
primary stored block: Muts([Indc(Tree)])
transient flat types: [Tree, nested List Tree]
recursor block:       Muts([Recr(Tree), Recr(nested List Tree)])
```

The auxiliary recursor occupies position 1 of the recursor block. Its auxiliary
inductive is not a second member of the primary stored block.

### 14.2 `NestedAlphaCollapse` — dedup across aliases

```lean
mutual
  inductive TreeA
    | leaf | fromB : TreeB → TreeA | node : List TreeA → TreeA
  inductive TreeB
    | leaf | fromA : TreeA → TreeB | node : List TreeB → TreeB
end
```

The primary class merges `TreeA` and `TreeB`. Under its alias substitution,
`List TreeA` and `List TreeB` become the same nested occurrence. The primary
block has one `Indc(rep)`; the transient flat layout has `rep` plus one nested
auxiliary, and the recursor block has the corresponding two positions.

### 14.3 `NestedAuxOrdering` — the canonicity test

```lean
mutual
  inductive A | mk : Array B → Option C → List A → A
  inductive B | mk : Array C → Option A → List B → B
  inductive C | mk : Array A → Option B → List C → C
end

mutual
  inductive C2 | mk : Array A2 → Option B2 → List C2 → C2
  inductive A2 | mk : Array B2 → Option C2 → List A2 → A2
  inductive B2 | mk : Array C2 → Option A2 → List B2 → B2
end
```

The required correspondence is `A↔A2`, `B↔B2`, `C↔C2`, with equal canonical
primary and recursor block content. Canonical classes determine the walk's
starting order; constructor traversal and the FIFO expansion then determine
canonical auxiliary discovery order. The source declaration order can change
Lean's `_N` numbering, and `AuxLayout` records that correspondence. No
`sort_aux_by_content_hash` step assigns the canonical order.

The test concerns the corresponding generated declarations and positions as
well as the primary member address. It is finite evidence for this fixture,
not a proof that every nested/collapsed block has the required correspondence.

### 14.4 `NestedAuxOrderingAlpha` — collapse with nested discovery

```lean
mutual
  inductive A | mk : Array B → Option A → A
  inductive B | mk : Array A → Option B → B
end
```

After primary collapse, the walk sees `Array rep` and `Option rep`. Nested
expansion may expose further external dependencies, so source container names
alone are not a complete census of the flat auxiliary list. The exact positions
come from opening the external groups and completing the canonical FIFO walk.
The stored primary block still contains only `Indc(rep)`; the recursor block
contains that primary recursor followed by the discovered auxiliary recursors.

## 15. Invariants by Module

The [pipeline map](compiler-passes.md#11-the-passes) and
[Rust module map](compiler-rust.md) identify the executable owners. The
[certification guide](compiler-certification.md#16-l1-theorem-42-at-pass-1s-level)
gives L1's actual clauses and hypotheses. In particular, comparison success,
name/address relations, environment well-formedness, source graph completeness
and name-map separation are explicit obligations where their theorems use them.
An audit on the standard axioms does not make those hypotheses automatic.

## 16. Validation

Use [compiler-gates.md](compiler-gates.md) for the exact commands, suite defaults,
reference files, coverage records and limitations. The relevant evidence includes
alpha/permutation twins, nested and mutual generators, source/metadata recovery,
canonical roundtrips, independent kernel checks, Lean/Rust parity, deterministic
scheduling and both-library byte checks. Negative controls retain valid
neighbours. No test's scope is expanded into a universal claim.

The [canonicity fixtures](../Tests/Ix/Compile/Canonicity.lean),
[mutual fixtures](../Tests/Ix/Compile/Mutual.lean),
[import/materialization suite](../Tests/Ix/ImportIxe.lean), and
[sharing specification](Ixon.md#sharing-system) provide the corresponding entry
points. Historical test counts and old toolchain timings are not current gates.

## 17. Open Work

The full general theorem still requires all inputs of its original domain,
representative independence, total generators, nested/source correspondence,
image construction, optimizer/clique refinement and driver/emission composition.
Every source name must satisfy its meaning contract, and the model pull-back must
follow for the full output. Successful library certification and the conditional
L2/L3 proof checkpoints leave those general obligations intact.

### 17.1 Production invariant bridges

Derive the name, reference, protected-allocation, graph and reader invariants
needed by the actual compiler calls. General callback statements retain their
original domains; supporting finite-source adapters do not replace them.

### 17.2 Decompile canonical-path unification

Layout-aware generation and the canonical/source reconstruction paths must agree
on the real collapsed and nested families. Retain the checks around missing
layout, source aliases, canonical positions and complete `ConstantInfo`
reconstruction. The source auxiliary recovery path still constructs singleton
classes from the source inductives, even when compilation collapsed equivalent
classes, and passes no recursor-layout override to preserve source-walk order.
Reconciling that path with canonical classes and the persisted layout remains
implementation and proof work; the complete correspondence theorem is open.
See [the current decompiler](../crates/compile/src/decompile.rs) and §9.3.

### 17.3 `check_decompile` scoping

Keep ordinary source-faithful recovery checks separate from checks of the actual
canonical/transformed declarations. Read the current gate guide's phase scopes;
source metadata replay must not conceal a transformed-value failure.

### 17.4 Nested mapping regression guards

Keep multi-SCC, out-of-component, nested-collapse and reordered-source controls,
including repeated generation and full source-position/name coverage. Removing
a failing case or weakening its comparison does not resolve its obligation.

### 17.5 Docstring persistence

Docstrings are separate from the supported `ConstantInfo` metadata roundtrip.
Persistence would need explicit ingestion, format and replay work; this guide
does not describe it as implemented.

### 17.6 Remaining compiler repairs and release checks

The source baseline still has the documented structural-clique fallback,
projection/value-check boundaries and promotion exception. Follow their precise
contracts in [compiler-passes.md](compiler-passes.md). Reviewed repairs must retain
the appropriate failure controls, ownership and both-library gates. Neither
this document update nor approval of a repair claims that it has landed.

## 19. Cross-References

| Reference | Purpose |
| --- | --- |
| [Compiler passes and output contract](compiler-passes.md) | Executable pipeline, transformations, fallbacks, names and records. |
| [Compiler certification](compiler-certification.md) | W/W+/S, proved conditional results, trust and remaining general obligations. |
| [Compiler gates](compiler-gates.md) | Tests, parity, byte checks and evidence limits. |
| [Rust compiler](compiler-rust.md) | Backend organization and correspondence boundaries. |
| [Ixon](Ixon.md) | Binary format, metadata, universe patches and canonical sharing. |
| [Kernel](kernel.md) | Admission and kernel-side validation. |
