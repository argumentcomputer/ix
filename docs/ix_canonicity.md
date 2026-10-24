# Anonymous Canonicity in Ix

> This document describes **anonymous canonicity**, the intended
> content-addressing invariants of the Ix compiler. It covers
> the property, the compile/decompile pipeline and metadata,
> worked examples from `Tests/Ix/Compile/Mutual.lean`, a testing plan,
> and implementation limitations. Retired call-site surgery is historical (§8);
> the current compiler uses Pass 3 images (§7). These are implementation
> contracts, not a completed compiler value-preservation theorem; see
> [the certification boundary](kernel.md#relation-to-compiler-certification).
>
> Companion document: [`docs/Ixon.md`](./Ixon.md) (binary format
> reference).

---

## 1. The Property

For corresponding constants in successfully compiled dependency closures,
**anonymous canonicity** targets the following invariance under the same
canonicalization rule:

```
    c₁ and c₂ differ only in supported erased choices:
      - local variable names
      - presentation mdata, ordinary Lean BinderInfo, docstrings, source positions
      - source declaration order within mutual blocks
      - nested-inductive aux discovery order
      - hygiene annotations on Name components

    ⇒ canonical payload bytes(c₁) = canonical payload bytes(c₂)
    ⇒ addr(c₁) = addr(c₂)
```

An address is BLAKE3 of the payload bytes. Equality of hashes is not a
proof of equality of bytes, and equality of canonical encodings is not a
general test for mathematical equivalence. Distinct encodings can denote
the same value. Preservation of the source value by compilation is a
separate proof obligation.

Semantic contracts are excluded from these erased choices. Reserved
`ix.contract` source mdata lowers into the anonymous binder fields: usage,
ownership, locality, arrow-result contracts and let borrow kind. Changing
those fields can change payload bytes and addresses (§5.1).

Informally: **renaming a bound variable, reordering a mutual block, or
adding ordinary presentation mdata does not move the content address.**
If it does, canonicity is broken and the property fails — which in turn
breaks the zk-PCC story, because two parties compiling the same library
would produce different hashes and could not share proofs.

The address hashes the constant's serialized bytes, and those bytes include
its sharing table and every `Share` occurrence. Since format version 4, the
sharing representation is itself canonical: a function of the constant's
anonymous expressions (§6.7). So the property also holds modulo:

- how the expression DAG happens to be shared in memory;
- the order in which the compiler built it;
- which compiler ran, Lean or Rust.

The Lean sharing proofs cover successful input expansion and output meaning,
representation congruence and conditional idempotence (§6.7). They do not
prove this whole compiler contract. Agreement of the Rust implementation
with the Lean compiler is tested, not a universal refinement theorem.

## 2. Why It Matters

Ix is a **zero-knowledge proof-carrying code** platform. A proof that
`constant X typechecks` is really a proof about `addr(X)`. If two
developers compile the same mathematical library and get different
addresses, the proof from one developer doesn't verify against the
other's hash — the whole interop story collapses.

The failure mode isn't subtle. Consider:

```lean
-- Developer A writes:
mutual
  inductive Tree  | leaf | node : List Tree  → Tree
  inductive Forest | nil  | cons : Tree → Forest → Forest
end

-- Developer B writes the same library but declares:
mutual
  inductive Forest | nil  | cons : Tree → Forest → Forest
  inductive Tree   | leaf | node : List Tree  → Tree
end
```

Both define the same mathematical objects. If `addr(A.Tree) ≠ addr(B.Tree)`,
a proof of `X : Tree` from A cannot be used by B's verifier. **Canonicity
restores this property** by erasing source order, binder names, and
metadata from the hash input.

## 3. Canonical Content and Source Reconstruction

The design separates anonymous content from source reconstruction:

```
Source ──(successful compile)──→ Canonical content
                                 + source metadata and original records
```

- **Canonical content is many-to-one.** Alpha-equivalent sources can share
  a payload, while the name map retains their separate source identities.
- **Source reconstruction uses additional data.** Binder names, presentation mdata,
  source member order and original records support the implemented
  decompile paths (§9). Source ranges and hygiene are outside that
  roundtrip contract (§5.3), and docstring persistence is still open
  (§17.5). There is no unrestricted bijection or total roundtrip theorem.

This pair is the entire design:

```
Lean  ──compile──▸  Ixon (canonical)
                    │
                    │    bytes flow through kernel / ZK pipeline
                    │    using only the canonical form.
                    │
                    ▼
Lean' ◀─decompile─  Ixon + Metadata
```

The roundtrip tests compare reconstructed `ConstantInfo`s under their
stated fidelity checks. Missing source records or malformed metadata can
make decompilation fail; metadata is not certified by the Ixon checker.

## 4. Four Operational Invariants

The abstract property in §1 decomposes into four concrete invariants
that every stage of the pipeline must uphold:

### 4.1 Content-address invariance under declaration permutation

Two Lean blocks whose inductives, constructors, and field types are
pairwise-equal **modulo source order** must compile to the same Ixon
block address, and each constituent inductive / constructor / recursor
must share a content address with its counterpart.

**Corollary.** The canonical block layout cannot embed any information
specific to a Lean source-walk: no aux names like
`<InductiveVal.all[0]>._nested.List_1` inside the canonical content, no
source-indexed `rec_N` positions inside bodies, no source-order
motive / minor binder positions.

### 4.2 Canonical round-trip fixed point

```
Lean(source₁)            → compile   → Ixon₁
Ixon₁                    → decompile → Lean(decompiled)
Lean(decompiled)         → compile   → Ixon₂      // must equal Ixon₁
```

Decompile must produce a Lean representation that, when recompiled,
yields byte-equal Ixon. This forces decompile to regenerate auxiliaries
using the same canonical layout that compile produced them in — **not**
to re-run a fresh Lean source walk against the decompiled
`InductiveVal` (which would re-introduce source-order fragility).

### 4.3 Lean-visible `_N` numbering stability

User code (including Lean-auto-generated `_sizeOf_N`, `_ctorIdx`, etc.)
references auxiliaries by their Lean-visible `<all0>.rec_N` /
`.below_N` / `.brecOn_N` names. That numbering is part of Lean's
public API, and Lean's elaborator chose a specific
`N ↦ source aux position` mapping when the source was compiled. We
must preserve the original `N ↦ source position` relationship on
decompile, even across Lean-version drift, so downstream constants
continue to resolve their references consistently.

### 4.4 Kernel-side canonicity validation

The kernel must not trust compile-side metadata for canonicity. It
runs an independent `sort_consts` port (`src/ix/kernel/canonical_check.rs`)
and validates against it in two modes:

1. **Primary validation with refinement fallback.** When a
   `Muts(Indc, …)` block
   is ingested, the stored member list is taken as the alleged
   canonical partition (each member at its own class index) and
   adjacent pairs are required to satisfy **strong** strict `Less`
   under the ported comparator. `Greater` rejects ordering violations;
   `Equal` rejects uncollapsed alpha-equivalent pairs (the compiler
   should have collapsed them to one canonical address). A weak
   `Less` means the singleton partition itself supplied the ordering
   for a block-local recursive reference, so the validator falls back
   to full `sort_kconsts` refinement and accepts only if refinement
   returns the same ordered list of singleton classes. Returns
   `TcError::NonCanonicalBlock` on failure. Implemented as
   `validate_canonical_block_single_pass` in `canonical_check.rs`,
   wired into `ingress_muts_block` (`src/ix/kernel/ingress.rs`).

2. **Iterative aux-discovery sort.** When the kernel rediscovers
   nested auxiliaries during recursor generation
   (`build_flat_block` in `src/ix/kernel/inductive.rs`), the
   resulting aux set is unsorted: discovery order depends on the
   primary ctor walk. The kernel synthesizes `KConst::Indc` views
   of each aux (instantiating ext type with `spec_params`,
   replacing the ctor result head with the synthetic aux KId) and
   runs `sort_kconsts` — the iterative partition-refinement port —
   to compute the canonical aux order. Stored aux recursors are
   then validated by position against the kernel-canonical aux:
   the stored `.rec_N` at rec-block position `n_originals + k`
   must validate against `generated[n_originals + k]` via
   `is_def_eq` on the recursor type.

The primary validator is cheap (O(n) comparator calls, no fixpoint
iteration) when every adjacent proof is strong. If any adjacent proof
is weak, it runs the full iterative algorithm for that block. The
iterative mode is also used when the kernel must derive canonical
order from scratch (rediscovered aux). Both share the same comparator:
`compare_kconst` / `compare_kexpr` / `compare_kuniv`.

**Trust boundary.** The kernel never reads `AuxLayout.perm` or any
other sidecar to decide canonical order — the sidecar persists
Lean-source `_N` numbering only (§6.4). The canonical *order* is
recomputed kernel-side every time, making it adversary-resistant:
shipping a permuted recursor block triggers the position-by-position
`is_def_eq` mismatch and rejects.

These four invariants taken together give the full canonicity story:
(4.1) fixes the forward direction, (4.2) fixes the round-trip,
(4.3) fixes Lean interop under the permuted aux layout, and (4.4)
makes the kernel an independent oracle that doesn't trust the
compiler's canonicity claims.

## 5. What Is Erased vs. What Is Preserved

### 5.1 Erased from canonical form

The following presentation choices are stripped before hashing. Ordinary
Lean `BinderInfo` (explicit/implicit/instance presentation) is distinct from
Ixon's semantic `BinderContract`. The compiler consumes reserved
`ix.contract` mdata into `lam`/`all`/`letE` payload fields
(`Ix.SemanticContract.Contract.lower`, called by `Ix/CompileM.lean` and Rust
`compile_expr`). These fields participate in serialized identity even
though the source wrapper is an `Expr.mdata` node. See
[source contracts](source-contracts.md#pure-input-and-source-identity).

| Category                           | Where it's erased                                    |
| ---------------------------------- | ---------------------------------------------------- |
| Bound variable names (λ, ∀, let)   | `Expr::Lam/All/Let` has no `name` field — `src/ix/ixon/expr.rs` |
| Ordinary Lean `BinderInfo` (impl/inst/strict) | not serialized in `put_expr`; semantic binder contracts are separate payload fields |
| Presentation `Expr.mdata` wrappers | stored in the sidecar; semantic `ix.contract` wrappers are consumed into the payload, not erased |
| Free variable identity             | FVar and MVar are rejected — `compile.rs:848-857`    |
| De Bruijn depth artifacts          | indices are **the** identifier; no names survive     |
| Lean `InductiveVal.all` order      | replaced by `sort_consts` canonical class order; kernel enforces via `validate_canonical_block_single_pass` at ingress (§4.4) |
| Nested-aux discovery order         | replaced by structural aux sort; kernel enforces via `sort_kconsts` on rediscovered aux + position-by-position recursor match (§4.4) |
| `_N` suffixes on aux names         | internal `_nested.Ext_N` uses canonical `N`          |
| Hygiene info on `Name`             | stripped by `compile_name`                           |
| Non-canonical universe-level spellings (§10.6) | `canonUniv` at the compile univ-intern boundary (`CompileM.compileAndInternUnivCanon` / `compile.rs compile_univ_idx`) |
| In-memory DAG sharing, construction order, compiler choice | the canonical sharing construction rebuilds `sharing` and every `Share` from the expanded roots (§6.7) |

### 5.2 Preserved in the metadata sidecar

Everything needed to round-trip back to a source-faithful Lean
`ConstantInfo`:

| Category                                | Where it lives                                       |
| --------------------------------------- | ---------------------------------------------------- |
| Binder names, `BinderInfo`              | `ExprMetaData::Binder { name, info, … }`             |
| Let binders                             | `ExprMetaData::LetBinder`                            |
| Presentation `Expr.mdata` KVMaps        | `ExprMetaData::Mdata`; semantic contracts are reconstructed from committed binder fields |
| Reference names (per `Const` / `Rec`)   | `ExprMetaData::Ref`; name choice at alias occurrences: §10.5 |
| Projection struct name                  | `ExprMetaData::Prj`                                  |
| Pass 3 call-site source occurrence      | `_ix.inline` record (`Mdata`) + `ConstantMeta.meta_sharing` |
| Level-parameter names                   | `ConstantMetaInfo::*.lvls`                           |
| `InductiveVal.all` (Lean source order)  | `ConstantMetaInfo::{Def,Indc,Rec}.all`               |
| `ReducibilityHints`                     | `Named.hints` (`.ixe` §5 header, exact per name) + merged `Env::anon_hints` (§3) |
| Original pre-aux_gen form               | `Named.original = Some((addr, meta))`                |
| Aux-name permutation (nested)           | `stt.aux_perms` in-memory → `ConstantMetaInfo::Muts.aux_layout` on disk — §10.2 |
| Docstrings                              | planned: `ConstantMeta.doc_string: Option<Address>`  |
| Original level spellings, per occurrence (§10.6) | `ConstantMeta.univPatches` (arena-indexed) + `metaUnivs` extension entries |

### 5.3 Explicitly **not** preserved

Source positions (`DeclarationRange`) and Lean's editor hygiene traces
are out of scope. Canonical + metadata yields a Lean term equal modulo
source-range and hygiene — which is enough for kernel, elaborator, and
proof-carrying use cases.

## 6. The Canonical Block Layout

A mutual inductive declaration in Lean generates **many** Ixon constants,
not one monolithic block. The inductive block, the recursor family and
the Prop `.below` inductive family (with its `.below.rec` family) each
live in one canonical `Muts` block; every auxiliary **definition**
(`casesOn`, `recOn`, a Type-level `below`/`below_N`, `brecOn`/`brecOn_N`
with their `.go` and `.eq`, `below.casesOn`) is its own standalone
constant, as Lean declares it, packed into a block only when several
genuinely form a strongly connected component (D6, one constant per
auxiliary: `aux_components` in `compile/mutual.rs`, `auxComponents` in
`Ix/AuxGen/CompileAux.lean`). They are compiled in a specific downstream
order and link to each other by content address, through projections
into the blocks. This section is the structural reference for each of
them.

### 6.0 What lives in each Ixon block

The Ixon types referenced below are defined in
`src/ix/ixon/constant.rs`. The relevant constructors:

```rust
pub enum MutConst {
  Defn(Definition),   // tag 0 — definitions, theorems, opaques
  Indc(Inductive),    // tag 1 — an inductive type with its ctors
  Recr(Recursor),     // tag 2 — an eliminator
}

pub struct Inductive {
  pub recr: bool, pub refl: bool, pub is_unsafe: bool,
  pub lvls: u64, pub params: u64, pub indices: u64, pub nested: u64,
  pub typ: Arc<Expr>,
  pub ctors: Vec<Constructor>,    // ← embedded; not separate MutConst entries
}

pub struct Recursor {
  pub k: bool, pub is_unsafe: bool,
  pub lvls: u64, pub params: u64, pub indices: u64,
  pub motives: u64, pub minors: u64,
  pub typ: Arc<Expr>,
  pub rules: Vec<RecursorRule>,   // ← one per ctor, in canonical order
}
```

For one user-written `mutual { … }` block of `n` user inductives that
exposes `m` distinct nested-aux signatures, compile produces these
canonical blocks (each block has its own content address):

#### Inductive block — `Muts([ Indc, Indc, … ])`

```
Muts([
  Indc(rep₀),  Indc(rep₁), … Indc(rep_{n−1}),     // user reps in sort_consts order
])
```

Each `Indc(I)` carries `I.ctors: Vec<Constructor>` inline. **Constructors
are not separate `MutConst` entries** — they live inside their parent
`Inductive`. This matters for projections (see [projections](#inter-block-references--projections)).

**Aux inductives are not serialized in the inductive block.** They are
transient compile-time entities, derived from primary ctor walks during
nested-occurrence detection. Per the compile pipeline
(`compile_mutual` in `src/ix/compile.rs`), `ixon_mutuals` is built by
iterating user (primary) classes only; aux `Indc`s are constructed
inside `expand_nested_block` and used solely as inputs to aux
recursor generation. The aux's only persistent footprint is via the
recursor block (one `.rec_N` per canonical aux signature) and any
downstream auxiliary blocks (`.below_N`, `.brecOn_N`).

The kernel rediscovers aux inductives from the primary ctors during
recursor regeneration (`build_flat_block` in
`src/ix/kernel/inductive.rs`) and computes the canonical aux order
itself via `sort_kconsts` (§4.4). There is no stored aux ordering
to validate against in the inductive block.

#### Recursor block — `Muts([ Recr, Recr, … ])`

```
Muts([
  Recr(rep₀.rec), Recr(rep₁.rec), … Recr(rep_{n−1}.rec),     // user-class recursors
  Recr(rep₀._nested.Ext_1.rec), …   Recr(rep₀._nested.Ext_m.rec),  // aux recursors
])
```

Each `Recr(R)` carries `R.rules: Vec<RecursorRule>` — one rule per
constructor of the inductive being eliminated, in canonical layout
order. For aux recursors, the rules cover the aux inductive's ctors.

The motive/minor split inside each recursor's `typ` follows §6.3:
`∀ params, [user-motives] [aux-motives] [user-minors] [aux-minors] indices major, target`.

#### `casesOn` — one standalone `Defn` per representative

```
Defn(rep₀.casesOn)   Defn(rep₁.casesOn)   …   Defn(rep_{n−1}.casesOn)
```

One `Defn` per user representative, each its own constant. Auxiliary
inductives don't get their own `.casesOn` (Lean only emits them for user
types). Each `.casesOn` body is
`λ params motive indices major, rep.rec p₀ … (λ … PUnit) …` — the `.rec`
with non-target motives stubbed to `PUnit`.

#### `recOn` — one standalone `Defn` per representative

```
Defn(rep₀.recOn)   Defn(rep₁.recOn)   …   Defn(rep_{n−1}.recOn)
```

Same shape as `.casesOn` but preserves all motives and reorders the
binder chain `(major after minors)` to `(major before minors)` —
matching Lean's `Iff.rec` / `Eq.rec` style.

#### `below` — a Prop block, or standalone Type-level definitions

```
Muts([                               // BELOW INDC BLOCK (Prop case)
  Indc(rep₀.below), Indc(rep₁.below), …,
  Indc(rep₀.below_1), … Indc(rep₀.below_m),    // nested aux .below_N
])

Defn(rep₀.below)  …  Defn(rep₀.below_1)  …   // Type case: one constant each
```

`.below` depends on the inductive's universe: inductives in `Prop` get
an `Inductive` family (no value, a type-level predicate per motive, built
from the recursor's minor premises as Lean's `IndPredBelow` does), one
mutual block; inductives in `Type` get a `Definition` per motive
(value-level, returning `PProd` of motives), each its own constant.

#### `below.rec` block — Prop case only

```
Muts([                               // BELOW.REC BLOCK
  Recr(rep₀.below.rec), Recr(rep₁.below.rec), …,
])
```

Recursors for the Prop-case `.below` inductives.

**Generation class order is semantic and canonicalized.** Unlike every
other aux phase (per-member generation, layout canonicalized by the
class sort), the `.below.rec` recursors are generated **jointly** as one
mutual family: the class order determines the motive order across the
block and the rule concatenation inside every member, and is therefore
baked into the block *bytes* before any layout sort runs. The
generation classes are ordered by the below inductives' own
partition-refinement (`sort_consts`) order — their canonical member
order in the compiled below-inductive block, equivalently ascending
anon projection index. This order is content-derived (alpha-invariant,
name-free) and is applied at the Phase-3 collection in both
implementations (`mutual.rs` `generate_and_compile_aux_recursors`
Phase 3; `Ix/AuxGen/CompileAux.lean` mirror), so Phase-5 generation and
the per-name metadata `all` lists inherit it.

History: the collection originally iterated a name-keyed hash map, so
the joint generation order followed hash-bucket order over the member
*names* — alpha-identical families could compile to different bytes (a
canonicity violation; observed as a 49-byte divergence at Mathlib scale
in the `SetTheory/Lists` mutual-Prop pair). The regression family
`ZFA`–`ZFA5` in `Tests/Ix/Compile/Canonicity.lean` (five alpha-identical
transcriptions of that shape) pins the fix: all five must produce the
same `.below.rec` block address, enforced by validate Phase 4b twin
groups and the aux-gen-diff driver gates. Ties in the canonical sort
are structurally unreachable — alpha-identical belows would require
alpha-identical parents, which collapse to a single class (and a single
below patch) upstream; the `PropCollapseA/B` fixtures pin that
collapsed path, including the `.below.rec` alias for non-representative
members.

#### `brecOn` — three batches of standalone definitions

```
Defn(rep₀.brecOn.go)  …  Defn(rep₀.brecOn_1.go)  …   // batch 1 (sub-defs)
Defn(rep₀.brecOn)     …  Defn(rep₀.brecOn_1)     …   // batch 2 (main entry)
Defn(rep₀.brecOn.eq)  …  Defn(rep₀.brecOn_1.eq)  …   // batch 3 (unfolding lemmas)
```

Three batches because of dependency order: `.go` is the inner worker,
`.brecOn` calls into `.go`, and `.eq` proves the unfolding equation
for `.brecOn`. Each definition is its own constant.

#### Inter-block references — projections

Constants that live in a `Muts` block (the inductives, their
constructors, the recursors, a Prop `.below` family) are exposed as
**projections** into it; a standalone auxiliary definition is referred to
by its own address:

```rust
pub enum ConstantInfo {
  …
  CPrj(ConstructorProj),  // → Muts inductive block, idx + cidx
  RPrj(RecursorProj),     // → Muts recursor block, idx
  IPrj(InductiveProj),    // → Muts inductive block, idx
  DPrj(DefinitionProj),   // → Muts definition block, idx
  …
}

pub struct InductiveProj   { pub idx: u64, pub block: Address }
pub struct ConstructorProj { pub idx: u64, pub cidx: u64, pub block: Address }
pub struct RecursorProj    { pub idx: u64, pub block: Address }
pub struct DefinitionProj  { pub idx: u64, pub block: Address }
```

So for a mutual block with primary `A`, `B` and one nested aux
`_nested.List_1`:

```
Lean-side name           Ixon resolution
─────────────────────────────────────────────────────────────────────
A                        IPrj { block: <ind-block-addr>, idx: 0 }
A.mk                     CPrj { block: <ind-block-addr>, idx: 0, cidx: 0 }
B                        IPrj { block: <ind-block-addr>, idx: 1 }
B.mk                     CPrj { block: <ind-block-addr>, idx: 1, cidx: 0 }
A._nested.List_1         (no IPrj) — aux Indc not stored; reached via rec block
A._nested.List_1.cons    (no CPrj) — aux ctor not stored; rule positions only
A.rec                    RPrj { block: <rec-block-addr>, idx: 0 }
B.rec                    RPrj { block: <rec-block-addr>, idx: 1 }
A.rec_1                  RPrj { block: <rec-block-addr>, idx: 2 }   ← canonical _N
A.casesOn                Defn (standalone, its own address)
A.below                  Defn (standalone; Type) / IPrj { block: <below-block-addr>, idx: 0 } (Prop)
A.brecOn                 Defn (standalone)
A.brecOn.go              Defn (standalone)
A.brecOn.eq              Defn (standalone)
```

A few key consequences:

- **The block address is the canonical content hash.** Two mutual
  declarations with the same canonical layout produce the same
  block address. Every projection into them therefore also has the
  same address (the `Address` field is identical, the `idx` is
  identical because the canonical order is identical).

- **Constructors don't have their own block address.** They live as
  `Constructor` records inside `Inductive.ctors`; their projection
  carries both `idx` (which inductive in the Muts block) and `cidx`
  (which constructor inside that inductive).

- **Aux inductives are not stored in the inductive block.** Only
  user reps live there (positions 0..n-1). Aux inductives are
  rediscovered structurally during recursor regeneration, both at
  compile time (`expand_nested_block` in `compile/aux_gen/nested.rs`)
  and kernel-side (`build_flat_block` in `kernel/inductive.rs`).
  No aux `IPrj` / `CPrj` exists; aux references inside other
  constants are routed through the recursor block by canonical
  position (`A.rec_1`, `A.rec_2`, …).

- **Aux recursors sit in the same block as user recursors.** Same
  layout: user recursors first (in `sort_consts` order), then aux
  recursors (in canonical aux order computed by `sort_consts` on
  rediscovered aux signatures). `A.rec` and `A.rec_1` differ only
  in `idx`. The kernel revalidates aux ordering by independently
  re-running `sort_kconsts` on its own discovery output and
  position-matching against the stored rec-block (§4.4).

- **Auxiliary definitions are standalone constants (D6).** Lean declares
  each `casesOn`, `recOn`, Type-level `below`/`below_N` and
  `brecOn`/`.go`/`.eq` as its own non-mutual definition, and Ix stores it
  the same way, so an auxiliary's address never depends on which
  siblings its batch held, and Lean's own form of the auxiliary of an
  unchanged block (`Named.original`) has the stored address. A batch is
  split into the strongly connected components of its members'
  references to one another, dependencies first; a genuine cycle would be
  one block. A recursor block compiled from Lean's own declarations is
  laid out in its family's flat order (`order_recursor_family`), as the
  regenerated family is.

- **`.casesOn` and `.recOn` have no aux variants.** Lean only emits
  them for user-declared inductives: exactly `n` of each.

- **Generation is per family, not per name.** A closure-only
  compile (`ix compile --consts`, a claim's dependency closure) may hold
  `A.brecOn` without `B.brecOn`, or `T.brecOn` without `T.brecOn_1`.
  `generate_aux_patches` generates a family's whole set whenever Lean
  exported any of its members, so each auxiliary (and every projection
  into a family block) has the same address as in a whole-environment
  compile. Generating a whole family can need constants none of the
  slice's own members reach (a nested block's `<all0>.brecOn_N.eq` cases
  on the external inductive, `List.casesOn`), so the closure
  producers close slices under "family of" as well as "references":
  `Lean.auxFamilySiblings` (`Ix/Common.lean`) names a member's family, and
  `Ix.EnvScope.collectDeps` and `Lean.collectDependencies` pull it and its
  dependencies. A slice built any other way that still lacks such a
  dependency gets the members present, with an `[aux_gen] warning` naming
  it. `ix pack` needs nothing extra: a block is one Ixon constant.

This structure is what gives canonicity its operational form: the
content of each block is byte-determined by `(sorted_classes, expanded
nested aux, level params, parameter telescope)` — none of which depend
on source declaration order.

### 6.0.1 Compile-time block ordering

The compile-time ordering (per `src/ix/compile/mutual.rs`) is:

```
compile_mutual_block                    // Primary inductives
  → Muts([ Indc(U₀), Indc(U₁), …,       // User classes in sort_consts order
           Indc(A₀), Indc(A₁), … ])     // Nested auxes, structurally sorted, dedup'd

compile_aux_block(rec_consts)           // Primary + aux recursors
  → Muts([ Recr(U₀.rec), Recr(U₁.rec), …,
           Recr(A₀.rec), Recr(A₁.rec), … ])

compile_aux_components(cases_on_defs)   // CasesOn definitions
  → Defn(U₀.casesOn), Defn(U₁.casesOn), …   // one constant each (D6)

compile_aux_components(rec_on_defs)     // RecOn definitions
  → Defn(U₀.recOn), Defn(U₁.recOn), …

compile_aux_block(below_indcs)          // Prop-level .below inductives
  → Muts([ Indc(U₀.below), Indc(U₁.below), … ])

compile_aux_components(below_defs)      // Type-level .below definitions
  → Defn(U₀.below), Defn(U₁.below), …, Defn(U₀.below_1), …

compile_below_recursors(below_indcs)    // .below's own recursors (Prop case)
  → Muts([ Recr(U₀.below.rec), … ])     //   (its .below.casesOn: one each)

compile_aux_components(brecon_defs) × 3 // BRecOn, split into 3 batches
  → Defn(U₀.brecOn.go), …               //   batch 0: .go sub-definitions
  → Defn(U₀.brecOn), …                  //   batch 1: main .brecOn
  → Defn(U₀.brecOn.eq), …               //   batch 2: .eq sub-definitions
```

`compile_aux_components` splits a batch into the strongly connected
components of its members' references to one another
(`aux_components`): a singleton is a standalone constant, and only a
genuine cycle would be one `Muts` block. Ixon references into the blocks
are **content-address projections** (`InductiveProj`, `RecursorProj`,
`DefinitionProj`): each projection carries a block address and an index
within that block's member list; a standalone constant is referred to by
its own address.
So the primary recursor `A₀.rec` lives at
`RecursorProj { block: <rec-block-addr>, idx: 0 }`, independent of
where the primary inductive `A₀` lives in the inductive block.

### 6.1 User-class ordering (applies to every block kind)

User classes are sorted by `sort_consts` (`src/ix/compile.rs:2526`),
which is a structural sort:

- Primary key: alpha-invariant structural comparison (ignores names,
  compares type/value structure).
- Secondary key: lexicographic on names, for ties.
- **Alpha-collapse**: if two user inductives are structurally
  equivalent modulo renaming, they collapse into one *class* with a
  representative. Only the representative appears in each canonical
  block; aliases get deep-renamed patches that also land in the same
  block under the alias's name mapping. Metadata display names at
  *synthesized* occurrences of a collapsed address inherit the
  spelling of the source occurrence each derives from (§10.5).

Every downstream block (rec, casesOn, recOn, below, brecOn) inherits
this user-class ordering by construction — each block enumerates the
primary members in the same order.

### 6.2 Nested-aux section ordering

The canonical nested-aux ordering is a **property recomputed at
validation time**, not a stored serialization. It appears positionally
in the **recursor block** (and below / brecOn derivatives), but never
in the inductive block — aux inductives are not stored on disk
(§6.0).

The canonical order is the **discovery order of the canonical
expansion** (A2-order; Pass 1's `Rules.compiler`,
`Ix/Compile/Canon/Nested.lean`):

- The block's classes are expanded in canonical order, each class by its
  representative, collapsed members renamed to their representatives
  (`expandNestedBlock … (canonicalGroups := true)`, Rust
  `expand_nested_block_canonical`). The walk is Lean's
  `elim_nested_inductive`: each constructor type is walked in pre-order,
  and a nested occurrence `ExtInd (args mentioning block members)` is
  replaced by a synthetic `_nested.ExtInd_N` auxiliary appended to the
  queue.
- A new occurrence opens the external group as that group's **compiled
  canonical classes** (one auxiliary per class, in canonical order),
  not as Lean's `ExtInd.all`.
- Occurrences are deduplicated by a **canonical key**: external constants
  by compiled address, universe levels in the serializer's positional
  normal form (`canonUniv`), with binder names, ordinary Lean `BinderInfo`
  and presentation metadata erased. Two occurrences that the stored Ixon cannot tell apart
  (collapsed or content-equal constants, `List.{max 0 0} T` and
  `List.{0} T`) share one auxiliary.
- There is no sort: the canonical expansion is already in canonical
  order. It equals Lean's `rec_N` numbering on every block whose members
  Lean lists in canonical order; elsewhere `compute_aux_perm` maps
  Lean's source positions onto the canonical ones (§6.4).

This gives a **source-order-independent** layout: the canonical
expansion starts from the canonical classes, so every permutation of
the source declaration produces the same aux section.

The recursor block's aux positions are the **only stored
manifestation** of this ordering. The kernels revalidate by the same
walk over the stored canonical members (`build_flat_block` in
`crates/kernel/src/inductive.rs`, `buildFlatBlock` in
`Ix/Tc/Inductive.lean`): over a compiled environment each external
group opens as its stored block, and occurrences are deduplicated by
address, stored universes and specialization. Each stored aux recursor
is then validated position by position against the kernel's aux at the
same offset. IxC's modeller reads the expansion off the recursor family
in any motive order.

All downstream blocks (recursors, below, brecOn) number their
aux-derived members in this same canonical order, so an aux at
canonical position `i` has its recursor at `i`-aligned position in
the recursor block, its `.below` at `i`-aligned position in the
below block, and so on.

### 6.3 Recursor binder layout

For any recursor (primary or nested-aux) in the canonical recursor
block, the type binder chain is:

```
∀ params, motives, minors, indices, major, motive_target(…)
```

with motives and minors split into user + aux segments:

```
motives:  [ user-motives in sort_consts order ]
          [ aux-motives in structural aux order, dedup'd ]
minors:   [ user-minors grouped by user class ]
          [ aux-minors grouped by aux class, structural aux order ]
rules:    one per ctor, flattened in the same user → aux layout.
```

The same user/aux split appears in `.below` value bodies (which apply
the rec with motive/minor wrappers in the same order), `.brecOn`,
`.casesOn`, `.recOn` — everything that holds a rec-shaped argument
list inherits the canonical split.

### 6.4 The `rec_N` / `below_N` / `brecOn_N` name mapping

Lean uses **source-walk indexing** for aux-member names:
`<source_all[0]>.rec_{source_j + 1}` where `source_j` is the order
in which Lean's elaborator discovered the aux during ctor scanning.

Ix canonical layout uses **canonical aux indexing** internally. To keep
Lean-visible naming stable, we carry a permutation:

```
perm[source_j] = canonical_i   // O(n_source_aux) mapping
```

and expose each `canonical aux at index i` under the Lean-visible
name `<source_all[0]>.rec_{source_j + 1}` for the *representative*
`source_j` of each canonical class (the minimum `source_j` whose
`perm[source_j] = canonical_i`). The mapping applies identically to
`.below_N`, `.brecOn_N`, `.brecOn_N.go`, `.brecOn_N.eq` — they all
share the canonical aux-section numbering.

Because of alpha-collapse in the aux section, multiple source `_N`
names can point at the same canonical aux; all such names resolve to
the same projection address (in the inductive block for the aux
inductive itself, and in the corresponding derived blocks for its
`.rec`, `.below`, `.brecOn`, etc.).

### 6.5 Evaporated auxiliaries (over-merge splits)

The example below explains evaporation. Its detailed `CallSitePlan` mechanism
records the retired surgery implementation (§8). Current callers use Pass 3
images and `_ix.inline` reconstruction records (§7); the old plan and metadata
constructors are not live APIs.

A source aux can lose its home entirely: its OWNER (the inductive
whose constructor walk discovers the occurrence) stays in an SCC while
every spec-param inductive splits into other SCCs. Example:

```lean
mutual
  inductive A | mk : List B → List C → A
  inductive B | leaf
  inductive C | leaf
end
```

SCC splitting yields `{A}`, `{B}`, `{C}`. From `{A}`'s view, `List B`
mentions no block member — it is no longer a nested occurrence at all.
Since SCCs partition the block, no SCC contains both the owner and the
specs: the aux **evaporates**. (`compute_aux_perm` marks these source
positions `PERM_OUT_OF_SCC`; an out-of-SCC entry whose owner is ALSO
out-of-SCC is just another SCC's aux, handled there.)

The canonical form follows from the isomorphism principle: a source
declaration with `C` outside the mutual is isomorphic and never had
the extra motives, so they are irrelevant and canonicalization drops
them. Dropping the irrelevant motives/minors from `<all0>.rec_N`
leaves exactly the EXTERNAL inductive's own generic recursor — which
is also what the kernel regenerates from the external block, so no
other stored form can check. Concretely:

- `<all0>.rec_N` claims are **address aliases of `<Ext>.rec`**
  (`aux_gen`'s evaporated-alias pass). All evaporated auxes with the
  same external head collapse to one address, across declarations.
- Call sites are rebuilt onto the external telescope by a
  **head-rewrite `CallSitePlan`**: spec args and the extended level
  list are derived from the source recursor's type instantiated with
  call-site args (`surgery::derive_head_rewrite_app`); the aux's own
  motive maps to the external motive slot; its minor band is kept,
  with `adapt_split_minor` synthesizing IHs consumed from dropped
  motives (via the target's source recursor — including AUX targets,
  which recurse through their own head-rewrite plans). The ORIGINAL
  head (source name + source levels) was preserved in `meta_sharing`,
  pointed at by `ExprMetaData::CallSite::orig_head` (retired, CQ3.6),
  and restored by decompile.
- `.below_N` / `.brecOn_N[.go|.eq]` of evaporated auxes have no
  canonical regeneration: they compile as **surgered originals**
  (source telescopes kept, embedded `rec_N` spines rewritten), exactly
  like `_sizeOf_N`. Their claims typecheck; address identity across
  isomorphic declarations is deliberately NOT promised for these
  derived definitions (their telescopes still carry the source arity).
- The rewrite domain is restricted to single-motive external targets;
  unsupported shapes skip both alias and plan together and fall back
  to original compilation, which kernel-check reports per constant.

Decompile regenerates the Lean-faithful over-merged view from the
stored `Muts` metadata, and the regeneration is **byte-exact**: for
every aux constant, `roundtrip_block`'s recompile of the regenerated
form reproduces `Named.original.0` exactly (this requires mirroring
the production compile paths' `preseed_expr_tables` call — the
serialized constant embeds its ref/univ tables in preseeded sorted
order, so an unseeded recompile permutes every `Ref`/univ index into
a byte-different, semantically identical constant). A Phase-A address
mismatch is therefore a **hard error** with no aux exemption; the
recovery path (`recover_aux_from_original`) only preserves the
Lean-facing constant for diagnosis while the error is recorded.

### 6.6 The content-address recipe

Each block's content hash is computed from its **members array in
canonical layout order**. The aux permutation and the Lean-visible
name mapping are metadata on the `Named` entries (see §10) — they do
not enter any block's content hash.

Because each block's canonical layout is deterministic from the set
of user-class inductives (after alpha-collapse) and the set of
nested-aux signatures (structurally sorted), two Lean mutual declarations
that agree on those two sets produce identical block content hashes
**and** identical projection addresses for every aux constant —
regardless of source declaration order.

Since the level canonicalization (§10.6), the recipe additionally
presupposes canonical (`canonUniv`-fixed) `univs` tables — level
spellings have left the hash input.

Since format version 4, the recipe also presupposes the canonical
`sharing` table of §6.7. The members array, `refs` and `univs` fix the
expressions. The sharing construction then fixes how they are written.

### 6.7 Canonical sharing

A block's `sharing` table, and the choice of each occurrence (inline or
`Share`), are part of the canonical definition. They are the output of
`Ix.Sharing.Exact.canonicalSharingTiered .tagN` (Rust
`canonical_sharing_tiered(ShareLayout::TagN, ..)`) on the block's roots,
with every existing `Share` expanded first. The roots are the
`ConstantInfo` expressions in their fixed order (`constantInfoRootExprs`).
The output depends only on those expanded expressions:

- **Identity is structural.** Subterms are identified by structural IDs,
  numbered by height and then by constructor, scalars and child IDs.
  Hashes and the interner's pointer cache only speed up discovery; they
  never decide identity. `canonicalize_det` proves that the numbering of
  interned terms depends only on the terms the roots denote. Successful
  input expansion is proved in `IxSharingVerify/CanonicalMeaning.lean`;
  the pointer cache uses structural confirmation before accepting a hit.
- **Presentation sidecars do not choose sharing.** The arena, display names,
  ordinary Lean `BinderInfo` and call-site reconstruction data are outside
  the anonymous payload. Changing only that sidecar leaves the payload's
  address fixed. Semantic source contracts have already been lowered into
  the payload and are inputs to sharing. Re-sharing preserves the sidecar's
  expression positions: arena nodes
  follow the unshared tree and a `Share` is transparent to them
  (`sharing-minimum-integration.md` §5.4).
- **Every tie is pinned.** The stored set is the `setPrec`-least minimum of
  phase 1's fixed K16 family. The first tier, the Kahn order and the width
  selection all have fixed tie-breaks. The result therefore does not depend on search order,
  parallelism or hash-map iteration. The Rust implementation's
  deterministic parallelism is checked by byte-identity tests.
- **Backward references.** Entry `i` references only entries below `i`.
  Expanding the table left to right reproduces every root exactly.
- **Conditional idempotence.** Repeating normalization reproduces the
  bytes when both runs succeed at the same configuration, layout and
  limits (`IxSharingVerify/FamilyIdempotence.lean`). Success of the output's
  raw expansion remains an explicit condition of the stronger repeat theorem.

[Ixon](Ixon.md#sharing-system) describes the three phases and the width
selection. Its [proof inventory](Ixon.md#what-is-proved-and-what-is-not)
distinguishes the production K16 family from the retained exact reference.
Successful production runs have input-expansion, meaning, format and
serialized-length proofs. Totality, output-domain closure and cost bounds
remain follow-ups; no global byte minimum or universal Rust refinement is
claimed. Rust/Lean agreement is checked by differential tests.

A failed construction, for example one that exceeds a resource limit, is a
compile error for that block. The initial component-size gate chooses the
exact or greedy family before search. Failure cannot select another family
or publish a best-so-far result.

Both compilers route every block through this construction, including
aux-gen blocks, and in Rust also kernel egress and the decompiler's
recompile. The recompile invariant `Named.original` (§9.2) relies on
recompile using exactly this route.

Historical exact-route runs produced identical Lean and Rust bytes for every
stored constant of the Init (56,783) and Init+Std (100,277) files compiled on Lean 4.34.0, and
did for Init (56,622) and a Mathlib sample of 20,284 constants on Lean
4.33.1; the merge-queue suite `lake test -- --ignored compile` requires
the Lean and Rust compilers to write identical environments for its whole
test environment (238,574 constants on Lean 4.34.0).

## 7. The Compile Pipeline

Both compilers use the three-pass driver. The Lean entry points are
`Ix/CompileDriver.lean`, `Ix/Compile/Canon.lean` and `Ix/Compile/Pass/Driver.lean`;
Rust's are `crates/compile/src/compile.rs`, `compile/mutual.rs` and
`compile/pass3/driver.rs`.

```
Lean.Env
  │
  ├─ dependency closure, groundedness and SCC scheduling
  ├─ canonical classes and nested expansion (Pass 1)
  ├─ canonical blocks and regenerated auxiliary families (Pass 2)
  ├─ changed-block images and caller rewrites (Pass 3)
  │    ├─ occurrence passes: O11a → O2 → O3 → O4 → O6
  │    └─ clique transport, with rows for successful WF plans
  ▼
canonical sharing, serialized records and publication
  + source metadata and original records
```

Pass 3 rewrites callers through images; it does not register the retired
`CallSitePlan`s. O5 supplies universe handling to the occurrence passes.
O11a is a definitional pass and emits no equation rows. Structural and
partial-fixpoint clique row support remains separate from the shipped WF
row route. The implementation and tests of these transformations do not
complete their value-preservation proofs.

Five invariants constrain the pipeline seams:

1. **Ingress is name-only via content-hash.** `compile_name(name)`
   uses `Blake3(name.components)`; hygiene is stripped.
2. **Sort is total, deterministic, and refinement-closed.**
   `sort_consts` iterates until the partition of a mutual block into
   equivalence classes stabilizes. Name-based tie-breaking only selects
   *within* a class — class membership is determined by structure.
3. **Nested-aux discovery is de-duped by a canonical key.**
   `replace_if_nested` in `nested.rs` keys its `aux_seen` table by the
   occurrence's canonical key (`addr_key`: compiled addresses, `canonUniv`
   levels, no binder names or metadata), compared exactly, so occurrences
   the stored Ixon cannot tell apart reuse the same aux.
4. **Nested-aux section is the canonical expansion's discovery order.**
   The expansion starts from the canonical classes and opens each external
   group as its compiled canonical classes, so two semantically equal
   blocks declared in different source orders produce byte-equal aux
   sections (§6.2).
5. **Binder names exit the bytes, into the arena.** `put_expr` omits
   names on `Lam`/`All`/`Let`; the arena records them as
   `ExprMetaData::Binder` entries that never contribute to
   `Constant::commit()`.

A sixth invariant governs the final step, where each block's bytes are
written:

6. **Sharing is canonical (format v4).** Each block's `sharing` table and
   `Share` occurrences are the output of the canonical construction (§6.7)
   on its expanded roots. They do not depend on how the compiler built or
   shared the expression DAG.

## 8. Call-Site Surgery

> **History.** This section describes the call-site surgery as it ran
> before Pass 3. Since the flip to Pass 3 no compile registers a plan:
> the callers of a changed block are rewritten through Pass 3 images
> instead, and the surgery was deleted from both compilers (CQ3.5,
> 2026-10-20). The `CallSite` metadata below was kept for decoding
> artifacts written before Pass 3 until CQ3.6 retired it from the format:
> kinds 10 and 11 are now refused, so such artifacts no longer decode.

User code — and Lean-auto-generated constants like `_sizeOf_N`,
`_ctorIdx`, `.noConfusion` — reference aux constants by applying them
to source-order argument lists:

```
<source_all[0]>.rec_N   p₁ … p_P   m₁ … m_K   x₁ … x_L   i₁ … i_I   j
                        params     motives    minors     indices    major
```

In Ix, the canonical `rec_N` has motives / minors in canonical order
(different positions from what the source call site expects). Surgery
**rewrites each call site's argument list** to match the canonical
aux's binder order, using the stored `perm` and `source_ctor_counts`.

The `CallSitePlan` per aux name records:

- `motive_keep[i]`: which source motives survive alpha-collapse
- `minor_keep[i]`: which source minors survive
- `source_to_canon_motive[i]`: permutation into canonical positions
- `source_to_canon_minor[i]`: same for minors

At every `App(rec, args)` site, surgery decomposes the spine and
reorders / drops arguments accordingly.

Each non-head-rewritten `X.rec` plan also derives a
`BRecOnCallSitePlan` (motive band + handler band, no minors) that is
registered for every regenerated sibling whose public telescope embeds
the motive order: `X.brecOn`, and — Type-level only — `X.brecOn.go`
and `X.brecOn.eq` (identical telescopes: params, motives, indices,
major, handlers), plus `X.below` (and, for Prop-level below
inductives, the below ctors and `.below.casesOn`). The `.go`/`.eq`
keys are load-bearing: Lean's auto-generated equation lemmas
(`f.eq_def`) reference `X.brecOn.go` / `X.brecOn.eq` DIRECTLY with
explicit motive arguments, so without those keys eq_def proofs ship
source-order motives against the canonical-order regenerated `.go` and
fail kernel check with `AppTypeMismatch` (the torchlean
`NN.GraphSpec.DAG.*.eq_def` family; fixture
`Tests/Ix/Compile/Mutual.lean` `TypeBrecOnEqDef`).

The IXON expression after surgery is already the canonical App spine.
`ExprMetaData::CallSite` is the metadata wrapper for that spine, with
two deliberately different views:

- `entries` is in **Lean source order**. Decompile uses it to rebuild
  the original source-order telescope. A `Kept` entry points at a
  canonical argument by `canon_idx`; a `Collapsed` entry points into
  `ConstantMeta.meta_sharing` for source arguments that did not survive
  canonicalization.
- `canon_meta` is in **canonical App-spine order**, one arena root per
  canonical argument actually present in the IXON expression. Kernel
  ingress uses it to assign binder / reference metadata to each
  canonical argument without guessing names from content addresses.

These two maps are both metadata. They do not choose the canonical
argument order — the IXON App spine already does that — and they are
not accepted as evidence of canonicity. Kernel ingress only checks that
`canon_meta.len()` matches the canonical telescope length and then
uses those roots as names / binder info for the already-present
arguments. The kernel still validates block order and aux-recursion
order independently (§4.4).

The separation matters for split-SCC minors: a source minor may be
stored as `Collapsed` for decompile while compile emits a synthesized
canonical wrapper argument. In that case there is no source-order
`Kept` entry from which kernel ingress could recover the wrapper's
reference metadata; `canon_meta` is the direct metadata sidecar for
the canonical wrapper.

**This is why patches must be emitted in canonical layout.** Surgery
operates on call sites, assuming the callee has canonical binder
order. If the patch were in source order, surgery's rewrites would
misalign with the actual callee, and transitively-dependent constants
(notably `_sizeOf_*`) would reference wrong addresses.

## 9. The Decompile Pipeline

Decompile is the inverse of compile: given an Ixon environment (bytes
+ `Named` metadata), reconstruct Lean `ConstantInfo` values that Lean
treats as equivalent to the original source. It has two audiences with
different requirements:

- **Kernel / ZK consumers** want the *canonical* Lean form — the one
  whose recompile will yield byte-equal Ixon, which is what the
  proof-carrying-code pipeline checks against.
- **Human / elaborator consumers** want the *source-faithful* Lean
  form — the one that matches what the user typed, with original
  binder names and the original Lean-visible `rec_N` / `below_N`
  numbering.

These two forms differ because aux_gen rewrites some constants
(notably recursors, `.below`, `.brecOn`) into canonical layouts that
are not byte-equal to Lean's own `.rec` / `.below` / `.brecOn` output.
The `Named.original` field (§9.2) is how we serve both audiences from
the same Ixon environment.

### 9.1 The three-track decompile

The diagram describes the source/canonical record choices. The Lean full
source decompiler now reads stored originals directly; Rust also retains
an auxiliary-regeneration path. Their actual entry points are in §9.3.

```
Ixon bytes + Named map
  │
  ▼
Ixon decoder → (Constant content, ConstantMeta, Option<(orig_addr, orig_meta)>)
  │                                             ───── Named.original ─────
  │
  │  (for each Named entry)
  ▼
route on constant kind + Named.original presence
  │
  ├─ Non-aux_gen constant (Def, Axio, Quot, ordinary Indc/Ctor/Rec):
  │     original == None
  │     → decompile Constant content directly using meta.arena for
  │       binder names.
  │     → Result: one LeanConstantInfo; canonical ≡ source for these.
  │
  ├─ Aux_gen-rewritten constant (.rec, .casesOn, .below, .brecOn,
  │                              .rec_N, .below_N, .brecOn_N, etc.):
  │     original == Some((orig_addr, orig_meta))
  │     │
  │     ├─ Canonical path (for recompile / kernel / ZK):
  │     │     Decompile the Constant at `named.addr` using
  │     │     `named.meta`. This is the structurally sorted, alpha-collapsed,
  │     │     source-order-independent form.
  │     │
  │     └─ Source-faithful path (for elaborator / decompile_check):
  │           Decompile the Constant at `orig_addr` using `orig_meta`.
  │           This is the original pre-aux_gen form, with Lean's
  │           source-order motives, source-order `rec_N`, and
  │           original binder names.
  │
  └─ Non-aux_gen projection into an aux_gen-rewritten block
    (e.g. `A.rec` where A's rec block was regenerated):
        Decompile resolves the projection against the canonical
        block's `idx`, then reconstructs the Lean recursor by
        composing the block's per-member Lean form with the
        per-member `original` when needed.
```

Key correspondence:

- `named.addr` is the **content address** of the canonical
  constant in `env.consts`. Equal for alpha-collapsed aliases
  (that's the epimorphism direction).
- `named.meta` is the **canonical metadata** — binder names, mdata,
  `all` field — aligned with the canonical-layout constant at
  `named.addr`.
- `named.original.as_ref().map(|(a, _)| a)` is the content address
  of the **pre-aux_gen constant** (if the rewrite changed the form).
- `named.original.as_ref().map(|(_, m)| m)` is the pre-aux_gen
  metadata — same arena shape, but with the Lean-source binder names
  and Lean-source `all` ordering.

### 9.2 The `Named.original` field

```rust
// src/ix/ixon/env.rs
pub struct Named {
  /// Address of the canonical Constant (in env.consts).
  /// Alpha-equivalent sources share this address.
  pub addr: Address,

  /// Metadata aligned with the canonical form: binder names, mdata,
  /// BinderInfo, Lean-source `all` list, reducibility hints, etc.
  pub meta: ConstantMeta,

  /// When aux_gen replaces the source Lean form with a canonical
  /// layout, `original` carries the pre-rewrite form:
  ///   - original.0 = content address of the source-form Constant
  ///                  (may equal `addr` if no rewrite; then `None`)
  ///   - original.1 = metadata for the source form
  ///
  /// None for constants that aux_gen doesn't touch (ordinary defs,
  /// axioms, user inductives) — their canonical IS the source.
  pub original: Option<(Address, ConstantMeta)>,
}
```

**Who writes it.** `src/ix/compile.rs:331` populates `original`
inside the aux_gen post-compilation step. For every constant whose
aux_gen patch differs from Lean's own output (i.e. any `.rec`,
`.casesOn`, `.recOn`, `.below`, `.brecOn` in a block that required
canonicalization), the compiler:

1. Compiles the canonical patch the way aux_gen emits it —
   its address becomes `named.addr`, its metadata `named.meta`.
2. Compiles the Lean-source form through `compile_const_no_aux`
   (`compile.rs:2584`), which is a pristine compile that does NOT
   enter aux_gen — its address becomes `named.original.0`, its
   metadata `named.original.1`.
3. Only the canonical patch goes into `env.consts`. The source-form
   compile is ephemeral: its constant is never stored (validate-aux
   phase 3, "No ephemeral leaks", fails if one is), so `original.0` is
   a provenance address, not a reference. The `Named` entry points at
   the canonical via `addr` and records the original via `original`;
   decompile tolerates the original's bytes being absent, and
   `Env::prune_to_closure` (`ix pack`) follows `original.0` only when
   the source env happens to store it.

**Who reads it.** `src/ix/decompile.rs`:

- Lines 2534, 2544: `if let Some((ref orig_a, _)) = named.original` —
  decompile uses the *original* address when it needs the
  source-faithful form (e.g. for roundtrip against Lean's own output
  in ValidateAux Phase 6).
- Line 2648: picks between `named.meta` and `named.original.as_ref().unwrap().1`
  depending on which form the caller asked for.
- Line 1889: `pub(crate) fn is_aux_gen_suffix(name: &Name) -> bool` —
  the suffix predicate.
- Line 3055: `if named.original.is_some() && is_aux_gen_suffix(name)` —
  routing gate that selects the canonical-vs-source two-track path.
- Line 4038: `if named.original.is_none()` — fast path for ordinary
  constants (no aux_gen involvement).

**Why two forms are needed.** Without `original`:

- Decompile could produce only the canonical form, which doesn't
  match what Lean's `A.rec` looks like (canonical has structurally sorted
  motives / aux, Lean has source-walk order). That breaks
  ValidateAux Phase 6 (aux congruence) and any source-faithful Lean
  isomorphism check layered on top of decompile.
- Or decompile could re-run aux_gen on the decompiled inductive
  block and derive a fresh canonical form. But Lean-version drift
  in the source walk would cause that fresh form to diverge from
  the stored canonical (invariant 4.2 violated).

Storing both forms is the cheapest way to serve both consumers and
preserve invariant 4.2 across Lean upgrades.

### 9.3 Mutual-block reconstruction

**Lean full source decompile** (`Ix/DecompileDriver.lean`) uses
`decompileOriginals`: select original addresses, metadata and hints with
`originalView`, decode the source records, skip reserved `_ix` support
names, and recompute inductive flags from the decoded declarations. It
neither regenerates auxiliaries nor invokes a kernel fallback. A missing
required original is an error requiring recompilation of the artifact.
The M6D originals and original-hint tables use the v5 envelope; checked
constant payloads and claims retain format 4.

**Rust full decompile** (`crates/compile/src/decompile.rs`, `decompile_env`)
still calls `decompile_block_aux_gen`. That path builds singleton source
classes and deliberately passes `None` as the aux-layout override to
`generate_canonical_recursors_with_layout`. It regenerates source-walk
order to reproduce `Named.original.0`, rather than replaying canonical
layout at `Named.addr`. `roundtrip_block` checks the regenerated form
against the stored original address; recovery of a source record does
not erase a recorded regeneration error. There is no live
`rehydrate_aux_perms_from_env` scan or `stt.aux_perms` table. The retained
Rust regeneration path and its singleton-class limitation are distinct
from Lean's stored-record route (§17.2).

### 9.4 Recompilation and the roundtrip fixed point

The strongest statement of canonicity is the **fixed-point property**:

```
∀ c ∈ Lean. compile(decompile(compile(c))) = compile(c)   as Ixon bytes
```

i.e. one compile → decompile → compile round-trip produces the same
canonical bytes as the first compile. This is invariant 4.2 made
operational.

The mechanism:

```
compile(c)                              ─▸ canonical bytes B₁,
                                            with Named { addr = A_canon,
                                                         meta = M_canon,
                                                         original = Some((A_orig, M_orig)) }
                                            when c is aux_gen-touched.

decompile( … )  ─ (source-faithful track) ─▸ Lean constant c'
  reads:                                      with binder names from
    - named.original.1 for aux_gen names      M_orig, mutual-member
    - named.meta for others                   order from M_orig.all,
                                              Lean-source _N numbering.

compile(c')                             ─▸ canonical bytes B₂
  path:
    - sort_consts sees the same α-classes as the first compile
      because c' has the same structural shape (only cosmetic fields
      may differ, and they don't affect sort_consts).
    - expand_nested_block produces the same ExpandedBlock because
      c''s ctors mention the same nested inductives applied to the
      same structural block members.
    - the canonical expansion produces the same aux order because it
      starts from the canonical classes and keys occurrences by
      structural content and resolved addresses, not source names.
    - aux_gen produces the same patches because its input is
      (sorted_classes, expanded, level params, etc.) — all of which
      are determined by c''s structure.
    - stt.aux_perms is repopulated with the same AuxLayout, and
      surgery rewrites call sites identically.

Therefore B₂ == B₁.
```

Where this can break:

- **Metadata incompleteness.** If decompile drops information that
  compile's canonicalization relies on — e.g. if `original` is not
  populated and decompile has to re-derive binder names from the
  canonical form — the second compile may produce a subtly different
  `ExpandedBlock` (different nested-aux param spellings), which then
  structurally sorts into a different order. Invariant 4.2 violated.
- **Permutation-comparator partiality.** The comparator used by
  ValidateAux Phase 6 to check `decompile(canonical) ≡ original`
  (see §16.3) must match aux_gen's actual canonicalization. If `PermCtx`
  misses a case, Phase 6 fails even though the canonical form itself is
  correct; decompile outputs differ from Lean's `.rec_N` at motive
  positions, and the roundtrip fixed-point becomes observable only
  through recompile-and-compare, not through the cheaper ≡-check.
- **Source-walk drift.** If Lean's internal source walk for nested-
  aux discovery changes between versions (commit history, library
  updates), the stored `AuxLayout` still anchors us to the original
  `source_j → canonical_i` mapping — but a fresh walk inside
  decompile would pick different source `_N`s. That's precisely why
  decompile must read `AuxLayout` from `Named`, not re-derive it.

In practice, the roundtrip test is:

```rust
for name in env.constants.keys() {
    let original   = env.find(name);
    let ixon_1     = compile(&[original], &env).bytes();
    let decompiled = decompile(ixon_1).find(name);
    let ixon_2     = compile(&[decompiled], &env).bytes();
    assert_eq!(ixon_1, ixon_2);
}
```

This is validate-aux Phase 7b (§16.2).

## 10. Metadata Required for Round-trip

Metadata is attached to `Named` entries in the Ixon env, one per Lean
name. It's distinct from the block content — metadata doesn't enter
any block's content hash. For a mutual inductive declaration,
canonicity requires metadata on the per-inductive Named entries
*and* on the block-level `Muts` Named entry.

### 10.1 Stored and wired through

- **Per-inductive `all` list**: the Lean source-order
  `InductiveVal.all`, including all alpha-collapsed aliases. Stored
  on each inductive's `ConstantMetaInfo::Indc { all, … }`
  (`src/ix/ixon/metadata.rs:131`) and likewise on `Def.all` / `Rec.all`
  for constants that carry a mutual context. Without this, decompile
  can't reconstruct alias names or re-run `sort_consts`.
- **Block-level `Muts.all`**: the synthetic metadata for the block
  itself, `all: Vec<Vec<Address>>` — each inner `Vec` is one
  alpha-equivalence class of name-hash addresses
  (`metadata.rs:166-169`).
- **Per-constant names and binder info**: each constant's Lean name
  (canonical `Named` entry key), plus the `ExprMetaData::Binder`
  arena entries.

### 10.2 Aux layout persistence (shipped)

`AuxLayout` lives in `crates/ixon/src/env.rs` and is stored on the block's
`ConstantMetaInfo::Muts.aux_layout`, not on each `Named` entry. It contains:

- `perm[source_j] = canonical_i`, with `PERM_OUT_OF_SCC` for an auxiliary
  outside this component;
- `source_ctor_counts`, in source-walk order;
- `evaporated`, distinguishing an auxiliary this component owns but whose
  canonical expansion disappeared from one owned by another component.

`compile_aux_gen_block` in `crates/compile/src/compile/mutual.rs` constructs
the layout from `generate_aux_patches` and `source_aux_order`. The caller in
`crates/compile/src/compile.rs` persists it on the primary block's Muts
metadata and passes it to Pass 3's changed-block handling. The metadata
codec is in `crates/ixon/src/metadata.rs`, mirrored by `Ix/Ixon.lean`.

Neither current full-decompile entry uses the old `stt.aux_perms` rehydrate
scan. Lean reads stored originals; Rust's retained regeneration deliberately
requests source-walk order without a layout override (§9.3). A persisted
canonical layout must not be described as the mechanism of either source
decompile path.

### 10.3 CallSite metadata alignment

This subsection is historical, for the retired metadata in §8. Current
`_ix.inline` records use `Pass/SideCar.lean`; `CallSite` kinds 10 and 11
are refused by the current metadata decoders.

`ExprMetaData::CallSite` is expression metadata, not block-layout
metadata. Its `entries` field is the source-order inverse map needed
by decompile; its `canon_meta` field is the canonical-order metadata
alignment needed by kernel ingress.

`canon_meta` is allowed because it stores arena roots for arguments
that already exist in the canonical IXON expression. It does not store
or influence:

- user-class order,
- nested-aux order,
- recursor block positions,
- the source-walk → canonical aux permutation.

Those remain derived from `sort_consts` / `sort_kconsts` and validated
kernel-side. A malformed `canon_meta` can make metadata-bearing kernel
ingress reject or assign different metadata names to already-present
arguments, but it cannot cause the kernel to accept a non-canonical
block order or pick a different canonical aux target.

### 10.4 Not stored (derived at compile and decompile time)

The **canonical block layout** (canonical aux positions, user-class
order, recursor binder split) is derived from the inductives plus
alpha-collapse plus structural aux sorting — all of which are computable from the
decompiled inductive data alone. Do not store the derived layout
directly; it falls out of the canonical rules, and storing it would
just create room for skew between storage and rederivation.

### 10.5 Metadata name canonicalization at alias occurrences

Alpha-collapse makes a content address many-named: every member of a
collapsed class resolves to one address (§6.1), and structurally
identical declarations from different blocks coincide on one address
as well (§13.5). The anonymous form is unaffected — any spelling of a
reference compiles to the same `Rec(idx)` / `Ref(addr)` bytes — but
the metadata sidecar records a **display name per occurrence**:
`ExprMetaData::Ref { name }` for each `Const` occurrence,
`Prj.struct_name` for projections, and source expressions saved by `_ix.inline`
(`metadata.rs`; Lean mirror `Ix/Ixon.lean`). Wherever the referenced
address carries more than one name, the metadata must record a name
at each such occurrence, and that choice was previously unspecified.
The ambiguity is invisible to
the §1 property, but it is visible to byte comparison of the
metadata: the two compiler implementations (`crates/compile`;
`Ix/CompileM.lean` + `Ix/AuxGen`) could disagree while both remaining
individually correct.

**Source-derived expressions are already determined.** Both compilers
record exactly the name spelled at the source occurrence:
`compile_expr` (`compile.rs`) and `compileExpr` (`Ix/CompileM.lean`)
allocate the `Ref` node from the input `Const` node's own name, alias
or not, while the anonymous side collapses it to the shared address.
That is normative — decompile reconstructs the source spelling from
`Ref.name` — so source fidelity governs every expression that *has* a
source: ordinary constants, each class member's own primary meta
(compiled from that member's source form in the per-class loop of
`compile_mutual` / `compileMutConsts`), the `Named.original` forms
compiled by `compile_const_no_aux` (§9.2), and the source expressions saved
by Pass 3's sidecar (`Ix/Compile/Pass/SideCar.lean`).

**Rule: synthesized occurrences inherit their source spelling.** An
expression the compiler synthesizes rather than reads — the
regenerated `.rec` / `.casesOn` / `.recOn` / `.below` / `.brecOn`
(and `.go` / `.eq`) families, aux `.rec_N` / `.below_N` derivatives,
and arguments synthesized by image construction inside otherwise
source-derived bodies (§7) — is not free-standing: it is derived from
identified source material of its own block. Minor premises splice
the constructor telescopes (`buildMinorType` in
`Ix/AuxGen/Recursor.lean` and its `recursor.rs` mirror),
`.casesOn` / `.recOn` are built from `.rec`'s type, `_nested`
expansions are restored to the original source application
(`RestoreCtx.restore` in `Ix/AuxGen/ExprUtils.lean`). The rule: every metadata
position in a synthesized expression that records a display name records **the
spelling of the source occurrence it derives from** — the name is
inherited through the derivation, never chosen at emission. Where the
synthesis introduces a reference with no source ancestor — the family
head applied under fresh motives, references to sibling auxiliaries
(`.rec` inside `.brecOn`), and primitives the algorithm names
outright (`Eq`, `PUnit`, …) — the spelling is fixed by the synthesis
algorithm itself, identically in both implementations by
construction.

**Corollary: kernel-cache state must not outlive the block.** Kernel
expression identity is name-erased (`ExprKey` keys on content
addresses; `KId` carries the display name alongside), so WHNF, infer,
and intern caches replay whichever alias spelling first populated
them — the "display-name aliasing" hazard documented on
`findRecTarget` / `decomposeInductiveType` in both pipelines. A
kernel context surviving across blocks therefore makes emitted names
depend on which blocks that context saw earlier — under a parallel
scheduler, on the work-stealing schedule itself. Both compilers must
run aux synthesis in kernel contexts scoped to the block, and on
egress restore source spellings structurally
(`restore_source_names_same_content` and the source-name hint maps in
`expr_utils.rs` / `source_name_hints.rs`; `restoreSourceNamesSameContent`
and mirrors in `Ix/AuxGen/Kernel.lean`). The restoration heuristics —
hint candidacy restricted to `App`/`Proj` subterms, first-insert-wins hint slots —
are part of the specified behavior: they must remain mirrored
hole-for-hole, since a restoration difference is a parity break even
with block-scoped contexts (§17.8).

The Rust hint pass uses exact, shallow structural keys over canonical child
identities, not a lossy digest as evidence of equality. Its conversion and
restoration memos are scoped to one pass with a fixed view of referenced
name resolutions; first-wins collection precedes restoration against the
completed hint map. These temporary identities never enter serialized output.

**Positions in scope.** The rule governs the metadata positions that
record a *reference to another constant*:

- `ExprMetaData::Ref { name }` — every `Const` occurrence,
  block-local (`Rec`) and external (`Ref`) alike;
- reference metadata in synthesized image arguments and in the source
  expressions saved by `_ix.inline`;
- `ExprMetaData::Prj { struct_name }` — the projected structure
  reference.

It does **not** govern positions fixed by the subject constant's own
identity or defined as whole-set enumerations: the meta variant's
`name` and `lvls`; `all` (Lean source order, aliases included —
§10.1); `ctx` (the full mutual-context enumeration); `Rec.rules`,
`Indc.ctors`, `Ctor.induct` (the subject constant's own constructors
and parent); and `Binder` / `LetBinder` names (locals, not constant
references).

**Why provenance.** The choice must be a deterministic function of
block content, not of traversal or discovery order, or two correct
implementations can diverge forever. Inherited spellings are exactly
that: a function of the block's source expressions and the fixed
synthesis algorithm, with no new ordering, no alias-set lookup, and
no hash impact (these display names live in the presentation sidecar, §6.6). The
fidelity checkers already enforce it: both decompile-side checkers
rebuild their reference by re-running the same generator over
decompiled source constants (`DecompileDriver` Pass 2 in Lean;
validate-aux Phase 2's `generate_aux_patches` on fresh per-block
contexts in Rust) and compare name-sensitively (`congruence.rs`
const-name check; hash-`BEq` in Lean) — under this rule, emitter and
checker agree by construction, and the comparators' name-sensitivity
enforces the rule instead of fighting it. Any one-name-per-address
canonicalization would instead require teaching all four
emitter/checker sites a shared alias-visibility order that is
ill-defined for cross-block coincidences (§13.5) under streaming
compilation. Decompiled auxiliaries also read like the source. The
class representative persists where it already governs — alias
registration clones the representative's `Named`
(`register_aux_aliases`), Lean-native originals are recovered from
`Named.original` (§9.2), `Muts.all` and block serialization keep the
`sort_consts` order (§11.1) — just not as an occurrence-spelling
rule.

**Motivating instance.** A whole-Mathlib parity run (736,624
constants) of the Rust and Lean compilers produced byte-identical
anonymous content — all 647,127 content-addressed constants, hints,
blobs, and name tables — and diverged by 47 bytes total, entirely
inside the `ConstantMeta.info` of `Quiver.FreeGroupoid.redStep.rec`,
`.casesOn`, and `.recOn`. The source spells the collapsed pair as
`Paths (Symmetrify V)` — `CategoryTheory.Paths` and
`Quiver.Symmetrify` are a §13.5 cross-block coincidence on one
address. The Lean output preserved each occurrence's source spelling
(outer `Paths`, inner `Symmetrify`) — conforming to this rule — while
the Rust output recorded `Paths` at both occurrences. The Rust
divergence traced not to a policy but to two defects. The observed
one is deterministic and in-block: `redStep`'s stored type is
`HomRel (Paths (Symmetrify V))`, whose recursor regeneration must
genuinely WHNF through `HomRel`; the kernel's intern/canonicalization
collapses the two spellings of the shared address to the
first-interned display name inside the reduct, and the hint-based
source-name restoration that should have undone this restored
*nothing*, because its keys were intern uids rather than content
digests (§17.8) — so the regenerated telescope spelled
`Paths (Paths V)`. Separately, the production scheduler's
worker-lifetime kernel contexts (`compile/env.rs`) let cache entries
recorded while compiling one block replay their spellings into later
blocks on the same worker — a schedule-dependent channel, closed by
giving each block compile a fresh `KernelCtx` (as the aux-dump and
validate-aux checker paths already did). With both fixed, the
redStep-closure and whole-Mathlib outputs are byte-identical; the
earlier reading of the Rust output as a deliberate
one-name-per-address canonicalization was coincidental. Both outputs
roundtrip correctly, so §1 held and only metadata determinism failed;
this rule closes that gap.

### 10.6 Universe-level canonicalization (live)

> **Status.** Adopted 2026-08-06; **live** as of 2026-08-07 (Rust
> pipeline first, Lean mirror after — see §17.9 for the landed
> record). Every gate below runs strict: whole-Mathlib `ix validate`
> and `validate-lean` report 0 failures with phase 3 STRICT (no
> `reduceIxonUniv` modulo) and phase 4 at 714,346 spellings checked /
> 0 findings; both compilers are byte-ALIGNED at 3,155,562,665 bytes;
> the census probe reports `Géran-noncanonical: 0` entries and 0
> spelling-collision constants on regenerated artifacts.

**The quotient.** Universe-level spellings are presentation, not
content. Two levels are identified in canonical form exactly when the
kernels' semantic level equality holds — `univEq`
(`Ix/Tc/Level.lean`), the relation all three kernels decide during
defeq. `univEq`'s normal-form comparison ignores EMPTY subsumption
entries (constant 0, no vars — bookkeeping the subsumption pass
leaves behind rather than removing; `normLevelLe` always ignored
them), so it is the exact semantic quotient: before that fix the
comparison distinguished 3 of 3,253,373 whole-Mathlib entries from
their semantic equals (e.g. `max (u+1) (imax (u+1) v)` vs
`max (u+1) v`). This is the endpoint quotient for levels: the content
address coincides with kernel identity, and no stronger level
quotient exists to migrate to later. Levels meet the criterion for
address-baked quotients — decidable equality, a computable canonical
representative, no environment context — where general expression
defeq does not; the quotient is the same *kind* as the §5.1
alpha-collapse and follows the §10.5 template: canonical content plus
per-occurrence metadata restoring source presentation, the
restoration a deterministic function of the source, never a choice
made at emission.

**Boundary.** Declaration-level universe-parameter **list** order
remains structural: §12.3's `h₁.{u,v}` / `h₂.{u,v}` keep distinct
addresses. What is quotiented is spelling *inside* level
expressions: `max u v` and `max v u` at an occurrence become one
content, as do `imax (imax 1 u) u` and `u` (the motivating
WF-recursion `eq_def` shape, where Lean metaprograms store
unnormalized substitution results).

**Canonical representative.** `canonUniv : Univ → Univ` is
`linearize ∘ subsumption ∘ normalizeAux` — the kernels' Géran
comparison form (`normalizeLevel`, `Ix/Tc/Level.lean:227-472`;
`crates/kernel/src/level.rs:335-696`;
`Ix/IxVM/Kernel/Levels.lean:336-386`), transliterated to positional
`Ixon.Univ` and then linearized back into a level term. The Géran
form is a map from **paths** (sorted lists of param indices —
imax-conditioning chains) to **nodes** (a constant offset plus
`(paramIdx, offset)` contributions sorted by ascending index): an
entry `(P, node)` contributes its max-value whenever every param in
`P` is ≥ 1, and the level is the pointwise max over contributing
entries. `linearize` emits a representative term from that form —
total and deterministic, with every ordering inherited from the
canonical structure itself (entries in lexicographic path order, vars
in ascending index order, a fixed right-nested `max` association) and
atoms `succ^c zero` / `succ^k (var i)`; entries at non-empty paths
are reconstructed as `imax`-gated subterms by **per-atom gate
inversion**: each atom self-strips gates its own value already
dominates (`covered` — a subset-path constant `≥ k`, or a var
`offset+1 ≥ k`) **provided the stripped context stays leak-free**
(`gatesLeakFree` / `gate_order(..).1`: each of its gates keeps an
absorber atom at a map path inside the gate's prefix, since
`imax t u_g ≥ u_g` wherever the outer gates are active), the
remaining gate order is recovered greedily outermost-first (the
smallest gate carrying a `(g,·)` absorber atom at a path within the
chosen set), marker entries are consumed, and a root constant is
absorbed into the emission (settled empirically during
implementation — formerly open detail O1; P2 pins it exhaustively over
all ≤8-node terms). Required properties, pinned by tests in both
languages:

- **P0 (value preservation):** `canonUniv u` and `u` take the same
  value at every valuation of the parameters. The compiler must not
  change the universe a declaration states: the kernel checks the
  stored canonical levels. Without the leak-free proviso above, P0
  fails on deep `imax`-by-parameter chains over three or more
  parameters: `imax (imax (imax u w + 1) u) v` canonicalizes to
  `max (imax (imax (w+1) u) v) (imax (imax (u+1) w) v)`, which is `2`
  at `u = 0, v = 1, w = 2` where the level is `1` (the self-strip of
  `u + 1` from `[u, v, w]` leaves gate `w` without an absorber in
  `[v, w]`). The proviso changes a canonical form only where the form
  without it has the wrong value; it changes no stored level of the
  Init+Std or Mathlib environments (0 of 345,177 and 3,343,350 table entries,
  0 of 16,621 and 426,093 original spellings), so no address moved.
  Tests: the witness family, every ≤8-node term (Rust) / ≤6-node term
  (Lean) over three parameters, and the kernel level comparison's
  biased random levels in both languages, with exact valuation sets.
  Proved for the Lean `canonUniv`, for every universe and every
  valuation, with no premise: `Ix.CompileCert.CanonUnivEmit.canonUniv_eval`
  (`Ix/CompileCert/CanonUniv*.lean`, frozen in `Ix/Cert/Audit.lean`).
- **P1 (idempotence):** `canonUniv (canonUniv u) = canonUniv u`.
  It holds wherever the normal forms involved carry no subsumption
  leftover (below), which covers every stored level of both environments;
  the random family pins how rare the exceptions are.
- **P2 (roundtrip-fixpoint):** `geran (linearize L) = L` on canonical
  forms — `linearize` picks a genuine representative of its class;
  with P1, `canonUniv` is constant on Géran classes. Like P1, it fails
  only on normal forms with a **subsumption leftover**: `subsumption`
  mirrors the kernels' normalizers, which test a gated constant
  against its own node's vars instead of the dominator's, so
  `max (v+1) (imax (imax 2 u) v)` keeps a constant `2` at `[u, v]` that
  `v + 1` dominates (`Ix/Tc/Level.lean`, `crates/kernel/src/level.rs`,
  `Ix/IxonUniv.lean` alike). Then two equal levels can have different
  normal forms. 239 of the 125,000 levels of the random family hit
  it, and none of the environments'. An exact subsumption (in all
  normalizers together, to keep P4's oracle aligned) would make P1, P2
  and P6 unconditional and the quotient exact; measured on both
  environments it changes no stored level either.
- **P3 (mk\*-fixpoint):** `linearize` output triggers no rule of the
  kernel-rebuild set below — rebuilding it through the `mk*`
  constructors is the node-for-node identity, so kernel ingress
  preserves stored canonical content exactly.
- **P4 (soundness):** `univEq u (canonUniv u)`, with the kernels'
  Géran implementation as the oracle.
- **P5 (mirror parity):** Rust and Lean `canonUniv` agree
  byte-for-byte on serialized output.
- **P6 (mk\* absorption):** `canonUniv ∘ reduceIxonUniv = canonUniv`
  (`reduceIxonUniv`, `Ix/Tc/Ingress.lean`, is the retained oracle
  for this).

`canonUniv` lives next to the wire type (`crates/ixon/src/univ.rs`
and the Lean mirror), kernel-free, so both compilers, the Tc egress,
and probes share one implementation per language; the three kernel
`NormLevel` implementations stay untouched as the P4 oracle. Worst
case, canonical forms are exponential in nested `imax`-of-`max`
depth (the Géran distribution rules duplicate the left subterm,
`Ix/Tc/Level.lean:333-351`); real levels are a handful of nodes, and
the blowup is paid once at compile time by whoever writes a
pathological spelling — never by readers of stored canonical forms.

**The kernel-rebuild rule set.** The `mk*` simplification rules —
Lean `kernel/level.cpp:81-103`/`:112-120`, mirrored at
`Ix/Tc/Level.lean:144-197`, `crates/kernel/src/level.rs:162-247`,
`Ix/IxVM/Kernel/Levels.lean:637-680` — are normative here in three
roles: the P3 fixpoint target (kernel ingress rebuilds through them),
the stage-1 decoration-presence test (below), and the P6 oracle.
They are **not** the address quotient (they miss commutative twins).
`nMax a b`, first applicable rule wins:

| # | Rule | Guard |
| --- | --- | --- |
| M1 | both explicit numerals → the larger (ties → `a`) | `a.isExplicit && b.isExplicit` |
| M2 | `max a a = a` | structural `a == b` |
| M3 | `max 0 b = b` | `a.isZero` |
| M4 | `max a 0 = a` | `b.isZero` |
| M5 | `max a (max x y) = max x y` if `x == a ∨ y == a` | absorption into `b` |
| M6 | `max (max x y) b = max x y` if `x == b ∨ y == b` | absorption into `a` |
| M7 | `max (succ^n x) (succ^m x) = succ^(max n m) x` | same offset base |
| M8 | otherwise raw `max a b` | — |

`nIMax a b`:

| # | Rule | Guard |
| --- | --- | --- |
| I1 | `imax a b = nMax a b` | `b.isNeverZero` |
| I2 | `imax a 0 = 0` | `b.isZero` |
| I3 | `imax 0 b = b` | `a.isZero` |
| I4 | `imax 1 b = b` | `a == succ zero` |
| I5 | `imax a a = a` | structural `a == b` |
| I6 | otherwise raw `imax a b` | — |

with predicates `isZero` / `isExplicit` (`succ^n zero`) /
`isNeverZero` / `offset` exactly as in `Ix/Tc/Level.lean:64-95` /
`crates/kernel/src/level.rs:111-150`. Both rule sets — `mk*` and the
Géran linearization — are **frozen** at the pinned toolchain's
behavior; upstream drift mints new spellings, which simply
canonicalize (or patch), and never redefines the address.

**Format invariant (stage 2).** Every `univs` table entry in a valid
artifact is `canonUniv`-fixed; tables are preseeded, sorted by
serialized key, and deduplicated as today (`univSortKey`,
`Ix/CompileM.lean:1115-1118`; `compile.rs:487-491`). Both compilers
canonicalize at the single univ-intern choke point
(`compileAndInternUniv`, `Ix/CompileM.lean:351-353`;
`compile_univ_idx`, `compile.rs:468-484`). Declared level-parameter
counts and the positional names channel are untouched —
canonicalization can only make a parameter unused in content, never
renumber it.

**Restoration metadata: `univPatches`.** For each `sort` / `ref` /
`recur` occurrence whose original level list differs from its
canonical list, the compiler records a patch keyed by the
occurrence's **metadata-arena node index**, with original spellings
stored in the `metaUnivs` extension table under the documented
virtual-index contract (index `< univs.size` → primary table; index
`≥ univs.size` → `metaUnivs[i − univs.size]`;
`crates/ixon/src/metadata.rs:205-213`). Encoding: a fourth
`ConstantMeta` wrapper vector after `metaUnivs` —

```
univPatches : Array UnivPatch
UnivPatch   ::= { arenaIdx : UInt64, univIdxs : Array UInt64 }
```

— empty (one zero byte, the count `N0(0)`) on the overwhelming majority of
constants. The arena key is exact because occurrence identity is
spelling-injective: `Ix.Level.mk*` hash spelling trees per node and
`Expr.mkSort`/`mkConst` fold those hashes into expression identity
(`Ix/Environment.lean:178-210`, `:333-345`), so occurrences sharing a
compile-cache entry (hence an arena root, `Ix/CompileM.lean:599-628`)
share a spelling, while spelling twins keep distinct arena subtrees.
A table-keyed alternative (patching `anonIdx → spelling`) is
**unsound**: canonicalization dedups distinct spellings onto one
entry, and a constant containing both a weird spelling and its
canonical form could restore only one of them. The patch obeys the
§10.5 provenance principle verbatim — it records the spelling of the
source occurrence it derives from, inherited through derivation,
never chosen at emission — and `Named.original` metas carry their own
patches (both meta slots are emitted; they describe different
constants' occurrences). Decompile applies patches at the
`.sort`/`.ref`/`.recur` arms, where the walk already pairs
expressions with arena indices; artifacts without patches (foreign
or pre-change) decompile to canonical spellings — semantically
equal, presentation-lossy, accepted.

**Kernel contract.** Anonymous ingress — the trust boundary feeding
checking and content hashing — never reads patches or extension
tables; patches influence no hash and no kernel judgment (a
malicious patch can only skew decompiled presentation, same trust
class as binder names, and is caught by the strict roundtrip gates).
**Meta** ingress, whose job is syntax-faithful reconstruction, is the
one kernel-side consumer: the original spelling rides as a
**decoration** on meta-mode `sort`/`const` occurrence nodes — folded
into the metadata-aware `metaAddr` (so interning and egress
memoization never collapse spelling twins, `Ix/Tc/Expr.lean:61-72`)
and **never** into the semantic `addr` (anon/meta address parity,
`tc-meta-addr`, is preserved; checking never sees spellings). Meta
egress replays the decoration at its `sort`/`const` arms
(`Ix/Tc/EgressLean.lean:119-128`) instead of egressing the
normalized kernel level. Decorations must not live on `KUniv` nodes
— KUniv interning is semantic-address-keyed and would collapse
spelling twins first-wins, the same lossiness as table-keyed
patches. Validation comparators are **never weakened**: the kernel
meta roundtrip (validate-lean phase 4) remains a strict syntactic
comparison and is an active spelling-fidelity gate through the
kernel's data path, complementing the decompiler gate (phase 5).
With stored content canonical, the anon roundtrip comparison is
strict too (the `reduceIxonUniv` modulo in `canonExpr` was deleted;
`Ix/Tc/Egress.lean` module doc).

**Decoration source.** Patches are the primary source: meta ingress
looks the occurrence's (post-mdata) arena index up in `univPatches`
and resolves the virtual indices through `univs ++ metaUnivs`. The
stage-1 rule — decorate from the primary table entry when its `mk*`
rebuild differs — remains as the patchless FALLBACK: on canonical
tables it never fires (P3), and it keeps hand-built raw-table
fixtures meaningful. The old surgery path copied head patches onto its
`CallSite` node; that node and its replay are retired (§8). Artifacts
predating the format carry a
"pre-normal-levels .ixe; recompile it" parse hint following the
pre-compact-keys precedent (`crates/ixon/src/serialize.rs`).

## 11. Sort Algorithms

### 11.1 User-class `sort_consts`

Iterative refinement (`src/ix/compile.rs:2526`):

```
Initial sort: lex by name (cs.sort_by_key(|x| x.name()))
classes := [cs]
loop:
  for each class with |class| > 1:
    ctx := MutConst::ctx(classes)
    sorted := sort_by_compare(class, ctx, cache, stt)
    groups := group_by(sorted, |a,b| eq_const(a, b, ctx, cache, stt))
    new_classes.extend(groups)
  re-sort each class by name
  if new_classes == classes: break
  classes := new_classes
```

`compare_const` and `eq_const` compare structurally under the current
partition, so alpha-equivalent constants end up grouped and
structurally-distinct constants end up separated. The refinement loop
terminates because the partition can only get finer, and there are
finitely many constants.

### 11.2 Nested-aux canonical expansion

The aux section is not sorted. The canonical expansion
(`expand_nested_block_canonical`, Lean `expandNestedBlock … (canonicalGroups
:= true)`) walks the canonical classes in order and appends auxes as it
discovers them; an external group opens as its compiled canonical classes,
and occurrences are deduplicated by their canonical key (§6.2). The result
is content-addressed: no source name enters the order. Source-walk aux
positions are related back to canonical positions by `compute_aux_perm`.

## 12. Worked Examples — Single Constants

### 12.1 α-rename

```lean
def f₁ : Nat → Nat := fun x => x + 1
def f₂ : Nat → Nat := fun y => y + 1
```

Under compile:

```
Ixon Expr for both:
  Lam( Ref(idx=Nat), App(App(Ref(idx=HAdd.hAdd), Var(0)), Nat(1)) )
```

The binder names `x` and `y` live in
`meta.arena[Binder { name: Address(x|y), info, … }]` — separate arena
entries, distinct addresses — but both addresses are outside the hash
input. `addr(f₁) == addr(f₂)`.

### 12.2 Presentation mdata strip

```text
e
Lean.Expr.mdata displayData e
```

When `displayData` contains only presentation fields, the compiler stores
it in the sidecar and both expressions produce the same anonymous bytes
on success. This example does not apply to `ix.contract` frames: the
compiler consumes them into semantic binder fields (§5.1).

### 12.3 Universe permutation (non-equal)

```lean
def h₁.{u, v} : Sort u → Sort v → Sort (max u v) := …
def h₂.{u, v} : Sort v → Sort u → Sort (max u v) := …
```

These are **not** α-equivalent: the order of universe params is part
of the structural signature. `addr(h₁) ≠ addr(h₂)`. Canonicity isn't
"equal up to any renaming" — it's equal up to the *specific*
equivalences in §1.

The level quotient (§10.6) keeps this boundary: the parameter *list*
order stays structural even as spellings *inside* level expressions
(`max u v` vs `max v u` at an occurrence) are quotiented.

### 12.4 Level-spelling twins (equal content, patched presentation)

```lean
axiom twin₁.{u, v} : Sort ((max u v) + 1)      -- succ-lifted spelling
axiom twin₂.{u, v} : Sort (max (u+1) (v+1))    -- Géran-canonical form
```

These ARE identified (§10.6): `canonUniv` maps both spellings to
`max (u+1) (v+1)` — the Géran linearization distributes `succ` into
`max`, the opposite direction from the kernel's `mk*` constructors —
so both constants intern the same primary `univs` entry and
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

The fixtures in `Tests/Ix/Compile/Mutual.lean` exercise the cases
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

Nested inductives are the hardest case. The pipeline:

```
expand_nested_block_canonical   (crates/compile/src/compile/aux_gen/nested.rs)
  → walks the canonical classes and replaces each
    `ExtInd (args-with-block-params)` with a synthetic `_nested.ExtInd_N`
    aux inductive sharing block params/levels, in discovery order (the
    canonical order; no sort).
  → dedupes occurrences by their canonical key (`addr_key`).

compute_aux_perm            (nested.rs:797)
  → builds the source-walk → canonical permutation for family generation.

Pass 3 images             (Ix/Compile/Image/Build.lean)
  → connect source-order auxiliary occurrences to the canonical family;
    Translate rewrites callers through those images.
```

### 14.1 `NestedSimple` — single inductive nesting

```lean
inductive Tree where
  | leaf : Nat → Tree
  | node : List Tree → Tree
```

Single inductive, no alpha-collapse. `expand_nested_block` creates one
aux `Tree._nested.List_1` with ctors mirroring `List.nil` and
`List.cons` but fixed to `Tree`. Canonical block:

```
Muts([
  Indc(Tree),                 // idx 0
  Indc(_nested.List_1),       // idx 1 — sole aux
])
```

Aux recursor `Tree.rec_1` lives at `RPrj { block: <rec-block>, idx: 1 }`.

### 14.2 `NestedAlphaCollapse` — dedup across aliases

```lean
mutual
  inductive TreeA
    | leaf | fromB : TreeB → TreeA | node : List TreeA → TreeA
  inductive TreeB
    | leaf | fromA : TreeA → TreeB | node : List TreeB → TreeB
end
```

`TreeA ≅ TreeB`, so `sort_consts` collapses them to one class with
`TreeA` as representative. Under the alias substitution, both
`List TreeA` and `List TreeB` rewrite to `List rep`, which — thanks to
`replace_if_nested`'s `aux_seen` dedup — yields **one** aux entry.
The canonical block has two members (`Indc(rep)`,
`Indc(_nested.List_1)`); not four.

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

Both blocks describe the same cyclic 3-inductive system over
`Array/Option/List`. They differ only in **source declaration order**,
which drives Lean's source-walk discovery of nested auxes into a
different `_N` numbering for each block.

The canonicity assertion:

```
addr(A)  ==  addr(A2)
addr(B)  ==  addr(B2)
addr(C)  ==  addr(C2)
addr(primary block)       ==  addr(primary block reordered)
addr(recursor block)      ==  addr(recursor block reordered)
```

This holds because:

- `sort_consts` produces the **same** class ordering for both blocks
  (alpha structure is source-order-blind);
- the canonical expansion assigns the **same canonical `_N`** to each
  nested aux: it walks the canonical classes, not the source order.

Without a canonical aux order, the two `Array/Option/List` auxes would be numbered
differently between the two blocks, and so would `A.rec_1` /
`A2.rec_1`, and so would every downstream constant that references
them. With structural aux sorting, the `_N`s match.

### 14.4 `NestedAuxOrderingAlpha` — combined alpha + aux sort

```lean
mutual
  inductive A | mk : Array B → Option A → A
  inductive B | mk : Array A → Option B → B
end
```

Here `A ≅ B`. After alpha-collapse both collapse to one representative,
and `Array rep` + `Option rep` become two distinct nested auxes
(different containers ⇒ different structural signatures). The canonical block:

```
Muts([
  Indc(rep),                   // idx 0 — alpha-class {A, B}
  Indc(_nested.Array_N),       // idx 1 — canonical aux position
  Indc(_nested.Option_M),      // idx 2 — canonical aux position
])
```

`N` and `M` are determined by structural comparison of the aux declarations
and their resolved references — content order, not source order.

## 15. Where Canonicity Comes From — Invariants by Module

A compact correspondence between the canonicity property and the code
that enforces it:

| Invariant                                                  | Enforced by                                                     |
| ---------------------------------------------------------- | --------------------------------------------------------------- |
| `Expr` has no binder names                                 | `src/ix/ixon/expr.rs` — no `name` field on `Lam/All/Let`        |
| Anonymous encoding omits presentation names/mdata and keeps semantic contracts | `Ix/CompileM.lean`, `Ix/SemanticContract.lean`; Rust `compile_expr` and `put_expr` |
| Hash is Blake3 over serializer output                      | `Constant::commit` at `serialize.rs:861` → `Address::hash`      |
| `sort_consts` is deterministic and refinement-stable       | `src/ix/compile.rs:2526-2564` (iterative refinement)            |
| Nested-aux dedup across aliases                            | `replace_if_nested` `aux_seen` table, `nested.rs:191-362`       |
| Nested-aux section is the canonical expansion's discovery order | `expand_nested_block_canonical`, `addr_key`, `crates/compile/src/compile/aux_gen/nested.rs` |
| Source auxiliary positions map to canonical positions or explicit out-of-component/evaporated cases | `compute_aux_perm`, `crates/compile/src/compile/aux_gen/nested.rs`; `AuxLayout` (§10.2) |
| Callers of changed auxiliary families use their images     | `Ix/Compile/Image/Build.lean`, `Ix/Compile/Pass/Translate.lean`, and Rust `compile/pass3/{build,translate}.rs` |
| Source expressions survive caller rewrites in metadata      | `_ix.inline`, `Ix/Compile/Pass/SideCar.lean`, and Rust `compile/pass3/sidecar.rs` |
| Optional original-kernel check isolates adversarial raw constants | `CompileOptions::check_originals`, `mutual.rs::check_originals`, `orig_kenv` in `compile/env.rs` |
| Stored primary order matches `sort_consts` (kernel-side)   | `validate_canonical_block_single_pass`, `src/ix/kernel/canonical_check.rs` (called from `ingress_muts_block`) |
| Aux ordering matches the canonical expansion             | `build_flat_block` (stored external groups), `crates/kernel/src/inductive.rs`; position-by-position recursor validation in `check_recursor` |

## 16. Testing Plan

The test strategy uses pairs expected to have the same or different
canonical encodings, with payload and address comparison as observations.
It does not decide general mathematical equivalence.

### 16.1 Rust-side unit tests

`src/ix/compile/canonicity_tests.rs` (new file, `#[cfg(test)]`):

- **`alpha_rename_hashes_equal`** — `λx.x+1` vs `λy.y+1` → same address.
- **`mdata_wrapper_stripped`** — `e` vs presentation-only `Mdata(kv, e)` → same address; semantic-contract frames are excluded.
- **`mutual_reorder_invariant`** — declare `[A, B]` and `[B, A]`
  (alpha-equivalent) → same block address.
- **`mutual_rename_invariant`** — declare `[A, B]` and `[X, Y]`
  with `A↔X, B↔Y` → same block address.
- **`nested_rename_invariant`** — `Tree | mk : List Tree → Tree` vs
  `Tree' | mk : List Tree' → Tree'` → same address; the
  `_nested.List_1` aux must collapse identically across both.
- **`nested_aux_permutation`** — `NestedAuxOrdering` fixture, two
  source orders, assert primary + aux block addresses match.
- **`non_equivalent_distinct`** — `λx.x+1` vs `λx.x+2` → different.
- **`universe_permutation_distinct`** — `f.{u,v}` vs `f.{v,u}` → different.
- **`sort_consts_classes_stable`** — invariant test: repeated sort on
  same input yields same classes.

### 16.2 Validate-aux phases

`Tests/Ix/Compile/ValidateAux.lean` ships the validation phases below.
The numbering matches current test output:

| Phase | Name                                   | Checks                                                               |
| ----- | -------------------------------------- | -------------------------------------------------------------------- |
| 1     | Compilation                            | Every seed compiles and gets an address                               |
| 2     | Aux_gen congruence                     | In-memory aux_gen output ≡ Lean original modulo canonical reorder     |
| 3     | No ephemeral leaks                     | Intermediate compile-time addresses don't leak into the final env     |
| 4     | Alpha-equivalence canonicity           | Same-class names share the canonical address                          |
| 4b    | Cross-namespace canonicity             | Structurally identical declarations across namespaces share addresses |
| 5     | Decompile (with debug)                 | Full env round-trips with compile-state metadata live                 |
| 6     | Aux congruence (roundtrip)             | Decompiled aux_gen ≡ Lean original modulo canonical reorder           |
| 7     | Decompile (no debug)                   | Serialize → drop state → deserialize → decompile round-trip           |
| 7b    | Roundtrip fidelity                     | Per-constant content address matches after Phase 7                    |
| 8     | Nested detection                       | `build_compile_flat_block` finds the expected auxiliaries             |

Phases 2 and 6 both compare aux_gen output against Lean originals using
the permutation-aware congruence comparator in `src/ix/congruence/perm.rs`.
Phase 4b is skipped for fully absent fixture groups when validating an
arbitrary environment that does not import the test fixtures.

### 16.3 Permutation-Aware Congruence

Aux-gen congruence is checked by `src/ix/congruence/perm.rs`, not by
rewriting Lean's source-order constants into a separate canonical form.
The comparator carries `AuxLayout`, constructor counts, source/canonical
member correspondence, and a `const_addr` map so it can compare Lean's
source telescopes against Ix's canonical aux layout directly.

### 16.4 Fixture Coverage

`Tests/Ix/Compile/Mutual.lean` and `Tests/Ix/Compile/Canonicity.lean`
cover reordered mutuals, alpha-collapse, nested aux ordering, over-merge
splits, parameterized nested blocks, and cross-namespace twins. New
fixtures should be added when a new equivalence mechanism is introduced
or when a failure mode cannot be reduced to one of those existing shapes.

### 16.6 Kernel canonicity validation

The kernel-side validator (§4.4) is exercised by both unit tests and
integration tests:

**Unit tests** (`src/ix/kernel/canonical_check.rs::tests`):

- `compare_kuniv_*` — universe comparator agrees with compile-side
  `compare_level` on the cases visible in Anon mode.
- `compare_kexpr_alpha_blind` — binder-named and binder-anonymous
  λ/∀/let bodies compare Equal under the comparator.
- `compare_kexpr_var_ordering` — `Var(0) < Var(1)` etc.
- `compare_kexpr_const_external_by_addr` — refs not in `KMutCtx`
  fall back to `Address` order.
- `compare_kexpr_const_block_local` — refs in `KMutCtx` resolve to
  class indices.
- `compare_kindc_alpha_collapse` — structurally-equal Indcs compare
  Equal.
- `sort_kconsts_canonical_three_indcs` — three Indcs in arbitrary
  input order produce the canonical (params-ascending) output.
- `sort_kconsts_alpha_collapses_into_one_class` — alpha-equivalent
  Indcs collapse to a single class.
- `validate_single_pass_accepts_canonical_order` — Ok on canonical
  input.
- `validate_single_pass_rejects_swap` — `Greater` rejection.
- `validate_single_pass_rejects_uncollapsed_alpha` — `Equal`
  rejection.

**Integration tests** (existing test suites that exercise the
validator end-to-end):

- `lake test -- validate-aux --ignored` — must remain at 0 failures
  (Phases 7 and 7b round-trip every constant through the kernel).
- `lake test -- kernel-tutorial --ignored` — 267/267, covering the
  manually-constructed kernel fixtures.
- `lake test -- kernel-check-const --ignored` — focus list of the
  Mathlib failure shapes; this is where Step 5 of the
  kernel-canonicity port shows up: stored aux recursor positions
  must align with the kernel-canonical aux order produced by Step 4.

### 16.5 Roundtrip fixed-point

The strongest test of canonicity + metadata is:

```
for c in env.constants:
    ixon  = compile(c, env)
    lean  = decompile(ixon)
    ixon2 = compile(lean, env')
    assert ixon.bytes == ixon2.bytes
```

If any step diverges, either (a) canonicity is broken (different
compile paths yielded different canonical forms for the same input),
or (b) metadata is incomplete (decompile didn't recover enough info
for recompile to find the same canonical form). Both are first-class
bugs.

This is implemented as validate-aux Phase 7b (§16.2), which checks that
each constant's content address is stable after serialize → deserialize →
decompile → recompile.

### 16.7 Level canonicalization (§10.6)

Landed with the §17.9 stages:

- `canonUniv` property tests P1–P6 in both languages (Rust in
  `crates/ixon/src/univ.rs` tests; Lean next to the existing
  level-algebra unit tests), with the kernel `NormLevel`
  implementations as the P4 oracle.
- A `LevelSpellings` fixture namespace in the validate-aux closure:
  one deliberately unnormalized spelling per `mk*` rule (M1–M7 /
  I1–I5) in both `Sort` and `Const`-arg position; order/association
  twins (`max u v` / `max v u`, reassociated `max`-chains) asserting
  post-stage-2 identical anon addresses with differing metadata; a
  constant containing both a spelling and its canonical form (the
  table-keyed-patch killer) asserting exact decompile; a WF-recursion
  `._unary.eq_def` reproducing the Mathlib shape.
- Decoration roundtrip: spelling in → meta ingress decorates → meta
  egress restores — pinned strictly by `tc-roundtrip` and
  `tc-meta-addr` from stage 1, before any format change.
- Extension-append fixture: a synthetic `Named` with populated
  `metaRefs`/`metaUnivs`, decompiled identically by both pipelines
  (FFI cross-check).
- `univPatches`/`metaUnivs` serde vectors in the property-test
  generators and hand-written wire fixtures.

### 16.8 Canonical sharing (§6.7)

- `lake test -- exact-sharing` covers the plan fixtures, with exact bytes
  (`T2 → T2` in 17 bytes, from 20 unshared). It also covers the uniform
  optimizer against the width-state reference, the tiered construction's
  slot allocation, idempotence, and brute force for the first tier.
- `lake test -- exact-sharing-ffi` compares Lean and Rust bytes on fixtures
  and on generated inputs.
- The Rust crate's `sharing_exact` tests cover:
  - representation independence: every valid incoming encoding normalizes
    to the same bytes;
  - parallel against sequential byte identity.
- Roundtrip (§16.5) adds the end-to-end check: a recompiled block must
  reproduce its address, so decompile's recompile and the compiler must
  produce the same canonical sharing.

## 17. Open Work

### 17.1 PermCtx Builder Consolidation

`src/ffi/lean_env.rs` currently has separate builders for validate-aux
Phase 2 and rust-compile Phase 1b. They should be factored into one
shared `PermCtx` construction path so the two validation modes cannot
drift in how they populate `aux_layout`, constructor counts, and
`const_addr`.

### 17.2 Rust auxiliary-regeneration path

The remaining singleton-class construction is in Rust's
`crates/compile/src/decompile.rs`, `decompile_block_aux_gen`. It deliberately
regenerates source-walk order with no aux-layout override and checks the
result against the original address (§9.3). Replacing it with canonical
classes is not a mechanical cleanup: source numbering, alpha-collapse and
the roundtrip check must continue to agree. This is separate from Lean's
full source decompiler, which reads original records and has no regeneration
state. No shared decompile-correctness theorem is claimed.

### 17.3 `check_decompile` scoping

Keep ordinary `check_decompile` scoped to source-faithful decompile output;
Phase 6 and Phase 7b are authoritative for aux_gen-specific canonical
roundtrip behavior.

### 17.4 `compute_aux_perm` Regression Guards

The out-of-SCC sentinel path is wired and covered by validate-aux. Keep
targeted regression fixtures for multi-SCC blocks whose `InductiveVal.all`
contains members split out by Ix's SCC pass, because those are the cases
where a source aux can belong to Lean's full mutual numbering but not to the
current canonical SCC block.

### 17.5 Docstring persistence

Add `doc_string: Option<Address>` to `ConstantMeta`. Ingest via
`Lean.findDocString?` at the FFI boundary
(`src/ffi/lean_env.rs`); re-attach in decompile via
`Lean.addDocString`. Optional but trivial to add.

### 17.6 Regression guards

- Assert `generate_aux_patches` called twice with same inputs returns
  byte-equal patches.
- Assert decompile's re-derived canonical aux order equals the stored
  `AuxLayout` for every nested-aux block.
- Targeted test: compile `NestedAuxOrdering { A | B | C }` and
  `NestedAuxOrdering.second { C2 | A2 | B2 }` (permuted sources),
  assert block addresses are equal.

### 17.7 `kernel-check-const` Category B residue

After the §4.4 kernel-canonicity port (position-based stored-recursor
lookup; the kernel no longer sorts auxes, §6.2),
Categories A, C, F, and G still showed some residual failures. Some failure modes may also reflect orthogonal
issues (e.g. `String.Legacy.back ""` reduction, `_sparseCasesOn_N`
regeneration) that surface alongside the canonical-order
mismatches but have unrelated root causes.

### 17.8 Alias-occurrence metadata audit (§10.5)

§10.5 fixes display names at synthesized occurrences as inherited
source spellings emitted from block-scoped kernel contexts. The
production Rust scheduler has been block-scoped (`compile/env.rs`:
fresh `KernelCtx` per block compile; the aux-dump and validate-aux
Phase 2 paths already were). Remaining audit items:

- **Restoration-heuristic mirror parity.** The kernel-egress
  restoration passes are heuristic: hint candidacy is `App`/`Proj`
  only (`Pass::candidate` in `source_name_hints.rs` — a bare
  aliased `Const` surviving a genuinely-reducing WHNF is not
  restored), and hint slots are first-insert-wins (two same-address
  source subterms take the traversal-first spelling). The Lean
  mirrors (`collectLeanSourceNameHints` /
  `restoreLeanSourceNameHints` / `restoreSourceNamesSameContent` in
  `Ix/AuxGen/Kernel.lean`) match arm-for-arm; what diverged — and
  produced the Mathlib redStep instance — was the **key
  equivalence**: the Lean side keys hints by `Ix.Tc.KExpr` content
  addresses, while the Rust side keyed by `KExpr::hash_key()`, which
  is an intern-assigned uid, fresh for every un-interned
  `to_kexpr_static` construction — so no restore-time key ever
  matched a collect-time key and the Rust hint pass restored nothing.
  Originally fixed by `kexpr_content_key` (a pure name-erased structural
  digest mirroring the `ExprKey`/`Ix.Tc` equivalence) and by making the
  WHNF no-op test structural (`==`) rather than uid equality. The hint
  pass now uses exact, pass-local structural identities instead of that
  digest, with full shallow-key equality on hash collisions. Any future
  keying change must preserve that both sides induce the identical
  equivalence.
- **Lean `nameForAddr` fallback.** `TcScopeSt.nameForAddr`
  (`Ix/AuxGen/Kernel.lean`) resolves a provisional kernel address by
  a linear scan of `cenv.nameToNamed` in `HashMap` iteration order —
  non-deterministic when the address is multiply-named. Confirm its
  result cannot reach emitted metadata, or make the scan canonical.
- **Rust decompile Pass 2 shared context.** The decompiler's
  regeneration loop (`decompile.rs`) reuses one `KernelCtx` across
  blocks (serial and deterministic, size-triggered clears). A checker
  cannot perturb emitted bytes, but a restoration-hole hit that
  differs from the block-scoped compile side could produce a spurious
  congruence failure; consider block-scoping it too.
- **Decompile name fallback via `addrToName`.**
  `Ixon.Env.addrToName` is single-valued (last-registered wins, i.e.
  the greatest alias in name-hash order) and serves as the
  decompiler's fallback when an occurrence has no arena `.ref` name
  (`Ix/DecompileM.lean`). Confirm no §10.5-governed position reaches
  this fallback.
- **Evaporated auxiliaries.** Aux names without `Named.original` are
  decompiled from the regenerated `constMeta` and compared
  name-sensitively against the source env
  (`Tests/Ix/Compile/DecompileDiff.lean`) — the one gate path that
  reads regenerated metas directly. It stays green exactly when
  emission inherits source spellings.

Pin the rule with reduced fixtures — a one-block alpha class, and
separately the cross-block coincident shape of §13.5 in **both
orientations** (`A (B x)` and `B (A y)`; the mirrored orientation
distinguishes spelling inheritance from any first-seen or least-name
policy) — asserting metadata byte-equality between the two compilers,
in the spirit of the `ZFA` family (§6.0).

### 17.9 Universe-level canonicalization staging (§10.6) — LANDED

All stages complete (2026-08-07), executed Rust-pipeline-first (Rust
compiler + kernel end-to-end, validated by Rust-only gates, then the
Lean mirror against the cross-compiler gates). The landed record:

**Stage 1 (no format change):** meta-ingress spelling decorations +
meta-egress replay in both kernels; the Lean decompiler
extension-append fix; the `LevelSpellings` fixtures (§16.7).

**Probe (D8):** `dump_reducible_univs` measured the whole-Mathlib
blast radius — 373,799 Géran-noncanonical entries in 134,929
constants (~1.04 M patch occurrences, ~10.9 MB, 0.34%), 79,088
spelling-collision constants (the table-keyed-patch killer
population), 84% transitive-dependent closure, 44 pinned primitives
(56 pins once dependent-address shifts are counted).

**Stage 2 (one format break):** `canonUniv` + P1–P6 in both
languages (the O1 gating construction settled by per-atom gate
inversion, §10.6); the `univPatches` wrapper vector across both
serializers, demoted encoders, FFI, diff labels, generators, and
fixtures; compile-side canonicalization + patch emission in both
pipelines; decompile patch replay; the decoration source switch to
patches (stage-1 rule retained as the patchless fallback); phase 3
strict; `univEq` empty-entry-insensitive (the exact semantic
quotient, §10.6); primitive pins regenerated in all mirrors
(`prim_addrs.rs`, `Ix/Tc/Primitive.lean`, the IxVM address
literals); artifacts regenerated with the format-break hint.

**Acceptance evidence:** `ix validate` and `ix validate-lean` at
whole-Mathlib scale both `RESULT: 0 total failures` (736,624
constants; phase 4 = 714,346 spellings checked / 0); Rust kernel
typecheck 736,624/736,624; both compilers byte-ALIGNED
(3,155,562,665 bytes); census probe on regenerated artifacts:
`Géran-noncanonical: 0`, collision constants 0.

**Follow-ups (open):** kernel-side univ-table canonicity enforcement
at ingress (§4.4-style, all three kernels, plus a foreign-`.ixe`
policy — reject, never silently canonicalize); Tc Verify-layer
proofs of P1/P2/P4.

## 18. Summary

The current implementation separates these obligations:

1. Anonymous payloads omit binder names and presentation metadata, while
   retaining semantic binder contracts lowered from source annotations.
2. Canonical classes determine mutual-block order and alpha-collapse;
   nested expansion uses canonical dependency identities.
3. Pass 3 images and occurrence passes rewrite references to changed
   auxiliary families. The retired call-site surgery is documented in §8.
4. Canonical sharing uses the fixed K16 rule, with successful-run proofs
   and explicit remaining totality/cost obligations (§6.7).
5. Metadata and original records support source reconstruction under the
   distinct Lean and Rust paths (§9.3); they are outside certification.
6. Kernel checks independently constrain stored block order and recursor
   layout (§4.4). Their acceptance does not establish that compilation
   preserved the source value.

The tests in §16 observe payload/address equality and reconstruction
fidelity on their inputs. The full compiler value-preservation composition
remains unproved and required in this PR.

## 19. Cross-References

- [Ixon](Ixon.md) — checked payload grammar, metadata and v4/v5 environment envelopes.
- [Canonical sharing](sharing-minimum.md#14-canonical-rule-revision-sharing-k16-greedy-v1)
  and [its proof inventory](Ixon.md#what-is-proved-and-what-is-not) — the fixed
  family, successful-run contracts and remaining totality/cost work.
- [Compiler driver](../Ix/CompileDriver.lean) and
  [Rust compiler](../crates/compile/src/compile.rs) — scheduling, block compilation,
  record assembly and publication.
- [Lean canonicalization](../Ix/Compile/Canon.lean) and
  [Rust mutual compilation](../crates/compile/src/compile/mutual.rs) — canonical
  classes, auxiliary generation and original-record handling.
- [Pass 3 module map](../crates/compile/src/compile/pass3/mod.rs),
  [image construction](../Ix/Compile/Image/Build.lean),
  [caller rewriting](../Ix/Compile/Pass/Translate.lean) and
  [occurrence passes](../Ix/Compile/Pass/Opt/Engine.lean) — current replacements
  for the retired surgery mechanism.
- [Rust nested expansion](../crates/compile/src/compile/aux_gen/nested.rs) and
  [recursor generation](../crates/compile/src/compile/aux_gen/recursor.rs) —
  canonical expansion, source/canonical positions and generated auxiliaries.
- [Rust canonical checker](../crates/kernel/src/canonical_check.rs),
  [ingress](../crates/kernel/src/ingress.rs) and
  [inductive checker](../crates/kernel/src/inductive.rs) — block-order and
  recursor-layout checks; [the certified checker](kernel.md) is a distinct entry.
- [Lean full decompile](../Ix/DecompileDriver.lean),
  [original-record reader](../Ix/DecompileM.lean) and
  [Rust decompile](../crates/compile/src/decompile.rs) — the distinct source
  reconstruction paths in §9.3.
- [Environment records](../crates/ixon/src/env.rs) and
  [metadata codec](../crates/ixon/src/metadata.rs) — `Named`, `AuxLayout` and
  source presentation data.
- [Mutual fixtures](../Tests/Ix/Compile/Mutual.lean),
  [auxiliary validation](../Tests/Ix/Compile/ValidateAux.lean) and
  [Pass 3 parity](../Tests/Ix/Compile/Pass3RustParity.lean) — concrete test entry points.
