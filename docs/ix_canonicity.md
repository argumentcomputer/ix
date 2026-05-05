# Anonymous Canonicity in Ix

> This is the authoritative spec for **anonymous canonicity** — the
> foundational content-addressing property of the Ix compiler. It covers
> the theory (what the property is and why we need it), the operational
> pipeline that achieves it (compile, decompile, surgery, metadata),
> worked examples from `Tests/Ix/Compile/Mutual.lean`, a testing plan,
> and the currently-open implementation work.
>
> Companion document: [`docs/Ixon.md`](./Ixon.md) (binary format
> reference).

---

## 1. The Property

Given a Lean 4 `ConstantInfo` `c`, compilation produces a content-address
`addr(c) ∈ Ixon`. The **anonymous canonicity** property is:

```
For every pair (c₁, c₂) of Lean constants:

    addr(c₁) = addr(c₂)
    ⇔
    c₁ and c₂ are structurally identical modulo:
      - local variable names
      - declaration metadata (mdata, binder info, docstrings, source positions)
      - source declaration order within mutual blocks
      - nested-inductive aux discovery order
      - hygiene annotations on Name components
```

Equivalently: two Lean constants share a hash iff they denote the same
mathematical object modulo cosmetic choices.

Informally: **renaming a bound variable, reordering a mutual block, or
decorating a term with `@[inline]` does not move the content address.**
If it does, canonicity is broken and the property fails — which in turn
breaks the zk-PCC story, because two parties compiling the same library
would produce different hashes and could not share proofs.

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

## 3. The Epimorphism / Isomorphism Pair

Write `Source` for the set of Lean source constants and `Canonical` for
the set of content addresses. Compilation induces two maps:

```
Source ──(compile)──→ Canonical              (many-to-one: α-equivalent sources
                                              collapse to one canonical form)
Source ──(compile)──→ Canonical × Metadata   (bijective: metadata preserves
                                              the information erased by compile)
```

- **Canonical alone is epimorphic onto Source.** Renaming, reordering,
  and stripping decoration are surjective: any canonical form is the image
  of some Lean term, but different Lean terms can share one canonical.
- **Canonical + metadata is isomorphic to Source** (modulo source
  ranges and hygiene, which are explicitly out of scope — see §5.3).
  The metadata sidecar carries exactly the information needed to
  reconstruct a particular Lean-visible term — binder names, mdata
  wrappers, source member order, docstrings — without contributing to
  the hash.

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

where `Lean' ≡ Lean` as Lean `ConstantInfo`s, not just observationally.

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

Everything that depends on source choices is stripped before hashing:

| Category                           | Where it's erased                                    |
| ---------------------------------- | ---------------------------------------------------- |
| Bound variable names (λ, ∀, let)   | `Expr::Lam/All/Let` has no `name` field — `src/ix/ixon/expr.rs` |
| `BinderInfo` (impl/inst/strict)    | not serialized in `put_expr`                         |
| `Expr.mdata` wrappers              | canonical form has no `Mdata` node                   |
| Free variable identity             | FVar and MVar are rejected — `compile.rs:848-857`    |
| De Bruijn depth artifacts          | indices are **the** identifier; no names survive     |
| Lean `InductiveVal.all` order      | replaced by `sort_consts` canonical class order; kernel enforces via `validate_canonical_block_single_pass` at ingress (§4.4) |
| Nested-aux discovery order         | replaced by structural aux sort; kernel enforces via `sort_kconsts` on rediscovered aux + position-by-position recursor match (§4.4) |
| `_N` suffixes on aux names         | internal `_nested.Ext_N` uses canonical `N`          |
| Hygiene info on `Name`             | stripped by `compile_name`                           |

### 5.2 Preserved in the metadata sidecar

Everything needed to round-trip back to a source-faithful Lean
`ConstantInfo`:

| Category                                | Where it lives                                       |
| --------------------------------------- | ---------------------------------------------------- |
| Binder names, `BinderInfo`              | `ExprMetaData::Binder { name, info, … }`             |
| Let binders                             | `ExprMetaData::LetBinder`                            |
| `Expr.mdata` KVMaps                     | `ExprMetaData::Mdata`                                |
| Reference names (per `Const` / `Rec`)   | `ExprMetaData::Ref`                                  |
| Projection struct name                  | `ExprMetaData::Prj`                                  |
| Call-site source/canonical metadata     | `ExprMetaData::CallSite { entries, canon_meta }`     |
| Level-parameter names                   | `ConstantMetaInfo::*.lvls`                           |
| `InductiveVal.all` (Lean source order)  | `ConstantMetaInfo::{Def,Indc,Rec}.all`               |
| `ReducibilityHints`                     | `ConstantMetaInfo::Def.hints`                        |
| Original pre-aux_gen form               | `Named.original = Some((addr, meta))`                |
| Aux-name permutation (nested)           | `stt.aux_perms` in-memory → `ConstantMetaInfo::Muts.aux_layout` on disk — §10.2 |
| Docstrings                              | planned: `ConstantMeta.doc_string: Option<Address>`  |

### 5.3 Explicitly **not** preserved

Source positions (`DeclarationRange`) and Lean's editor hygiene traces
are out of scope. Canonical + metadata yields a Lean term equal modulo
source-range and hygiene — which is enough for kernel, elaborator, and
proof-carrying use cases.

## 6. The Canonical Block Layout

A mutual inductive declaration in Lean generates **many** Ixon blocks,
not one monolithic block. Each kind of auxiliary lives in its own
canonical `Muts` block, compiled in a specific downstream order, and
the blocks link to each other via content-address projections.
This section is the structural reference for what's in each block.

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
`Inductive`. This matters for projections (see [projections](inter-block-references--projections)).

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

#### `casesOn` block — `Muts([ Defn, Defn, … ])`

```
Muts([
  Defn(rep₀.casesOn), Defn(rep₁.casesOn), … Defn(rep_{n−1}.casesOn),
])
```

One `Defn` per user representative. Auxiliary inductives don't get
their own `.casesOn` (Lean only emits them for user types). Each
`.casesOn` body is `λ params motive indices major, rep.rec p₀ … (λ … PUnit) …`
— the `.rec` with non-target motives stubbed to `PUnit`.

#### `recOn` block — `Muts([ Defn, Defn, … ])`

```
Muts([
  Defn(rep₀.recOn), Defn(rep₁.recOn), … Defn(rep_{n−1}.recOn),
])
```

Same shape as `.casesOn` but preserves all motives and reorders the
binder chain `(major after minors)` to `(major before minors)` —
matching Lean's `Iff.rec` / `Eq.rec` style.

#### `below` blocks — two of them

```
Muts([                               // BELOW INDC BLOCK (Prop case)
  Indc(rep₀.below), Indc(rep₁.below), …,
])

Muts([                               // BELOW DEF BLOCK (Type case + nested aux)
  Defn(rep₀.below), Defn(rep₁.below), …,
  Defn(rep₀.below_1), … Defn(rep₀.below_m),    // nested aux .below_N
])
```

`.below` lives in different blocks depending on the inductive's universe:
inductives in `Prop` get an `Inductive` payload (no value, just a
type-level predicate); inductives in `Type` get a `Definition`
payload (value-level, returning `PProd` of motives).

#### `below.rec` block — Prop case only

```
Muts([                               // BELOW.REC BLOCK
  Recr(rep₀.below.rec), Recr(rep₁.below.rec), …,
])
```

Recursors for the Prop-case `.below` inductives.

#### `brecOn` blocks — three of them

```
Muts([ Defn(rep₀.brecOn.go), … ])    // BRECON.GO BLOCK (sub-defs)
Muts([ Defn(rep₀.brecOn),    … ])    // BRECON BLOCK (main entry)
Muts([ Defn(rep₀.brecOn.eq), … ])    // BRECON.EQ BLOCK (unfolding lemmas)
```

Three batches because of dependency order: `.go` is the inner worker,
`.brecOn` calls into `.go`, and `.eq` proves the unfolding equation
for `.brecOn`.

#### Inter-block references — projections

Individual constants are exposed as **projections** into their
containing `Muts` block:

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
A.casesOn                DPrj { block: <cases-block-addr>, idx: 0 }
A.below                  DPrj/IPrj { block: <below-block-addr>, idx: 0 }
A.brecOn                 DPrj { block: <brecon-block-addr>, idx: 0 }
A.brecOn.go              DPrj { block: <brecon-go-block-addr>, idx: 0 }
A.brecOn.eq              DPrj { block: <brecon-eq-block-addr>, idx: 0 }
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

- **Aux `.below_N` definitions sit inside the existing below-def
  block.** They're appended after the user-class `.below` defs.

- **`.casesOn` and `.recOn` have no aux variants.** Lean only emits
  them for user-declared inductives. The blocks contain exactly
  `n` entries.

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

compile_aux_block(cases_on_defs)        // CasesOn definitions
  → Muts([ Defn(U₀.casesOn), Defn(U₁.casesOn), … ])

compile_aux_block(rec_on_defs)          // RecOn definitions
  → Muts([ Defn(U₀.recOn), Defn(U₁.recOn), … ])

compile_aux_block(below_indcs)          // Prop-level .below inductives
  → Muts([ Indc(U₀.below), Indc(U₁.below), … ])

compile_aux_block(below_defs)           // Type-level .below definitions
  → Muts([ Defn(U₀.below), Defn(U₁.below), …,
           Defn(U₀.below_1), Defn(U₀.below_2), … ])

compile_below_recursors(below_indcs)    // .below's own recursors (Prop case)
  → Muts([ Recr(U₀.below.rec), … ])

compile_aux_block(brecon_defs) × 3      // BRecOn, split into 3 batches
  → Muts([ Defn(U₀.brecOn.go), … ])     //   batch 0: .go sub-definitions
  → Muts([ Defn(U₀.brecOn), … ])        //   batch 1: main .brecOn
  → Muts([ Defn(U₀.brecOn.eq), … ])     //   batch 2: .eq sub-definitions
```

Ixon references between these blocks are **content-address projections**
(`InductiveProj`, `RecursorProj`, `DefinitionProj`): each projection
carries a block address and an index within that block's member list.
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
  block under the alias's name mapping.

Every downstream block (rec, casesOn, recOn, below, brecOn) inherits
this user-class ordering by construction — each block enumerates the
primary members in the same order.

### 6.2 Nested-aux section ordering

The canonical nested-aux ordering is a **property recomputed at
validation time**, not a stored serialization. It appears positionally
in the **recursor block** (and below / brecOn derivatives), but never
in the inductive block — aux inductives are not stored on disk
(§6.0).

- `expand_nested_block` walks user-class ctors, replacing each nested
  occurrence `ExtInd (args containing block params)` with a synthetic
  `_nested.ExtInd_N α` aux inductive (compile time).
- `sort_aux_by_content_hash` is a legacy name. The implementation
  builds temporary aux `Indc` values and runs `sort_consts` on the
  aux slice, so ordering and alpha-collapse use the same structural
  relation as normal mutual blocks.
- References to already-compiled originals/external constants
  compare by compiled content address. If a referenced name cannot
  be resolved, the comparator errors instead of falling back to a
  namespace-sensitive name hash.
- Alpha-equivalent auxes collapse into one aux class; source auxes
  that share that class all point at the same canonical
  representative aux inductive.

This gives a **source-order-independent** canonical layout: any
permutation of user source declaration produces the same ordered
aux section, because the sort key is structural content plus
resolved addresses.

The recursor block's aux positions (`<addr>.rec_1`, `.rec_2`, …) are
the **only stored manifestation** of this canonical ordering. The
kernel revalidates by:

1. Rediscovering aux from primary ctor walks
   (`build_flat_block` in `src/ix/kernel/inductive.rs`).
2. Synthesizing comparable `KConst::Indc` views (instantiating ext
   types with `spec_params`, replacing aux ctor result heads with
   the synthetic aux KId).
3. Running `sort_kconsts` (§4.4) to compute the kernel-canonical
   aux order.
4. Position-by-position validating each stored aux recursor against
   the kernel-canonical aux at the same offset
   (`is_def_eq` on the recursor type).

Compile-side and kernel-side use the same comparator
(`sort_consts` ↔ `sort_kconsts`), so they produce the same canonical
order on the same input. A divergence is a kernel correctness bug,
immediately observable as a `kernel-check-const` regression.

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

### 6.5 The content-address recipe

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

## 7. The Compile Pipeline

```
Lean.Env
  │
  │  (for each mutual inductive block)
  ▼
sort_consts → sorted_classes: Vec<Vec<Name>>                  [compile.rs]
  │                                                           // alpha-collapse
  │
  ▼
compile_mutual_block(primary_inductives)                      [compile.rs]
  → Muts([ Indc(U₀), Indc(U₁), …, Indc(A₀), Indc(A₁), … ])    // INDUCTIVE BLOCK
  // Constructors are embedded in each Indc's `ctors` field.
  //
  // Nested-aux inductives live in this SAME block, after the user
  // classes. They're the `_nested.ExtInd_N` synthetic inductives
  // built by expand_nested_block and structurally sorted.
  │
  │
  ▼
generate_aux_patches(sorted_classes, original_all, …)         [aux_gen.rs]
  │
  ├─ expand_nested_block(ordered_originals, alias_to_rep)     [nested.rs]
  │    → ExpandedBlock { types, aux_to_nested, aux_ctor_map, … }
  │
  ├─ sort_aux_by_content_hash(&mut expanded, stt)             [nested.rs]
  │    → perm[old_j] = new_j  (mutates expanded.types in place)
  │
  ├─ compute_aux_perm(expanded, original_all, …)              [nested.rs]
  │    → perm[source_j] = canonical_i
  │
  ├─ generate_recursors_from_expanded(sorted_classes, expanded) [recursor.rs]
  │    → Vec<(Name, RecursorVal)>  // in canonical layout
  │
  ├─ RestoreCtx::restore — map _nested.X_N references in rec bodies
  │    back to ExtInd spec_params form                        [expr_utils.rs]
  │
  ├─ generate_below_constants, generate_brecon_constants,
  │    generate_cases_on, generate_rec_on                     [below/brecon/…]
  │    → Derived patches (Defn or Indc, per aux kind)
  │
  └─ alias_patches — deep-rename each rep's patches for each
       non-rep class member                                   [aux_gen.rs:648-700]
  │
  ▼
AuxPatchesOutput { patches, perm, … }
  │
  │  (per aux kind, each compiled into its OWN downstream Muts block:)
  ▼
compile_aux_block(rec_consts)     → Muts([ Recr(…), … ])      // REC BLOCK
compile_aux_block(cases_on_defs)  → Muts([ Defn(…), … ])      // CASES_ON BLOCK
compile_aux_block(rec_on_defs)    → Muts([ Defn(…), … ])      // REC_ON BLOCK
compile_aux_block(below_indcs)    → Muts([ Indc(…), … ])      // BELOW INDC BLOCK (Prop)
compile_aux_block(below_defs)     → Muts([ Defn(…), … ])      // BELOW DEF BLOCK (Type)
compile_below_recursors(…)        → Muts([ Recr(…), … ])      // BELOW.REC BLOCK (Prop)
compile_aux_block(brecon_go)      → Muts([ Defn(…), … ])      // BRECON.GO BLOCK
compile_aux_block(brecon_main)    → Muts([ Defn(…), … ])      // BRECON BLOCK
compile_aux_block(brecon_eq)      → Muts([ Defn(…), … ])      // BRECON.EQ BLOCK
  │
  │  Each block's member order is [user-classes (sort_consts) | aux (structural sort)].
  │  Blocks reference each other via content-address projections
  │  (IndcProj / RecrProj / DefnProj), NOT by embedding.
  │
  ▼
stt.aux_perms.insert(
    name_of(<source_all[0]>),           // key: Name (from env.get_name(addr))
    AuxLayout { perm, source_ctor_counts },
)
  │
  ▼
compute_call_site_plans (per aux name) → surgery              [surgery.rs]
  │
  ▼
Ixon bytes (many canonical blocks + per-block metadata)
```

Five invariants hold at the pipeline seams:

1. **Ingress is name-only via content-hash.** `compile_name(name)`
   uses `Blake3(name.components)`; hygiene is stripped.
2. **Sort is total, deterministic, and refinement-closed.**
   `sort_consts` iterates until the partition of a mutual block into
   equivalence classes stabilizes. Name-based tie-breaking only selects
   *within* a class — class membership is determined by structure.
3. **Nested-aux discovery is de-duped by bundle-hash.**
   `replace_if_nested` in `nested.rs` keeps an `aux_seen: Vec<(Hash, Name)>`
   table so alpha-equivalent nested occurrences reuse the same aux name.
4. **Nested-aux section is structurally sorted.** `sort_aux_by_content_hash`
   renames `_nested.Ext_<new_idx>` after `sort_consts`-style structural
   sorting, so two semantically equal blocks declared in different source
   orders produce byte-equal aux sections.
5. **Binder names exit the bytes, into the arena.** `put_expr` omits
   names on `Lam`/`All`/`Let`; the arena records them as
   `ExprMetaData::Binder` entries that never contribute to
   `Constant::commit()`.

## 8. Call-Site Surgery

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
3. Both entries go into `env.consts` (keyed by distinct addresses);
   the `Named` entry points at the canonical via `addr` and retains
   the original via `original`.

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

For aux_gen-rewritten mutual blocks, decompile's canonical path needs
to regenerate the block in the same layout compile produced. The
entry point is `decompile_block_aux_gen` at
`src/ix/decompile.rs:3226`, which today proceeds as follows:

```
decompile_block_aux_gen(block_addr, env):
  1. Before any block work, rehydrate_aux_perms_from_env (decompile.rs:3148)
     has already scanned every Muts-tagged Named entry and populated
     `stt.aux_perms[source_first_name] = layout` from
     ConstantMetaInfo::Muts.aux_layout (§10.2).
  2. Load Muts block at `block_addr`.
  3. For each primary inductive in the block, decompile its user-form
     InductiveVal (using original.1 for source-faithful binder names).
  4. Build a singleton-class alpha layout (decompile.rs:3252-3259) —
     one inductive per class. This is a tactical workaround for the
     full sort_consts re-run and is the remaining open item here
     (§17.2); it's sufficient for non-alpha-collapsed blocks but
     skips the collapse-class rebuild.
  5. Look up the block's stored AuxLayout from `stt.aux_perms`
     (populated by step 1). When present, pass it to
     `generate_canonical_recursors_with_layout` at decompile.rs:3324
     to recover the exact canonical aux layout compile produced.
     When absent (block had no nested auxes), fall back to
     `generate_canonical_recursors_with_overlay`.
  6. Insert decompiled user-form ConstantInfos into dstt.env.
```

**Decompile MUST NOT** run a fresh source walk on the decompiled
inductives to re-derive the nested-aux order. A fresh walk's
discovery order could differ from the original compile-time source
walk (Lean-version drift, ctor reordering in the source), which
would produce different `_N` numbering and break invariants 4.2 and
4.3. The persisted `ConstantMetaInfo::Muts.aux_layout` **preserves
the original compile-time source-walk numbering** forever; that's
the whole point of storing it.

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
    - sort_aux_by_content_hash produces the same canonical order
      because aux comparison depends on structural content and resolved
      addresses, not source names.
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

The aux permutation lives on the block's `Muts` meta variant, not on
`Named` itself — it's a property of the block rather than of any
individual member:

```rust
// src/ix/ixon/metadata.rs
ConstantMetaInfo::Muts {
    all: Vec<Vec<Address>>,
    aux_layout: Option<AuxLayout>,   // Some for blocks with nested auxes
}

// src/ix/ixon/env.rs
pub struct AuxLayout {
    /// `perm[source_j] = canonical_i`: source-walk → canonical aux order.
    pub perm: Vec<usize>,
    /// Ctor count of each source-walk aux at position j.
    pub source_ctor_counts: Vec<usize>,
}
```

- **Aux permutation** `perm: Vec<usize>` — length `n_source_aux`,
  where `perm[source_j] = canonical_i`. The sentinel
  `PERM_OUT_OF_SCC = usize::MAX` (`nested.rs:762`) marks source
  auxes that belong to a different SCC (so they shouldn't be
  resolved via this block).
- **Source ctor counts** `source_ctor_counts: Vec<usize>` — ctor
  count of each source-walk aux. Surgery consumes this to rewrite
  call sites, and decompile consumes it to reconstruct the
  source-indexed `_N` names that Lean exposes.

**Compile** constructs the layout as a local in
`compile_aux_gen_block` (`mutual.rs:453-483`) using `aux_out.perm`
from `generate_aux_patches` plus ctor counts from
`nested::source_aux_order`. The same local is (a) passed directly
to surgery (`compute_call_site_plans` at `surgery.rs:166` takes
`aux_layout: Option<&AuxLayout>`) and (b) embedded on the block's
`ConstantMetaInfo::Muts.aux_layout` for persistence.

**Decompile** recovers it by scanning every Muts-tagged Named entry
at startup via `rehydrate_aux_perms_from_env`
(`src/ix/decompile.rs:3148`). The scan resolves each block's
`Muts.all[0][0]` — the first canonical-class representative — back
to its source-order first inductive via `rep.meta.Indc.all[0]`, and
writes `stt.aux_perms[source_first_name] = layout`. This DashMap
(`compile.rs:187`, `DashMap<Name, AuxLayout>`) is the shared
lookup table that `decompile_block_aux_gen` (§9.3) uses to retrieve
a block's layout before handing it to
`generate_canonical_recursors_with_layout`.

**Serialization.** The Muts payload round-trips through
`metadata.rs:1056-1065` (write) and `metadata.rs:1144-1161` (read);
the 0/1 tag for `Option<AuxLayout>` lives on disk.

### 10.3 CallSite metadata alignment

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

### 11.2 Nested-aux `sort_aux_by_content_hash`

The name is historical; this is now a structural sort, not a direct
Blake3 bundle sort.

```
expanded auxes → temporary MutConst::Indc values
sort_consts(aux slice, cache, stt)
  where compare_expr resolves non-mutual Const/Proj names by content address
  and errors if a name is unresolved

after sort, rebuild aux names as `<all0>._nested.<Ext>_<new_j+1>`,
where `<Ext>` is recovered from the pre-sort name's suffix (e.g.
`Array`, `Option`, `List`).

cascade rename:
  - aux_ctor_map keys and values
  - aux_to_nested keys
  - every member.typ and ctor.typ (auxes can reference other auxes)
```

This gives content-addressed canonical ordering without using source names as
a tie-breaker. Alpha-equivalent auxes collapse through `sort_consts`, and
source-walk aux positions are related back to canonical positions by
`compute_aux_perm`.

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

### 12.2 mdata strip

```lean
def g₁ : Nat := n + n
def g₂ : Nat := @[inline] (n + n)   -- conceptually; Lean stores via `mdata`
```

`put_expr` ignores `Mdata` nodes entirely — the canonical form has no
`Mdata` variant. Both values hash to the same bytes;
`addr(g₁) == addr(g₂)`.

### 12.3 Universe permutation (non-equal)

```lean
def h₁.{u, v} : Sort u → Sort v → Sort (max u v) := …
def h₂.{u, v} : Sort v → Sort u → Sort (max u v) := …
```

These are **not** α-equivalent: the order of universe params is part
of the structural signature. `addr(h₁) ≠ addr(h₂)`. Canonicity isn't
"equal up to any renaming" — it's equal up to the *specific*
equivalences in §1.

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
expand_nested_block        (src/ix/compile/aux_gen/nested.rs:369)
  → replaces each `ExtInd (args-with-block-params)` with a synthetic
    `_nested.ExtInd_N` aux inductive sharing block params/levels.
  → dedupes alpha-equivalent occurrences via hash-keyed aux_seen table.

sort_aux_by_content_hash   (nested.rs:538)
  → sorts auxes with the same structural comparator as `sort_consts`
    and renames them to canonical _N positions.

compute_aux_perm            (nested.rs:797)
  → builds the source-walk → canonical permutation for surgery.

compute_call_site_plans    (src/ix/compile/surgery.rs:166)
  → rewrites call-site arg lists so `f.rec_2 args` produced by Lean's
    source-walk lands in our canonical-order recursor.
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
- `sort_aux_by_content_hash` assigns **same canonical `_N`** to each
  nested aux based on structural content and resolved addresses — not on
  source-walk position.

Without canonical aux sorting, the two `Array/Option/List` auxes would be numbered
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
| Serializer omits names, mdata, universe names              | `src/ix/ixon/serialize.rs:111-210` `put_expr`                   |
| Hash is Blake3 over serializer output                      | `Constant::commit` at `serialize.rs:861` → `Address::hash`      |
| `sort_consts` is deterministic and refinement-stable       | `src/ix/compile.rs:2526-2564` (iterative refinement)            |
| Nested-aux dedup across aliases                            | `replace_if_nested` `aux_seen` table, `nested.rs:191-362`       |
| Nested-aux section is structurally sorted                  | `sort_aux_by_content_hash`, `nested.rs`                         |
| Source-walk → canonical permutation is reversible          | `compute_aux_perm`, `nested.rs:797-907`                         |
| Call sites are surgically rewritten to canonical order     | `compute_call_site_plans`, `surgery.rs:166-570`                 |
| CallSite metadata keeps source and canonical views separate | `ExprMetaData::CallSite { entries, canon_meta }`; `compile_expr::BuildCallSite`; `kernel/ingress.rs` |
| Optional original-kernel check isolates adversarial raw constants | `CompileOptions::check_originals`, `mutual.rs::check_originals`, `orig_kenv` in `compile/env.rs` |
| Stored primary order matches `sort_consts` (kernel-side)   | `validate_canonical_block_single_pass`, `src/ix/kernel/canonical_check.rs` (called from `ingress_muts_block`) |
| Aux ordering matches `sort_consts` on rediscovered aux     | `sort_kconsts`, `src/ix/kernel/canonical_check.rs` (called from `canonical_aux_order` in `inductive.rs`); position-by-position recursor validation in `check_recursor` |

## 16. Testing Plan

The canonicity property is an equivalence, so the test strategy is
**pairs of known-equivalent and known-inequivalent Lean inputs with
address comparison as the observation**.

### 16.1 Rust-side unit tests

`src/ix/compile/canonicity_tests.rs` (new file, `#[cfg(test)]`):

- **`alpha_rename_hashes_equal`** — `λx.x+1` vs `λy.y+1` → same address.
- **`mdata_wrapper_stripped`** — `e` vs `Mdata(kv, e)` → same address.
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
- **`sort_aux_by_content_hash_idempotent`** — sorting already-sorted
  auxes is identity.

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

## 17. Open Work

### 17.1 PermCtx Builder Consolidation

`src/ffi/lean_env.rs` currently has separate builders for validate-aux
Phase 2 and rust-compile Phase 1b. They should be factored into one
shared `PermCtx` construction path so the two validation modes cannot
drift in how they populate `aux_layout`, constructor counts, and
`const_addr`.

### 17.2 Decompile canonical-path unification

`decompile_block_aux_gen` now lives at `src/ix/decompile.rs:3226`
and is layout-aware: the rehydrate scan at
`src/ix/decompile.rs:3148` (`rehydrate_aux_perms_from_env`)
populates `stt.aux_perms` from `ConstantMetaInfo::Muts.aux_layout`,
and the function calls `generate_canonical_recursors_with_layout`
at line 3324 with that layout (falling back to
`generate_canonical_recursors_with_overlay` when the block has no
nested auxes).

What's still tactical rather than principled: decompile builds an
**un-collapsed singleton-class layout** (one inductive per class)
at `src/ix/decompile.rs:3252-3259` instead of re-running
`sort_consts` on the decompiled inductives to recover the
alpha-collapse classes compile saw. For non-alpha-collapsed blocks
this is observationally identical; for blocks that compile
alpha-collapsed, the workaround lets surgery still find
callee positions but doesn't reconstruct the collapse at the
decompiled-inductive level.

Remaining work: replace the singleton-class builder with a proper
`sort_consts` run over the decompiled inductives, so the
alpha-collapse story survives the full compile → decompile →
compile round trip at the `ConstantInfo` level, not just at the
`addr` level.

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

After the §4.4 kernel-canonicity port (independent `sort_consts`
on rediscovered aux + position-based stored-recursor lookup),
Categories A, C, F, and G still show some residual failures.
Investigate whether the kernel's synthetic aux Indc views
(in `canonical_aux_order`) need a more faithful mirror of
compile-side's `replace_ctor_result_head_with_aux` — the current
implementation rewrites the result head but does not re-wrap with
block-param Pis. Some failure modes may also reflect orthogonal
issues (e.g. `String.Legacy.back ""` reduction, `_sparseCasesOn_N`
regeneration) that surface alongside the canonical-order
mismatches but have unrelated root causes.

## 18. Summary

Anonymous canonicity in Ix reduces to six operational commitments:

1. Binder names, mdata, and hygiene **never enter the hash input**.
2. Mutual blocks are **structurally sorted** by an iterative-refinement
   equivalence-class algorithm (`sort_consts`); source order and name
   choices don't leak into the block address.
3. Nested-inductive auxes are **structurally sorted** and **de-duped**
   independent of Lean's source-walk discovery.
4. Call sites are **surgically rewritten** so source-order aux
   references resolve to canonical-order auxes.
5. A **metadata sidecar** — binder names, mdata, Lean-order `all`,
   `CallSite.entries` / `CallSite.canon_meta`, and `AuxLayout` on
   the block's Muts metadata (plus docstrings, planned) — preserves
   everything the hash erases, making
   `canonical + metadata` isomorphic to source Lean.
6. The **kernel independently re-runs `sort_consts`** on every
   stored mutual block when the primary validator needs refinement
   (fast strong-adjacent validation at ingress)
   and on every set of rediscovered auxes (full iterative sort
   during recursor regeneration). The kernel never trusts the
   compiler's claim that an input is canonical; it verifies the
   claim by recomputing it. See §4.4 and
   `src/ix/kernel/canonical_check.rs`.

The failure of any one commitment breaks the zk-PCC story. The test
harness in §16 makes each commitment observable as an address-equality
predicate. The open items in §17 are where the current implementation
is known to be partial.

## 19. Cross-References

- [`docs/Ixon.md`](./Ixon.md) — binary format, Expr/Constant/Meta
  layout, serialization details.
- `src/ix/compile.rs` — `sort_consts`, `Frame`, `compile_expr`.
- `src/ix/kernel/canonical_check.rs` — kernel-side `sort_consts`
  port: `compare_kuniv`, `compare_kexpr`, `compare_kconst`,
  `sort_kconsts`, `validate_canonical_block_single_pass`. The
  kernel's independent canonicity oracle (§4.4).
- `src/ix/kernel/ingress.rs::ingress_muts_block` — wires
  `validate_canonical_block_single_pass` for stored Indc blocks.
- `src/ix/kernel/inductive.rs::canonical_aux_order` — synthesizes
  `KConst::Indc` views of rediscovered auxes and runs
  `sort_kconsts` to compute the kernel-canonical aux order.
  Position-by-position recursor validation lives in
  `check_recursor`.
- `src/ix/kernel/error.rs::TcError::NonCanonicalBlock` — rejection
  variant emitted when ingress finds a non-canonical primary block.
- `src/ix/compile/aux_gen.rs` — main `generate_aux_patches` entry
  and the `AuxPatchesOutput` return type.
- `src/ix/compile/aux_gen/nested.rs` — `expand_nested_block`,
  `sort_aux_by_content_hash`, `compute_aux_perm`, `source_aux_order`.
- `src/ix/compile/aux_gen/recursor.rs` — canonical recursors from an
  expanded block, plus targeted canonical KEnv ingress for aux_gen
  sort/recursor generation. Reducible definitions referenced by inductive
  target types or constructor fields are loaded as real definitions;
  type-only dependencies remain stubs to avoid mirroring the full Lean env.
- `src/ix/compile/aux_gen/below.rs`, `brecon.rs`, `cases_on.rs`,
  `rec_on.rs` — derived aux generation.
- `src/ix/compile/aux_gen/expr_utils.rs` — FVar-based expression
  manipulation primitives (`forall_telescope`, `mk_forall`, etc.).
- `src/ix/compile/aux_gen/expr_utils.rs::RestoreCtx` — maps
  `_nested.X_N` references back to `ExtInd spec_params` form.
- `src/ix/compile/surgery.rs` — call-site argument reordering;
  `CallSitePlan`, `compute_call_site_plans`.
- `src/ix/compile/mutual.rs` — orchestrates `generate_aux_patches` +
  surgery + compilation per mutual block. Normal trusted compile paths skip
  the full `orig_kenv`; adversarial raw-constant tests can opt into
  `CompileOptions::check_originals` to validate Lean-original constants
  against a separate `lean_ingress` kernel environment.
- `src/ix/decompile.rs::rehydrate_aux_perms_from_env` — rehydrates
  `stt.aux_perms` from `ConstantMetaInfo::Muts.aux_layout` before any
  block is decompiled.
- `src/ix/decompile.rs::decompile_block_aux_gen` — canonical → Lean
  reconstruction, layout-aware (calls
  `generate_canonical_recursors_with_layout` when the block carries
  a persisted aux layout).
- `src/ix/ixon/env.rs::{Named, AuxLayout, Env}` — on-disk env
  layout; aux permutation lives on the `Muts` meta variant.
- `src/ix/ixon/metadata.rs::ConstantMetaInfo::Muts.aux_layout` —
  persisted aux permutation sidecar (read/written at
  `metadata.rs:1056-1065` / `1144-1161`).
- `src/ix/ixon/expr.rs`, `serialize.rs`, `metadata.rs` — canonical
  data types.
- `Tests/Ix/Compile/Mutual.lean` — canonicity fixtures.
- `Tests/Ix/Compile/ValidateAux.lean` — validate-aux phases.
- `refs/lean4/src/kernel/inductive.cpp` — Lean's reference
  implementation of nested inductive handling; our
  `expand_nested_block` port mirrors the source walk.
- `refs/lean4/src/Lean/Meta/Constructions/BRecOn.lean` — Lean's
  `.below` / `.brecOn` generator; our `below.rs` / `brecon.rs`
  follow it.
