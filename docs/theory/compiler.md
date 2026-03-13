# Formalizing the Ix Compiler

This document describes the correctness properties of Ix's content-addressed
compilation pipeline — the path from Lean constants to Ixon binary format and
back. For the kernel typechecker formalization, see [kernel.md](kernel.md).
For the ZK/commitment layer, see [zk.md](zk.md).


## Architecture

The compiler is a five-stage pipeline:

```
┌──────────────────────────────────────────────────────────┐
│  1. Canonicalization  (CanonM)                           │
│     Lean.Environment → Ix.Environment                    │
│     Embed blake3 hashes, pointer-based caching           │
├──────────────────────────────────────────────────────────┤
│  2. SCC Condensation  (CondenseM)                        │
│     Dependency graph → Strongly connected components     │
│     Tarjan's algorithm, mutual block detection           │
├──────────────────────────────────────────────────────────┤
│  3. Compilation  (CompileM)                              │
│     Ix.ConstantInfo → Ixon.Constant                      │
│     De Bruijn universe params, reference indirection,    │
│     metadata separation, sharing analysis                │
├──────────────────────────────────────────────────────────┤
│  4. Serialization  (Ixon.Serialize)                      │
│     Ixon.Constant → ByteArray → Address (blake3 hash)   │
│     Tag0/Tag2/Tag4 encoding, telescope compression       │
├──────────────────────────────────────────────────────────┤
│  5. Decompilation  (DecompileM)                          │
│     Ixon.Constant → Ix.ConstantInfo (→ Lean.ConstantInfo)│
│     Table resolution, share expansion, metadata reattach │
└──────────────────────────────────────────────────────────┘
```

Two implementations exist: Lean (`Ix/CompileM.lean`, `Ix/DecompileM.lean`) for
correctness and formalization, and Rust (`src/ix/compile.rs`, `src/ix/ixon/`)
for performance. Both must agree.

**Current state**: The Lean and Rust implementations are complete and tested
(see `Tests/Ix/Commit.lean`). The formalization tiers below describe formal
*proofs* of correctness properties that do not yet exist.


## Part I: Design Principles

### Content Addressing

Every `Ixon.Constant` is serialized to bytes and hashed with blake3. The
resulting 256-bit hash is its `Address`. Two constants with identical structure
have identical addresses, enabling automatic deduplication and cryptographic
verification of equality.

```
address(c) = blake3(serialize(c))
```

### Alpha-Invariance

The central design invariant: structurally identical terms produce identical
serialized bytes, regardless of variable names. Achieved through:

- **De Bruijn indices** for bound variables (`Var(n)`)
- **De Bruijn indices** for universe parameters (`Univ::Var(n)`)
- **Content addresses** for constant references (`Ref(idx, univs)` where
  `refs[idx]` is a blake3 hash, not a name)
- **Metadata separation**: names, binder info, reducibility hints stored
  outside the hashed content in `ConstantMeta` / `ExprMeta`

### Metadata Separation

The Ixon format separates:
- **Alpha-invariant data** (`Ixon.Constant`): hashed for addressing
- **Metadata** (`ConstantMeta`, `ExprMeta`): needed for roundtrip but not
  part of the constant's identity

Cosmetic changes (renaming variables, changing binder info from implicit to
explicit) do not change the constant's address.


## Part II: Canonicalization (CanonM)

**Files**: `Ix/CanonM.lean`

Converts Lean kernel types to Ix types with embedded blake3 hashes.

### What It Does

```
canonName  : Lean.Name  → CanonM Ix.Name
canonLevel : Lean.Level → CanonM Ix.Level
canonExpr  : Lean.Expr  → CanonM Ix.Expr
canonConst : Lean.ConstantInfo → CanonM Ix.ConstantInfo
canonEnv   : Lean.Environment  → CanonM Ix.Environment
```

Each Ix type embeds a blake3 hash at construction time (e.g., `Ix.Expr.mkApp`
hashes the function and argument hashes). This provides O(1) structural
equality via hash comparison.

### Pointer-Based Caching

`CanonM` uses `ptrAddrUnsafe` to cache results by Lean pointer identity.
If two Lean values share the same pointer, they map to the same canonical
Ix value without re-traversal.

```lean
structure CanonState where
  namePtrAddrs  : HashMap USize Address
  names         : HashMap Address Ix.Name
  exprPtrAddrs  : HashMap USize Address
  exprs         : HashMap Address Ix.Expr
  ...
```

### Roundtrip Property

Uncanonicalization (`uncanonName`, `uncanonLevel`, `uncanonExpr`,
`uncanonConst`) is the inverse:

```
∀ env, uncanonEnv(canonEnv(env)) = env
```

More precisely: for each constant name `n` in `env`, the uncanonicalized
constant is structurally equal to the original (modulo `MData` metadata
entries which are carried through faithfully).

### Parallel Canonicalization

`canonEnvParallel` splits the environment into chunks processed by separate
`Task`s, each with independent `CanonState`. Results are merged into a single
`HashMap Ix.Name Ix.ConstantInfo`. The `compareEnvsParallel` function
validates roundtrip correctness using pointer-pair-cached structural equality.


## Part III: SCC Condensation (CondenseM)

**Files**: `Ix/CondenseM.lean`

### What It Does

Tarjan's algorithm partitions the constant dependency graph into strongly
connected components. Each SCC becomes a mutual block — a set of constants
that are mutually recursive.

### Output

```lean
structure CondensedBlocks where
  lowLinks  : Map Ix.Name Ix.Name         -- constant → SCC representative
  blocks    : Map Ix.Name (Set Ix.Name)   -- representative → all members
  blockRefs : Map Ix.Name (Set Ix.Name)   -- representative → external refs
```

### Correctness Properties

1. **Partition**: every constant belongs to exactly one SCC
2. **Mutual recursion**: constants in the same SCC can reference each other;
   constants in different SCCs cannot form a cycle
3. **External references**: `blockRefs` for each SCC contains only constants
   from other (already-compiled) SCCs
4. **Discovery order**: SCCs are produced in reverse topological order
   (leaves first), so dependencies are always compiled before dependents

### Invariants

The algorithm maintains:
- `lowLink[id] ≤ id` for all nodes
- `lowLink[id] = id` iff the node is the root of an SCC
- The stack contains exactly the nodes in the current DFS path plus
  unfinished SCCs


## Part IV: Compilation (CompileM)

**Files**: `Ix/CompileM.lean`

### What It Does

Compiles a single mutual block (or singleton constant) from `Ix.ConstantInfo`
to `Ixon.Constant`, producing the alpha-invariant binary representation.

### Expression Compilation

| Ix.Expr | Ixon.Expr | Notes |
|---------|-----------|-------|
| `bvar idx` | `Var(idx)` | De Bruijn index preserved |
| `sort level` | `Sort(idx)` | Level added to univs table |
| `const name levels` | `Ref(idx, univ_idxs)` | Name resolved to address via refs table |
| `const name levels` (mutual) | `Rec(ctx_idx, univ_idxs)` | Index into mutual context |
| `lam name ty body bi` | `Lam(ty, body)` | Name/binder info → metadata |
| `forallE name ty body bi` | `All(ty, body)` | Name/binder info → metadata |
| `letE name ty val body nd` | `Let(nd, ty, val, body)` | Name → metadata |
| `proj typeName idx struct` | `Prj(type_idx, idx, struct)` | Type name → refs table |
| `lit (Nat n)` | `Nat(idx)` | Bytes stored in blobs |
| `lit (Str s)` | `Str(idx)` | Bytes stored in blobs |

### Indirection Tables

Expressions don't store addresses or universes directly. Instead:

- `Ref(idx, univ_indices)` → `constant.refs[idx]` is the address,
  `constant.univs[univ_indices[i]]` are the universe arguments
- `Sort(idx)` → `constant.univs[idx]` is the universe
- `Str(idx)` / `Nat(idx)` → `constant.refs[idx]` is a blob address

This indirection enables sharing and smaller serializations.

### Universe Parameter De Bruijn Indices

Lean uses named universe parameters (`{u v}`). Ixon uses de Bruijn indices:
the first declared universe parameter is `Var(0)`, the second `Var(1)`, etc.
The `BlockEnv.univCtx` maps names to their indices during compilation.

### Mutual Block Handling

For a mutual block `{A, B, C}`:

1. Build `MutCtx`: map each name to its index within the block
2. Compile each constant with the mutual context — intra-block references
   become `Rec(ctx_idx, univs)` instead of `Ref(refs_idx, univs)`
3. Create `Muts` block with shared `refs`, `univs`, and `sharing` tables
4. Create projections (`IPrj`, `DPrj`, `RPrj`, `CPrj`) for each named
   constant pointing back to the shared block

### Metadata Extraction

During compilation, an `ExprMetaArena` is built bottom-up:

```rust
pub enum ExprMetaData {
    Leaf,                                           // Var, Sort, Nat, Str
    App { children: [u64; 2] },                     // [fun_idx, arg_idx]
    Binder { name: Address, info: BinderInfo,
             children: [u64; 2] },                  // [type_idx, body_idx]
    LetBinder { name: Address, children: [u64; 3] },
    Ref { name: Address },                          // Const/Rec name
    Prj { struct_name: Address, child: u64 },
    Mdata { mdata: Vec<KVMap>, child: u64 },
}
```

Each expression node gets an arena index. The `ConstantMeta` stores arena
root indices (`type_root`, `value_root`) to reconstruct names and binder info
during decompilation.


## Part V: Sharing Analysis

**Files**: `Ix/Sharing.lean`

### Algorithm

Two-phase O(n) algorithm:

1. **Phase 1 — Build DAG**: Post-order traversal with Merkle-tree hashing
   (blake3). Each unique subterm gets a content hash. Pointer-based caching
   (`ptrAddrUnsafe`) avoids re-traversal of shared subterms.

2. **Phase 2 — Propagate usage counts**: Walk the DAG in reverse topological
   order, accumulating usage counts from roots to leaves.

### Profitability Heuristic

Share a subterm when the bytes saved exceed the cost of the `Share(idx)` tag:

```
profitable(N, term_size, share_ref_size) :=
    (N - 1) * term_size > N * share_ref_size
```

Where `N` is the number of occurrences, `term_size` is the serialized size
of the subterm, and `share_ref_size` is the size of `Share(idx)` (1–2 bytes
depending on the index).

### Sharing Vector Construction

Shared subterms are sorted in topological order (leaves first) by hash bytes
for determinism. Each entry in the sharing vector can only reference earlier
entries (no forward references). Root expressions are rewritten last, using
all available `Share` indices.

### Determinism

Both Lean and Rust must produce identical sharing vectors. This is achieved
by:
- Sorting candidates by decreasing gross benefit `(N-1) * term_size`
- Using lexicographic hash comparison as tie-breaker
- Sorting the topological order by hash bytes


## Part VI: Serialization

**Files**: `Ix/Ixon.lean`, `docs/Ixon.md`

### Tag Encoding

Three variable-length encoding schemes:

| Scheme | Header format | Used for |
|--------|---------------|----------|
| **Tag4** | `[flag:4][large:1][size:3]` | Expressions, constants, env/proof |
| **Tag2** | `[flag:2][large:1][size:5]` | Universes |
| **Tag0** | `[large:1][size:7]` | Plain u64 values |

### Telescope Compression

Nested constructors of the same kind are collapsed:

- `App(App(App(f, a), b), c)` → `Tag4{flag:0x7, size:3} + f + a + b + c`
- `Lam(t₁, Lam(t₂, body))` → `Tag4{flag:0x8, size:2} + t₁ + t₂ + body`
- `Succ(Succ(Succ(Zero)))` → `Tag2{flag:0, size:3} + Zero`

### Constant Layout

```
Tag4 { flag: 0xD, size: variant }   -- 1 byte (variant 0-7)
+ ConstantInfo payload
+ sharing vector (Tag0 length + expressions)
+ refs vector (Tag0 length + 32-byte addresses)
+ univs vector (Tag0 length + universes)
```

For mutual blocks: `Tag4 { flag: 0xC, size: entry_count }` followed by
`MutConst` entries, then shared tables.

### Correctness Properties

**Roundtrip (byte-level)**: `serialize(deserialize(bytes)) = bytes`

For any valid serialized constant, deserializing and re-serializing produces
identical bytes. This is the strongest roundtrip property and implies
determinism.

**Roundtrip (structural)**: `deserialize(serialize(c)) = c`

Serializing a constant and deserializing the result produces the same
constant structure.

**Determinism**: `serialize` is a function — the same `Ixon.Constant`
always produces the same bytes.


## Part VII: Alpha-Invariance

### Core Theorem

Alpha-equivalent expressions serialize to identical bytes.

More precisely: if two Lean expressions `e₁` and `e₂` differ only in
variable names, binder info, or the names of referenced constants (but have
structurally identical types and values), then their compiled Ixon forms
serialize to the same `ByteArray`.

### Why It Holds

1. **Bound variables**: de Bruijn indices. `fun (x : Nat) => x` and
   `fun (y : Nat) => y` both become `Lam(Ref(nat_addr, []), Var(0))`.

2. **Universe parameters**: de Bruijn indices. The first declared parameter
   is `Var(0)` regardless of its name.

3. **Constant references**: content addresses. A constant is referenced by
   the blake3 hash of its serialized content, not by name.

4. **Metadata**: stored outside the hash. Names, binder info, reducibility
   hints are in `ConstantMeta` / `ExprMeta`, which don't affect the
   `Address`.

### Runtime Verification

`Ix.Commit.commitDef` includes an alpha-invariance check: it compiles the
same definition under two different names (anonymous and the commitment name)
and asserts the resulting addresses are equal. This catches any name leakage
into the serialized content.

### Formal Statement

```
∀ e₁ e₂ : Lean.Expr, alpha_equiv e₁ e₂ →
  ∀ env₁ env₂ : CompileEnv, consistent_addresses env₁ env₂ →
    serialize(compile(e₁, env₁)) = serialize(compile(e₂, env₂))
```

Where `consistent_addresses` means that for every pair of corresponding
constants in the two environments, their content addresses are equal.


## Part VIII: Decompilation

**Files**: `Ix/DecompileM.lean`

### What It Does

Reconstructs `Ix.ConstantInfo` from `Ixon.Constant` by resolving indirection
tables, expanding shares, and reattaching metadata.

### Process

1. **Load constant** from `Ixon.Env.consts` by address
2. **Initialize tables** from `sharing`, `refs`, `univs`
3. **Load metadata** from `Ixon.Env.named` (arena, universe param names,
   mutual context names)
4. **Decompile expressions**: resolve `Ref(idx, univs)` → look up
   `refs[idx]` address → look up name from arena metadata; resolve
   `Sort(idx)` → look up `univs[idx]`; resolve `Share(idx)` → inline or
   cache `sharing[idx]`
5. **Decompile universes**: `Var(idx)` → `param(univParams[idx])`
6. **Reconstruct constant**: attach names, binder info, reducibility hints

### Roundtrip

```
decompile(compile(const)) ≈ const    (via Ix.Expr hash equality)
```

The decompiled constant has the same Ix types (with identical content hashes)
as the original. This is tested in `Tests/Ix/Commit.lean`.


## Part IX: Content Addressing

### Definition

```
address(c) = blake3(serialize(c))
```

Where `c : Ixon.Constant` and `serialize` produces the deterministic byte
encoding described in Part VI.

### Properties

**Determinism**: same constant → same address. Follows from serialization
determinism.

**Collision resistance**: assumed from blake3 (256-bit security). Two
distinct constants have different addresses with overwhelming probability.

**Alpha-invariance**: `address(compile(e₁)) = address(compile(e₂))` when
`e₁` and `e₂` are alpha-equivalent. Follows from alpha-invariance of
serialization.

**Injectivity (modulo blake3)**: `address(c₁) = address(c₂)` implies `c₁`
and `c₂` are alpha-equivalent, assuming no blake3 collisions.


## Part X: Formalization Tiers

### Tier 1: Serialization Roundtrip

The foundation — everything else depends on serialization being correct.

- [ ] `serialize(deserialize(bytes)) = bytes` (byte-level identity)
- [ ] `deserialize(serialize(c)) = c` (structural identity)
- [ ] `serialize` is deterministic (same input → same bytes)
- [ ] Tag encoding/decoding is an isomorphism
- [ ] Telescope compression/expansion is an isomorphism

**Key files**: `Ix/Ixon.lean`

### Tier 2: Alpha-Invariance

Core theorem enabling content addressing.

- [ ] Alpha-equivalent Lean expressions compile to identical `Ixon.Expr`
- [ ] De Bruijn encoding is name-independent for bound variables
- [ ] De Bruijn encoding is name-independent for universe parameters
- [ ] Constant references use addresses, not names
- [ ] Metadata does not affect serialized bytes

**Key files**: `Ix/CompileM.lean`, `Ix/CanonM.lean`

### Tier 3: Sharing Correctness

Sharing is a semantics-preserving optimization.

- [ ] `Share(idx)` is semantically equivalent to `sharing[idx]`
- [ ] No forward references in the sharing vector
- [ ] Shared form ≤ unshared form in serialized bytes
- [ ] Sharing vector is deterministic (Lean and Rust agree)

**Key files**: `Ix/Sharing.lean`

### Tier 4: Compilation Roundtrip

Compile then decompile recovers the original.

- [ ] `decompile(compile(const))` has the same content hash as `const`
- [ ] Expression structure is preserved (modulo sharing expansion)
- [ ] Universe parameters are correctly de Bruijn indexed and recovered
- [ ] Mutual block structure (SCCs) is correctly identified
- [ ] Projections correctly reference their parent mutual block

**Key files**: `Ix/CompileM.lean`, `Ix/DecompileM.lean`, `Ix/CondenseM.lean`

### Tier 5: Content Addressing

Follows from Tiers 1–2 plus blake3 assumptions.

- [ ] Determinism: `address` is a function
- [ ] Alpha-invariance: alpha-equivalent → same address
- [ ] Injectivity: same address → alpha-equivalent (modulo blake3 collision)
- [ ] Canonicalization roundtrip: `uncanonEnv(canonEnv(env)) = env`

**Key files**: `Ix/CanonM.lean`, `Ix/Address.lean`

### Estimated Effort

| Tier | Est. LOC | Notes |
|------|----------|-------|
| 1: Serialization roundtrip | ~1,500 | Foundation; `Ix/Ixon.lean` is large |
| 2: Alpha-invariance | ~1,000 | De Bruijn encoding proofs |
| 3: Sharing correctness | ~500 | Semantics-preserving, determinism |
| 4: Compilation roundtrip | ~1,000 | CompileM + DecompileM |
| 5: Content addressing | ~300 | Follows from Tiers 1–2 + Blake3 |


## Part XI: Key References

### Lean Implementation
- `Ix/CanonM.lean` — Canonicalization and uncanonicalization
- `Ix/CondenseM.lean` — Tarjan's SCC algorithm
- `Ix/CompileM.lean` — Compilation monad and expression compilation
- `Ix/DecompileM.lean` — Decompilation and table resolution
- `Ix/Sharing.lean` — Sharing analysis (Merkle hashing, profitability)
- `Ix/Ixon.lean` — Ixon types and serialization
- `docs/Ixon.md` — Ixon format specification

### Rust Implementation
- `src/ix/compile.rs` — Rust compilation pipeline
- `src/ix/ixon/` — Rust Ixon serialization/deserialization

### Tests
- `Tests/Ix/Commit.lean` — Alpha-invariance and roundtrip tests
