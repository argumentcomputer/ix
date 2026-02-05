# Ixon: Ix Object Notation

Ixon is a content-addressed, alpha-invariant binary serialization format for Lean kernel types. It is designed for the Ix platform's cryptographic verification and zero-knowledge proof systems.

## Design Goals

1. **Alpha-invariance**: Structurally identical terms have identical serializations, regardless of variable names. The expression `fun (x : Nat) => x` and `fun (y : Nat) => y` serialize to the same bytes.

2. **Content-addressing**: Every constant is identified by the blake3 hash of its serialized content. This enables deduplication and cryptographic verification.

3. **Compact storage**: Variable-length encoding, telescope compression, and expression sharing minimize serialized size.

4. **Metadata separation**: Names, binder info, and other source information are stored separately from the alpha-invariant core, enabling roundtrip compilation while preserving deterministic hashing.

5. **ZK-compatibility**: Cryptographic commitments allow proving knowledge of constants without revealing their content.

## Key Concepts

### Alpha-Invariance

Ixon achieves alpha-invariance through:
- **De Bruijn indices** for bound variables: `Var(0)` refers to the innermost binder
- **De Bruijn indices** for universe parameters: `Univ::Var(0)` is the first universe parameter
- **Content addresses** for constant references: constants are referenced by their hash, not their name

### Content-Addressing

Every `Constant` in Ixon is serialized and hashed with blake3. The resulting 256-bit hash is its `Address`. Two constants with identical structure have identical addresses, enabling:
- Automatic deduplication
- Cryptographic verification of equality
- Merkle-tree style proofs

### Metadata Separation

The Ixon format separates:
- **Alpha-invariant data** (`Constant`): The mathematical content, hashed for addressing
- **Metadata** (`ConstantMeta`, `ExprMeta`): Names, binder info, reducibility hints—stored separately

This separation means cosmetic changes (renaming variables) don't change the constant's address.

## Document Overview

| Section | Contents |
|---------|----------|
| [Tag Encoding](#tag-encoding-schemes) | Variable-length integer encoding |
| [Universes](#universes) | Type-level hierarchy |
| [Expressions](#expressions) | Lambda calculus terms |
| [Constants](#constants) | Top-level declarations |
| [Sharing](#sharing-system) | Expression deduplication |
| [Metadata](#metadata) | Names and source info |
| [Environment](#environment) | Storage and serialization |
| [Proofs and Claims](#proofs-and-claims) | ZK claims and proofs |
| [Commitments](#cryptographic-commitments) | Commitment scheme |
| [Compilation](#compilation-lean--ixon) | Lean to Ixon conversion |
| [Decompilation](#decompilation-ixon--lean) | Ixon to Lean conversion |
| [Worked Examples](#comprehensive-worked-example) | End-to-end walkthroughs |

---

## Tag Encoding Schemes

Ixon uses three variable-length encoding schemes for compact representation.

### Tag4 (4-bit flag)

Used for expressions, constants, and environment/proof structures. Header byte format:

```
[flag:4][large:1][size:3]
```

- **flag** (4 bits): Discriminates type (see table below)
- **large** (1 bit): If 0, size is in the low 3 bits. If 1, (size+1) bytes follow with the actual value
- **size** (3 bits): Small values 0-7, or byte count for large values

**Complete Tag4 flag allocation:**

| Flag | Category | Type | Size field meaning |
|------|----------|------|-------------------|
| 0x0 | Expr | Sort | Universe index |
| 0x1 | Expr | Var | De Bruijn index |
| 0x2 | Expr | Ref | Univ argument count |
| 0x3 | Expr | Rec | Univ argument count |
| 0x4 | Expr | Prj | Field index |
| 0x5 | Expr | Str | Refs table index |
| 0x6 | Expr | Nat | Refs table index |
| 0x7 | Expr | App | Application count (telescoped) |
| 0x8 | Expr | Lam | Binder count (telescoped) |
| 0x9 | Expr | All | Binder count (telescoped) |
| 0xA | Expr | Let | 0=dep, 1=non_dep |
| 0xB | Expr | Share | Share vector index |
| 0xC | Constant | Muts | Entry count |
| 0xD | Constant | Non-Muts | Variant (0-7) |
| 0xE | Env/Proof | Env/Claim/Proof/Comm | Variant (0-7) |
| 0xF | - | Reserved | - |

```rust
pub struct Tag4 {
    pub flag: u8,   // 0-15
    pub size: u64,  // Variable-length payload
}
```

**Examples:**

```
Tag4 { flag: 0x1, size: 5 }
Header: 0b0001_0_101 = 0x15
Total: 1 byte

Tag4 { flag: 0x2, size: 256 }
Header: 0b0010_1_001 = 0x29  (large=1, 2 bytes follow)
Bytes:  0x00 0x01            (256 in little-endian)
Total: 3 bytes
```

### Tag2 (2-bit flag)

Used for universes. Header byte format:

```
[flag:2][large:1][size:5]
```

- **flag** (2 bits): Discriminates universe type (0-3)
- **large** (1 bit): If 0, size is in the low 5 bits (0-31). If 1, (size+1) bytes follow
- **size** (5 bits): Small values 0-31, or byte count

```rust
pub struct Tag2 {
    pub flag: u8,   // 0-3
    pub size: u64,  // Variable-length payload
}
```

**Examples:**

```
Tag2 { flag: 0, size: 15 }
Header: 0b00_0_01111 = 0x0F
Total: 1 byte

Tag2 { flag: 3, size: 100 }
Header: 0b11_1_00000 = 0xE0  (large=1, 1 byte follows)
Bytes:  0x64                 (100)
Total: 2 bytes
```

### Tag0 (no flag)

Used for plain variable-length u64 values. Header byte format:

```
[large:1][size:7]
```

- **large** (1 bit): If 0, size is in the low 7 bits (0-127). If 1, (size+1) bytes follow
- **size** (7 bits): Small values 0-127, or byte count

**Examples:**

```
Tag0 { size: 42 }
Header: 0b0_0101010 = 0x2A
Total: 1 byte

Tag0 { size: 1000 }
Header: 0b1_0000001 = 0x81  (large=1, 2 bytes follow)
Bytes:  0xE8 0x03           (1000 in little-endian)
Total: 3 bytes
```

---

## Universes

Universes represent type-level hierarchy in the dependent type system.

```rust
pub enum Univ {
    Zero,                         // Type 0 / Prop
    Succ(Arc<Univ>),              // Successor: Type (n+1)
    Max(Arc<Univ>, Arc<Univ>),    // Maximum of two universes
    IMax(Arc<Univ>, Arc<Univ>),   // Impredicative max (0 if second is 0)
    Var(u64),                     // Universe parameter (de Bruijn index)
}
```

### Serialization (Tag2)

| Flag | Variant | Size field | Body |
|------|---------|------------|------|
| 0 | Zero/Succ | Succ count (0 = Zero) | None |
| 1 | Max | Unused | Two Univs |
| 2 | IMax | Unused | Two Univs |
| 3 | Var | Variable index | None |

**Telescope compression**: Nested `Succ` constructors are collapsed. `Succ(Succ(Succ(Zero)))` serializes as a single Tag2 with flag=0 and size=3.

### Examples

```
Univ::Zero
Tag2 { flag: 0, size: 0 } = 0b00_0_00000
Bytes: 0x00

Univ::Succ(Zero)  // Type 1
Tag2 { flag: 0, size: 1 } + base
Bytes: 0x01 0x00

Univ::Succ(Succ(Succ(Zero)))  // Type 3
Tag2 { flag: 0, size: 3 } + base
Bytes: 0x03 0x00

Univ::Var(0)  // First universe parameter
Tag2 { flag: 3, size: 0 } = 0b11_0_00000
Bytes: 0xC0

Univ::Var(1)  // Second universe parameter
Tag2 { flag: 3, size: 1 } = 0b11_0_00001
Bytes: 0xC1

Univ::Max(Zero, Var(1))
Tag2 { flag: 1, size: 0 } + Zero + Var(1)
Bytes: 0x40 0x00 0xC1
```

---

## Expressions

Expressions are alpha-invariant lambda calculus terms with de Bruijn indices.

```rust
pub enum Expr {
    Sort(u64),                              // Type at universe level (index into univs table)
    Var(u64),                               // De Bruijn variable index
    Ref(u64, Vec<u64>),                     // Constant reference (refs index, univ indices)
    Rec(u64, Vec<u64>),                     // Mutual recursion (ctx index, univ indices)
    Prj(u64, u64, Arc<Expr>),               // Projection (type refs index, field, value)
    Str(u64),                               // String literal (refs index to blob)
    Nat(u64),                               // Natural literal (refs index to blob)
    App(Arc<Expr>, Arc<Expr>),              // Application
    Lam(Arc<Expr>, Arc<Expr>),              // Lambda (type, body)
    All(Arc<Expr>, Arc<Expr>),              // Forall/Pi (type, body)
    Let(bool, Arc<Expr>, Arc<Expr>, Arc<Expr>), // Let (non_dep, type, value, body)
    Share(u64),                             // Reference to sharing vector
}
```

### Key Design Choices

1. **No names**: Binders have no names—they use de Bruijn indices. Names are stored in metadata.

2. **No binder info**: Implicit/explicit info is stored in metadata.

3. **Indirection tables**: `Ref`, `Str`, `Nat` store indices into the constant's `refs` table, not raw addresses. `Sort` stores an index into the `univs` table.

4. **Share nodes**: Common subexpressions can be deduplicated via `Share(idx)` references to the constant's `sharing` vector.

### Serialization (Tag4)

| Flag | Variant | Size field | Body |
|------|---------|------------|------|
| 0x0 | Sort | Universe index | None |
| 0x1 | Var | De Bruijn index | None |
| 0x2 | Ref | Univ count | Ref index (Tag0) + univ indices |
| 0x3 | Rec | Univ count | Rec index (Tag0) + univ indices |
| 0x4 | Prj | Field index | Type ref index (Tag0) + value Expr |
| 0x5 | Str | Refs index | None |
| 0x6 | Nat | Refs index | None |
| 0x7 | App | App count | Function + args (telescoped) |
| 0x8 | Lam | Binder count | Types + body (telescoped) |
| 0x9 | All | Binder count | Types + body (telescoped) |
| 0xA | Let | 0=dep, 1=non_dep | Type + value + body |
| 0xB | Share | Share index | None |

### Telescope Compression

Nested constructors of the same kind are collapsed:

**Applications**: `App(App(App(f, a), b), c)` becomes:
```
Tag4 { flag: 0x7, size: 3 }  // 3 applications
+ f + a + b + c
```

**Lambdas**: `Lam(t1, Lam(t2, Lam(t3, body)))` becomes:
```
Tag4 { flag: 0x8, size: 3 }  // 3 binders
+ t1 + t2 + t3 + body
```

**Foralls**: Same as lambdas with flag 0x9.

### Expression Examples

```
Expr::Var(0)  // Innermost bound variable
Tag4 { flag: 0x1, size: 0 }
Bytes: 0x10

Expr::Sort(0)  // First universe in univs table
Tag4 { flag: 0x0, size: 0 }
Bytes: 0x00

Expr::Ref(0, vec![0, 1])  // First constant with 2 univ args
Tag4 { flag: 0x2, size: 2 }
+ Tag0(0)  // refs index
+ Tag0(0)  // first univ index
+ Tag0(1)  // second univ index
Bytes: 0x22 0x00 0x00 0x01

Expr::Lam(type_expr, Lam(type_expr2, body))  // 2-binder lambda
Tag4 { flag: 0x8, size: 2 }
+ type_expr + type_expr2 + body

Expr::Share(5)  // Reference to sharing[5]
Tag4 { flag: 0xB, size: 5 }
Bytes: 0xB5
```

---

## Constants

A `Constant` is the top-level unit of storage, containing an alpha-invariant declaration plus reference tables.

```rust
pub struct Constant {
    pub info: ConstantInfo,       // The declaration payload
    pub sharing: Vec<Arc<Expr>>,  // Shared subexpressions
    pub refs: Vec<Address>,       // Referenced constant addresses
    pub univs: Vec<Arc<Univ>>,    // Referenced universes
}
```

### Reference Tables

Expressions don't store addresses or universes directly. Instead:

- `Expr::Ref(idx, univ_indices)` → `constant.refs[idx]` is the address, `constant.univs[univ_indices[i]]` are the universe arguments
- `Expr::Sort(idx)` → `constant.univs[idx]` is the universe
- `Expr::Str(idx)` / `Expr::Nat(idx)` → `constant.refs[idx]` is an address into the blob store

This indirection enables sharing and smaller serializations.

### Serialization

Constants use two Tag4 flags:
- **Flag 0xD**: Non-Muts constants. Size field (0-7) holds the variant. Always 1-byte tag.
- **Flag 0xC**: Muts constants. Size field holds the entry count.

**Non-Muts format:**
```
Tag4 { flag: 0xD, size: variant }  // Always 1 byte (variant 0-7)
+ ConstantInfo payload
+ sharing vector (Tag0 length + expressions)
+ refs vector (Tag0 length + 32-byte addresses)
+ univs vector (Tag0 length + universes)
```

**Muts format:**
```
Tag4 { flag: 0xC, size: entry_count }
+ MutConst entries (no length prefix - count is in tag)
+ sharing vector
+ refs vector
+ univs vector
```

### ConstantInfo Variants

```rust
pub enum ConstantInfo {
    Defn(Definition),       // variant 0
    Recr(Recursor),         // variant 1
    Axio(Axiom),            // variant 2
    Quot(Quotient),         // variant 3
    CPrj(ConstructorProj),  // variant 4
    RPrj(RecursorProj),     // variant 5
    IPrj(InductiveProj),    // variant 6
    DPrj(DefinitionProj),   // variant 7
    Muts(Vec<MutConst>),    // uses FLAG_MUTS (0xC), not a variant
}
```

| Variant | Type | Notes |
|---------|------|-------|
| 0 | Defn | Definition/Opaque/Theorem |
| 1 | Recr | Recursor |
| 2 | Axio | Axiom |
| 3 | Quot | Quotient |
| 4 | CPrj | Constructor projection |
| 5 | RPrj | Recursor projection |
| 6 | IPrj | Inductive projection |
| 7 | DPrj | Definition projection |
| - | Muts | Uses flag 0xC |

#### Definition (variant 0)

Covers definitions, theorems, and opaques.

```rust
pub struct Definition {
    pub kind: DefKind,           // Definition | Opaque | Theorem
    pub safety: DefinitionSafety, // Safe | Unsafe | Partial
    pub lvls: u64,               // Universe parameter count
    pub typ: Arc<Expr>,          // Type expression
    pub value: Arc<Expr>,        // Value expression
}
```

**Serialization**:
```
DefKind+Safety packed (1 byte): (kind << 2) | safety
  - kind: 0=Definition, 1=Opaque, 2=Theorem
  - safety: 0=Unsafe, 1=Safe, 2=Partial
+ lvls (Tag0)
+ typ (Expr)
+ value (Expr)
```

#### Recursor (variant 1)

Eliminator for inductive types.

```rust
pub struct Recursor {
    pub k: bool,           // K-like (eliminates into Prop)
    pub is_unsafe: bool,
    pub lvls: u64,         // Universe parameter count
    pub params: u64,       // Number of parameters
    pub indices: u64,      // Number of indices
    pub motives: u64,      // Number of motives
    pub minors: u64,       // Number of minor premises
    pub typ: Arc<Expr>,    // Type expression
    pub rules: Vec<RecursorRule>,
}

pub struct RecursorRule {
    pub fields: u64,       // Field count for this constructor
    pub rhs: Arc<Expr>,    // Right-hand side
}
```

**Serialization**:
```
Packed bools (1 byte): bit 0 = k, bit 1 = is_unsafe
+ lvls (Tag0)
+ params (Tag0)
+ indices (Tag0)
+ motives (Tag0)
+ minors (Tag0)
+ typ (Expr)
+ rules.len (Tag0)
+ [RecursorRule]*
```

Each `RecursorRule` serializes as:
```
fields (Tag0)
+ rhs (Expr)
```

#### Axiom (variant 2)

```rust
pub struct Axiom {
    pub is_unsafe: bool,
    pub lvls: u64,
    pub typ: Arc<Expr>,
}
```

**Serialization**:
```
is_unsafe (1 byte: 0 or 1)
+ lvls (Tag0)
+ typ (Expr)
```

#### Quotient (variant 3)

Quotient type primitives (there are exactly 4 in Lean: `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`).

```rust
pub struct Quotient {
    pub kind: QuotKind,  // Type | Ctor | Lift | Ind
    pub lvls: u64,
    pub typ: Arc<Expr>,
}
```

**Serialization**:
```
QuotKind (1 byte: 0=Type, 1=Ctor, 2=Lift, 3=Ind)
+ lvls (Tag0)
+ typ (Expr)
```

#### Projections (variants 4-7)

Projections reference a mutual block and an index within it:

```rust
pub struct InductiveProj { pub idx: u64, pub block: Address }
pub struct ConstructorProj { pub idx: u64, pub cidx: u64, pub block: Address }
pub struct RecursorProj { pub idx: u64, pub block: Address }
pub struct DefinitionProj { pub idx: u64, pub block: Address }
```

When a constant is part of a mutual block, it's stored as a projection pointing to the shared `Muts` block. This avoids duplication.

#### Mutual Block (flag 0xC)

Muts uses its own flag (0xC) instead of a variant under flag 0xD. The size field contains the entry count, eliminating the need for a separate length prefix.

Contains multiple related constants:

```rust
pub enum MutConst {
    Defn(Definition),  // tag 0
    Indc(Inductive),   // tag 1
    Recr(Recursor),    // tag 2
}
```

Each `MutConst` entry serializes as a 1-byte tag followed by the payload. The `sharing`, `refs`, and `univs` tables are shared across all members of the mutual block.

#### Inductive (inside MutConst)

An inductive type definition with its constructors.

```rust
pub struct Inductive {
    pub recr: bool,        // Has recursive occurrences
    pub refl: bool,        // Is reflexive
    pub is_unsafe: bool,
    pub lvls: u64,         // Universe parameter count
    pub params: u64,       // Number of parameters
    pub indices: u64,      // Number of indices
    pub nested: u64,       // Nested inductive depth
    pub typ: Arc<Expr>,    // Type expression
    pub ctors: Vec<Constructor>,
}
```

**Serialization**:
```
Packed bools (1 byte): bit 0 = recr, bit 1 = refl, bit 2 = is_unsafe
+ lvls (Tag0)
+ params (Tag0)
+ indices (Tag0)
+ nested (Tag0)
+ typ (Expr)
+ ctors.len (Tag0)
+ [Constructor]*
```

#### Constructor (inside Inductive)

A constructor within an inductive type.

```rust
pub struct Constructor {
    pub is_unsafe: bool,
    pub lvls: u64,         // Universe parameter count
    pub cidx: u64,         // Constructor index
    pub params: u64,       // Number of parameters
    pub fields: u64,       // Number of fields
    pub typ: Arc<Expr>,    // Type expression
}
```

**Serialization**:
```
is_unsafe (1 byte: 0 or 1)
+ lvls (Tag0)
+ cidx (Tag0)
+ params (Tag0)
+ fields (Tag0)
+ typ (Expr)
```

---

## Sharing System

The sharing system deduplicates common subexpressions within a constant.

### How It Works

1. **Merkle hashing**: Every subexpression is assigned a structural hash using blake3
2. **Usage counting**: Count how many times each unique subexpression appears
3. **Profitability analysis**: Decide which subexpressions to share based on size savings
4. **Rewriting**: Replace selected subexpressions with `Share(idx)` references

### Profitability Heuristic

Sharing a subterm is profitable when:

```
(N - 1) * term_size > N * share_ref_size
```

Where:
- `N` = number of occurrences
- `term_size` = serialized size of the subterm
- `share_ref_size` = size of `Share(idx)` tag (typically 1-2 bytes)

### Sharing Vector

The sharing vector is built incrementally:
- Each entry can only reference earlier entries (no forward references)
- Entries are sorted by profitability (most savings first)
- Root expressions are rewritten using all available share indices

### Example

Before sharing:
```
App(
  Lam(Nat, Lam(Nat, App(add, Var(1), Var(0)))),
  App(
    Lam(Nat, Lam(Nat, App(add, Var(1), Var(0)))),  // Duplicate!
    zero
  )
)
```

After sharing:
```
sharing[0] = Lam(Nat, Lam(Nat, App(add, Var(1), Var(0))))

App(
  Share(0),
  App(Share(0), zero)
)
```

---

## Metadata

Metadata stores non-structural information that's needed for roundtrip compilation but doesn't affect the constant's identity.

### ExprMeta Arena

Expression metadata is stored as an append-only arena of `ExprMetaData` nodes, built bottom-up during compilation. Each node has an arena index, and parent nodes reference children by index.

```rust
/// Arena for expression metadata within a single constant.
pub struct ExprMeta {
    pub nodes: Vec<ExprMetaData>,
}

pub enum ExprMetaData {
    Leaf,                                             // Var, Sort, Nat, Str (no metadata)
    App { children: [u64; 2] },                       // [fun_idx, arg_idx]
    Binder { name: Address, info: BinderInfo, children: [u64; 2] }, // [type_idx, body_idx]
    LetBinder { name: Address, children: [u64; 3] },  // [type_idx, value_idx, body_idx]
    Ref { name: Address },                            // Const/Rec reference name
    Prj { struct_name: Address, child: u64 },         // Projection struct name
    Mdata { mdata: Vec<KVMap>, child: u64 },          // Metadata wrapper
}
```

**ExprMetaData Serialization** (tags 0-9, with BinderInfo packed into Binder tags):

| Tag | Variant | Payload |
|-----|---------|---------|
| 0 | Leaf | (none) |
| 1 | App | children: [u64, u64] |
| 2 | Binder (Default) | name_idx + children: [u64, u64] |
| 3 | Binder (Implicit) | name_idx + children: [u64, u64] |
| 4 | Binder (StrictImplicit) | name_idx + children: [u64, u64] |
| 5 | Binder (InstImplicit) | name_idx + children: [u64, u64] |
| 6 | LetBinder | name_idx + children: [u64, u64, u64] |
| 7 | Ref | name_idx |
| 8 | Prj | struct_name_idx + child: u64 |
| 9 | Mdata | kvmap_count + kvmaps + child: u64 |

Packing BinderInfo into the Binder tag (tags 2-5) saves 1 byte per binder. Name addresses are serialized as indices into a `NameIndex` for compactness.

### ConstantMeta

Per-constant metadata. Each variant stores a name, universe parameter names, an `ExprMeta` arena, and root indices pointing into the arena:

```rust
pub enum ConstantMeta {
    Empty,                                              // tag 255
    Def { name, lvls, hints, all, ctx,
          arena, type_root, value_root },               // tag 0
    Axio { name, lvls, arena, type_root },              // tag 1
    Quot { name, lvls, arena, type_root },              // tag 2
    Indc { name, lvls, ctors, all, ctx,
           arena, type_root },                          // tag 3
    Ctor { name, lvls, induct, arena, type_root },      // tag 4
    Rec { name, lvls, rules, all, ctx,
          arena, type_root, rule_roots },               // tag 5
}
```

**ConstantMeta Serialization:**

| Tag | Variant | Payload |
|-----|---------|---------|
| 0 | Def | name_idx, lvl_idxs, hints, all_idxs, ctx_idxs, arena, type_root, value_root |
| 1 | Axio | name_idx, lvl_idxs, arena, type_root |
| 2 | Quot | name_idx, lvl_idxs, arena, type_root |
| 3 | Indc | name_idx, lvl_idxs, ctor_idxs, all_idxs, ctx_idxs, arena, type_root |
| 4 | Ctor | name_idx, lvl_idxs, induct_idx, arena, type_root |
| 5 | Rec | name_idx, lvl_idxs, rule_idxs, all_idxs, ctx_idxs, arena, type_root, rule_roots |
| 255 | Empty | (none) |

### Indexed Serialization

Metadata uses indexed serialization for efficiency. A `NameIndex` maps addresses to sequential indices, reducing 32-byte addresses to 1-2 byte indices:

```rust
pub type NameIndex = HashMap<Address, u64>;
pub type NameReverseIndex = Vec<Address>;
```

---

## Environment

The `Env` structure stores all Ixon data using concurrent `DashMap`s.

```rust
pub struct Env {
    pub consts: DashMap<Address, Constant>,      // Alpha-invariant constants
    pub named: DashMap<Name, Named>,             // Name -> (address, metadata)
    pub blobs: DashMap<Address, Vec<u8>>,        // Raw data (strings, nats)
    pub names: DashMap<Address, Name>,           // Hash-consed Name components
    pub comms: DashMap<Address, Comm>,           // Cryptographic commitments
    pub addr_to_name: DashMap<Address, Name>,    // Reverse index
}

pub struct Named {
    pub addr: Address,        // Address of constant in consts
    pub meta: ConstantMeta,   // Metadata for this constant
}
```

### Storage Layers

| Map | Key | Value | Purpose |
|-----|-----|-------|---------|
| `consts` | Content hash | Constant | Alpha-invariant data |
| `named` | Lean Name | Named | Name → address + metadata |
| `blobs` | Content hash | Bytes | String/nat literals |
| `names` | Name hash | Name | Hash-consed name components |
| `comms` | Commitment | Comm | ZK commitments |

### Blob Storage

Blobs store raw byte data for string and natural number literals. When an expression contains `Expr::Str(idx)` or `Expr::Nat(idx)`, the `refs[idx]` address points to a blob entry.

**String encoding**: UTF-8 bytes directly.

**Natural number encoding**: Little-endian bytes (minimum representation).

```rust
// String "hello" -> 5 bytes: [0x68, 0x65, 0x6C, 0x6C, 0x6F]
// Nat 256 -> 2 bytes: [0x00, 0x01]
// Nat 0 -> 1 byte: [0x00]
```

Blobs are content-addressed: the blob's address is `blake3(bytes)`.

### Name Hash-Consing

Lean names are hierarchical (e.g., `Nat.add` = `Str(Str(Anonymous, "Nat"), "add")`). Ixon hash-conses names so identical name components share storage.

```rust
pub enum NameData {
    Anonymous,              // Root/empty name
    Str(Name, String),      // Parent + string component
    Num(Name, Nat),         // Parent + numeric component (for hygiene)
}
```

**Name serialization** (component form, for Env section 3):
```
Tag (1 byte): 0 = Anonymous, 1 = Str, 2 = Num
+ (if Str/Num) parent_address (32 bytes)
+ (if Str) string_len (Tag0) + UTF-8 bytes
+ (if Num) nat_len (Tag0) + little-endian bytes
```

Names are topologically sorted in the environment so parents are serialized before children, enabling reconstruction during deserialization.

### Environment Serialization

The environment serializes in 5 sections with a version header:

```
Header: Tag4 { flag: 0xE, size: VERSION }
```

Current version is 2 (supports zstd compression after header).

**Section 1: Blobs** (Address → raw bytes)
```
count (Tag0)
[Address (32 bytes) + len (Tag0) + bytes]*
```

**Section 2: Constants** (Address → Constant)
```
count (Tag0)
[Address (32 bytes) + Constant]*
```

**Section 3: Names** (Address → NameComponent, topologically sorted)
```
count (Tag0)
[Address (32 bytes) + NameComponent]*
```

**Section 4: Named** (Name Address → Named with indexed metadata)
```
count (Tag0)
[NameAddress (32 bytes) + ConstAddress (32 bytes) + ConstantMeta]*
```

**Section 5: Commitments** (Address → Comm)
```
count (Tag0)
[Address (32 bytes) + secret_addr (32 bytes) + payload_addr (32 bytes)]*
```

---

## Proofs and Claims

Claims, proofs, commitments, and environments share Tag4 flag 0xE.

### Tag4 0xE Variant Layout

| Size | Byte | Type | Payload |
|------|------|------|---------|
| 0 | `0xE0` | Environment | sections |
| 1 | `0xE1` | CheckProof | 1 addr + proof bytes |
| 2 | `0xE2` | EvalProof | 2 addr + proof bytes |
| 3 | `0xE3` | CheckClaim | 1 addr |
| 4 | `0xE4` | EvalClaim | 2 addr: input, output |
| 5 | `0xE5` | Commitment | 2 addr: secret, payload |
| 6 | `0xE6` | RevealClaim | 1 addr + RevealConstantInfo |
| 7 | `0xE7` | RevealProof | 1 addr + RevealConstantInfo + proof bytes |

### Claim Types

```rust
/// Evaluation claim: the constant at `input` evaluates to the constant at `output`.
pub struct EvalClaim {
    pub input: Address,   // Input constant address
    pub output: Address,  // Output constant address
}

/// Type-checking claim: the constant at `value` is well-typed.
pub struct CheckClaim {
    pub value: Address,   // Value constant address
}

/// Selective revelation of fields of a committed constant.
pub struct RevealClaim {
    pub comm: Address,              // Commitment address
    pub info: RevealConstantInfo,   // Revealed field information
}

pub enum Claim {
    Evals(EvalClaim),
    Checks(CheckClaim),
    Reveals(RevealClaim),
}
```

### Commitment Hashing

Commitments are serialized with Tag4(0xE, 5) and hashed with blake3:
```
commitment_address = blake3(0xE5 + secret_address + payload_address)
```

The payload address is always the transparent hash of the constant, regardless of the secret.
Two commitments to the same constant share the same payload address.

### RevealConstantInfo Format

RevealClaim allows selective revelation of constant metadata fields (kind, safety, idx, etc.)
without opening the full commitment. Serialization: `variant (1 byte) + field_mask (Tag0) + field values...`

The field_mask uses Tag0 encoding (1 byte for masks < 128). Fields are serialized in mask bit order.
Expression fields are revealed as `Address = blake3(serialized Expr bytes)`.

### Proof Structure

```rust
pub struct Proof {
    pub claim: Claim,     // The claim being proven
    pub proof: Vec<u8>,   // Opaque proof data (e.g., ZK proof bytes)
}
```

### Serialization Examples

**EvalClaim** (0xE4, 2 addresses):
```
E4                    -- Tag4 { flag: 0xE, size: 4 } (EvalClaim)
[32 bytes]            -- input address
[32 bytes]            -- output address
```

**EvalProof** (0xE2, 2 addresses + proof):
```
E2                    -- Tag4 { flag: 0xE, size: 2 } (EvalProof)
[32 bytes]            -- input address
[32 bytes]            -- output address
04                    -- proof.len = 4 (Tag0)
01 02 03 04           -- proof bytes
```

**CheckClaim** (0xE3, 1 address):
```
E3                    -- Tag4 { flag: 0xE, size: 3 } (CheckClaim)
[32 bytes]            -- value address
```

**RevealClaim** — reveal that a committed Definition has `safety = Safe`:
```
E6                    -- Tag4 { flag: 0xE, size: 6 } (RevealClaim)
[32 bytes]            -- comm_addr
00                    -- variant: Definition
02                    -- mask: bit 1 (safety) [Tag0]
01                    -- DefinitionSafety::Safe
```
Total: 36 bytes.

---

## Compilation (Lean → Ixon)

Compilation transforms Lean constants into Ixon format.

### CompileState

```rust
pub struct CompileState {
    pub env: IxonEnv,                        // Ixon environment being built
    pub name_to_addr: DashMap<Name, Address>, // Name → Ixon address
    pub blocks: DashSet<Address>,            // Mutual block addresses
}
```

### Expression Compilation

The `compile_expr` function transforms Lean expressions:

| Lean | Ixon | Notes |
|------|------|-------|
| `Bvar(n)` | `Var(n)` | De Bruijn index preserved |
| `Sort(level)` | `Sort(idx)` | Level added to univs table |
| `Const(name, levels)` | `Ref(idx, univ_idxs)` | Name resolved to address |
| `Const(name, levels)` in mutual | `Rec(ctx_idx, univ_idxs)` | Uses mutual context |
| `Lam(name, ty, body, info)` | `Lam(ty, body)` | Name/info to metadata |
| `ForallE(name, ty, body, info)` | `All(ty, body)` | Name/info to metadata |
| `LetE(name, ty, val, body, nd)` | `Let(nd, ty, val, body)` | Name to metadata |
| `Proj(type, idx, val)` | `Prj(type_idx, idx, val)` | Type name resolved |
| `Lit(Nat n)` | `Nat(idx)` | Bytes stored in blobs |
| `Lit(Str s)` | `Str(idx)` | Bytes stored in blobs |

### Metadata Extraction

During compilation, metadata is extracted into `ExprMetas`:

1. **Pre-order index**: Each expression node gets an index during traversal
2. **Binder info**: Lambda/forall binder names and info stored at their index
3. **Const names**: For `Rec` references, the original name is stored
4. **Mdata**: Key-value metadata wrappers are collected

### Mutual Block Handling

1. **Build MutCtx**: Map from constant name to index within the block
2. **Compile each constant** with the mutual context
3. **Create Muts block** with shared tables
4. **Create projections** for each named constant

---

## Decompilation (Ixon → Lean)

Decompilation reconstructs Lean constants from Ixon format.

### Process

1. **Load constant** from `env.consts` by address
2. **Initialize tables** from `sharing`, `refs`, `univs`
3. **Load metadata** from `env.named`
4. **Reconstruct expressions** with names and binder info from metadata
5. **Resolve references**: `Ref(idx, _)` → lookup `refs[idx]`, get name from `addr_to_name`
6. **Expand shares**: `Share(idx)` → inline `sharing[idx]` (or cache result)

### Roundtrip Verification

The `check_decompile` function verifies:
- Decompiled constants structurally match originals
- All names are correctly reconstructed
- No information is lost

---

## Comprehensive Worked Example

Let's trace the compilation of a simple definition through the entire system.

### Lean Source

```lean
def double (n : Nat) : Nat := Nat.add n n
```

### Step 1: Lean Expression

```
ConstantInfo::DefnInfo {
  name: `double
  type: Π (n : Nat) → Nat
  value: λ (n : Nat) => Nat.add n n
  ...
}
```

In Lean `Expr` form:
```
type:  ForallE("n", Const(`Nat, []), Const(`Nat, []), Default)
value: Lam("n", Const(`Nat, []),
         App(App(Const(`Nat.add, []), Var(0)), Var(0)), Default)
```

### Step 2: Ixon Compilation

**Build reference tables**:
- `refs[0]` = Address of `Nat`
- `refs[1]` = Address of `Nat.add`
- `univs` = [] (no universe parameters)

**Compile type**:
```
All(Ref(0, []), Ref(0, []))
```
Binary: `0x91` (All, 1 binder) + `0x20 0x00` (Ref, 0 univs, idx 0) + `0x20 0x00`

**Compile value**:
```
Lam(Ref(0, []), App(App(Ref(1, []), Var(0)), Var(0)))
```
Binary: `0x81` (Lam, 1 binder) + `0x20 0x00` (Ref 0) + `0x72` (App, 2 apps) + `0x20 0x01` (Ref 1) + `0x10` (Var 0) + `0x10` (Var 0)

**Sharing analysis**: `Var(0)` appears twice, but too small to benefit from sharing.

**Build Constant**:
```rust
Constant {
  info: Defn(Definition {
    kind: Definition,
    safety: Safe,
    lvls: 0,
    typ: All(Ref(0, []), Ref(0, [])),
    value: Lam(Ref(0, []), App(App(Ref(1, []), Var(0)), Var(0))),
  }),
  sharing: [],
  refs: [addr_of_Nat, addr_of_Nat_add],
  univs: [],
}
```

### Step 3: Serialization

```
D0                    -- Tag4 { flag: 0xD, size: 0 } (Constant, Defn variant)
01                    -- DefKind+Safety packed: (Definition=0 << 2) | Safe=1
00                    -- lvls = 0 (Tag0)
91 20 00 20 00        -- type: All(Ref(0,[]), Ref(0,[]))
81 20 00 72 20 01     -- value: Lam(Ref(0,[]), App(App(Ref(1,[])...
   10 10              --        ...Var(0)), Var(0)))
00                    -- sharing.len = 0
02                    -- refs.len = 2
[32 bytes]            -- refs[0] = addr_of_Nat
[32 bytes]            -- refs[1] = addr_of_Nat_add
00                    -- univs.len = 0
```

Total: ~69 bytes for the constant data (plus 64 bytes for addresses).

Note: The constant tag is always 1 byte (0xD0) since all non-Muts variants (0-7) fit in the 3-bit size field.

### Step 4: Content Address

```
address = blake3(serialized_constant)
```

This address is how `double` is referenced by other constants.

### Step 5: Metadata

Stored separately in `Named`:

```rust
Named {
  addr: address_of_double,
  meta: ConstantMeta::Def {
    name: addr_of_name("double"),
    lvls: [],
    hints: ReducibilityHints::Regular(1),
    all: [addr_of_name("double")],
    ctx: [],
    arena: ExprMeta { nodes: [
      // type arena: All(Ref(0,[]), Ref(0,[]))
      Leaf,                                       // 0: Ref(0,[]) inner
      Leaf,                                       // 1: Ref(0,[]) body
      Binder { name: "n", info: Default, children: [0, 1] }, // 2: All binder
      // value arena: Lam(Ref(0,[]), App(App(Ref(1,[]),Var(0)),Var(0)))
      Leaf,                                       // 3: Ref(0,[])
      Leaf,                                       // 4: Ref(1,[])
      Leaf,                                       // 5: Var(0)
      App { children: [4, 5] },                   // 6: App(Ref(1), Var(0))
      Leaf,                                       // 7: Var(0)
      App { children: [6, 7] },                   // 8: App(App(...), Var(0))
      Binder { name: "n", info: Default, children: [3, 8] }, // 9: Lam binder
    ]},
    type_root: 2,
    value_root: 9,
  }
}
```

### Step 6: Decompilation

To reconstruct the Lean constant:

1. Load `Constant` from `consts[address]`
2. Load `Named` from `named["double"]`
3. Resolve `Ref(0, [])` → `refs[0]` → `Nat` (via `addr_to_name`)
4. Resolve `Ref(1, [])` → `refs[1]` → `Nat.add`
5. Attach names from metadata: the binder gets name "n" from `type_meta[0]`

Result: Original Lean `ConstantInfo` reconstructed.

---

## Worked Example: Inductive Type (Bool)

Let's trace the compilation of a simple inductive type.

### Lean Source

```lean
inductive Bool : Type where
  | false : Bool
  | true : Bool
```

### Mutual Block Structure

Since `Bool` is an inductive type, it's stored in a mutual block containing:
1. The inductive type itself (`Bool`)
2. Its constructors (`Bool.false`, `Bool.true`)
3. Its recursor (`Bool.rec`)

### Ixon Compilation

**Inductive (Bool)**:
```rust
Inductive {
  recr: false,       // No recursive occurrences
  refl: false,       // Not reflexive
  is_unsafe: false,
  lvls: 0,           // No universe parameters
  params: 0,         // No parameters
  indices: 0,        // No indices
  nested: 0,         // Not nested
  typ: Sort(0),      // Type : Type 0
  ctors: [ctor_false, ctor_true],
}
```

**Constructor (Bool.false)**:
```rust
Constructor {
  is_unsafe: false,
  lvls: 0,
  cidx: 0,           // First constructor
  params: 0,
  fields: 0,         // No fields
  typ: Rec(0, []),   // : Bool (mutual reference to inductive at index 0)
}
```

**Constructor (Bool.true)**:
```rust
Constructor {
  is_unsafe: false,
  lvls: 0,
  cidx: 1,           // Second constructor
  params: 0,
  fields: 0,
  typ: Rec(0, []),   // : Bool (mutual reference to inductive at index 0)
}
```

### Serialization

The mutual block uses flag 0xC with entry count in size field:

```
C3                    -- Tag4 { flag: 0xC, size: 3 } (Muts, 3 entries)

-- Entry 0: Inductive (Bool)
01                    -- MutConst tag 1 = Indc
00                    -- Packed bools: recr=0, refl=0, is_unsafe=0
00                    -- lvls = 0
00                    -- params = 0
00                    -- indices = 0
00                    -- nested = 0
00                    -- typ: Sort(0)
02                    -- ctors.len = 2
  -- ctor_false
  00                  -- is_unsafe = false
  00                  -- lvls = 0
  00                  -- cidx = 0
  00                  -- params = 0
  00                  -- fields = 0
  30 00               -- typ: Rec(0, []) - mutual reference to Bool at index 0
  -- ctor_true
  00                  -- is_unsafe = false
  00                  -- lvls = 0
  01                  -- cidx = 1
  00                  -- params = 0
  00                  -- fields = 0
  30 00               -- typ: Rec(0, []) - mutual reference to Bool at index 0

-- Entry 1: Recursor (Bool.rec) - omitted for brevity
02 ...

-- Entry 2: Definition for Bool.casesOn or similar - if present
...

-- Shared tables
00                    -- sharing.len = 0
00                    -- refs.len = 0 (no external references needed)
01                    -- univs.len = 1
00                    -- univs[0] = Zero
```

### Projections

Individual constants are stored as projections into this block:
- `Bool` → `IPrj { idx: 0, block: block_addr }`
- `Bool.false` → `CPrj { idx: 0, cidx: 0, block: block_addr }`
- `Bool.true` → `CPrj { idx: 0, cidx: 1, block: block_addr }`
- `Bool.rec` → `RPrj { idx: 0, block: block_addr }`

---

## Cryptographic Commitments

For zero-knowledge proofs, Ixon supports cryptographic commitments:

```rust
pub struct Comm {
    pub secret: Address,   // Random blinding factor
    pub payload: Address,  // Address of committed constant
}
```

The commitment address is computed as:
```
commitment = blake3(Tag4(0xE, 5) + secret + payload)
```

The payload address is the content hash of the committed constant. Two commitments to the
same constant share the same payload address (canonicity). The secret provides blinding.

Commitments enable:
- **Whole-constant hiding** via `Comm` (hides everything including metadata)
- **Selective revelation** via `RevealClaim` (proves specific field values about a committed constant)
- **Expression-level blinding** via `Expr.ref <comm_addr>` within expression trees
- **Verifiable computation** on committed data (the ZK circuit opens commitments privately)

---

## Summary

Ixon provides a sophisticated serialization format optimized for:

| Feature | Mechanism |
|---------|-----------|
| Deterministic hashing | Alpha-invariance via de Bruijn indices |
| Compact storage | Variable-length tags, telescope compression |
| Deduplication | Merkle-tree sharing within constants |
| Roundtrip fidelity | Separate metadata layer |
| Cryptographic proofs | Content-addressed storage, commitments |

The separation of alpha-invariant data from metadata is the key innovation, enabling content-addressing where structurally identical terms share the same hash regardless of cosmetic naming choices.
