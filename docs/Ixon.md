# Ixon: Ix Object Notation

Ixon is a content-addressed, alpha-invariant binary serialization format for Lean kernel types. It is designed for the Ix platform's cryptographic verification and zero-knowledge proof systems.

## Design Goals

1. **Alpha-invariance**: Structurally identical terms have identical serializations, regardless of variable names. The expression `fun (x : Nat) => x` and `fun (y : Nat) => y` serialize to the same bytes.

2. **Content-addressing**: Every constant is identified by the blake3 hash of its serialized content. This enables deduplication and cryptographic verification.

3. **Compact storage**: One variable-length integer code (TagN), telescope compression, and canonical expression sharing keep serialized constants small.

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
- **Metadata** (`ConstantMeta`, `ExprMeta`): Names and binder info—stored separately (reducibility hints live at the environment level, in `Env::anon_hints`)

This separation means cosmetic changes (renaming variables) don't change the constant's address.

## Document Overview

| Section | Contents |
|---------|----------|
| [Integer Encoding](#integer-encoding-tagn) | TagN variable-length integers |
| [Universes](#universes) | Type-level hierarchy |
| [Expressions](#expressions) | Lambda calculus terms |
| [Constants](#constants) | Top-level declarations |
| [Sharing](#sharing-system) | Canonical expression sharing |
| [Metadata](#metadata) | Names and source info |
| [Environment](#environment) | Storage and serialization |
| [The .ixc Catalog](#the-ixc-catalog-manifest) | Multi-env merkle catalog |
| [Proofs and Claims](#proofs-and-claims) | ZK claims and proofs |
| [Commitments](#cryptographic-commitments) | Commitment scheme |
| [Compilation](#compilation-lean--ixon) | Lean to Ixon conversion |
| [Decompilation](#decompilation-ixon--lean) | Ixon to Lean conversion |
| [Worked Examples](#comprehensive-worked-example) | End-to-end walkthroughs |

---

## Integer Encoding (TagN)

Every variable-length integer in the Ixon grammar uses one code, **TagN**.
That includes expression, constant, environment, claim and proof headers,
universe terms, counts, indices and lengths. Fixed-width fields are raw bytes,
unchanged: packed flag bytes, contract bytes, option bytes, variant tags and
32-byte addresses. A TagN integer carries a flag of `f ∈ {0, 2, 4}` bits:

| `f` | Used for | Notation in this document |
|---|---|---|
| 4 | Expression, constant, environment, claim and proof headers | `N4(flag, v)` |
| 2 | Universe terms | `N2(flag, v)` |
| 0 | Counts, indices, lengths and other unsigned integers | `N0(v)` |

Format version 4 introduced TagN. It replaces v3's three codes Tag4, Tag2
and Tag0, which had the same flag widths (4, 2 and 0 bits). For values below
128 (`f = 0`), 32 (`f = 2`) or 8 (`f = 4`), both codes write the same single
byte. Larger values are encoded differently.

The implementation is Lean `Ixon.putTagN f flag value` / `Ixon.getTagN f`
(`Ix/Ixon/Codec.lean`, which documents the bit layout) and Rust
`ixon::tag::TagN::put` / `TagN::get`.

### Layout

A TagN integer is one header byte followed by 0, 1, 2, 3, 4 or 8 bytes. The
header is

```
[flag : f bits][payload : r = 8 − f bits]
```

Let `L` be the top payload bit, `M` the next bit, and `c` the remaining low
`r − 2` bits:

| Header payload | Bytes that follow | Values | Decoded value |
|---|---|---|---|
| `L = 0` | none | `[0, R₁)` | the low `r − 1` payload bits |
| `L = 1, M = 0` | 1 | `[R₁, R₂)` | `R₁ + c·256 + byte` (`c` is the high part, the byte the low 8 bits) |
| `L = 1, M = 1, c = 0` | 2, little-endian | `[R₂, R₃)` | `R₂ + u16` |
| `L = 1, M = 1, c = 1` | 3, little-endian | `[R₃, R₄)` | `R₃ + u24` |
| `L = 1, M = 1, c = 2` | 4, little-endian | `[R₄, R₅)` | `R₄ + u32` |
| `L = 1, M = 1, c = 3` | 8, little-endian | `[R₅, 2^64)` | `R₅ + u64` |
| `L = 1, M = 1, c ≥ 4` | — | invalid (`f = 0, 2` only: for `f = 4`, `c` has two bits) | |

The rung ends are `R₁ = 2^(r−1)`, `R₂ = R₁ + 2^(r−2+8)`, `R₃ = R₂ + 2^16`,
`R₄ = R₃ + 2^24` and `R₅ = R₄ + 2^32`. The encoded widths are 1, 2, 3, 4, 5
and 9 bytes.

| `f` | R₁ | R₂ | R₃ | R₄ | R₅ |
|---|---:|---:|---:|---:|---:|
| 0 | 128 | 16,512 | 82,048 | 16,859,264 | 4,311,826,560 |
| 2 | 32 | 4,128 | 69,664 | 16,846,880 | 4,311,814,176 |
| 4 | 8 | 1,032 | 66,568 | 16,843,784 | 4,311,811,080 |

**Bijective.** Each rung starts where the previous one ends. So every
`UInt64` value has exactly one encoding, and every accepted byte string is the
encoding of the value it decodes to. There is no non-minimal form for readers
to reject. A reader rejects only three things:

- a code `c ≥ 4` (`f = 0` or `2`);
- an 8-byte rung whose value would reach `2^64`;
- truncated input.

The Lean proofs are in `Ix/Ixon/Verify/TagN.lean` (namespace
`Ixon.Verify.TagN`, built with the codec proofs by `lake -d IxKernel build`):

- `runGetExact_getTagN_eq`: accepted encodings are canonical;
- `putTagN_inj`: distinct values or flags have distinct encodings;
- `getTagN_rejects_code` and `getTagN_rejects_overflow`: the two rejection rules.

All four are roots of the sharing proofs' audit manifest
(`Ix/Sharing/Verify/Audit/Statements.lean`).

### Flag allocation (`f = 4`)

| Flag | Category | Type | Header value meaning |
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
| 0xA | Expr | Let | Bit 0 non-dependent, bit 1 shared borrow (values 0–3) |
| 0xB | Expr | Share | Sharing table index |
| 0xC | Constant | Muts | Entry count |
| 0xD | Constant | Non-Muts | Variant (0-7) |
| 0xE | Env/Claim | Env/Comm/AssumptionTree/Claim | `.ixe` header: format version (4, byte `0xE4`); Comm/AssumptionTree/Claim: variant |
| 0xF | Proof | ZK proofs | Variant (0-6) |

### Examples

These bytes were produced by `Ixon.putTagN`, and each decodes back to its
value with `Ixon.getTagN`:

| Integer | Bytes | Width |
|---|---|---:|
| `N4(0x1, 5)` (`Var(5)`) | `15` | 1 |
| `N4(0xB, 7)` (`Share(7)`) | `B7` | 1 |
| `N4(0xB, 8)` (`Share(8)`) | `B8 00` | 2 |
| `N4(0xB, 1031)` | `BB FF` | 2 |
| `N4(0xB, 1032)` | `BC 00 00` | 3 |
| `N4(0xB, 66568)` | `BD 00 00 00` | 4 |
| `N4(0xB, 16843784)` | `BE 00 00 00 00` | 5 |
| `N4(0xB, 4311811080)` | `BF 00 00 00 00 00 00 00 00` | 9 |
| `N4(0x2, 256)` (`Ref` with 256 universe arguments) | `28 F8` | 2 |
| `N4(0xE, 4)` (the version-4 `.ixe` header) | `E4` | 1 |
| `N4(0xE, 9)` (Resource claim) | `E8 01` | 2 |
| `N2(3, 100)` (`Univ::Var(100)`) | `E0 44` | 2 |
| `N0(42)` | `2A` | 1 |
| `N0(128)` | `80 00` | 2 |
| `N0(1000)` | `83 68` | 2 |
| `N0(16512)` | `C0 00 00` | 3 |
| `N0(82048)` | `C1 00 00 00` | 4 |
| `N0(16859264)` | `C2 00 00 00 00` | 5 |
| `N0(2^64 − 1)` | `C3 7F BF FE FE FE FF FF FF` | 9 |

`getTagN 0` rejects the header `C4` (`L = M = 1`, `c = 4`) with "invalid TagN
code 4". `getTagN 4` has no invalid header: its code `c` has two bits.

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

### Serialization (TagN, `f = 2`)

| Flag | Variant | Value | Body |
|------|---------|------------|------|
| 0 | Zero/Succ | Succ count (0 = Zero) | None |
| 1 | Max | Unused | Two Univs |
| 2 | IMax | Unused | Two Univs |
| 3 | Var | Variable index | None |

**Telescope compression**: Nested `Succ` constructors are collapsed. `Succ(Succ(Succ(Zero)))` serializes as the single integer `N2(0, 3)`.

### Examples

```
Univ::Zero
N2(0, 0)
Bytes: 0x00

Univ::Succ(Zero)  // Type 1
N2(0, 1) + base
Bytes: 0x01 0x00

Univ::Succ(Succ(Succ(Zero)))  // Type 3
N2(0, 3) + base
Bytes: 0x03 0x00

Univ::Var(0)  // First universe parameter
N2(3, 0)
Bytes: 0xC0

Univ::Var(1)  // Second universe parameter
N2(3, 1)
Bytes: 0xC1

Univ::Max(Zero, Var(1))
N2(1, 0) + Zero + Var(1)
Bytes: 0x40 0x00 0xC1

Univ::Var(100)  // 101st universe parameter (value ≥ 32: two bytes)
N2(3, 100)
Bytes: 0xE0 0x44
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
    Lam(BinderContract, Arc<Expr>, Arc<Expr>), // Lambda (input contract, type, body)
    All(BinderContract, ValueContract, Arc<Expr>, Arc<Expr>), // Forall/Pi
    Let(LetContract, Arc<Expr>, Arc<Expr>, Arc<Expr>), // Let/borrow (contract, type, value, body)
    Share(u64),                             // Reference to sharing vector
}
```

### Key Design Choices

1. **No names**: Binders have no names—they use de Bruijn indices. Names are stored in metadata.

2. **Independent contracts** (introduced in v3, unchanged in v4): `BinderContract { uses, value }` separates
   quantity (`erased`, `linear`, `affine`, `many`) from the
   `ValueContract { owned, locality }` axes. Both bound and returned values
   can be unique/shared and local/unrestricted. Foralls carry an independent
   result contract. `LetContract { nonDep, kind, binder }` distinguishes
   ordinary binding from a scoped shared borrow. Ordinary Lean compilation
   uses many/shared/unrestricted inputs and shared/unrestricted results.
   Names and implicit/explicit binder information remain metadata.
   See [the v4 specification](Ixon-v4.md) for the resource semantics.

3. **Indirection tables**: `Ref`, `Str`, `Nat` store indices into the constant's `refs` table, not raw addresses. `Sort` stores an index into the `univs` table.

4. **Share nodes**: Repeated subexpressions are written once in the constant's `sharing` table and referenced with `Share(idx)`. The table is canonical: see [Sharing System](#sharing-system).

### Serialization (TagN, `f = 4`)

| Flag | Variant | Header value | Body |
|------|---------|------------|------|
| 0x0 | Sort | Universe index | None |
| 0x1 | Var | De Bruijn index | None |
| 0x2 | Ref | Univ count | Ref index (`N0`) + univ indices (`N0` each) |
| 0x3 | Rec | Univ count | Rec index (`N0`) + univ indices (`N0` each) |
| 0x4 | Prj | Field index | Type ref index (`N0`) + value Expr |
| 0x5 | Str | Refs index | None |
| 0x6 | Nat | Refs index | None |
| 0x7 | App | App count | Function + args (telescoped) |
| 0x8 | Lam | Binder count | `(input-contract byte + type)` per binder + body |
| 0x9 | All | Binder count | `(input/result-contract byte + type)` per binder + body |
| 0xA | Let | Non-dependent flag in bit 0; borrow flag in bit 1 | Binder-contract byte + type + value + body |
| 0xB | Share | Sharing table index | None |

### Telescope Compression

Nested constructors of the same kind are collapsed:

**Applications**: `App(App(App(f, a), b), c)` becomes:
```
N4(0x7, 3)  // 3 applications
+ f + a + b + c
```

**Lambdas**: `Lam(t1, Lam(t2, Lam(t3, body)))` becomes:
```
N4(0x8, 3)  // 3 binders
+ contract1 + t1 + contract2 + t2 + contract3 + t3 + body
```

Value codes are `0 = !`, `1 = unmarked`, `2 = ~!`, `3 = ~`.
The binder byte is `uses | (value << 2)`, with quantity codes
`0 = erased`, `1 = linear`, `2 = affine`, `3 = many`.
Foralls store `input | (result << 4)`. Bits above bit 3 on lambdas
or bit 5 on foralls are invalid. The ordinary lambda byte is `0x07`;
the ordinary forall byte is `0x17`.

Foralls use the same telescope layout with flag 0x9. Readers require
nonempty, maximal telescopes and reject a nested constructor of the same
kind as the decoded base/body. Let header values above 3 and invalid TagN codes
are rejected. TagN has no non-minimal encodings to reject. A syntactically valid borrow record is still subject
to the separate owner-place and resource checks.

### Expression Examples

```
Expr::Var(0)  // Innermost bound variable
N4(0x1, 0)
Bytes: 0x10

Expr::Sort(0)  // First universe in univs table
N4(0x0, 0)
Bytes: 0x00

Expr::Ref(0, vec![0, 1])  // First constant with 2 univ args
N4(0x2, 2)
+ N0(0)  // refs index
+ N0(0)  // first univ index
+ N0(1)  // second univ index
Bytes: 0x22 0x00 0x00 0x01

Expr::Lam(many_shared, type_expr, Lam(affine_shared, type_expr2, body))
N4(0x8, 2)
+ 0x07 + type_expr + 0x06 + type_expr2 + body

Expr::Share(5)  // Reference to sharing[5]
N4(0xB, 5)
Bytes: 0xB5

Expr::Share(8)  // first index of the 2-byte rung
N4(0xB, 8)
Bytes: 0xB8 0x00

Expr::Share(1032)  // first index of the 3-byte rung
N4(0xB, 1032)
Bytes: 0xBC 0x00 0x00
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

**Univ-table invariant (canonicity §10.6):** every `univs` entry in a
valid artifact is `canonUniv`-fixed — the compiler canonicalizes at
its univ-intern choke point and preseeds tables sorted by serialized
key. Source spellings that differ from their canonical form live in
metadata only (`ConstantMeta.metaUnivs` + `univPatches`, below);
readers of pre-format artifacts get a "pre-normal-levels .ixe;
recompile it" parse error.

### Serialization

Constants use two `f = 4` flags:
- **Flag 0xD**: Non-Muts constants. The header value (0-7) is the variant, so the header is always 1 byte.
- **Flag 0xC**: Muts constants. The header value is the entry count.

**Non-Muts format:**
```
N4(0xD, variant)  // Always 1 byte (variant 0-7)
+ ConstantInfo payload
+ sharing vector (N0 length + expressions)
+ refs vector (N0 length + 32-byte addresses)
+ univs vector (N0 length + universes)
```

**Muts format:**
```
N4(0xC, entry_count)
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
+ lvls (N0)
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
+ lvls (N0)
+ params (N0)
+ indices (N0)
+ motives (N0)
+ minors (N0)
+ typ (Expr)
+ rules.len (N0)
+ [RecursorRule]*
```

Each `RecursorRule` serializes as:
```
fields (N0)
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
+ lvls (N0)
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
+ lvls (N0)
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
    pub is_unsafe: bool,
    pub lvls: u64,         // Universe parameter count
    pub params: u64,       // Number of parameters
    pub indices: u64,      // Number of indices
    pub typ: Arc<Expr>,    // Type expression
    pub ctors: Vec<Constructor>,
}
```

**Serialization**:
```
is_unsafe (1 byte: 0 or 1)
+ lvls (N0)
+ params (N0)
+ indices (N0)
+ typ (Expr)
+ ctors.len (N0)
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
+ lvls (N0)
+ cidx (N0)
+ params (N0)
+ fields (N0)
+ typ (Expr)
```

---

## Sharing System

A constant's `sharing` table holds subexpressions that its roots, and
later table entries, reference with `Share(idx)`. In format version 4 the
table is part of the canonical definition of the constant. The canonical
sharing of a constant is defined as a function of its anonymous
expressions. Two constants with equal expanded roots, `ConstantInfo`
fields, `refs`, `univs` and format must get identical bytes, whatever their
in-memory pointer sharing, construction history, compiler (Lean or Rust) or
existing table. Metadata never influences it. Which parts of this the proofs
cover, and which are checked at run time or by tests, is stated in
[What is proved, and what is not](#what-is-proved-and-what-is-not).

Both compilers build every table with this construction
(`Ix.Sharing.Exact.canonicalSharingTiered .tagN`, Rust
`canonical_sharing_tiered(ShareLayout::TagN, ..)`): single constants,
mutual blocks and aux-gen blocks, and in Rust also kernel egress and the
decompiler's recompile check. It is the only sharing construction.

### Table rules

- **Roots.** The roots are the expressions of the `ConstantInfo`, in this
  order:
  - definitions: type, then value;
  - axioms and quotients: type;
  - recursors: type, then each rule's right-hand side;
  - mutual blocks: each member's roots in member order, where an inductive
    contributes its type and then its constructors' types.

  Projections have no roots (`Ix.CompileM.constantInfoRootExprs`).
- **Backward references.** Entry `i` references only entries `j < i`.
  Roots may reference any entry. Expanding each `Share(j)` to entry `j`,
  left to right, reproduces the roots exactly. No de Bruijn index is shifted
  at a `Share`. Readers reject a `Share` index outside the table; the
  decompilers and kernel ingress do not yet check backwardness (see
  [Sharing in metadata expressions](#sharing-in-metadata-expressions)). The
  canonical construction guarantees it for compiler output.
- **Encoding.** A Share is `N4(0xB, idx)`: 1 byte for indices 0–7, 2 bytes
  for 8–1,031, 3 bytes for 1,032–66,567, then 4, 5 and 9 bytes. The table is
  written as `N0(count)` followed by the entries in order. A `Share` written
  where a telescope would continue ends that telescope. For example, the body
  `Share(j)` of an `All` ends the `All` telescope, even if entry `j` is an
  `All`.

### Canonical construction

The canonical table is the output of `Ix.Sharing.Exact.canonicalSharingTiered
.tagN` (Lean, `Ix/Sharing/Exact/Tiered.lean`) and of
`canonical_sharing_tiered(ShareLayout::TagN, ..)` (Rust,
`crates/ixon/src/sharing_exact/tiered.rs`). It runs on the roots with every
existing `Share` expanded. A constant that already carries its canonical
table normalizes to the same bytes (tested; proved under a hypothesis, see
"Idempotence" below).

1. **Structural IDs.** The distinct subterms of the roots form a DAG
   (`expand`: share expansion, then interning). Nodes are numbered by
   height, then by (constructor tag, scalar fields, child IDs)
   (`docs/sharing-minimum.md` §3.2). Hashes and the interner's pointer
   cache only speed up discovery: identity is the structural key, never a
   hash, pointer or traversal order. `canonicalize_det`
   (`Ix/Sharing/Verify/SharingExactCanon.lean`) proves that the numbering
   of interned terms depends only on the terms the roots denote, not on the
   interner's temporary IDs.
2. **Phase 1: selection, at each uniform width `w ∈ {1, 2, 3}`.**
   `optimizeSharingUniform w` finds a stored set that minimizes the
   constant's length when every `Share` costs `w` bytes and everything else
   is priced at its encoded length, telescopes and table count included.
   - Only terms with compact in-degree at least 2 are considered. The
     in-degree counts DAG edges with multiplicity, plus root occurrences.
   - Ties go to the minimum that is least in the pinned order `setPrec`.
   - Each candidate is classified as certain-stored, certain-excluded or
     uncertain using DAG bounds. The uncertain ones are searched exhaustively,
     component by component.
3. **Phase 2: slot allocation.** Let `ref(t)` be the number of `Share(t)` in
   the phase-1 output.
   - The 1-byte tier (indices 0–7) gets a set of at most 8 stored terms that
     is closed under body references and has the maximum total `ref`.
     Among such sets, it is the first in the order (`ref` descending, ID
     ascending).
   - Those terms come first, in the pinned order: stored descendants first,
     then larger in-degree, then smaller ID.
   - The rest follow in the Kahn priority order: repeatedly, the available
     entry with the largest `ref`, ties broken by the smaller ID.
   - If this order's reference cost `Σ ref · width` exceeds the phase-1
     order's, the phase-1 order is kept.
4. **Phase 3: re-materialization.** Each entry is re-encoded at minimum
   length against the entries before it, with every `Share` priced at its
   real TagN width. The roots are re-encoded against the whole table. An
   occurrence may now be written inline instead of shared.
5. **Width selection.** The canonical result is the one of the three
   (one per `w`) with the fewest real bytes, ties going to the lower `w`.
   An error at any width fails the whole construction, with the error of
   the lowest failing width.

**Run-time checks.** Each candidate is checked as it is built, and a failed
check is an internal error, never a different table. Lean builds and checks
all three candidates. Phase 3's checks (`rematerialize`) are, in order: the
layout length equals the evaluated length; it is at most phase 1's layout
length; the output re-expands, through the same interner, to the stored terms
and to the input's root IDs; and every output expression is in the wire
domain. On a DAG of at least 1,024 terms the three widths run as parallel
tasks (`tieredCandidates`; `tieredCandidates_eq` proves the result and the
error order equal to the sequential run). Rust's default mode, which the
compiler uses, applies every limit and every length check of phases 1 to 3
to all three candidates, but builds only the returned candidate's expressions
and checks those: their layout price, their re-expansion and node count, and
their serialized length. Its checked mode (`ExactSharingLimits::full_check`,
used by the unit tests, the FFI parity hooks and `sharing_corpus
--full-check`) builds and checks all three; over all of Init and all of
Mathlib it returns the same output as the default mode. The exact list is the
"Checks" section of the module documentation of
`crates/ixon/src/sharing_exact/tiered.rs`.

**Limits.** The construction runs under explicit resource limits (Lean
`Ix.Sharing.Exact.Limits`, Rust `ExactSharingLimits`). They are a safety net,
not part of the definition: they decide whether a run succeeds, never which
bytes a success produces. The defaults are far above every value observed on
the Init and Mathlib corpora. Each limit is at least 2^6 (Lean) or 2^8 (Rust)
times the earlier default under which those corpora were measured, for
example `states` 2^40 and `materialize_work` 2^56. `knapsack_cells` is 2^28 in
both languages, about 27 times the largest table-count knapsack of any width
on Init and Mathlib (9,959,424 cells). The number of sharing candidates is
recorded but not limited on this path in either language: Rust's
`candidates` limit (2^16) bounds only the exhaustive width-state search kept as
a test oracle, which is also the only meter of `transitions`.

`ix compile --sharing-limits SPEC` (also `ix compile-lean --sharing-limits`)
overrides the defaults. It sets the `IX_SHARING_LIMITS` environment variable,
which both compilers read once per run: Rust once per compile or decompile
entry point (`CompileState::sharing_limits`), Lean in `compileEnvParallelAux`
and `decompileEnvFullParallel`. An invalid value therefore fails the run once,
before any block is shared. `SPEC` is a comma-separated list of items, each
`key=value` or the word `unbounded` (every production limit at its maximum). A
value is ASCII decimal digits (no sign, no `_` separator), `2^k` with
`k ≤ 63`, or `max` (2^64 − 1). Items, keys and values are trimmed of spaces,
tabs, line feeds and carriage returns only. The keys are the limit names of
either implementation (for example `states`, `depth`, `materialize_work`,
`distinct_nodes`); keys of the other language are accepted and ignored, so one
string serves both compilers. One list of 35 specifications pins both parsers
(`LIMIT_SPEC_PARITY` in `crates/ixon/src/sharing_exact/tests.rs`,
`limitSpecParity` in `Tests/Ix/SharingExact.lean`).

Exceeding a limit is a compile error (`CompileError.resourceLimit`) that
names the limit's key and the override, for example `canonical sharing:
resource exhausted: states (limit 1099511627776); raise it with
--sharing-limits states=N (IX_SHARING_LIMITS)`. Every other construction
failure is `CompileError.sharingConstruction`. In Rust, kernel egress and the
decompiler's recompile name the constant in the message (`egress '<name>':
…`, `recompile of '<name>' (sharing): …`). There is no fallback to another
construction, and a partial or best-so-far table is never emitted.

### What is proved, and what is not

The following theorems are machine-checked in Lean, in `Ix/Sharing/Verify`
(the `IxSharingVerify` library; the TagN theorems are in
`Ix/Ixon/Verify/TagN.lean`). They are roots of the audit manifest
`Ix/Sharing/Verify/Audit/Statements.lean` (111 roots), which
`lake build --wfail IxSharingVerify` checks: every root uses exactly its
listed axioms, which are among `propext`, `Classical.choice` and
`Quot.sound`, and no declaration of an `Ix.Sharing` module uses `sorry`
(`Audit/SorryFrontier.lean`). `lake lint` builds the library too. The construction theorems are stated for a
successful run on the canonical DAG of the input (`ex.dag`, `ex.roots`); the
step that builds that DAG is outside them (see "Expansion" below).

- **Phase 1 minimality** (`Ix/Sharing/Verify/UniformOptimality.lean`):
  `optimizeUniform_minimum` and `optimizeUniform_least`. Suppose
  `optimizeUniformExpanded w limits ex` succeeds with the default
  branch-and-bound search (`limits.uniformSubsetSearch = false`; the
  compiler cannot change it). Then:
  - its stored set minimizes the uniform-width length `ulen` over all stored
    sets of terms with in-degree at least 2;
  - its `modelBytes` is that minimum;
  - it is the `setPrec`-least such minimum.

  The certain-excluded rule needs every telescope spine to be shorter than
  `teleSubaddEnd` (the fifth TagN rung end for `f = 4`, 4,311,811,080). The
  optimizer checks this before it runs and otherwise fails with a format
  error, so the theorems carry no extra hypothesis.
- **Phase 2** (`TieredTier.lean`: `allocate_spec`, `firstTier_spec`;
  `TieredGuard.lean`: `allocate_optimal`):
  - the first tier is a maximum-`ref` set of at most 8 terms closed under
    body references, and the first such set in the tie order;
  - the final order is a permutation of the phase-1 table in which every
    entry's body references come before it;
  - it is the phase-1 order when the guard kept that order, and otherwise
    the first tier followed by the Kahn order;
  - its reference cost is at most that of the phase-1 order;
  - when the table has at most 1,032 entries, so that every index from 8 on
    has width 2, its reference cost `Σ ref · width` is the minimum over all
    orders that place every body reference first.
- **Phase 3** (`TieredPhase3.lean`: `materializeTable_min`,
  `rematerialize_spec`; `TieredIdem.lean`: `canonicalTiered_reexpand`):
  - every entry, and every root, has the minimum layout length among all
    writings of its term with its dictionary;
  - the output re-expands, against the canonical DAG, to the stored terms
    and exactly the input's root IDs;
  - entry `k` references only entries below `k`;
  - the layout length is at most the phase-1 candidate's.
- **Width selection** (`TieredSelect.lean`: `canonicalTieredCore_select`): the
  result has the fewest final layout bytes of the three candidates, and the
  lowest width among ties.
- **Serialized length** (`TieredWire.lean`: `canonicalSharingTiered_serialized`;
  `canonicalSharingTieredTable_serialized` for roots given with a table): if
  `canonicalSharingTiered .tagN roots limits` returns `r`, then the length it
  reports, `r.result.variableBytes`, is the length of the table count
  (`tag0Size`) plus the serialized length (`serExpr`) of every table entry and
  root, and the layout price it minimized, `r.result.modelBytes`, equals it.
  So the layout bytes that phase 3 and the width selection minimize are
  serialized bytes.
- **Wire validity** (`TieredWire.lean`: `canonicalSharingTiered_format`):
  every output entry and root is `wireWF`, the table count is below `2^64`,
  and Shares are backward: entry `k` references only entries below `k`, and
  roots only table entries.
- **The compiler's sharing builder** (`Ix/Sharing/Verify/Builder.lean`,
  stated over the wire-validity theorem): every block
  `Ix.CompileM.buildConstantWithSharing` builds from a `wireWF` payload and
  representable reference and universe tables is `wireWF`
  (`buildConstantWithSharing_wireWF`), and its stored bytes decode
  exactly to it. The singleton-driver tail `finishConstantInfoWithSharing`
  either returns such a block or fails with an error that the sharing
  builder returns (`finishConstantInfoWithSharing_run_codecWF`, concluding
  `SharingRunOK`). The theorems about the stored bytes
  (`BlockResult.mk'_codec_roundtrip`,
  `BlockResult.constantInfo_codec_roundtrip`,
  `finishConstantInfoWithSharing_run_codecWF`) are proved but are not audit
  roots: `BlockResult.mk'` hashes the block, and the Blake3 package's
  `HasherOps.hash` carries a `native_decide` axiom, which the manifest does
  not admit. No theorem covers the compiler's per-declaration drivers
  before that tail.
- **Structural IDs** (`SharingExactCanon.lean`: `canonicalize_det`): two
  interner outputs that pass the interner's checks, are hash-consed and
  whose roots denote the same terms canonicalize to the same DAG and root
  IDs.
- **Integers**: the TagN theorems of [Integer Encoding](#integer-encoding-tagn).

**Compiled code.** The compiler runs faster bodies than the specifications
the theorems describe. Each fast twin is attached to its specification by a
`@[csimp]` theorem `@f = @fFast`, an unconditional equality over every input
(results, metered counts and errors), so compiled code calls the twin while
every theorem keeps talking about the specification; the module map of
`Ix/Sharing/Exact.lean` lists them. The audit module
`Ix/Sharing/Verify/Audit/CompiledCode.lean` fails the build unless every
`@[csimp]` theorem of an `Ix` module on the compiler's import path is an audit
root (19), and unless no declaration of `Ix.Sharing.*` is
`unsafe`, `partial`, `@[implemented_by]` or `@[extern]`, except the
interner's pointer-cache key `exprPtr`.

**Role of the run-time checks.** The phase-3 checks listed under
[Canonical construction](#canonical-construction) stay in the code: the
layout length against the evaluated length and against phase 1, the
re-expansion to the stored terms and the input's root IDs, and the wire
domain (`phase3_le_phase1` proves that the comparison with phase 1 never
fails). Rust runs every check listed in the module documentation of
`sharing_exact/tiered.rs`. The theorems are stated for successful runs, so a
failing check turns a run into an error, never into a different table.

Not claimed:

- **No global minimum.** The canonical table is not a global byte minimum
  over all tables, orders and occurrence choices. Each phase is exact for
  its own problem; their composition is not claimed to be optimal.
- **Phase 2 on larger tables.** For tables of more than 1,032 entries, whose
  indices span the 2- and 3-byte rungs, the Kahn order is not claimed to
  minimize `Σ ref · width`.
- **Expansion.** The step from the input expressions to the canonical DAG
  (`expand`: share expansion and interning, with a pointer cache keyed by
  `exprPtr`, an `unsafe` address read) is not covered: no theorem states
  that the DAG denotes the input expressions. The round trip to the input is
  therefore proved only relative to that DAG; the run-time re-expansion
  check uses the same interner, so it does not check the expansion
  independently. Logically `exprPtr` is an arbitrary function of the
  expression; no theorem inspects it, so the theorems hold whatever addresses
  a run sees. Independence from in-memory pointer sharing is tested, not
  proved: in `exact-sharing`, pool-shared, deserialized, DAG-shared and
  re-encoded inputs give identical bytes under the tiered construction and
  the exact search (120 generated inputs).
- **Idempotence** is proved only under the hypothesis that expanding the
  output yields the input's canonical DAG and root IDs
  (`canonicalSharingTieredTable_idem`). It is tested: re-running the Rust
  construction on every stored constant reproduces the stored bytes, for
  the Init and Init+Std files compiled on Lean 4.34.0 and for the Init and
  Mathlib files compiled on Lean 4.33.1.
- **Rust.** The Rust implementation is not proved. It is checked against
  Lean by differential tests (`exact-sharing-ffi`; with `IX_SHARING_CORPUS`
  it runs over a whole `.ixe`). Its phase-1 search evaluates each
  component's area under a truncated cost model, where Lean's specification
  evaluates the component's whole closure; the outputs are equal on every
  input tested. On corpora compiled with `ix compile` on Lean 4.34.0, with
  Rust in its checked mode, Lean and Rust produce the same bytes for all
  56,783 stored constants of Init and all 100,277 of Init+Std, with no
  resource exhaustion on either side; on Lean 4.33.1 the same held for
  Init (56,622 stored constants; the 4.34.0 `Init` is a larger library) and
  for all 20,284 constants of a Mathlib sample (every 50th constant, plus
  every constant with more than 2,000 candidates). The merge-queue suite
  `lake test -- --ignored compile` compiles every constant of its test
  environment (238,574 on Lean 4.34.0) with the Lean and the Rust compiler
  and requires identical serialized environments
  ([performance](sharing-minimum-performance.md)).
- **Length range in Rust.** Lean computes lengths with arbitrary-precision
  `Nat`. Rust's phase 1 uses 128-bit length arithmetic and fails closed
  (`format bound: LengthOverflow`) on an input whose phase-1 lengths leave
  that range, where Lean succeeds: for example the chain
  `e(i+1) = App(e(i), e(i))` at depth 127 or more (at depth 126 both give the
  same bytes). No Init or Mathlib constant comes near this bound. This is a
  known divergence of the two implementations.
- **Failure.** The theorems describe successful runs. A run that exceeds a
  limit returns an error.

### Example

`T2 → T2`, where `T2 = Prop → Prop → Prop`, is a fixture from
`docs/sharing-minimum.md` §2. As an axiom with `univs = [Zero]`, so that
`Sort(0)` is `Prop`, the unshared constant is 20 bytes:

```
D2 00 00                    -- N4(0xD, 2) Axiom, not unsafe, lvls = 0
93 17 92 17 00 17 00 00 17  -- typ: one All telescope of 3 binders
   00 17 00 00
00                          -- sharing: N0(0)
00                          -- refs: N0(0)
01 00                       -- univs: N0(1), Zero
```

The canonical construction stores `T2` once and gives 17 bytes:

```
D2 00 00                    -- N4(0xD, 2) Axiom, not unsafe, lvls = 0
91 17 B0 B0                 -- typ: All(Share(0), Share(0)); the body Share
                            --   ends the telescope
01                          -- sharing: N0(1)
92 17 00 17 00 00           --   entry 0 = T2 = All(Sort 0, All(Sort 0, Sort 0))
00                          -- refs: N0(0)
01 00                       -- univs: N0(1), Zero
```

The bytes were produced by `normalizeConstantSharingTiered .tagN`, and the
`exact-sharing` suite checks them. The compilers' sharing builders
(`Ix.CompileM.buildConstantWithSharing`, Rust
`apply_sharing_to_axiom_with_limits`) build the same bytes from the unshared
constant (`exact-sharing-ffi`). Every integer here is below the first TagN
rung end, so v3's integer codes would write the same bytes for this table.

### Sharing in metadata expressions

Metadata expressions are the entries of `ConstantMeta.metaSharing`: the
compiled call-site arguments that call-site surgery collapsed, and rewritten
call-site heads. A `Share(i)` inside them is read in an extended index
space. This is a reader rule; it adds no bytes. Let `p` be the size of the
primary `sharing` table (for a projection, the table of its `Muts` block)
and `q` the size of `metaSharing`.

- **Primary expressions** (roots and primary entries): `Share(i)` is
  `sharing[i]` and needs `i < p`. Metadata never changes how primary bytes
  decode.
- **Inside `metaSharing[j]`:**
  - `Share(i)` with `i < p` is primary entry `i`. Shares nested inside that
    entry are again primary.
  - `Share(i)` with `p ≤ i < p + j` is `metaSharing[i − p]`, read in the
    scope of entry `i − p`.
  - Any other index is rejected: `i ≥ p + q` is out of range, and
    `p + j ≤ i < p + q` is a forward or self reference.

  Every metadata-to-metadata step goes to a lower entry, so expansion
  terminates.
- **Call-site references.** `CallSiteEntry.collapsed sharingIdx` and
  `origHead = some (sharingIdx, _)` index `metaSharing` directly, not offset
  by `p`, and read that entry in its own scope.

Both decompilers implement the rule: Lean `Ix.DecompileM` (`ShareScope`,
`resolveShareIn`) and Rust `ix_compile::decompile` (`ShareScope`). When a
constant's metadata is loaded, they check the whole table first
(`validateMetaSharing`, Rust `validate_meta_sharing`): every `Share(i)`
occurring in `metaSharing[j]` must have `i < p + j`. The first violation, in
entry order and then left-to-right pre-order, is reported as
`invalidMetaShareIndex` (Rust `DecompileError::InvalidMetaShareIndex`,
error tag 11). An out-of-range index in a primary expression, or an
out-of-range call-site `sharingIdx`, is `invalidShareIndex`. The
semantic-contract scan (`Ix.SemanticContract.containsIxon`, Rust
`semantic_contract::contains_ixon`) expands Shares with the same scopes.
Kernel ingress, the IxVM circuit and the resource validators do not read
`metaSharing` contents. Two older gaps remain: a call site nested inside a
metadata expression may reference any `metaSharing` entry, including its own,
and neither the decompilers nor kernel ingress check that primary entries
reference only earlier entries. A malformed table of either kind can make
them loop instead of failing; hardening the readers against malformed input
is follow-up work.

The primary table is built first and never depends on metadata. No compiler
emits a `Share` in metadata expressions, and there is no canonical metadata
construction. On Mathlib, metadata expressions total 42,929 bytes (0.0013%
of the environment file), and no metadata expression contains a `Share`
([measurements](sharing-minimum-measurements.md#metasharing)).


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

**ExprMeta serialization.** An arena is `N0(len)` followed by its nodes in
index order. Node `i` starts with a tag byte `kind << 3 | mask`; the fields
follow in declaration order:

| kind | Variant | Payload (in order) | structural slots |
|-----|---------|---------|---|
| 0 | Leaf | (none) | — |
| 1 | App | fun?, arg? | fun, arg |
| 2–5 | Binder (2 + BinderInfo: Default, Implicit, StrictImplicit, InstImplicit) | name_idx, type?, body? | type, body |
| 6 | LetBinder | name_idx, type?, value?, body? | type, value, body |
| 7 | Ref | name_idx | — |
| 8 | Prj | struct_name_idx, child? | child |
| 9 | Mdata | kvmap_count + kvmaps, child? | child |
| 10 | CallSite | name_idx, entries, canon_meta, orig_head | — |
| 11 | EtaCallSite | n_synth, name_idx, entries, canon_meta, wrapper_meta | — |

Child references are never absolute indices:

- **Implicit (post-order) children.** Bit `s` of `mask` set means
  structural slot `s` is not written: it is the node a post-order cursor
  expects. The cursor `top` starts at `i` and visits the slots last to
  first; an implicit slot is node `top − 1`, after which `top` becomes
  `lo[top − 1]`, and `lo[i]` is `top` after the last slot (the first index
  of node `i`'s contiguous post-order block; `lo[i] = i` for a node without
  structural slots). The compiler allocates the arena bottom-up in
  post-order, so an unshared subtree costs one tag byte per App and no
  child bytes at all.
- **Explicit references.** A structural slot whose bit is clear (a shared
  node: an expression-cache hit, or any other position), and every
  call-site reference (entry `meta`, `canon_meta`, `orig_head` meta,
  `wrapper_meta`), is `N0` of the backward delta `(i − 1 − c) mod 2^64`.
  Forward references are representable (they wrap), so every arena of
  `u64` indices has an encoding.
- **One encoding per arena.** The writer marks a slot implicit exactly
  when its child is `top − 1`; the reader rejects an explicit slot equal to
  `top − 1`, an implicit slot with `top = 0`, mask bits beyond the kind's
  slot count, and kinds above 11.

The decoded arena (absolute `u64` indices) is identical to the one the
compiler built, so readers of `ExprMeta` see no difference.

Example: `fun (x : T) => f x` allocated as `[Ref T, Ref f, Leaf, App(1, 2),
Binder(x, Default, [0, 3])]` serializes (name indices `T = 1`, `f = x = 0`)
to `05 38 01 38 00 00 0B 13 00`: both App children and both Binder children
are implicit (`0B = 1 << 3 | 0b11`, `13 = 2 << 3 | 0b11`). Sharing the leaf
in `[Leaf, App(0, 0)]` gives `02 00 0A 00`: the argument is implicit, the
function an explicit delta `1 − 1 − 0 = 0`.

Name addresses are serialized as indices into a `NameIndex` for
compactness. Measurements and the design are in
[`sharing-minimum-arena.md`](sharing-minimum-arena.md).

### ConstantMeta

Per-constant metadata: a variant payload (`ConstantMetaInfo`) plus
four extension vectors appended after it (the wrapper):

```rust
pub struct ConstantMeta {
    pub info: ConstantMetaInfo,        // variant payload (below)
    pub meta_sharing: Vec<Arc<Expr>>,  // collapsed call-site args (surgery)
    pub meta_refs: Vec<Address>,       // refs-table extension (virtual space)
    pub meta_univs: Vec<Arc<Univ>>,    // univs-table extension (virtual space)
    pub univ_patches: Vec<UnivPatch>,  // original level spellings (§10.6)
}

pub struct UnivPatch {
    pub arena_idx: u64,      // metadata-arena node of the occurrence
    pub univ_idxs: Vec<u64>, // virtual space: < univs.len() → primary,
                             // else meta_univs[i - univs.len()]
}
```

Each wrapper vector serializes as an `N0` count + entries and is
empty (one zero byte) on most constants. `meta_univs`/`univ_patches`
restore source level spellings the §10.6 canonicalization displaced
from content; `meta_sharing` holds call-site surgery's collapsed
arguments, whose `Share` references use the extended index space of
[Sharing in metadata expressions](#sharing-in-metadata-expressions). Each `ConstantMetaInfo` variant stores a name, universe
parameter names, an `ExprMeta` arena, and root indices pointing into
the arena:

```rust
pub enum ConstantMetaInfo {
    Empty,                                              // tag 255
    Def { name, lvls, all, ctx,
          arena, type_root, value_root },               // tag 0
    Axio { name, lvls, arena, type_root },              // tag 1
    Quot { name, lvls, arena, type_root },              // tag 2
    Indc { name, lvls, ctors, all, ctx,
           arena, type_root },                          // tag 3
    Ctor { name, lvls, induct, arena, type_root },      // tag 4
    Rec { name, lvls, rules, all, ctx,
          arena, type_root, rule_roots },               // tag 5
    Muts { all, aux_layout },                           // tag 6
}
```

**ConstantMeta Serialization:**

| Tag | Variant | Payload |
|-----|---------|---------|
| 0 | Def | name_idx, lvl_idxs, all_idxs, ctx_idxs, arena, type_root, value_root |
| 1 | Axio | name_idx, lvl_idxs, arena, type_root |
| 2 | Quot | name_idx, lvl_idxs, arena, type_root |
| 3 | Indc | name_idx, lvl_idxs, ctor_idxs, all_idxs, ctx_idxs, arena, type_root |
| 4 | Ctor | name_idx, lvl_idxs, induct_idx, arena, type_root |
| 5 | Rec | name_idx, lvl_idxs, rule_idxs, all_idxs, ctx_idxs, arena, type_root, rule_roots |
| 6 | Muts | class count (N0) + per-class name-idx vecs, then `Option<AuxLayout>` |
| 255 | Empty | (none) |

**`AuxLayout`** (the `Muts` sidecar — nested-auxiliary layout for
mutual blocks that underwent nested-inductive expansion; metadata
only, never entering any content hash):

```
0x00                                  -- None (no nested auxes)
0x01                                  -- Some, followed by:
  perm count (N0) + [N0]*         -- perm[sourceJ] = canonicalI
  ctor-count count (N0) + [N0]*   -- per-source-position aux ctor counts
  evaporated count (N0) + [u8]*     -- one 0/1 flag per perm entry
```

The three vectors always serialize together (one unified format), and
`evaporated` always carries `perm.len()` flags — a flag set means the
block owns the evaporation of that source position (its alias resolves
to an external head's generic recursor; call-site surgery keys
head-rewrite plans off these flags alone). Writers normalize
legacy-constructed values with defaulted-empty `evaporated` to
all-zero flags, so Lean and Rust serializers agree byte-for-byte.

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

**Name serialization** (component form, for Env section 4):
```
Tag (1 byte): 0 = Anonymous, 1 = Str, 2 = Num
+ (if Str/Num) parent_address (32 bytes)
+ (if Str) string_len (N0) + UTF-8 bytes
+ (if Num) nat_len (N0) + little-endian bytes
```

Names are topologically sorted in the environment so parents are serialized before children, enabling reconstruction during deserialization.

### Environment Serialization

Serialized environments are stored on disk with the **`.ixe`** file
extension (e.g., `compilemathlib.ixe`). The `ix compile` CLI produces
these files; the default output name is the lowercased input file stem
plus `.ixe`. See `crates/ixon/src/serialize.rs` (`Env::put`) for the
byte-level layout.

The .ixe layout is an `N4(0xE, VERSION)` header byte followed by a
32-byte canonical merkle root, the bundle header fields, and then 6
sections (hot data first, metadata last).

The format has the stable identifier `ixon-v4`. The header value is the
numeric **format version** (`Env::VERSION`, currently `4`, so the first byte
of a v4 file is `0xE4`). Any change
to serialized bytes bumps the version; every reader
(`read_env_header` on the Rust side, `Ixon.getEnv` /
`getEnvVerifiedLazy` on the Lean side) rejects a mismatch with an
error naming both versions and asking for a recompile. There is no
back-compat reading of old versions — `.ixe` files are regenerated
artifacts. Versions 0–7 fit in the header byte; later versions use the
multi-byte TagN rungs.

Format version 4 also sets the object-format byte of claims, proofs and
catalog manifests (`Ixon.Env.OBJECT_FORMAT`, Rust `Env::OBJECT_FORMAT`, equal
to the version). Artifacts that cache `.ixe` files key them by the version:
the TruthMines piece cache includes `ixe=<VERSION>` in its key, and the test
environment `tc-parity.ixe` is recompiled when its header carries another
version.

The version-4 header byte `0xE4` is the same byte as the Check claim tag
`N4(0xE, 4)` (see [Proofs and Claims](#proofs-and-claims)), just as
version 3's `0xE3` was the same byte as the Eval claim tag. Readers decide
what the byte means from context: an `.ixe` reader expects an environment
header and a claim reader expects a claim. The byte alone does not identify
the object kind.

```
Header:      N4(0xE, VERSION)            -- 0xE4 for version 4
Root:        32 bytes                     -- canonical merkle root over
                                            consts.keys(); for empty
                                            const sets this is the
                                            fixed `zero_address`
                                            sentinel.
Main:        1 byte (0x00 | 0x01) + 32 bytes if 0x01
                                          -- optional bundle root; see
                                            "Bundles" below.
Assumptions: count (N0) + [Address (32 bytes)]*
                                          -- strictly ascending; the
                                            bundle trust boundary.
```

The root is mandatory (non-optional): every env has a unique canonical
identity recoverable from its file. Two envs with the same const set
produce byte-identical roots regardless of construction order.
Deserialization recomputes the root from `consts` and rejects any
mismatch as tampered.

`main` and `assumptions` are NOT covered by the consts merkle root —
`main` is a convenience pointer (readers verify `main ∈ consts`;
consumers holding an externally-expected address must compare), and
the assumptions root, when a claim needs it, is recomputed as
`merkle_root_canonical(leaves)` from the section (identical to the
root `AssumptionTree::canonical` produces over the same leaves).

**Section 1: Blobs** (Address → raw bytes)
```
count (N0)
[Address (32 bytes) + len (N0) + bytes]*
```

Every reader verifies `blake3(bytes) == addr` per blob entry — a
swapped blob would otherwise silently change a Nat/String literal's
value under an otherwise-valid file.

**Section 2: Constants** (Address → length-prefixed Constant bytes)
```
count (N0)
[Address (32 bytes) + len (N0) + Constant bytes]*
```

The `N0` length sidecar is a **section-level** framing integer: it is not
part of the constant's content-addressed bytes. The address is
computed as `blake3` over only the constant bytes (verified per
entry on load). This layout lets a lazy loader slice each constant
directly into a [`LazyConstant`](../crates/ixon/src/lazy.rs) without
parsing its header, deferring full deserialization until first
access.

**Section 3: Reducibility hints** (§2 index → ReducibilityHints)
```
count (N0)                          -- must be ≤ the §2 count
[index_delta (N0) + fused_hint (N0)]*
```

The **anon hint channel** — merged advisory hints per constant
address, for readers that never see names (`get_anon`/`get_anon_mmap`,
the anon-mode kernel, `--anon` bundles). Entries are keyed by **index
into §2's ascending-address order**, delta-coded: the k-th entry's
constant index is `idx_k = idx_{k-1} + delta_k` with `idx_{-1} = -1`
(so the first delta stores `index + 1`). Every delta must be ≥ 1,
which makes the section strictly ascending and duplicate-free by
construction; an index ≥ the §2 count is malformed. The hint fuses
variant and height into one `N0` value: `0` = Opaque, `1` = Abbrev,
`h + 2` = Regular(h) with `h : u32`. A typical entry is 2-3 bytes
(previously a 32-byte address + 1-3 bytes).

Hints never appear in `ConstantMeta`. Because anonymization conflates
alpha-identical definitions (many names, one address), this per-address
map holds one **min-merged winner** per constant
(`Env::register_hint`, order-independent under
`Opaque < Abbrev < Regular(h)`) — fine for the kernel's def-eq unfold
ordering, which is all this channel feeds. The EXACT per-definition
hints live per name in §5 entry headers. Hints keyed by an address not
stored in §2 are unrepresentable — writers reject such envs. Hints are
performance-only advice (the `Regular(0)` fallback is always correct)
and are intentionally outside the consts merkle root.

**Section 4: Names** (Address → NameComponent, topologically sorted)
```
count (N0)
[Address (32 bytes) + NameComponent]*
```

**Section 5: Named** (name §4-index → Named with indexed metadata)
```
count (N0)
[ name_idx  (N0)         -- absolute index into §4's topo order
  const_idx (N0)         -- absolute index into §2's ascending order
  hint      (N0)         -- fused option: 0 = none, 1 = Opaque,
                              2 = Abbrev, h+3 = Regular(h)
  meta_len  (N0)         -- byte length of the metadata blob below
  ConstantMeta             -- name references are §4 indices
  original: 0x00 | 0x01 + Address (32 bytes) + ConstantMeta ]*
                           -- ConstantMeta + original span meta_len bytes
```

Entries stay sorted by ascending name hash (the diff meta sweep
merge-joins two files' §5 sections on it), so `name_idx` values are
not monotonic — both indices are absolute, not delta-coded.

`hint` is the **exact per-name reducibility hint** (`none` for
theorems etc.). It lives here — not in §3 — because alpha-identical
definitions under different names share one §2 constant, so the
per-address §3 channel can only hold a min-merged advisory winner;
faithful decompilation needs the per-definition value. The hint sits
in the entry header, before the length-prefixed metadata blob, so a
reader can scan every `name → hint` pair while skipping the blobs
outright (`meta_len` bytes each) — `parse_lazy_index` does exactly
that instead of parsing and discarding each metadata arena. Full
readers parse the blob and reject entries whose parsed size disagrees
with `meta_len`.

The `original` address (aux_gen provenance) stays a **raw 32 bytes**:
the compiler records the address of Lean's source form but never stores
that constant, so an original that differs from the entry's address is
not in §2 (nor, after a prune cut, is an *assumed* one), which a §2
index cannot represent.

Because §2 order is load-bearing for §3/§5 index resolution, every
reader enforces strictly ascending §2 addresses during its scan (this
also makes the collected §2 key list directly usable for the merkle
recompute, with no re-sort).

**Section 6: Commitments** (Address → Comm)
```
count (N0)
[Address (32 bytes) + secret_addr (32 bytes) + payload_addr (32 bytes)]*
```

The full reader (`Env::get` / Lean `getEnv`) rejects trailing bytes
after Section 6.

### Anonymous-only loading

`Env::get_anon` (`crates/ixon/src/serialize.rs`) is a sibling of
`Env::get` that reads the header, §1 blobs, §2 consts, and §3 hints,
then STOPS — the metadata sections are laid out after the hints
precisely so anon readers never touch them. The returned `Env` has
empty `named`/`names`/`comms` and is suitable for anon-mode kernel
workflows that never consult metadata. Steady-state memory for a
Mathlib-scale env drops from ~3-4 GB (structured + metadata) to ~1 GB
(lazy bytes only).

Exposed to Lean via `rs_de_env_anon` (`Ix.Ixon.rsDeEnvAnon`);
`Env::get_anon_mmap` is the zero-copy mmap sibling and
`Env::parse_lazy_index` the zero-copy index variant (walks every
section, but reads only the §5 entry headers — name index, const
rank, hint — and seeks past each `meta_len`-framed metadata blob, so
no metadata arena is ever parsed).

### Bundles: pinning a single value

A **bundle** is an `.ixe` whose `main` points at a distinguished
constant (e.g. an anonymous `Defn` wrapping a value, produced by
`Ix.Commit.compileDef`) and whose contents are closed up to
`assumptions`. Because a constant's address is a merkle root over its
entire dependency DAG (refs tables hold addresses of constants and
literal blobs, recursively), `main`'s 32 bytes alone pin the value;
the bundle is the data-availability artifact that ships the bytes
behind those addresses.

- `Env::prune_to_closure(main, assumed)` builds a bundle: the 3-edge
  closure of `main` (Expr refs; projection → `Muts` block; `Muts`
  block → member/constructor projections), cut at `assumed`, carrying
  constants (genuine bytes), blobs, per-constant hints, and display
  metadata (named entries, name components + string blobs, `DataValue`
  payload blobs, `meta_refs` extension edges, aux_gen originals).
- `Env::validate_closed()` is the receiver-side check: `main ∈ consts`
  and every reachable address is carried (consts ∪ blobs) or assumed.
- Whole-environment files are the degenerate case (`main` absent,
  `assumptions` empty).

The CLI producer is `ix pack`:

```
lake exe ix pack <env.ixe> <name> [--out <path>]
                 [--assume <name|hex64,...>] [--assume-file <f>] [--verbose]
```

It resolves `<name>` (displayed form) against the env's `named` table,
runs the prune, re-validates with `validate_closed`, and writes the
bundle (default `<name>.ixe`). `--assume` entries — names or 64-hex
constant addresses — declare trust-boundary cut points; the ones
actually reached become the bundle's `assumptions` (thin bundle).

The source env is memory-mapped and lazily loaded; display metadata is
carried by **re-streaming §5 per prune fixpoint round**
(`Env::prune_to_closure_streaming`) so resident metadata is
O(survivors), not O(env) — byte-identical output to the in-memory
`prune_to_closure`, which shares the same carry engine. `--anon` skips
metadata entirely (`Env::prune_to_closure_anon`): value closure + §3
hints, empty §4/§5 — the minimal artifact a receiver needs to
typecheck/evaluate the pinned value, since `validate_closed` checks
only the value pin. (`ix shard extract` is the non-bundle sibling: a
general sub-env for the kernel-check pipeline, no `main` root.)

### Diffing environments

```
lake exe ix diff <old.ixe> <new.ixe> [--anon | --meta] [--verbose]
```

`ix diff` (engine: `ixon::diff`) joins two envs on names: a name
"changed" ⇔ its constant address changed, with per-field
classification (`type`/`value`/`lvls`/…, `block.*` through projection
descent, `"encoding"` for pure representation churn). Because one
edited constant re-addresses its whole reverse-dependency cone, every
changed row also carries a **root vs rippled** verdict: changed pairs
are re-classified under the quotient of all changed rows' old→new
address mapping, and rows fully explained by dependency re-addressing
are `rippled` (hidden by default; `--verbose` lists). A 5-day mathlib
window classifies 143k changed names into ~4.5k roots.

Memory: both files are mmap'd and lazily parsed in both modes
(constant windows stay zero-copy; `ConstantMeta` is never
bulk-materialized). `--meta` compares metadata by streaming both §5
named sections in a lockstep merge-join — each side's entry is parsed
against its own §4 reverse index, compared, and dropped. Raw §5
windows are *not* comparable across files (metadata name references
are file-relative §4 indices), so the sweep compares parsed,
Address-valued `ConstantMeta`. Exit codes follow GNU diff: 0 = no
difference in the selected mode, 1 = differences, 2 = error.

---

## The `.ixc` Catalog Manifest

A catalog commits a SET of `.ixe` environments ("pieces") as one
artifact — semantically one big anonymous env, the union of the
members' constant sets, never materialized as a single file. Anonymous
Ixon is conflict-free (§2 is content-addressed: a key collision between
two files implies byte-equal values), so catalog identity involves no
names, no qualification, and no merging. Two roots commit everything:

- `members_root`: `merkle_root_canonical` over member ENV ROOTS — the
  membership commitment.
- `content_root`: `merkle_root_canonical` over the UNION of the
  members' §2 constant addresses — the env root of the virtual union
  env, computed by a k-way streaming sweep over the members'
  already-sorted §2 address lists (O(members) resident).

Because both roots are set functions of content, re-partitioning
storage never moves a commitment.

On disk a `.ixc` is a self-contained DIRECTORY — manifest and piece
files together, no separate pieces dir and no report side-files (the
manifest is the machine-readable record; `ix catalog info` dumps it):

```
<name>.ixc/
  manifest              the binary manifest below
  <label>.ixe           one piece per member (fat profile)
  <label>.chunk<i>.ixe  chunk files (chunked profile)
  .cache/               drivers' build metadata; ignored by verify
```

`ix catalog assemble` ingests external pieces by hard link (copy
fallback), so assembling from same-filesystem pieces moves no bytes.

Manifest wire format (Convention B — own magic + explicit version,
fixed-width little-endian like `.ixes`; source of truth
`crates/ixon/src/catalog.rs`, Lean mirror `Ix/Catalog.lean`):

```
magic    b"IXC\0\0\0\0\0"            (8)
version  u32 = 2
flags    u32                          # bit0: storage profile (0 = fat, 1 = chunked)
object_format     u8 = 4              # ixon-v4
validator         u8 = 1              # erased-lean-v1 catalog claims
members_root      32 bytes
content_root      32 bytes
member_count      u32
per member:
  env_root        32 bytes            # anon semantic identity
  const_count     u64
  label           u16 len + utf8      # qualifier; doubles as the piece
                                      #   filename stem (<label>.ixe)
  toolchain       u16 len + utf8
  source_pin      u16 len + utf8      # e.g. git:<url>@<rev>; empty = local
  deps            u32 count + [u32]*  # member indices, all < self (topo)
  preimage        0x00 | 0x01+32      # store key of the member's const-set
                                      #   AssumptionTree (`ix tree env`)
storage (by flags bit0):
  fat:     per member: file_hash 32 + file_bytes u64
           # self-contained pieces; closures may overlap (identity
           #   dedup only — never a soundness issue)
  chunked: chunk_count u32; per chunk:
           chunk_root 32 + file_hash 32 + file_bytes u64 + owner u32
           # disjoint chunks partitioning the union; an address in two
           #   chunks is a HARD error (no-redeclaration invariant)
trailing bytes: reserved future sections, preserved opaquely
```

Both roots are recomputed against a stored manifest: `members_root`
from the entries on every parse, `content_root` by the k-way sweep in
`ix catalog verify` (which also enforces the profile's dedup rule and
every piece's env root, counts, and sizes; `--deep` re-hashes files
and fully verifies each piece load — all against the pieces inside
the directory). `ix merge` materializes any subset as one ordinary
anonymous `.ixe` (a derived view — the catalog directory stays the
source of truth). The `Catalog` claim (below) binds both roots.

---

## Proofs and Claims

Envs, commitments, the AssumptionTree data type, and all claims share
the `f = 4` flag 0xE. Proofs (opaque ZK bytes) share flag 0xF. Values
0..=7 fit in single-byte headers. Catalog (variant 8) and Resource
(variant 9) are in TagN's two-byte rung: `0xE8 0x00` and `0xE8 0x01`.
Environment headers are interpreted in the `.ixe` context: the v4
environment header is `0xE4`, the same byte as the Check claim tag. The
enclosing protocol must identify the object kind.

Every claim and proof payload starts with two bytes immediately after its
header: object format `4`, then validator `0` (structural-v1),
`1` (erased-lean-v1), or `2` (resource-v1). Readers require the validator
assigned to that variant. Whole-object readers reject trailing bytes and
earlier unscoped encodings. These bytes are included in the claim digest
and proof statement. A claim with another object format is rejected with
`claim: unsupported object format N, expected 4 — regenerate the claim`
(catalog manifests likewise: `catalog: unsupported object format N, expected
4 — regenerate the catalog`).

### Flag 0xE Variant Layout (Env + Comm + AssumptionTree + Claims)

| Value | Bytes | Type | Payload |
|------|------|------|---------|
| 4 (format) | `0xE4` | Environment (`.ixe` context) | 32-byte merkle root + main/assumptions + 6 sections |
| 1 | `0xE1` | Commitment | 2 addr: secret, payload |
| 2 | `0xE2` | AssumptionTree | recursive merkle-tree body (see below) |
| 3 | `0xE3` | Eval claim | 2 addr (input, output) + opt assumptions |
| 4 | `0xE4` | Check claim | 1 addr (const) + opt assumptions |
| 5 | `0xE5` | CheckEnv claim | 1 addr (env root) + opt assumptions |
| 6 | `0xE6` | Reveal claim | 1 addr (comm) + RevealConstantInfo |
| 7 | `0xE7` | Contains claim | 2 addr (tree, const) |
| 8 | `0xE8 0x00` | Catalog claim | 2 addr (members root, content root) + opt assumptions |
| 9 | `0xE8 0x01` | Resource claim | 2 addr (complete env root, resource profile) |

The claim payloads in this table follow the two scope bytes. Reveal and
Contains require validator `0`; Eval, Check, CheckEnv, and Catalog require
validator `1`; Resource requires validator `2`.

`opt assumptions` encoding: 1 byte `0x00` for `None`, or `0x01` followed
by 32 bytes for `Some(merkle_root)`.

The Catalog claim's two roots use two DISTINCT leaf vocabularies,
never mixed: `members` leaves are member ENV ROOTS; `content` (and
`assumptions`) leaves are CONSTANT ADDRESSES. See
`crates/ixon/src/catalog.rs` for the `.ixc` artifact it binds. The
exact wire bytes are pinned by twin tests
(`proof.rs::catalog_claim_wire_bytes_pinned` and the `claim` suite's
digest-parity test) so the Rust and Lean serializers cannot drift on
the multi-byte-tag path.

### Flag 0xF Variant Layout (Proofs)

| Value | Byte | Type | Payload |
|------|------|------|---------|
| 0 | `0xF0` | Eval proof | claim payload + N0 length + opaque ZK bytes |
| 1 | `0xF1` | Check proof | claim payload + N0 length + opaque ZK bytes |
| 2 | `0xF2` | CheckEnv proof | claim payload + N0 length + opaque ZK bytes |
| 3 | `0xF3` | Reveal proof | claim payload + N0 length + opaque ZK bytes |
| 4 | `0xF4` | Contains proof | claim payload + N0 length + opaque ZK bytes |
| 5 | `0xF5` | Catalog proof | claim payload + N0 length + opaque ZK bytes |
| 6 | `0xF6` | Resource proof wrapper | claim payload + N0 length + opaque proof bytes |

Proof bytes are uniform opaque ZK proofs — witness data (e.g., merkle
paths for Contains) is prover-side scratch consumed by the ZK circuit
and NOT transmitted on the wire. Wrapper decoding alone proves nothing.
IxVM supports Check, CheckEnv, Reveal, and Contains; Resource is currently
validated by the native Lean/Rust boundary and is explicitly rejected as an
IxVM proof request. Catalog proofs compose erased CheckEnv claims.

### Claim Types

```rust
pub enum Claim {
    /// `input` evaluates to `output`, optionally modulo `assumptions`.
    Eval { input: Address, output: Address, assumptions: Option<Address> },
    /// The constant at `const_addr` is well-typed, optionally modulo
    /// `assumptions`.
    Check { const_addr: Address, assumptions: Option<Address> },
    /// Every constant in the env merkle-rooted at `root` is well-typed,
    /// optionally modulo `assumptions` (typically the env's axiom leaves).
    CheckEnv { root: Address, assumptions: Option<Address> },
    /// Selective field revelation of a committed constant.
    Reveal { comm: Address, info: RevealConstantInfo },
    /// `const_addr` is a leaf in the merkle tree rooted at `tree`.
    Contains { tree: Address, const_addr: Address },
    /// The `.ixc` catalog claim: `content` is exactly the union of the
    /// member envs committed at `members`, and every constant in it is
    /// well-typed, optionally modulo `assumptions`. Verified by
    /// COMPOSITION of per-piece CheckEnv claims with set discharge —
    /// there is deliberately no whole-catalog interpreter arm.
    Catalog { members: Address, content: Address, assumptions: Option<Address> },
    /// Complete closure passes resource-v1 under the committed profile.
    Resource { root: Address, profile: Address },
}
```

### AssumptionTree

A serializable merkle tree over `Address` leaves, used to recover the
leaf set committed to by a conditional claim's `assumptions` root.

The body has **three** variants — leaves, internal nodes, and an
explicit `Padding` sentinel that the canonical builder inserts at
odd-count levels so the byte-tree matches `merkle_root_canonical`'s
zero-mixing shape (a `Padding` hashes to `zero_address()`).

```
[N4(0xE, 2) = 0xE2] [body]

body recursive:
  Leaf(addr):   [0x00] [addr:32]
  Padding:      [0x01]
  Node(l, r):   [0x02] [body l] [body r]
```

Size is shape-dependent: each `Leaf` is 33 bytes, each `Padding` is
1 byte, each `Node` is 1 byte plus its children, and the top-level
header `0xE2` adds 1 byte. For example, `N = 1` ⇒ 34 bytes; `N = 2` ⇒ 68
bytes; `N = 3` (padded to 4) ⇒ 104 bytes.

### Commitment Hashing

Commitments are serialized with `N4(0xE, 1)` (byte `0xE1`) and hashed with blake3:
```
commitment_address = blake3(0xE1 + secret_address + payload_address)
```

The payload address is always the transparent hash of the constant, regardless of the secret.
Two commitments to the same constant share the same payload address.

### RevealConstantInfo Format

The Reveal claim allows selective revelation of constant metadata fields
(kind, safety, idx, etc.) without opening the full commitment.
Serialization: `variant (1 byte) + field_mask (N0) + field values...`

The field_mask is an `N0` integer (1 byte for masks < 128). Fields are
serialized in mask bit order. Expression fields are revealed as `Address
= blake3(serialized Expr bytes)`.

### Proof Structure

```rust
pub struct Proof {
    pub claim: Claim,     // The claim being proven
    pub proof: Vec<u8>,   // Opaque ZK proof bytes (uniform across variants)
}
```

### Serialization Examples

**Eval claim** (0xE3, 2 addresses + opt assumptions byte):
```
E3                    -- N4(0xE, 3) (Eval)
04 01                 -- object format 4, erased-lean-v1
[32 bytes]            -- input address
[32 bytes]            -- output address
00                    -- assumptions = None (or 01 + [32 bytes] for Some)
```

**Eval proof** (0xF0, claim payload + opaque ZK bytes):
```
F0                    -- N4(0xF, 0) (Eval proof)
04 01                 -- object format 4, erased-lean-v1
[32 bytes]            -- input address
[32 bytes]            -- output address
00                    -- assumptions = None
04                    -- proof.len = 4 (N0)
01 02 03 04           -- opaque ZK proof bytes
```

**Check claim** (0xE4, 1 address + opt assumptions byte):
```
E4                    -- N4(0xE, 4) (Check)
04 01                 -- object format 4, erased-lean-v1
[32 bytes]            -- const address
00                    -- assumptions = None
```

**Reveal claim** — reveal that a committed Definition has `safety = Safe`:
```
E6                    -- N4(0xE, 6) (Reveal)
04 00                 -- object format 4, structural-v1
[32 bytes]            -- comm_addr
00                    -- variant: Definition
02                    -- mask: bit 1 (safety) [N0]
01                    -- DefinitionSafety::Safe
```
Total: 38 bytes.

**Contains claim** (0xE7, 2 addresses):
```
E7                    -- N4(0xE, 7) (Contains)
04 00                 -- object format 4, structural-v1
[32 bytes]            -- tree (merkle root)
[32 bytes]            -- const address (asserted leaf)
```
Total: 67 bytes.

**Resource claim** (`0xE8 0x01`, 2 addresses):
```
E8 01                 -- N4(0xE, 9) (Resource): two-byte TagN rung
04 02                 -- object format 4, resource-v1
[32 bytes]            -- complete env root
[32 bytes]            -- resource profile address
```
Total: 68 bytes.

The claims fixture `Tests/Fixtures/ixon-v4/claims.tsv` holds the canonical
bytes and BLAKE3 digest of one claim of every variant; its headers and scope
bytes match the claim examples above. `lake exe ixon-v4-tests` compares the file
with the serializers' output, and `--export-fixtures` regenerates it under
`ixon-v4-fixtures/` in the scratch directory `$IX_IXON_V4_DIR` (default
`/tmp`).


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
| `Lam(name, ty, body, info)` | `Lam(many_shared, ty, body)` | Ordinary contract; name/info to metadata |
| `ForallE(name, ty, body, info)` | `All(many_shared, shared, ty, body)` | Ordinary contracts; name/info to metadata |
| `LetE(name, ty, val, body, nd)` | `Let({nonDep: nd, kind: value, binder: many_shared}, ty, val, body)` | Name to metadata; ordinary let contract |
| `Proj(type, idx, val)` | `Prj(type_idx, idx, val)` | Type name resolved |
| `Lit(Nat n)` | `Nat(idx)` | Bytes stored in blobs |
| `Lit(Str s)` | `Str(idx)` | Bytes stored in blobs |

This table describes unannotated source. The source-contract frontend resolves
annotations before canonicalization and sharing, then transports their exact
contracts through the reserved semantic metadata frame. Both production
compilers validate resources and erased typing before emitting annotated
artifacts. Unsupported transformations reject explicitly.

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

### Sharing

Every block, whether a single constant, a mutual block or an aux-gen
block, gets its `sharing` table from the canonical construction of the
[Sharing System](#sharing-system), applied to the block's roots after
`refs` and `univs` are allocated. The metadata arena follows the unshared
expression tree, and a `Share` is transparent to it. Re-sharing a constant
therefore leaves its metadata valid. A construction failure is a compile
error for that block.

---

## Decompilation (Ixon → Lean)

Decompilation reconstructs Lean constants from Ixon format.

### Process

1. **Load constant** from `env.consts` by address
2. **Initialize tables** from `sharing`, `refs`, `univs`
3. **Load metadata** from `env.named`
4. **Reconstruct expressions** with committed contracts, and names/binder info from metadata
5. **Resolve references**: `Ref(idx, _)` → lookup `refs[idx]`, get name from `addr_to_name`
6. **Expand shares**: `Share(idx)` → inline `sharing[idx]` (or cache result). Inside a `meta_sharing` entry, indices at or above the primary table size resolve into earlier `meta_sharing` entries (see [Sharing in metadata expressions](#sharing-in-metadata-expressions))

Nondefault contracts are reconstructed from semantic bytes even without names
or optional metadata. Optional metadata cannot inject contracts or replay an
unsupported rewrite that would erase them.

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
All(many_shared, shared, Ref(0, []), Ref(0, []))
```
Binary: `0x91 0x17` (All, 1 ordinary binder/result) + `0x20 0x00` (Ref, 0 univs, idx 0) + `0x20 0x00`

**Compile value**:
```
Lam(many_shared, Ref(0, []), App(App(Ref(1, []), Var(0)), Var(0)))
```
Binary: `0x81 0x07` (Lam, 1 ordinary binder) + `0x20 0x00` (Ref 0) + `0x72` (App, 2 apps) + `0x20 0x01` (Ref 1) + `0x10` (Var 0) + `0x10` (Var 0)

**Canonical sharing**: the two roots are the type and the value.
- `Ref(0, [])` is 2 bytes and occurs three times. Written inline that is
  6 bytes. Stored once (2 bytes) and referenced three times with a 1-byte
  `Share(0)`, it is 5 bytes. The table count `N0(1)` is one byte, the same
  as `N0(0)`.
- `Var(0)` occurs twice but is one byte, and a `Share` costs at least one
  byte, so storing it never pays.

The canonical table is therefore `[Ref(0, [])]`, and the constant is 84
bytes instead of the 85 it would take unshared.

**Build Constant**:
```rust
Constant {
  info: Defn(Definition {
    kind: Definition,
    safety: Safe,
    lvls: 0,
    typ: All(many_shared, shared, Share(0), Share(0)),
    value: Lam(many_shared, Share(0), App(App(Ref(1, []), Var(0)), Var(0))),
  }),
  sharing: [Ref(0, [])],
  refs: [addr_of_Nat, addr_of_Nat_add],
  univs: [],
}
```

### Step 3: Serialization

```
D0                    -- N4(0xD, 0) (Constant, Defn variant)
01                    -- DefKind+Safety packed: (Definition=0 << 2) | Safe=1
00                    -- lvls = 0 (N0)
91 17 B0 B0           -- type: All(Share(0), Share(0))
81 07 B0 72 20 01     -- value: Lam(Share(0), App(App(Ref(1,[])...
   10 10              --        ...Var(0)), Var(0)))
01                    -- sharing.len = 1
20 00                 --   sharing[0] = Ref(0, [])
02                    -- refs.len = 2
[32 bytes]            -- refs[0] = addr_of_Nat
[32 bytes]            -- refs[1] = addr_of_Nat_add
00                    -- univs.len = 0
```

Total: 20 bytes for the scalar/expression data, table counts and table
entry, plus 64 bytes for the two addresses: **84 bytes**.

Note: The constant header is always 1 byte (0xD0) since every non-Muts
variant (0-7) is below TagN's first rung end of 8.

`ix compile` writes exactly these bytes. For a file `Double.lean` that
contains only the definition above, `ix compile Double.lean --no-build
--consts double --out double.ixe` stores this 84-byte constant, in hex:

```
d0 01 00 91 17 b0 b0 81 07 b0 72 20 01 10 10 01 20 00 02
35e1cc809f6f076521a43f85068d5592220407c0532b6a08952f40d8523d04bc   -- Nat
3e8aadcc611c4d8677cadf00c78506561d33738ee3d571f7a4196e260580c9b8   -- Nat.add
00
```

### Step 4: Content Address

```
address = blake3(serialized_constant)
```

This address is how `double` is referenced by other constants. For the
bytes above it is
`eefff4002f029ee49aa94e8e9127b0b1664c86fec956e62332fd3be1672d0cef`
(`ix addr-of double --ixe double.ixe`).

### Step 5: Metadata

Stored separately in `Named`:

```rust
Named {
  addr: address_of_double,
  meta: ConstantMeta::Def {
    name: addr_of_name("double"),
    lvls: [],
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
3. Expand each `Share(0)` to `sharing[0]` = `Ref(0, [])`
4. Resolve `Ref(0, [])` → `refs[0]` → `Nat` (via `addr_to_name`)
5. Resolve `Ref(1, [])` → `refs[1]` → `Nat.add`
6. Attach names from metadata: the binder gets name "n" from `type_meta[0]`

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

The family block contains one inductive entry for `Bool`, including its two
constructor records. The recursor has a separate block referring to the family.
Constructors are nested in their inductive entry, rather than additional mutual
members.

### Ixon Compilation

**Inductive (Bool)**:
```rust
Inductive {
  is_unsafe: false,
  lvls: 0,           // No universe parameters
  params: 0,         // No parameters
  indices: 0,        // No indices
  typ: Sort(0),      // univs[0] = Succ(Zero), so Bool : Type
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
C1                    -- N4(0xC, 1) (Muts, 1 entry)

-- Entry 0: Inductive (Bool)
01                    -- MutConst tag 1 = Indc
00                    -- is_unsafe = false
00                    -- lvls = 0
00                    -- params = 0
00                    -- indices = 0
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

-- Shared tables
00                    -- sharing.len = 0
00                    -- refs.len = 0 (no external references needed)
01                    -- univs.len = 1
01 00                 -- univs[0] = Succ(Zero)
```

### Projections

Individual constants are stored as projections into this block:
- `Bool` → `IPrj { idx: 0, block: block_addr }`
- `Bool.false` → `CPrj { idx: 0, cidx: 0, block: block_addr }`
- `Bool.true` → `CPrj { idx: 0, cidx: 1, block: block_addr }`
- `Bool.rec` → `RPrj { idx: 0, block: recursor_block_addr }`

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
commitment = blake3(N4(0xE, 1) + secret + payload)
```

The payload address is the content hash of the committed constant. Two commitments to the
same constant share the same payload address (canonicity). The secret provides blinding.

Commitments enable:
- **Whole-constant hiding** via `Comm` (hides everything including metadata)
- **Selective revelation** via `Claim::Reveal` (proves specific field values about a committed constant)
- **Expression-level blinding** via `Expr.ref <comm_addr>` within expression trees
- **Verifiable computation** on committed data (the ZK circuit opens commitments privately)

---

## Summary

Ixon provides a sophisticated serialization format optimized for:

| Feature | Mechanism |
|---------|-----------|
| Deterministic hashing | Alpha-invariance via de Bruijn indices |
| Compact storage | One variable-length integer code (TagN), telescope compression |
| Deduplication | Canonical sharing within constants (phase-1 minimality machine-checked) |
| Roundtrip fidelity | Separate metadata layer |
| Cryptographic proofs | Content-addressed storage, commitments |

The separation of alpha-invariant data from metadata is the key innovation, enabling content-addressing where structurally identical terms share the same hash regardless of cosmetic naming choices.
