# Formalizing the Ix ZK Layer

This document describes the correctness properties of Ix's zero-knowledge
proof and commitment layer. This layer builds on the compiler pipeline
([compiler.md](compiler.md)) and ultimately depends on the kernel typechecker
([kernel.md](kernel.md)) for checking claims.


## Architecture

The ZK layer sits on top of the compiler:

```
┌────────────────────────────────────────────────────────┐
│  Claims & Proofs                                       │
│  EvalClaim, CheckClaim, RevealClaim                    │
│  Soundness: what each claim asserts about constants    │
├────────────────────────────────────────────────────────┤
│  Commitments                                           │
│  Comm = (secret, payload)                              │
│  Hiding via random blinding, binding via blake3        │
├────────────────────────────────────────────────────────┤
│  IxVM  (ZK Circuits)                                   │
│  Aiur DSL: blake3 circuit, Ixon serde circuit          │
│  Goldilocks field arithmetic                           │
├────────────────────────────────────────────────────────┤
│  Compiler Pipeline  (see compiler.md)                  │
│  Content addressing, alpha-invariant serialization     │
└────────────────────────────────────────────────────────┘
```

The ZK layer assumes the compiler's content addressing is correct — addresses
are deterministic, alpha-invariant, and collision-resistant (via blake3).

**Current state**: The commitment scheme, claim system, and IxVM circuits
(blake3, Ixon serde) are implemented. The formalization tiers below describe
formal proofs to be written.


## Part I: Commitment Scheme

**Files**: `Ix/Commit.lean`, `Ix/Claim.lean`

### Structure

A commitment hides a constant behind a blake3 hash with a random secret:

```lean
structure Comm where
  secret  : Address   -- 32 random bytes (blinding factor)
  payload : Address   -- address(constant) = blake3(serialize(constant))
```

The commitment address is:

```
commit(Comm) = blake3(0xE5 || secret || payload)
```

Where `0xE5` is the `Tag4(flag=0xE, size=5)` header byte for commitments.

### Properties

**Hiding**: The secret provides cryptographic blinding. Given only
`commit(Comm)`, an adversary cannot determine the payload (the constant's
address). This relies on blake3 preimage resistance: recovering `secret` and
`payload` from `blake3(0xE5 || secret || payload)` is computationally
infeasible.

**Binding**: Changing the constant changes the commitment. If the committed
constant changes, its `payload = address(constant)` changes (by content
addressing determinism), so `commit(Comm)` changes. This relies on blake3
collision resistance.

**Canonicity**: Two commitments to the same constant share the same payload
address. Different secrets produce different commitment addresses, but the
payload is always `blake3(serialize(constant))`.

### Commitment Creation

`Ix.Commit.commitDef` implements the full pipeline:

1. Compile the definition under anonymous name → `payloadAddr`
2. Generate random 32-byte secret → `secret`
3. Compute `commitAddr = blake3(0xE5 || secret || payloadAddr)`
4. **Alpha-invariance check**: recompile under `commitName` and assert
   the address matches `payloadAddr`
5. Register the committed constant in the environment

The alpha-invariance check (step 4) catches any name leakage. If the
compiler is not alpha-invariant, this step fails immediately rather than
letting a broken commitment propagate silently.


## Part II: Selective Revelation

**Files**: `Ix/Claim.lean`

### RevealConstantInfo

A commitment holder can selectively reveal fields of a committed constant
without opening the full commitment. `RevealConstantInfo` uses bitmask-based
field selection:

```lean
inductive RevealConstantInfo where
  | defn (kind : Option DefKind) (safety : Option DefinitionSafety)
         (lvls : Option UInt64) (typ : Option Address) (value : Option Address)
  | recr (k : Option Bool) (isUnsafe : Option Bool) ...
  | axio (isUnsafe : Option Bool) (lvls : Option UInt64) (typ : Option Address)
  | quot ...
  | cPrj ... | rPrj ... | iPrj ... | dPrj ...
  | muts (components : Array (UInt64 × RevealMutConstInfo))
```

Each field is `Option`: `some` means revealed, `none` means hidden.
Serialization uses a bitmask where bit `i` indicates whether field `i` is
present. Expression fields (type, value) are revealed as their blake3 hash
(`Address = blake3(serialize(expr))`), not the full expression tree.

### Opening a Commitment

`Ix.Commit.openConstantInfo` extracts a fully-revealed `RevealConstantInfo`
from a compiled `Ixon.ConstantInfo`. To build a partial reveal, set unwanted
fields to `none` afterward:

```lean
def openConstantInfo (ci : Ixon.ConstantInfo) : RevealConstantInfo
def openCommitment (compileEnv : CompileEnv) (commitAddr : Address)
    : Except String RevealConstantInfo
```

### Correctness

For a reveal claim to be valid:

1. The commitment must have been correctly constructed (hiding a real constant)
2. Each revealed field must match the corresponding field of the committed
   constant
3. The bitmask encoding must be deterministic (same revealed fields → same
   serialized claim)


## Part III: Claim System

**Files**: `Ix/Claim.lean`

### Claim Types

```lean
inductive Claim where
  | eval   (input : Address) (output : Address)
  | check  (value : Address)
  | reveal (comm : Address) (info : RevealConstantInfo)
```

#### EvalClaim

**Asserts**: the constant at `input` evaluates to the constant at `output`.

```
EvalClaim(input, output):
  ∃ c_in c_out, address(c_in) = input ∧ address(c_out) = output ∧
    eval(c_in) = c_out
```

**Soundness**: if a proof of `EvalClaim(input, output)` is valid, then the
constant at `input` genuinely evaluates (via the kernel's reduction rules)
to the constant at `output`.

#### CheckClaim

**Asserts**: the constant at `value` is well-typed.

```
CheckClaim(value):
  ∃ c, address(c) = value ∧ well_typed(c)
```

**Soundness**: depends on the kernel typechecker being correct
(see [kernel.md](kernel.md)). If a proof of `CheckClaim(value)` is valid,
then the constant at `value` passes the kernel's type checking.

#### RevealClaim

**Asserts**: a committed constant has the revealed fields.

```
RevealClaim(comm, info):
  ∃ secret payload c,
    commit(secret, payload) = comm ∧
    address(c) = payload ∧
    fields_match(c, info)
```

**Soundness**: if a proof of `RevealClaim(comm, info)` is valid, then the
constant behind commitment `comm` has the field values specified in `info`.

### Serialization

Claims are serialized using `Tag4` with flag `0xE`:

| Size | Byte | Type | Payload |
|------|------|------|---------|
| 3 | `0xE3` | CheckClaim | 1 address |
| 4 | `0xE4` | EvalClaim | 2 addresses (input, output) |
| 6 | `0xE6` | RevealClaim | 1 address + RevealConstantInfo |

Claims can themselves be content-addressed:

```lean
def Claim.commit (c : Claim) : Address := Address.blake3 (Claim.ser c)
```


## Part IV: IxVM (ZK Circuits)

**Files**: `Ix/IxVM.lean`, `Ix/IxVM/`

### Aiur DSL

IxVM circuits are written in Aiur, an embedded domain-specific language for
ZK constraint systems. Aiur provides:

- **Field type** `G` — Goldilocks field elements (p = 2^64 - 2^32 + 1)
- **Fixed arrays** `[G; N]` and **tuples** `(G, G, ...)`
- **Algebraic data types** (`enum`) with pattern matching
- **Heap allocation** via `store()`/`load()` pointers
- **Byte-level operations**: `u8_bit_decomposition`, `u8_xor`, `u8_add`
- **Loop unrolling** via `fold(i..j, init, |acc, @v| body)`
- **Constraint assertions** via `assert_eq!(a, b)`
- **I/O interface** via `io_read`, `io_write`, `io_get_info`

### Constrained vs. Unconstrained

Functions can be marked `#[unconstrained]`, meaning they execute without
generating ZK constraints. Their correctness is assumed, not proven within
the circuit. The constrained code then re-verifies the result.

Pattern: unconstrained deserialization produces a witness, constrained
re-serialization and hashing verifies it matches the original hash.

### Blake3 Circuit

**File**: `Ix/IxVM/Blake3.lean`

Complete blake3 hash implementation in Aiur (~500 lines):

- `blake3(input: ByteStream) -> [[G; 4]; 8]` — main entry
- `blake3_compress()` — single compression block (6 rounds of mixing)
- `blake3_g_function()` — core primitive with bit-level rotations
- Bitwise operations implemented via `u8_bit_decomposition` and
  `u8_recompose`

The circuit computes blake3 on byte streams represented as linked lists
(`ByteStream = Cons(G, &ByteStream) | Nil`). The result is a 256-bit digest
represented as `[[G; 4]; 8]` (8 groups of 4 field elements = 32 bytes).

### Ixon Serde Circuit

**Files**: `Ix/IxVM/IxonSerialize.lean`, `Ix/IxVM/IxonDeserialize.lean`

Implements Ixon serialization and deserialization in Aiur:

- `serialize(ixon: Ixon) -> ByteStream` — constrained serialization
- `deserialize(stream: ByteStream) -> Ixon` — unconstrained deserialization

The verification pattern:
1. Deserialize (unconstrained) to get an `Ixon` witness
2. Re-serialize (constrained) back to bytes
3. Hash the re-serialized bytes with blake3
4. Assert the hash matches the original input hash

This proves: "I know an Ixon value whose serialization hashes to this
address" without revealing the value.

For the Aiur constraint model, compilation pipeline, and formal verification
framework, see [aiur.md](aiur.md).


## Part V: End-to-End ZK Verification

### How It Fits Together

A complete ZK-verified claim about a Lean constant:

```
1. Compile:  Lean constant → Ixon.Constant → serialize → bytes → blake3 → Address
2. Commit:   Address + random secret → Comm → blake3 → commitment Address
3. Claim:    construct EvalClaim / CheckClaim / RevealClaim
4. Prove:    ZK circuit (IxVM) generates proof that the claim holds
5. Verify:   verifier checks ZK proof against the claim
```

### What a Verified Proof Guarantees

For `CheckClaim(addr)` with a valid ZK proof:
- There exists a constant `c` with `address(c) = addr`
- The constant `c` passes the kernel typechecker

For `EvalClaim(input, output)` with a valid ZK proof:
- There exist constants `c_in`, `c_out` with the given addresses
- Reducing `c_in` via the kernel produces `c_out`

For `RevealClaim(comm, info)` with a valid ZK proof:
- There exist `secret`, `payload` producing `comm`
- The constant at `payload` has the revealed field values

### Trust Assumptions

The end-to-end guarantee rests on:

1. **Blake3 collision resistance**: distinct constants have distinct addresses
   (256-bit security)
2. **Blake3 preimage resistance**: commitments hide their payload
3. **Aiur circuit soundness**: the ZK proof system is sound (a valid proof
   implies the circuit accepted)
4. **Circuit correctness**: the Aiur circuit computes the same function as
   the native Lean/Rust implementation
5. **Kernel correctness**: `CheckClaim` soundness depends on the kernel being
   a correct typechecker for the Lean type theory (see [kernel.md](kernel.md))
6. **Serialization correctness**: content addressing is deterministic and
   alpha-invariant (see [compiler.md](compiler.md))

### Trust Model

| Component | Trust basis |
|-----------|-------------|
| Blake3 | Cryptographic assumption (standard) |
| ZK proof system | Cryptographic assumption (Plonky2/Goldilocks) |
| Kernel correctness | Formal proof (Ix/Theory/, target: 0 sorries) |
| Serialization | Formal proof target (compiler formalization) |
| Aiur circuits | Code review + testing; formal proof of equivalence is Tier 4 |


## Part VI: Formalization Tiers

### Tier 1: Commitment Soundness

Assuming blake3 is a random oracle:

- [ ] **Hiding**: `commit(Comm)` reveals nothing about `payload`
  (given random `secret`)
- [ ] **Binding**: changing `payload` changes `commit(Comm)` (collision
  resistance)
- [ ] **Canonicity**: same constant → same `payload` (from compiler
  determinism)
- [ ] Commitment serialization is deterministic

**Key files**: `Ix/Commit.lean`

### Tier 2: Claim Soundness

Each claim type correctly asserts its intended property:

- [ ] `EvalClaim(input, output)` is valid iff the constant at `input`
  evaluates to the constant at `output`
- [ ] `CheckClaim(value)` is valid iff the constant at `value` is well-typed
  (depends on kernel.md Tier 1+)
- [ ] `RevealClaim(comm, info)` is valid iff the committed constant's fields
  match `info`
- [ ] Claim serialization is deterministic and injective

**Key files**: `Ix/Claim.lean`

### Tier 3: Selective Revelation Correctness

- [ ] Revealed fields match the committed constant's actual fields
- [ ] Bitmask encoding is correct (bit `i` ↔ field `i` present)
- [ ] Expression fields are correctly hashed (`blake3(serialize(expr))`)
- [ ] Partial reveals are consistent with full reveals (revealing fewer
  fields is always valid if the full reveal is valid)

**Key files**: `Ix/Claim.lean` (RevealConstantInfo serialization)

### Tier 4: ZK Circuit Equivalence

The Aiur circuit computes the same function as the native implementation:

- [ ] Blake3 circuit = native blake3 (for all byte stream inputs)
- [ ] Ixon serialize circuit = native Ixon serialize
- [ ] Ixon deserialize circuit = native Ixon deserialize
- [ ] Tag encoding/decoding in Aiur = native Tag encoding/decoding

**Key files**: `Ix/IxVM/Blake3.lean`, `Ix/IxVM/IxonSerialize.lean`,
`Ix/IxVM/IxonDeserialize.lean`

### Tier 5: End-to-End Soundness

A verified proof implies the stated property holds:

- [ ] `CheckClaim` proof + kernel soundness → constant is well-typed in
  Lean's type theory
- [ ] `EvalClaim` proof + kernel soundness → evaluation relationship holds
- [ ] `RevealClaim` proof + commitment soundness → revealed fields are
  correct
- [ ] Composition: sequential claims about the same addresses are consistent

**Depends on**: compiler.md Tiers 1–5, kernel.md Tiers 1–6, ZK Tiers 1–4

### Estimated Effort

| Tier | Est. LOC | Notes |
|------|----------|-------|
| 1: Commitment soundness | ~300 | Mostly Blake3 assumptions |
| 2: Claim soundness | ~500 | Depends on kernel.md Tier 1+ |
| 3: Selective revelation | ~400 | Bitmask encoding proofs |
| 4: ZK circuit equivalence | ~2,000 | Blake3 + Ixon circuit proofs |
| 5: End-to-end | ~500 | Composition of lower tiers |


## Part VII: Key References

### Lean Implementation
- `Ix/Claim.lean` — Claim types and serialization
- `Ix/Commit.lean` — Commitment pipeline, claim construction, alpha-invariance
  checks
- `Ix/IxVM.lean` — ZK VM entrypoints and module composition
- `Ix/IxVM/Blake3.lean` — Blake3 hash circuit in Aiur
- `Ix/IxVM/Ixon.lean` — Ixon format in Aiur
- `Ix/IxVM/IxonSerialize.lean` — Ixon serialization circuit
- `Ix/IxVM/IxonDeserialize.lean` — Ixon deserialization circuit
- `Ix/IxVM/ByteStream.lean` — Byte stream type for circuits
- `Ix/Aiur/Meta.lean` — Aiur DSL macros and elaboration
- `Ix/Aiur/Goldilocks.lean` — Goldilocks field definition

### Tests
- `Tests/Ix/Commit.lean` — Commitment and alpha-invariance tests

### Cross-References
- [kernel.md](kernel.md) — Kernel typechecker formalization
  (CheckClaim soundness depends on this)
- [compiler.md](compiler.md) — Compiler pipeline formalization
  (content addressing, serialization, alpha-invariance)
