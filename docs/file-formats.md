# Ix File Formats & Wire Protocols Inventory

This document is the canonical inventory of every on-disk file format, content-addressed object encoding, container/manifest format, and cache layout used across the Ix codebase (`crates/` and `Ix/`), followed by an audit of **overlapping / redundant formats** and how they can be consolidated.

---

## 1. Executive Summary Table

| # | Format / Extension | Magic / Header | Encoding Style | Primary Producers / Consumers | Purpose |
|---|---|---|---|---|---|
| 1 | **`.ix` / `.lean`** | UTF-8 text | Surface syntax | `Ix/Frontend/Parser/`, `Ix/Frontend/Format.lean`, `ix frontend` | Pure Ix surface language (substructural contracts `0`/`1`/`&`/`!`/`~`, `#<hash>` pins, `map Name := #<hash>`, order-free decls, tactics). |
| 2 | **`.ixon`** | UTF-8 text | Closed IR text grammar | `Ix/IxonSyntax.lean`, `crates/ixon/src/syntax/`, `ix decompile` | Low-level textual representation of `Ix.Constant` / `Ix.Expr` trees (pre-`Ix.Frontend` decompiler format). |
| 3 | **`lean4export`** | UTF-8 line stream | Line-oriented (`#0`, `#NS`, `#DEF`, …) | `Ix/LeanExport.lean`, `ix compile-export` | External compatibility ingress for upstream `lean4export` text dumps. |
| 4 | **`Ixon.Expr`** | `TagN(4, 0x0..0xB, _)` | `TagN` post-order / prefix | `crates/ixon/src/expr.rs`, `Ix/Ixon.lean`, `Ix/IxVM/` | Alpha-invariant expression nodes (`Sort`, `Var`, `Ref`, `Rec`, `Prj`, `Str`, `Nat`, `App`, `Lam`, `All`, `Let`, `Share`). |
| 5 | **`Ixon.Constant`** | `TagN(4, 0xC..0xD, _)` | `TagN` + canonical sharing | `crates/ixon/src/constant.rs`, `Ix/Ixon.lean`, `IxStore` | Canonical alpha-invariant constant (`Muts` block `0xC` or singleton `0xD0..0xD7`); its `blake3` digest IS the constant's `Address`. |
| 6 | **`.ixe` (`Ixon.Env`)** | `0xE4` (v4) / `0xE5` (v5) | `TagN` 5-section bundle | `crates/ixon/src/serialize.rs`, `Ix/Ixon.lean`, `ix compile`, `ix frontend compile`, `ix pack` | Self-contained environment or pruned single-closure value bundle (`Header` + `§1 Blobs` + `§2 Constants` + `§3 Hints` + `§4 Names` + `§5 Metadata`). |
| 7 | **`Ixon.Comm`** | `0xE1` (`TagN(4, 0xE, 1)`) | `TagN` + 64 bytes | `crates/ixon/src/comm.rs`, `Ix/Ixon.lean` | Blinded cryptographic commitment (`0xE1 \|\| secret:32 \|\| payload:32`) to a constant address. |
| 8 | **`Ix.AssumptionTree`** | `0xE2` (`TagN(4, 0xE, 2)`) | `TagN` recursive Merkle tree | `crates/ixon/src/assumption_tree.rs`, `Ix/AssumptionTree.lean`, `ix tree` | Binary Merkle tree of assumption addresses (`Leaf` / `Branch`), stored in `IxStore` under its Merkle root via `Store.writeAt`. |
| 9 | **`Ix.Claim` / `ElabClaim`** | `0xE3..0xE7`, `E8 00..02`, `E8 04` | `TagN` statement | `crates/ixon/src/proof.rs`, `Ix/Claim.lean`, `ix claim` | Public statement to be proven (`Eval`, `Check`, `CheckEnv`, `Reveal`, `Contains`, `Catalog`, `Resource`, `Binding`, `ElabClaim`). |
| 10 | **`Ix.RoleTable`** | `E8 03` (`TagN(4, 0xE, 11)`) | `TagN` + fixed 33B rows | `crates/ixon/src/role_table.rs`, `IxC/Kernel/Ixon/RoleTable.lean` | Canonical 103-entry primitive role-binding table + sorted evidence addresses (embedded in v5 `.ixe` header). |
| 11 | **`Ixon.Proof`** | `0xF0..0xF7` (`TagN(4, 0xF, 0..7)`) | `TagN` wrapper | `crates/ixon/src/proof.rs`, `Ix/Ixon.lean`, `ix prove`, `ix verify` | Bundles a `Claim` with its opaque `AiurProof` (`BatchProof<GoldilocksBlake3Config>`) bytes; stored in `IxStore`. |
| 12 | **`.ixpack` + `.ixidx`** | `IXPACK01` / `IXIDX001` | 8B-aligned mmap + 256-fanout index | `crates/common/src/store.rs`, `Ix/Store.lean`, `ix store` | Immutable, memory-mapped packfile pair in `~/.ix/store/packs/` with $O(\log(N/256))$ zero-syscall lookup. |
| 13 | **`.ixc/` (`manifest`)** | `IXC\0\0\0\0\0` (8B) | Fixed LE (`u32`/`u64`) | `crates/ixon/src/catalog.rs`, `Ix/Catalog.lean`, `ix catalog` | Self-contained catalog directory (`<name>.ixc/manifest` + `<label>.ixe` pieces) committing to `members_root` and `content_root`. |
| 14 | **`.ixes`** | `IXES\0\0\0\0` (8B) | Fixed LE (`u32`/`u64`/`u128`) | `crates/kernel/src/shard.rs`, `Ix/Cli/ShardCmd.lean`, `ix shard` | Kernel shard partition manifest (per-shard `blocks`, `foreign_blocks`, `assumption_root`, bisection tree, peak RSS). |
| 15 | **`.ixprof`** | `IXPROF\0\0` (8B) | Fixed LE (`u32`/`u64`) + CSR | `crates/kernel/src/profile.rs`, `Ix/Cli/ProfileCmd.lean`, `ix profile` | Per-block kernel execution counters (80B/block) + CSR consumer→producer $\delta$-unfolding hypergraph. |
| 16 | **`IXHC`** | `IXHC` (4B) | Fixed LE + option tags | `Ix/HostAdmission/Codec.lean`, `crates/ixon/src/host_admission.rs`, `ix check-lean`, `ix verify-host` | Host-checked target-artifact admission statement (`logical` or `tiered (logicalRoot, tierRoot)`). |
| 17 | **Aiur VK v5 & `BatchProof`** | 14B header (`7 × u16 LE`) | Dense `u16 LE` / `bincode` | `crates/aiur/src/vk_codec.rs`, `MultiStark/SystemDeserialize.lean` | In-circuit-parseable Multi-STARK verifier key (`vk_codec` v5) and Goldilocks/BLAKE3 FRI `BatchProof`. |
| 18 | **Cache Hints (`~/.ix/cache/`)** | 65B ASCII `<64-hex>\n` | Plaintext hex pointer | `Ix/Cli/ShardProofIndex.lean`, `crates/ffi/src/aiur/aggregate/store.rs` | Wipeable, untrusted lookup hints (`shard-proofs/<claim-digest>` and `aggregate/<slot-key>`) pointing to `Ixon.Proof` wrappers in `IxStore`. |

---

## 2. The Unified `TagN` (`0x0`–`0xF`) Header Registry

All core Ixon semantic objects use the **`TagN` varint code** ([`crates/ixon/src/tag.rs`](file:///home/jcb/projects/ix-frontend/crates/ixon/src/tag.rs), [`Ix/Ixon.lean`](file:///home/jcb/projects/ix-frontend/Ix/Ixon.lean)). With `flag_bits = 4`, the leading byte has layout:

```text
  7   6   5   4     3     2   1   0
+---------------+-------+-----------+
|   flag (4b)   | large |  payload  |
+---------------+-------+-----------+
```

- **Rung 1 (`large = 0`, single byte)**: `value` in `0..=7` is stored directly in bits `2..0`.
- **Rung 2+ (`large = 1`, `1 + k` bytes where `k = (bits 2..0) + 1` in `1..=8`)**: `value` is encoded as a canonical minimal-width offset from the previous rung's ceiling (`8`, `264`, `65800`, `16843016`, …).

### 4-Bit `flag` Allocation (`0x0`–`0xF`)

| `flag` | Domain | Rung 1 (`0..=7`) / Rung 2 (`8+`) Assignments |
|---|---|---|
| `0x0` | `Expr::Sort` | `value` = universe table index |
| `0x1` | `Expr::Var` | `value` = de Bruijn index |
| `0x2` | `Expr::Ref` | `value` = refs table index (followed by `TagN(0)` universe list length + indices) |
| `0x3` | `Expr::Rec` | `value` = mutual recursion index (followed by `TagN(0)` universe list) |
| `0x4` | `Expr::Prj` | `value` = struct ref index (followed by `TagN(0)` field index + child expr) |
| `0x5` | `Expr::Str` | `value` = refs table index of UTF-8 blob address |
| `0x6` | `Expr::Nat` | `value` = refs table index of LE-limb blob address |
| `0x7` | `Expr::App` | `value` = telescope application count |
| `0x8` | `Expr::Lam` | `value` = telescope binder count (followed by packed `BinderContract`s) |
| `0x9` | `Expr::All` | `value` = telescope $\forall$-binder count (followed by packed `BinderContract` + `ValueContract`s) |
| `0xA` | `Expr::Let` | `value` = packed `(nonDep, LetKind, BinderContract)` |
| `0xB` | `Expr::Share` | `value` = canonical sharing-table index |
| `0xC` | `Constant::Muts` | `value` = number of mutual constants in the SCC block |
| `0xD` | `Constant` (singleton) | `0`: `Defn`, `1`: `Recr`, `2`: `Axio`, `3`: `Quot`, `4`: `IPrj`, `5`: `CPrj`, `6`: `RPrj`, `7`: `DPrj` |
| `0xE` | **Envelopes, Data & Claims** | `1` (`0xE1`): `Comm` (commitment)<br>`2` (`0xE2`): `AssumptionTree`<br>`3` (`0xE3`): `Claim::Eval`<br>`4` (`0xE4`): `Claim::Check` *(also `.ixe` v4 header — see §5.1)*<br>`5` (`0xE5`): `Claim::CheckEnv` *(also `.ixe` v5 header — see §5.1)*<br>`6` (`0xE6`): `Claim::Reveal`<br>`7` (`0xE7`): `Claim::Contains`<br>`8` (`E8 00`): `Claim::Catalog`<br>`9` (`E8 01`): `Claim::Resource`<br>`10` (`E8 02`): `Claim::Binding`<br>`11` (`E8 03`): `RoleTable` section<br>`12` (`E8 04`): `ElabClaim` (`Text -> Syntax -> Environment`) |
| `0xF` | **`Ixon.Proof` Wrappers** | `0` (`0xF0`): `Eval` proof<br>`1` (`0xF1`): `Check` proof<br>`2` (`0xF2`): `CheckEnv` proof<br>`3` (`0xF3`): `Reveal` proof<br>`4` (`0xF4`): `Contains` proof<br>`5` (`0xF5`): `Catalog` proof<br>`6` (`0xF6`): `Resource` proof<br>`7` (`0xF7`): `Binding` proof |

---

## 3. Container & Store Formats in Detail

### 3.1 `.ixe` Environment & Bundle File ([`crates/ixon/src/serialize.rs`](file:///home/jcb/projects/ix-frontend/crates/ixon/src/serialize.rs))
An `.ixe` file is a 5-section sequential container:
1. **Header**:
   - `0xE4` (legacy v4) or `0xE5` (role-bound v5)
   - `stored_root : [u8; 32]` — canonical binary Merkle root over the sorted constant addresses in §2.
   - `main : Option<Address>` (`0x00` or `0x01 || [u8; 32]`) — set for single-closure value bundles (`ix pack`).
   - `assumptions : Vec<Address>` (`TagN(0)` count + strictly ascending 32-byte addresses).
   - *(v5 `0xE5` only)* `role_binding : (Address, TagN(0) len, E8 03 RoleTable bytes)`.
2. **§1 Blobs**: `TagN(0)` count + `(Address: [u8; 32], TagN(0) len, raw_bytes)`. Verified on load (`blake3(raw_bytes) == Address`).
3. **§2 Constants**: `TagN(0)` count + strictly ascending `(Address: [u8; 32], TagN(0) byte_len, ConstantBytes)`.
   - Length-prefixing each constant allows `Env::parse_lazy_index` and `Env::get_anon_mmap` to index §2 in one pass without parsing expression trees.
4. **§3 Hints**: `TagN(0)` count + delta-coded `(const_idx_delta: TagN(0), fused_reducibility_hint: TagN(0))`.
   - Anonymous readers (`Env::get_anon`, `Env::get_anon_mmap`) **stop immediately after §3** and never read §4 or §5.
5. **§4 Names**: `TagN(0)` count + `(Address: [u8; 32], NameComponents)`. Verified on load (`Name::hash == Address`).
6. **§5 Named Metadata**: `TagN(0)` count + delta-coded `(const_idx_delta: TagN(0), ConstantMeta)` carrying human display names, post-order `ExprMetaArena` diffs, `original` flags, and `KVMap` attributes.

### 3.2 `IxStore`: Native `.ixe` + `.ixidx` Indexing, `.ixpack` Loose Compaction, & 1-Level Shards ([`crates/common/src/store.rs`](file:///home/jcb/projects/ix-frontend/crates/common/src/store.rs))
Because `.ixe` is the circuit's claim source of truth and portable environment bundle (and `.ixc` preserves the composition-order Merkle-inclusion structure across environments), **`IxStore` adapts `.ixidx` directly to `.ixe` files**:
```text
~/.ix/store/
  packs/
    env-<env_root>.ixe      # Hardlinked portable .ixe bundle (circuit source of truth, zero byte copy!)
    env-<env_root>.ixidx    # 256-fanout index pointing directly to §1 (Blobs) and §2 (Constants) windows inside .ixe
    pack-<64-hex>.ixpack    # 8-byte header ("IXPACK01") + 8-byte-aligned compacted loose objects (Claims, Proofs, AssumptionTrees)
    pack-<64-hex>.ixidx     # Companion 256-fanout index for compacted loose objects
  objects/
    00/..ff/                # 256 1-level loose object shards (<62-hex> filenames)
```
- **Zero-Copy `.ixe` & `.ixc` Ingest (`IxStore::ingest_ixe` / `ix store ingest`)**:
  - Given an `.ixe` file (or a `.ixc/` catalog directory of `<label>.ixe` / `<label>.chunk<i>.ixe` files), `IxStore` hardlinks each `.ixe` into `packs/env-<stored_root>.ixe` and scans its §1 (`Blobs`) and §2 (`Constants`) windows in a single pass to emit `packs/env-<stored_root>.ixidx`.
  - Every constant and blob inside the `.ixe` is then served via zero-syscall $O(\log(N/256))$ mmap slices directly out of `env-<stored_root>.ixe`, while `IxStore::env_path(&env_root)` locates the full portable `.ixe` bundle by its Merkle `env_root` in $O(1)$.
- **`.ixidx` Binary Layout**:
  - `0..8`: `b"IXIDX001"`
  - `8..16`: `object_count : u64 LE` ($N$)
  - `16..2064`: `fanout : [u64 LE; 256]` — `fanout[b]` is the cumulative number of objects in the pack whose `Address` has first byte $\le b$.
  - `2064 .. 2064 + 32*N`: `keys : [[u8; 32]; N]` sorted lexicographically.
  - `2064 + 32*N .. 2064 + 48*N`: `entries : [(offset: u64 LE, len: u32 LE, flags: u32 LE); N]` pointing into the companion `.ixe` or `.ixpack` file.

### 3.3 `.ixc/` Catalog Directory ([`crates/ixon/src/catalog.rs`](file:///home/jcb/projects/ix-frontend/crates/ixon/src/catalog.rs))
A `.ixc` is a directory containing `manifest` (`b"IXC\0\0\0\0\0"`) plus member `.ixe` files (`<label>.ixe` in `Fat` profile or `<label>.chunk<i>.ixe` in `Chunked` profile). It preserves the **Merkle-inclusion structure** of environment composition (since composition order determines how Merkle openings are constructed):
- `members_root`: canonical Merkle root over member `.ixe` env roots in composition order.
- `content_root`: canonical Merkle root over the deduplicated union of all members' §2 constant addresses.

### 3.4 `.ixes` Shard Manifest ([`crates/kernel/src/shard.rs`](file:///home/jcb/projects/ix-frontend/crates/kernel/src/shard.rs)) & `.ixprof` Kernel Profile ([`crates/kernel/src/profile.rs`](file:///home/jcb/projects/ix-frontend/crates/kernel/src/profile.rs))
- **`.ixes` (`b"IXES\0\0\0\0"`)**: Produced by `ix shard`, consumed by `ix prove`, `ix verify`, and `ix aggregate`. Encodes the shard partition (owned `blocks`, imported `foreign_blocks`, `assumption_root`), the binary bisection tree for recursive proof aggregation, and optional measured peak RSS per shard.
- **`.ixprof` (`b"IXPROF\0\0"`, v2)**: Produced by `ix profile`, consumed by `ix shard --profile`. Records 80-byte per-block execution cost counters (`heartbeats`, `subst`, `whnf`, `def_eq`, `nat_arith`, `intern`) and the CSR consumer→producer $\delta$-unfolding graph.

---

## 4. Redundancy & Overlap Audit

As the codebase evolved through multiple milestones (v3 → v4 `TagN`, standalone `.ixe` files → `.ixc` catalogs → `IxStore`, `liblean` ingress → pure `Ix.Frontend`), **four concrete redundancies / overlaps** stand out:

### 4.1 Resolved: `.ixidx` Now Indexes `.ixe` Directly (Instead of Duplicating `.ixe` into `.ixpack`)
- **Design**:
  - `.ixe` is the circuit's claim source of truth and portable bundle, and `.ixc` preserves the Merkle-inclusion structure of composed environments.
  - Rather than re-serializing `.ixe` constants and blobs into a separate `.ixpack` container, `IxStore::ingest_ixe` hardlinks `<stem>.ixe` into `packs/env-<stored_root>.ixe` and writes a companion `env-<stored_root>.ixidx` index directly over the `.ixe`'s §1 (`Blobs`) and §2 (`Constants`) byte windows.
  - `.ixpack` (`IXPACK01`) is reserved solely for compacting standalone loose store objects (`Claim`, `Ixon.Proof`, `AssumptionTree`) via `ix store compact`.

### 4.2 Overlap 2: `IXHC` (`Ix.HostAdmission.Statement`) vs. `Ix.Claim` (`0xE5 CheckEnv` + `E8 02 Binding`)
- **Current state**:
  - [`Ix/HostAdmission/Codec.lean`](file:///home/jcb/projects/ix-frontend/Ix/HostAdmission/Codec.lean) defines a standalone fixed-width binary format with magic `b"IXHC"` committing to `(kind, hostSpecDigest, bindingHash, contentRoot, main, policy)` for `ix check-lean` / `ix verify-host`.
  - [`Ix/Claim.lean`](file:///home/jcb/projects/ix-frontend/Ix/Claim.lean) defines `Claim.checkEnv` (`0xE5`) and `Claim.binding` (`E8 02`) using `TagN`, committing to `(ClaimContext { spec, binding }, envRoot, assumptions)`.
- **Recommendation**:
  - `IXHC` is semantically a `CheckEnv` claim with an optional `tiered (logicalRoot, tierRoot)` split and `main` pointer. Folding `IXHC` into a `TagN(4, 0xE, ...)` claim variant (or unifying `HostAdmission.Statement` with `Ix.Claim`) eliminates a parallel codec and unifies `ix verify` and `ix verify-host`.

### 4.3 Overlap 3: `.ixon` Text Format vs. `.ix` Surface Language (`Ix.Frontend.Format`)
- **Current state**:
  - `.ixon` ([`Ix/IxonSyntax.lean`](file:///home/jcb/projects/ix-frontend/Ix/IxonSyntax.lean), [`crates/ixon/src/syntax/`](file:///home/jcb/projects/ix-frontend/crates/ixon/src/syntax/mod.rs)) is a parallel parser and pretty-printer (~3,000 LoC across Lean and Rust) for a simplified Lean-like syntax over `Ix.Expr`.
  - `.ix` ([`Ix/Frontend/Parser/`](file:///home/jcb/projects/ix-frontend/Ix/Frontend/Parser/Module.lean), [`Ix/Frontend/Format.lean`](file:///home/jcb/projects/ix-frontend/Ix/Frontend/Format.lean)) is the full, pure, certified surface language supporting `#<hash>` pins, `map Name := #<hash>`, substructural contracts (`0`, `1`, `&`, `!`, `~`, `let borrow`), inductives, structures, typeclasses, and tactics.
- **Recommendation**:
  - Make `.ix` (`Ix.Frontend.Format`) the canonical human-readable decompilation target for `ix decompile`, deprecating `.ixon` as a separate user-facing file format.

### 4.4 Overlap 4: First-Byte Collision in `TagN(4, 0xE, ...)` Between `.ixe` Envelopes (`0xE4`, `0xE5`) and Claims (`0xE4`, `0xE5`)
- **Current state**:
  - `.ixe` envelope v4 begins with byte `0xE4`, which is identical to `Claim::Check` (`TagN(4, 0xE, 4)` = `0xE4`).
  - `.ixe` envelope v5 begins with byte `0xE5`, which is identical to `Claim::CheckEnv` (`TagN(4, 0xE, 5)` = `0xE5`).
  - While `.ixe` files are currently not written into `IxStore` as untyped objects (whereas `Claim`s are), any tool or store inspector that sniffs object types from the leading `TagN(4)` tag cannot distinguish a v5 `.ixe` header from a `CheckEnv` claim by the tag alone.
  - *(Fixed in `970388f0f`+)*: `ElabClaim` previously used variant `11` (`E8 03`), which collided with `RoleTable` (`E8 03`). `ElabClaim` is now assigned variant `12` (`E8 04`).
- **Recommendation**:
  - When bumping the `.ixe` envelope version (or adopting thin `.ixe` manifests), prefix `.ixe` files with an explicit 8-byte magic (`b"IXENV005"`) like `.ixpack` (`IXPACK01`), `.ixc` (`IXC\0\0\0\0\0`), `.ixes` (`IXES\0\0\0\0`), and `.ixprof` (`IXPROF\0\0`), reserving `TagN` `0x0..0xF` strictly for content-addressed `IxStore` objects (`Expr`, `Constant`, `Comm`, `AssumptionTree`, `Claim`, `RoleTable`, `Proof`).

### 4.5 Overlap 5: Duplicate Cache-Hint Implementations (`shard-proofs` vs. `aggregate`)
- **Current state**:
  - [`Ix/Cli/ShardProofIndex.lean`](file:///home/jcb/projects/ix-frontend/Ix/Cli/ShardProofIndex.lean) implements `~/.ix/cache/shard-proofs/<digest> -> <addr>\n` in Lean.
  - [`crates/ffi/src/aiur/aggregate/store.rs`](file:///home/jcb/projects/ix-frontend/crates/ffi/src/aiur/aggregate/store.rs) implements `~/.ix/cache/aggregate/<key> -> <addr>\n` in Rust.
- **Recommendation**:
  - Expose `read_cache_hint(namespace, key)` and `write_cache_hint(namespace, key, addr)` directly on `ix_common::store::IxStore` and `Ix/Store.lean` so all cache namespaces share atomic temp-rename and path resolution.
