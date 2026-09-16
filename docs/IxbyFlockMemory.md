# Authenticated cells and batched execution memory

The Stage 3 backend now has constrained mutable 32-byte cells, immutable
allocation, and an exact batched read/write relation. Real Flock component
proofs verify in fresh processes. These components will supply execution
memory; full instruction, allocation and program-admission consumers
still need integration into the segmented execution relation.
The [paged frame component](IxbyFlockPagedExecution.md) now consumes these
memory wires for frame and continuation transitions, with separate real proof
tests covering their joint wiring and fuel accounting.

## Cell authentication and allocation

[`auth_memory`](../flock-stage3/host/src/ixby/auth_memory/mod.rs) admits a
setup-owned tree depth from zero through 64. Addresses are checked as full
u64 integers. A cell is two F128 words. Leaves hash the 32-byte zero-padded
`IxBy/memory/cell/v0` domain followed by the cell; internal nodes use the fixed
BLAKE3 parent/root compression. Direction, level, address, compression flags
and counter are constrained. A replacement authenticates the old value before
computing the new root with the same address and sibling path.

Sparse native storage generates advice only. The verifier never consults that
storage or accepts a native memory verdict. Clearing a cell to zero restores
the corresponding empty-tree nodes.

The immutable arena carries two root words and a full u64 allocation count.
Allocation uses exactly that count as its address, authenticates an old zero
cell, and increments without wrap. Reads require an index strictly below the
allocated prefix. All three words must be bound at segment boundaries. At
depth 64, the u64 counter deliberately prevents an allocation whose resulting
count would be 2^64.

## Exact batched read/write relation

[`memory_log`](../flock-stage3/host/src/ixby/memory_log/mod.rs) authenticates
each distinct touched address once per batch. It connects the initial root
to a sequence of checked old/new cell replacements. Those actual old and final
value wires become seed and seal records in the access log.

Each machine access supplies its actual address, Boolean write flag and
two-word value. The circuit assigns time from its position in the access
list. A constrained switch chooses read or write; it cannot manufacture a
seed, seal or padding record. Seeds use time zero and seals use `u64::MAX`.

A setup-owned switching network permutes entire five-word records. Its
stages pair lanes at distances `1,2,...,N/2,...,2,1`. Each selector satisfies
`s²=s`; the two outputs are `x+s(x+y)` and `y+s(x+y)` for every record word.
Sixteen switches share a native element-table row. Thus records cannot be
created, dropped or assembled from different accesses. Routing bits are
untrusted advice; the graph and table are fixed before any witness exists.

The Boolean audit checks the resulting sequence:

- Addresses increase between groups; times strictly increase within a group.
- Every address begins with one seed and ends with one seal.
- Reads and seals preserve the preceding value; writes supply a new value.
- Every address has an authenticated boundary opening. Duplicate boundary
  addresses and unbacked accesses reject.
- Padding is canonical, appears only after all real addresses are sealed,
  and cannot be followed by another real record.

Unused switches, rows and columns use checked zero padding. A reused witness
buffer is fully overwritten. This construction uses exact routing and direct
Flock constraints; it introduces no separate randomized RAM protocol.

## Verification evidence

| Component class | Honest proofs | Complete bundle bytes |
| --- | ---: | ---: |
| Mutable cells, depth 16, three writes and one read | 3 | 205,963 |
| Immutable arena, depth 16, three allocations and one read | 1 | 206,083 |
| Batched memory, depth 16, ten accesses and four boundary cells | 3 | 270,123 |
| Batched memory, depth 40, 512 accesses and 32 boundary cells | 1 | 341,619 |

Fresh verifiers run outside the worktree with cleared environments and receive
only expected public words and proof bytes. The conformance tests reject every
changed expected word, invalid envelopes, truncation and trailing bytes.
Seventeen fully recomputed attacks preserve the modified local table relations
but reject at Flock's wiring check: seven cell/path/hash attacks, four immutable
allocation attacks and six batched routing/order/value/boundary attacks.

Ordinary checks include bit-63 addresses, exact counter overflow/read bounds,
restoration of empty roots, every permutation through eight records, sampled
routes through 16,384 records, whole-record output mutations, non-Boolean
selectors, poisoned padding, and count/emit parity. Native hashing is checked
against separately implemented constrained BLAKE3 compression.

### Measured 512-access batch

This class uses 32 distinct cells in a depth-40 tree, 1,024 audit records,
640 packed switch rows and 2,624 BLAKE3 compressions. The row domain has 12
variables and the dense commitment has 27. It uses the pinned Fast128 profile.

| Measurement | Result |
| --- | ---: |
| Setup compilation | 2.312 s |
| Native advice and circuit witness | 21.521 ms |
| Proving | 417.425 ms |
| Fresh verifier setup | 2.507 s |
| Verification after setup | 27.903 ms |
| Full test process wall time | 5.65 s |
| GNU-time maximum process RSS | 1,785,804 KiB |

The measured executable ran with four Rayon threads and a 32 GiB virtual
address cap. Compilation is excluded. The RSS field is a process maximum,
not a sum of parent and verifier memory. This is a synthetic memory workload,
not a CSLib execution segment or an estimate of the full proving cost.

Proof-free censuses also cover 128–8,192 accesses, 16–128 touched cells and
depths 16, 40 and 64. Their dense domains range from 24 to 31 variables, within
the pinned configurations. Those larger counts alone are not proving or
peak-memory measurements.

## Shared tree authentication

[`auth_memory::multi`](../flock-stage3/host/src/ixby/auth_memory/multi/mod.rs)
authenticates all boundary cells through one shared tree. Leaves use the same
domain-separated cell hash as the original memory. Each internal node hashes
its actual old and new children. An unchanged sibling subtree contributes one
private frontier digest, used identically on both sides.

An exact permutation connects complete six-word node records: presence,
`(level, index)`, old digest and new digest. Its supplied records are the
leaves, frontier and parent outputs. Its requested records are every parent's
two children and one externally expected root pair. Levels decrease by one
at every child edge; indices become `2*i` and `2*i+1`. Every supplied node
must therefore connect to that single root. There can be no disconnected
cycle, orphan, duplicate branch or substituted address. The cryptographic
leaf/parent checks bind the values; frontier nodes cannot change between
the two roots.

The setup fixes `L` leaves and at most `P` internal nodes. It reserves
`P+1-L` frontier slots. Unused internal/frontier records are canonical zero.
Directed equality gates compare the routed records with actual child/root
wires without introducing cycles in the circuit graph. The existing exact
memory audit uses the same leaf address and old/new value wires.

Two genuine proofs verify in fresh processes:

| Depth-40 class | Actual parents / capacity | Compressions | Proof bytes | Setup | Prove |
| --- | ---: | ---: | ---: | ---: | ---: |
| Three cells | 41 / 48 | 102 | 296,723 | 1.896 s | 0.259 s |
| 96 clustered cells | 162 / 192 | 576 | 380,771 | 2.310 s | 0.313 s |

The 96-cell class uses `M=25` and 220,546 dense field words. Separate paths
would require 7,872 compressions for those 96 cells. The measurements use
four Rayon threads; another execution proof test ran concurrently. Both
memory tests, fresh receivers and attacks completed in 11.90 seconds, with
1,627,100 KiB maximum process RSS under a 32 GiB virtual-memory cap.

Every expected-word change and malformed envelope rejects. Eleven locally
valid recomputed attacks against leaf addresses, parent positions/levels,
children, parent/frontier digests, record equality, routing, cell hashes,
compression flags and inactive-node activation reject at Flock's wiring
check. Ordinary tests check every output bit and recycled padding, compare
simultaneous updates with sequential roots/openings, and cover empty updates,
depth-zero root leaves and complete depth-64 paths.

`MemoryBatch::finish_shared` generates the native simultaneous-update advice.
The fixed and timed memory-log APIs expose this path alongside their original
single-cell-path APIs. Callers must use the same actual leaf wires for both
tree authentication and the ordered access audit.

## Reproduce

```sh
RUSTFLAGS='-C target-cpu=native' RAYON_NUM_THREADS=4 cargo test --release \
  --offline --manifest-path flock-stage3/Cargo.toml auth_memory::multi:: \
  -- --ignored --nocapture --test-threads=1
cargo test --release --locked --manifest-path flock-stage3/Cargo.toml \
  --workspace auth_memory -- --test-threads=1
cargo test --release --locked --manifest-path flock-stage3/Cargo.toml \
  --workspace memory_log -- --test-threads=1

RAYON_NUM_THREADS=4 cargo test --release --locked \
  --manifest-path flock-stage3/Cargo.toml auth_memory::proof_tests:: \
  -- --ignored --nocapture --test-threads=1
RAYON_NUM_THREADS=4 cargo test --release --locked \
  --manifest-path flock-stage3/Cargo.toml memory_log::proof_tests:: \
  -- --ignored --nocapture --test-threads=1
cargo test --release --locked --manifest-path flock-stage3/Cargo.toml \
  memory_batch_census -- --ignored --nocapture --test-threads=1
```

The primitive cell, arena and log envelopes use distinct component identities
(`IXFMEM00`, `IXFARN00`, `IXFLOG00`). They are not accepted as Exec bundles.
Their roots and actual access wires still need to be connected to the complete
execution state, admitted code/input and global fuel ledger. See the
[remaining execution work](IxbyStage3ScalePlan.md).
