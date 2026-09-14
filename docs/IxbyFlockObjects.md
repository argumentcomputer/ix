# Immutable constructor execution in Flock

The explicit native object setup implements bounded constructor inputs,
construction, projection, `caseCtor`, and canonical tree output, composed with
all 35 crypto-v0 primitives and first-order CEK control. Twenty-one execution
proofs verify under one setup. This is not yet native constraint-to-reference
refinement, a compiled Stage 2 guest, or a terminal SNARK. Closure/PAP support is
an explicit separate [application setup](IxbyFlockApplications.md), not a
change to this constructor-only factory.
This v0 factory still rejects [Nat revision 1](IxbyNat.md). The separate
[Nat factory](IxbyFlockNats.md) composes exact Nats with these constructors
under an explicit implementation/key upgrade; it does not change this setup.

## Setup and representation

`compile_exec_object_profile(profile, machineCapacity, byteCapacity,
objectCapacity, primitives, backend)` receives only verifier-owned setup, not
guest code, input, proof, trace, or Stage 2 keys. `SemanticProfile::objects`
uses the unchanged crypto-v0 envelope with explicit constructor/node/depth
bounds. Its separate implementation/capacity/circuit identities and
`ix:ixby:object-exec:v0` transcript prevent replay under byte-only or scalar keys.

Physical constructor cells have tag 7 and a canonical u32 arena index. These
are not external ABI pointers. Every record has a declaration-table index,
field count, presence bit, and ordered typed field cells. The program decoder
derives the complete 256-bit block ID, u32 member and u32 tag from authenticated
bytes, rejects duplicate identities, and derives all case tables. Whole-image
admission includes unused declarations and unreachable instructions.

Input trees use setup-fixed preorder slots. The decoder checks exact IDs,
declared arities, shared forest node limits, and depth without resetting budgets
at siblings. Child indices are derived from the fixed finite traversal, never
advised. Each execution step owns one future-zero allocation slot; construction
can refer only to already available records. Existing records are immutable.
Byte records use their separate authenticated arena.

Projection constrains the selected record and field; projection of Erased
returns Erased for any canonical u32 field index. Constructor cases match the
admitted declaration, select an admitted alternative, and append the exact
fields in their original order. Calls and saved frames transport these handles
without changing the underlying records. Case control is normalized into the
existing ordered-frame update only after this constrained resolution.

Output is a constrained finite preorder traversal, not supplied serialization.
Sharing is expanded into repeated inline values; it still consumes the full
external node budget. Cycles, bad/dangling records, noncanonical cells/bytes,
depth overflow, and oversized output reject. Producer wiring authenticates
the arenas; a read component alone does not revalidate every unselected record.

## Evidence and bounds

The proof fixture fixes program/input/output byte capacities 256/192/192,
2 functions, 3 blocks per function, 4 locals, 2 operands, 2 continuations,
2 input roots, 8 transitions, 33 bytes per byte scalar, 2 constructor
declarations, depth 3 and 7 external nodes. Its census is `nu=12`, `m=24`,
37 tables, largest inner exponent 22. Setup identity:

```text
fe8b3a81a2a549ced09a52a9b53db2bcf2e18c3b521ab78cd3f1848343e9d8ff
```

All 21 executions produced 301,091-byte Flock proof envelopes. They include
empty/nonempty and shared/nested objects, mixed byte/word/extension fields,
construction followed by projection/case, both case outcomes, direct/tail
calls, saved caller objects, projected-byte hashing, changed full declaration
identities, and zero/one/two-node tail-recursive walks.

Fresh verifier processes received only approved setup, externally expected
statement digest, and proof. Two locally valid, fully recomputed object-row
forgeries changed an operand or substituted a different declaration; both
rejected with `Wiring(Gkr(ProductMismatch))`. Wrong outputs, proof mutations,
and cross-capacity/byte-only replay reject, including renamed proof headers.

On the local 2026-09-13 run, the complete 21-case plus two-forgery test took
290.53 seconds; proofs took 3.57–3.83 seconds and fresh verification
7.95–8.29 seconds each. GNU time reported maximum RSS 27,306,712 KiB
(about 26.04 GiB), not an aggregate concurrent-process peak. The run used four
Rayon threads, a 64 GiB virtual-address limit and a 1,800-second timeout.
These are diagnostic measurements, not production or maximum-profile sizing.
The previous 32 GiB virtual-address budget was insufficient even though RSS
was lower; virtual reservations and physical resident memory are different.

Twelve focused ordinary component tests check actual Boolean R1CS satisfaction:
four dispatch tests, three input tests, two program tests, and three output
tests. They cover all 320 constructor-ID bits, malformed code/values, exact
record order, shared budgets, cycles, output mutations, and recycled padding.
`Tests/Ixby/Flock/Objects.lean` adds 14 pure reference checks and two shared
whole-statement goldens. Its construction/case/return/halt trace is
kernel-checked using the extended `Resolves.reference` and `Step.reference`.
None of these tests supplies the missing native-matrix refinement theorem.

```sh
cargo test --release --locked --manifest-path flock-stage3/Cargo.toml --workspace
RAYON_NUM_THREADS=4 prlimit --as=68719476736 --core=0 -- \
  timeout 900 cargo test --release --locked --manifest-path flock-stage3/Cargo.toml \
  -p ixby-flock ixby::exec::object_tests:: -- --ignored --test-threads=1
lake test -- ixby-flock-objects
```

The factories remain small selector/unrolling prototypes: 1–4 constructor
declarations, depth 1–3, 1–32 external nodes, at most 64 expanded input slots
and 128 arena entries. Increasing these bounds is not evidence that the
multi-megabyte Stage 2 guest can be proved. Scalable code/byte/heap access,
guest capacity measurement, formal refinement, and terminal sizing for the
upgraded setup are still required.
