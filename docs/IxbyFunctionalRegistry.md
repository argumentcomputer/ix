# Source-bound declaration and header registries

`flock-stage3/host/src/ixby/ixbf_decode/registry/` materializes constructor
declarations, function headers and owned block headers from the actual
[original-wire dispatcher](IxbyFunctionalDispatch.md). Insertion addresses
come from carried grammar counters. Completion checks exact coverage, full
constructor-identity uniqueness and every function's entry frame. Typed reads
select only present records and retain their original header spans.

This is a bounded declaration/header component, **not whole-program semantic
admission or an Exec profile**. It does not register instruction bodies, check
all their references/alternative semantics, or construct typed value arenas.
The caller must authenticate the dispatcher's exact requests to one expected
original file. The test proof below supplies that link for a small-file class;
the component alone is not a source-authentication oracle.

Existing decoder/dispatcher relations, Exec factories, keys, proof envelopes,
Flock revision, compression backends and security settings are unchanged. A
test-only dispatcher helper reuses its existing AST-free model to compute
independently expected final grammar words; it changes no production table.

## Physical bank and typed records

`RegistryCapacity::new(C, F, B)` admits zero through four constructors, one
through four functions and one through eight blocks per function. These are
separate component capacities, not an increase to any native Exec limit.
The dense bank has `7*C + 5*F + 4*F*B` F128 words, at most 176 words. Replicating
it at every step is a small-class prototype, not a scalable Init registry.

| Record | Stored words after presence | Physical ownership |
| --- | --- | --- |
| Constructor | block digest limbs 0/1, member, tag, field count, header range | declaration index |
| Function | arity, entry block, block count, header range | function index |
| Block | local count, instruction tag, header range | function index and block index |

Presence is exactly zero or one. Every absent cell is entirely zero. Header
ranges have exact u64 start/end lanes and are nonempty for present records.
They cover the decoded header, **not the entire function or block body**.
Instruction tags retain all their bits and must be below eight. Function
block counts are positive and fit the physical capacity; entry indices must
be below those counts.

All declaration metadata remains exact u128. Constructor identity includes
the full 256-bit block digest plus full 128-bit member and tag values. Low-lane
comparison is insufficient, and changing only field count never makes a
duplicate identity distinct. Physical registry capacity does not replace
the artifact's declared operand/local or other semantic limits.

## State-selected insertion and completion

`ProgramRegistrySlots` owns a Program dispatcher and five setup-owned registry
tables. Its private state type couples the dispatcher state, full bank and
physical capacity. Initialization creates the genuine zero-offset Program
state with zero context and an entirely zero bank.

Every `step` calls the actual dispatcher, then consumes its committed flag,
tag, fields and next cursor with the same old grammar state. It takes no
decoded table, insertion index, host event schedule or acceptance bit.

- Constructor index is `constructors - constructors_left`.
- Function index is the next-function index, also checked against
  `functions - functions_left` at the header.
- A block belongs to `next_function_index - 1`, with block index
  `blocks - blocks_left`.

These are checked full-width integer operations. Header events must select
exactly one physical cell. An insertion requires an empty destination,
previous-prefix coverage and source ordering. Block insertion also requires
its actual function header, matching block count and arity, and an in-range
owned block index. Every untouched bank word is carried, not supplied again
as independent advice.

The committed flag is one for ordinary events and zero for Done padding;
String chunks may remain uncommitted. Only constructor/function/block header
events insert a cell. Scalar, operand, instruction-body, intermediate UTF-8
and padding events preserve the bank while still passing the full decoder
and grammar relation.

`finish` first requires the dispatcher's real Done/EOF and finished UTF-8 state,
then binds the entire registry to that final grammar:

- Presence matches the exact constructor/function counts and every function's
  complete block count. Missing, extra and absent-owner records reject.
- Every header span ends within the same file, and arities/local counts respect
  their actual declared limits.
- Every function's entry block exists and has exactly its arity as the local
  count. Program-entry arity matches the actual stored entry function.
- Every pair of live constructor declarations has a distinct full identity.

The returned `FinishedProgramRegistry` is not a whole-image admission
certificate. It exposes the actual final grammar/context and supports typed
constructor/function/block reads. Each read uses full u128 indices, derives
its selectors in the constraint system, and requires a present record with
the specified owner. Disabled reads require zero indices and return zero.
Unused result fields are zero; the range is the stored original header range.
The later [instruction/reference wrapper](IxbyFunctionalReferences.md) consumes
these wires for every actual Program event, including forward references,
arity/frame checks and duplicate alternatives. Typed value/transport consumers
remain to be connected.

Input constants and validity residuals use separate verifier-owned zero wires.
Residual outputs are never recycled as initial bank/context inputs; that would
create a producer/consumer cycle. Both sets of fixed values are reconstructed
from setup. No native acceptance callback discharges a residual.

## Tables and proof-free emission

All five operations have distinct setup-owned schemas. At `(C,F,B)=(2,2,2)`,
the bank has 40 words:

| Table | Input words | Output words | `k_log` / used columns |
| --- | ---: | ---: | --- |
| Capture | 84 | 41 | 17 / 60,984 |
| Finish | 68 | 1 | 17 / 35,211 |
| Constructor read | 43 | 7 | 17 / 19,909 |
| Function read | 43 | 7 | 17 / 19,141 |
| Block read | 43 | 7 | 17 / 19,918 |

Each table's last output is its validity residual. Capture inputs are the old
28-word grammar, committed flag, tag, thirteen event fields, next cursor, and
old bank. Finish takes the actual final grammar and bank. Read inputs are
enable, index, owner, and bank; outputs are five zero-padded fields, range,
and residual. Non-block reads require a zero owner.

The row domain is explicitly bounded from three through twenty. Count-only
emission builds no Boolean plan and evaluates no witness. Tests compare actual
count/schema/shape layouts and check every output bit, unused column, constant
stripe and poisoned/recycled padding buffer.

## Small-file proof statement

The test-only class fixes a 1,024-byte private buffer, 32 dispatcher/capture
steps, 4,096 physical Nat bits, and `(C,F,B)=(2,2,2)`. It uses thirty-five tables,
row domain `nu=7`, the existing legacy BLAKE3 implementation, and pinned
`Fast128` with `M=25`. Each source window reads the same buffer wires; the whole
buffer is hashed once using seventeen compression rows.

There are 72 private input words: narrow file length, 64 byte-buffer words,
and seven query words. The 55 externally expected public words are:

- two raw file-digest limbs;
- the complete final 28-word grammar state;
- constructor enable/index, function enable/index, and block enable/owner/index;
- the three six-word read results, including their exact header ranges.

Queries are externally expected lookup parameters, not a replacement for
instruction/reference semantics or application approval. The bank is derived
and checked inside the relation, not admitted by a host lookup. The raw file
digest is still **not** the Exec commitment chain.

Envelope `IXFREG00` requires revision zero, canonical fixed-integer
little-endian encoding, no trailing bytes and at most 8 MiB. Its distinct domain
is `ix:ixby:ixbf-program-registry:bytes1024:steps32:nat4096:c2:f2:b2:v0`.
There is no fallback to a dispatcher, component or Exec envelope.

Fresh verifier children clear their environment, run outside the worktree and
receive only expected public words and proof through stdin. They rebuild the
approved setup; they receive no source files, ASTs, registries, decoder results
or native-execution advice, and run no native parser/hash/admission predicate
to verify.

## Verification evidence

Eight honest proofs verify under one exact setup. Independently encoded
original-wire fixtures cover empty/nonempty constructor tables, two functions
with different block owners, nonzero entry blocks, unused blocks, changed
identities/arities, a forward-declared callee, a 512-byte split-UTF-8 string,
a 4,096-bit Nat, and full-width metadata. The wide fixture has `2^100`
arity/locals and u128-max constructor metadata under matching declared limits;
it proves header registration, not execution of such a frame. All fixtures
also pass the independent native IXBF loader and exact re-encoding.

Every complete serialized proof is 403,052 bytes, excluding independently
expected public data. Seven forged proofs recompute locally valid rows for:

1. A substituted decoded constructor field count.
2. A changed grammar insertion ordinal with a fabricated previous declaration.
3. A substituted registry word in a Done carry row.
4. Changed unused final-state fuel metadata.
5. A substituted unselected registry entry in a function read.
6. A different valid block-read index.
7. A substituted buffer byte outside the current source window.

Fresh verification rejects every forgery at `Wiring`. The fourth, fifth and
seventh attacks preserve all local outputs. Registry attacks additionally
check the recomputed Boolean row against its actual R1CS before proving.
Changed digest/state/query/result/range words, the old dispatcher domain, bad
magic/revision, truncation, trailing bytes and wrong public width also reject.

Eight ordinary tests cover independent integer/Boolean agreement for all 256
control bytes, high/reserved bits and underflows; every constructor-identity
bit; append/ownership/coverage and entry-frame failures; full-width read indices;
every presence/padding/output bit; and lazy count/emission and data-independent
whole-source layouts. The complete circuit rejects grammar-valid duplicate
constructors and wrong entry frames, plus separately labeled physical-capacity
and query failures. The capacity fixtures remain valid to the native loader:
they demonstrate a bounded class, not a change to wire semantics.

The ordinary run passes eight tests (one proof test opt-in) in 11.68 seconds
in the body, 26.17 seconds wall including compilation, with 2,735,764 KiB
maximum RSS. The isolated-verifier proof run passes in 99.66 seconds in the
body, 100.16 seconds wall, with 5,483,916 KiB maximum RSS. It uses four Rayon
workers, a 32 GiB virtual-address cap and a 600-second timeout. Workspace
regressions overlapped this run; these are per-command regression measurements,
not exclusive-host or single-proof timings, nor combined simultaneous memory.
Local evidence is retained in `/tmp/ixby-registry.BDGnDV/`.

Full release workspace regressions pass 231 Stage 3 tests (39 opt-in) and
266 Stage 4 tests (39 opt-in). Both workspaces pass formatting and release
Clippy on all targets with warnings denied. Stage 3 takes 358.93 seconds in
the body, 359.40 seconds wall, with 11,178,100 KiB maximum RSS. Stage 4 takes
169.68 seconds wall including compilation, with 1,145,116 KiB maximum RSS.

The complete combined codec regression passes all eighteen opt-in tests:
74 honest proofs verify and 58 forged proofs reject at wiring, including the
previous seventeen tests and the new registry proof test. Existing original
compiler-corpus and full-Init row differentials also pass; the new registry
does not extend its physical capacity to those large files. The combined run
takes 438.39 seconds in the body, 438.88 seconds wall, with 5,574,628 KiB
maximum RSS under the unchanged 32 GiB cap and a 900-second timeout. It overlaps
the workspace runs for part of its duration. These are regression measurements,
not isolated performance improvements over earlier checkpoints. All jobs
completed successfully.

```sh
RAYON_NUM_THREADS=4 cargo test --release --locked \
  --manifest-path flock-stage3/Cargo.toml -p ixby-flock \
  ixby::ixbf_decode::registry:: -- --test-threads=1
RAYON_NUM_THREADS=4 cargo test --release --locked \
  --manifest-path flock-stage3/Cargo.toml -p ixby-flock \
  ixby::ixbf_decode::registry::proof_tests:: -- --ignored --nocapture --test-threads=1
```

## Remaining work

The [instruction/reference layer](IxbyFunctionalReferences.md) now connects
actual typed reads to all Program reference/arity and successor-frame checks
and rejects duplicate alternatives. The [typed value layer](IxbyFunctionalValues.md)
now connects constructor values/PAP captures to that checked program, derives
bounded forest ownership/order/depth and complete subtree spans, and supplies
typed reads. Executable body records and their spans remain unfinished;
native loader depth/allocation obligations for larger classes are not
discharged by these bounded records.

Larger files still require shared chunk authentication and scalable registry
access; this dense bank and small-file setup cannot admit the full Init image.
The raw-file/Exec commitment bridge, streaming execution witnesses, scalable
authenticated code/memory, actual VM-derived global fuel, complete state
segments and sound composition remain separate gates. Source/image/ABI and
native constraint-to-reference refinement, the full pinned Init proof and
terminal compression are not claimed. See the [scaling plan](IxbyStage3ScalePlan.md).
