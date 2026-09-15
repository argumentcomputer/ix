# State-selected original-wire dispatch

`flock-stage3/host/src/ixby/ixbf_decode/dispatch/` connects the existing
header, thirteen record decoders, canonical naturals, guest Nat limits,
payload cursors, strict UTF-8 and complete grammar control in a fixed circuit
topology. Decoder selection and byte requests come from the carried state.
No host AST, event schedule, natural byte length or acceptance bit selects a
row's decoder.

The test-only whole-grammar proof class authenticates one private 1,024-byte
buffer once, then reuses those same byte wires for every read. This establishes
source-bound, complete wire-grammar/scalar checking for an explicit small-file
class. It is **not** the native loader's full semantic admission, an Exec
profile, a scalable Init parser proof, or an execution proof.

No existing codec relation, Exec factory, key, proof decoder, capacity, Flock
pin, compression backend or security setting changes. The only change to the
existing source gate is a test-only input accessor for malicious-witness tests.

## Component contract

`DispatchConfig` fixes the grammar kind (Program/Input/Output) and the
physical Nat capacity, from zero through 4,096 bits. The byte-window width is
`max(272, 16 * natural.encoded_words())`, hence 592 bytes at the largest class.
Metadata remains exact u128; file cursors and payload extents use checked u64
lanes. Physical Nat capacity does not replace the program's declared Nat limit.

`DispatchState` contains all 28 grammar words plus a streaming UTF-8 cursor
and remaining-length/DFA word. Every state word is connected between steps.
`initialize` creates the genuine zero-offset Start state. Program context
must be zero; transport context contains the constructor/function counts,
ten limits, entry, entry arity and fuel. Transport callers must bind that
context to an admitted program or an explicitly expected public statement.
Private copies of program metadata are not registry authentication.

Every `step` emits the same sequence:

1. Derive event tag, exact bounds, read cursor/take and payload controls from
   the actual carried grammar/UTF-8 state.
2. Read the requested source bytes. The caller supplies an authenticated
   reader; its returned file-length wire is also connected to the request.
3. Derive one-hot enables and route masked inputs to **all** record/scalar
   decoders. Inactive records get zero bounds/lookahead. The header receives
   either its actual prefix or one canonical setup-owned dummy header.
4. Derive the first Nat terminator and mask the exact encoded prefix, then
   check canonicality, the magnitude and the actual guest bit limit. Check
   payload extents and one UTF-8 chunk using their real decoder outputs.
5. Merge the selected decoder fields/cursor into the grammar relation.
6. Commit the new grammar state, or carry an unfinished string's UTF-8 state
   without advancing the grammar.

The source reader must authenticate these exact request wires to one fixed
expected artifact. An arbitrary callback returning host-selected words would
not establish source identity. `SourceReadSlots` can implement that contract
for larger files, but its repeated per-read authentication is not a scalable
integration. The small-file proof uses the separately constrained shared
buffer described below.

### Streaming strings and materialization

The grammar's full payload transition is checked speculatively on each string
chunk, using the original payload start and checked end. While UTF-8 bytes
remain, the finisher preserves **all** old grammar words and carries only the
actual UTF-8 outputs. The final chunk must have zero remaining bytes, a complete
DFA, and an end cursor equal to the checked whole-payload end before the
grammar can advance. A later malformed byte cannot be skipped by accepting an
earlier chunk. Empty strings/byte arrays finish at their count event and need
no zero-progress payload event.

The returned `DispatchStepWires` expose actual tag, bounds, fields, source
cursor, next cursor, Nat magnitude and payload spans. `committed` is zero for
intermediate string steps and Done padding. Consumers must use that flag when
materializing events; speculative string rows are not extra values. The later
[registry layer](IxbyFunctionalRegistry.md) materializes bounded constructor
declarations, function headers and owned block headers from these actual events.
Complete instruction/reference checks and typed value arenas remain separate.

`finish` separately pins both streaming words to zero and emits an explicit
Done grammar row. That row requires genuine terminal phase, exact EOF and
exhausted obligations. A fixed step budget is an admission bound, not permission
to omit the end of a file.

## New control tables

All six operations are setup-owned `DispatchGate` variants with distinct I/O
schemas. Every output bit, including each validity residual, is constrained.
The slot wrapper pins residuals to verifier-owned zero. At 4,096 Nat bits:

| Operation | Input words | Output words | `k_log` / used columns |
| --- | ---: | ---: | --- |
| Initialize | 16 | 31 | 13 / 8,009 Program; 6,086 transports |
| Request | 30 | 10 | 15 / 22,524 Program; 22,535 transports |
| Route | 46 | 194 | 16 / 55,589 |
| Natural lookahead | 38 | 39 | 15 / 21,186 |
| Merge | 110 | 15 | 15 / 32,164 |
| Finish | 62 | 32 | 15 / 20,080 |

The row domain is explicit, from 3 through 20. Each step emits two rows to the
shared payload-cursor table; the grammar table also needs the final Done row.
Count-only emission does not evaluate a witness or build the control plans.
Every driver overwrites recycled padding and constant columns.

## Small-file proof statement

The private conformance class fixes 1,024 physical bytes, 32 dispatcher steps,
4,096 physical Nat bits, a seven-bit row domain and the existing legacy BLAKE3
compression backend. It uses thirty tables and `Fast128` with `M=25`.

The private input has only 80 words: narrow file length, 64 original byte
words and 15 context words. The existing `BoundedBlake3` checks length and
zero padding and hashes the whole prefix **once**. Its 17 compression rows
are shared by all 32 requests, not repeated for each decoder. Each depth-zero
source-window row reads that same authenticated buffer and derives its
offset/take/EOF mask from the dispatch request.

Externally expected variable public data has 45 words: the raw file digest
(two), the transport context (15, all zero for Program), and the complete final
grammar state (28). Fixed public positions are reconstructed from the setup's
layout; they are not supplied as prover advice. This public ABI does not claim
an authenticated decoded registry or an Exec statement commitment.

Envelope `IXFDSP00` has strict grammar tags 0/1/2 and distinct transcript domains
`ix:ixby:ixbf-dispatch-{program,input,output}:bytes1024:steps32:nat4096:v0`.
Little-endian fixed-integer encoding rejects wrong magic/kind, noncanonical
encoding, trailing bytes and proofs over 8 MiB. There is no fallback to or
from an old Exec/component envelope.

Fresh verifier children clear their environment, run in a temporary working
directory, and receive only the grammar tag, externally expected words and
proof bytes through stdin. They reconstruct the fixed setup. They do not
receive source files, source paths, ASTs, payload-length advice or decoder
results, and do not call a native parser/hasher or gate evaluator to admit the
proof.

## Verification evidence

Seven ordinary tests cover native/Boolean equality for all 256 tag/phase byte
values, high/reserved bits, full-width counters and underflows, all 586 possible
Nat terminators, exact prefix masking, every control output bit, unused columns,
poisoned/recycled buffers, lazy count/emit parity and data-independent full-file
layouts. Program/Input/Output tests cover every scalar type, 4,096-bit Nats,
UTF-8 splits (including a restricted four-byte sequence across a boundary),
invalid suffixes, empty payloads, truncated files, trailing bytes, wrong initial
context and exhausted step capacity. Malformed cases also exercise the actual
fixed circuit's residual/state wiring, not just a host parser.

Eight complete grammar proofs verify in fresh processes: six programs
(erased return, 4,096-bit Nat, 65-/512-byte strings, 800-byte ByteArray, and
the declaration/Let/Copy/case-alternative program), plus one input and one
output carrying a split UTF-8 string. All use the same byte/step/Nat capacities;
the six programs share one exact setup. Each serialized proof is 381,732 bytes,
excluding externally expected public data.

Six additional proofs recompute locally valid rows for a substituted request
state, substituted source buffer byte outside the current read, an unselected
decoder result, premature UTF-8 completion, changed Nat bytes, and a changed
compression counter. Fresh verification rejects each at `Wiring`. The first,
second and third attacks preserve every local output of the modified row;
the other attacks derive new outputs normally. The tests also reject altered
root/context/final-state words, the wrong transcript domain, wrong envelope
magic/kind, trailing bytes and wrong public width.

The AST-free original-source differential checks every new control row and
selected decoder/grammar row against its Boolean relation, then compares full
grammar state with an independent checked-integer reference. Native artifact
metadata and syntax censuses are compared only after dispatch; they never choose
the schedule. Retained results, including explicit final Done rows:

| Original source | Bytes | Dispatcher steps |
| --- | ---: | ---: |
| 81 independent compiler programs | varying | 3,536 total |
| Exact Init program | 1,002,355 | 37,879 |
| Exact Init input | 9,611,120 | 10 |
| Exact Init output | 49 | 6 |

Init covers 146 constructor declarations, 681 functions, 6,763 blocks and
608 Nat payloads. Its six ByteArray scalars include three empty arrays, so
only three require payload-advance events. The large input's bytes are covered
by checked spans in this differential; they are **not** all hashed/proved by
the small-file class. These results do not prove registry/arity admission or
the earlier 5,372,353,187-transition native Init execution.

The final targeted ordinary run passes seven tests (two opt-in), taking
16.50 seconds in the body and 31.50 seconds wall including compilation,
with 2,432,912 KiB maximum RSS. The completed isolated-verifier proof regression
takes 81.93 seconds in the body, 82.44 seconds wall and 5,101,064 KiB maximum
RSS. The completed original-corpus/Init differential takes 96.31 seconds in
the body, 96.36 seconds wall and 602,556 KiB maximum RSS. The latter two runs
overlapped Stage 4 and each other; these are per-command regression
measurements, not isolated single-proof timings or aggregate host memory.
Proof and external tests use four Rayon workers, a 32 GiB virtual-address
limit and 600-/900-second timeouts respectively. No security parameter or
old capacity is raised to accommodate them.

Full release workspace regressions pass 223 Stage 3 tests (38 opt-in) and
266 Stage 4 tests (39 opt-in). Both workspaces pass strict release Clippy on
all targets and formatting checks. Stage 3 takes 454.84 seconds in the body,
455.76 seconds wall and 11,178,220 KiB maximum RSS; Stage 4 takes 156.33 seconds
wall including compilation and 1,127,792 KiB maximum RSS. The workspace runs
overlapped other checks and are not exclusive-host benchmarks.

The complete combined codec regression passes all seventeen opt-in tests:
66 honest proofs verify and 51 locally recomputed forgeries reject at wiring.
This includes the previous fifteen tests plus the new dispatcher proof and
original-source differential. It takes 506.02 seconds in the test body,
507.01 seconds wall, with 5,173,632 KiB maximum RSS and no rebuild. It overlapped
the full Stage 3 workspace for part of its run; it is a combined regression
measurement, not a single-proof or exclusive-host benchmark. Local evidence is
in `/tmp/ixby-dispatch.SPxTDL/`. All verification jobs completed successfully.

```sh
RAYON_NUM_THREADS=4 cargo test --release --locked \
  --manifest-path flock-stage3/Cargo.toml -p ixby-flock \
  ixby::ixbf_decode::dispatch:: -- --test-threads=1
RAYON_NUM_THREADS=4 cargo test --release --locked \
  --manifest-path flock-stage3/Cargo.toml -p ixby-flock \
  ixby::ixbf_decode::dispatch::proof_tests:: -- --ignored --nocapture --test-threads=1
```

For the external test, set the four explicit retained-fixture variables in
[the record document](IxbyFunctionalRecords.md) and select
`ixby::ixbf_decode::dispatch::external_tests::` with `--ignored`. The broader
`ixby::ixbf_decode::` opt-in filter also runs all prior codec proofs/differentials.

## Remaining admission and execution work

The generic dispatcher now connects source, canonical decoders and grammar in
the small-file class. Larger files still need scalable shared chunk
authentication; the full Init differential is not a source-bound Init proof.
The [bounded registry layer](IxbyFunctionalRegistry.md) now binds exact
constructor/function/block-header coverage, block ownership, constructor
uniqueness and entry frames to these events and supports typed reads. The
[instruction/reference layer](IxbyFunctionalReferences.md) connects every
Program event to those reads, including forward references, exact/partial
arities, successor frames and duplicate alternatives. The
[typed value layer](IxbyFunctionalValues.md) now materializes bounded IXFI/IXFO
forests with registry-bound references, scalar payloads, derived parentage,
child order, depth and complete subtree spans. The
[typed body layer](IxbyFunctionalBodies.md) now constructs bounded executable
function/block records, ordered operands, scalars, targets and alternatives
from the same Program events and supplies constrained reads.
[Authenticated typed code access](IxbyFunctionalCode.md) now seals those
actual records with their original digest and reuses authenticated chunk
handles for typed consumers. Full-image sealing and execution consumers remain.
Native loader depth/allocation limits and a formal
source/native correspondence remain separate obligations.

The raw-file digest still needs an explicit bridge to the Exec commitment
chain. Execution needs streaming witnesses, authenticated value/local/continuation memory,
access, complete state segments with actual VM-derived global fuel, sound
composition, and the full pinned Init proof. These component checks remain local.
