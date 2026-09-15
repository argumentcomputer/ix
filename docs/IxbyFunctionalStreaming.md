# Streaming proofs of the original file grammars

`flock-stage3/host/src/ixby/ixbf_decode/stream/` connects the existing
state-selected dispatcher to reusable authenticated source chunks. The
complete original [CSLib guest](IxbyStage2CSLib.md) now has a verified Program
grammar chain: 37,878 decoder steps in 1,217 Flock batch proofs. Its original
input and output each require one additional grammar proof. A fresh process
verified all three chains with transport context derived from the verified
Program's final state.

This establishes original-file grammar, canonical scalar payloads, strict
UTF-8 and complete parser-state continuity. Full constructor uniqueness,
instruction/reference admission, typed code/value materialization, execution
memory, the raw-file/Exec commitment bridge and guest execution remain separate
obligations. The semantic materializers still have their small-file capacity
bounds. This chain is not a single recursive proof or a Stage 3 Exec proof.
No existing Exec setup, key, capacity, dependency pin or security profile changes.

## Checked batches and source reuse

`StreamSlots::authenticate` checks three original BLAKE3 chunks against the
same root: the chosen first chunk, its successor clamped to the last chunk,
and the exact final chunk. The final chunk binds the file length, including
when opaque siblings hide the suffix. Only that constrained operation can
construct a `CachedSource`; the handle retains the checked length, indices
and actual byte wires.

Each batch reuses this handle for up to 32 dispatcher steps. A positive byte
request must start in the first authenticated chunk and may cross into its
successor. A zero-byte request returns checked zeros and can advance over an
opaque ByteArray payload without reading every payload byte. The original
digest still commits to those bytes; runtime use requires authenticated reads.
Strings do not use this shortcut: carried UTF-8 state must consume their
contents and finish validation.

Three new control relations enforce this contract:

| Operation | Inputs / outputs, F128 words | Useful / padded Boolean columns |
| --- | ---: | ---: |
| Cache indices and length | 2 / 3 | 2,223 / 32,768 |
| Read cursor, length and cache membership | 4 / 3 | 3,259 / 32,768 |
| Remaining steps and padding preparation | 31 / 33 | 16,391 / 32,768 |

Every validity output is constrained to zero. The actual 64-bit remaining
step count decrements inside the circuit and must be zero at batch end.
Padding runs the dispatcher on a canonical dummy Done state, then selects
back **all 30 actual state words unchanged** and a zero committed-event flag.
Batches can stop at a page boundary while a file or UTF-8 string is unfinished,
but cannot discard those obligations.

The source window independently derives its length and chunk indices; full
F128 equalities connect them to the cache. The dispatcher consumes the actual
window outputs and its own state-derived cursor/take. No host event schedule
or byte buffer supplies accepted decoder outputs.

## Untrusted witness generator

`dispatch::DispatchEvaluator` evaluates the existing dispatcher and decoder
gates to prepare advice. `stream::witness::BatchWitness` retains the original
byte slice, a native BLAKE3 chaining-value tree and the current 30-word state.
It emits one bounded batch at a time, stopping at 32 steps, a change of source
chunk or completion. It does not build an AST or retain the whole parser
trace. Source storage remains proportional to the file size; this is not a
constant-memory disk reader.

The native tree is checked against the existing independent source-advice
implementation. Tests compare final parser state to the independent integer
grammar model and typed host decoder **after** generating batches. Neither
model chooses the witness schedule. Verification never calls the native
evaluator, reads original files or accepts the host decoder's verdict.

## Fixed proof classes and complete-chain verification

The harness defines separate Program, Input and Output classes with:

- Source-tree depth 14, admitting files through 16 MiB.
- 32 physical dispatcher steps and 4,096 physical Nat bits; the program's
  own Nat limit remains enforced.
- A seven-bit row domain, 35 tables, legacy BLAKE3 compression and pinned
  `Fast128`, `M=25` PCS configuration.
- 311 private advice words and 63 externally expected variable public words:
  exact file length, two original-digest limbs, 30 initial and 30 final words.

Each batch uses 90 compression rows: three chunks times 16 blocks plus 14
path levels, shared across all 32 steps. Other source/control rows include
48 block rows, 42 path rows, 90 chaining-value selections, 32 windows, one
Cache, 32 Read, 32 Prepare, 32 state selections and 96 equalities. The generic
dispatcher emits its complete decoder family at every step.

The strict `IXFSTB00` envelope uses a grammar tag, fixed-width little-endian
bincode, an 8 MiB bound and rejection of trailing bytes. Transcript domains are
`ix:ixby:ixbf-stream-{program,input,output}:d14:steps32:nat4096:v0`.
There is no fallback to an old component or Exec decoder.

`IXFSTC00` frames contain a little-endian u32 proof length, 30 final-state
words and that batch proof; zero length terminates the chain with strict EOF.
The verifier admits at most 4,096 frames. From the externally expected length,
original digest and 15-word context it constructs the genuine Start state.
Program context must be zero. Every verified final state becomes the next
proof's expected initial state, including both UTF-8 words. Each batch must
make progress. The final state must be Done at exact EOF with no pending
functions, blocks, constructors, items, payload or forest obligations.

The joint CSLib verifier first cryptographically verifies the entire Program
chain. It derives transport context from that verified final state, then
verifies both transport chains against their original expected digests and
lengths. Prover-side boundary extraction is only advice; it does not establish
the verifier's context. This binds grammar metadata across the three files
without claiming the Program's full semantic admission.

This proof serialization and chain verifier currently live in the opt-in
test harness. Reusable gates, slots and witness generation are library
components. A production execution API is still required.

## Verification evidence

The full Stage 3 workspace passed 268 ordinary tests. There are now 50 opt-in
proof/benchmark/external-artifact tests. Release compilation, formatting and
Clippy with warnings denied passed.

The cryptographic conformance run produced 16 honest proofs covering a
standalone batch and five complete chains across all three grammar kinds.
Fresh children run outside the worktree with a cleared environment and receive
only expected statements and proof bytes. Program bundles were 404,108 bytes;
Input/Output bundles were 400,204 bytes.

Nine recomputed attacks satisfy their changed local R1CS rows but reject at
the actual Flock wiring check: cache length, cache index, read cursor,
zero-byte-read length, paused state, remaining step count, unused source-buffer
bytes, path sibling and compression counter. Reordered or replayed frames,
missing head/tail, altered intermediate/UTF-8 states, changed root/length/context,
wrong expected words, old domains, changed magic/kind/proof bytes, truncation
and trailing bytes also reject.

Ordinary checks cover full-word controls, source depths through 54, empty and
partial chunks, cross-page UTF-8, a multi-megabyte opaque ByteArray, every
output bit, recycled padding and count/emit parity. Native full-CSLib batches
match both independent parsers; the inventory includes 146 constructors,
681 functions and 6,763 blocks.

### Complete retained CSLib run

| Original file | Source bytes | Decoder steps | Flock proofs | Complete chain bytes |
| --- | ---: | ---: | ---: | ---: |
| Program | 1,016,587 | 37,878 | 1,217 | 492,388,476 |
| Input | 4,813,238 | At most 32 | 1 | 400,700 |
| Output | 49 | At most 32 | 1 | 400,700 |

On the local machine, 12 prover workers with two Rayon threads each produced
the complete Program chain in 130.044 seconds. Independent four-thread
verification took 48.032 seconds internally, 48.22 seconds process wall time.
Maximum RSS was 2,660,088 KiB for the largest worker and 2,353,220 KiB for the
verifier. These are per-process values. The runner's process-tree sampler
missed workers created by non-main threads, so its aggregate peak field is
invalid; no aggregate memory measurement is claimed.

A subsequent fresh process verified all three grammars and their shared
Program-derived context in 52.554 seconds. It received only the three chain
paths and fixed expected original-file identities, with a cleared environment.
Process wall time was 52.77 seconds and maximum RSS was 2,407,676 KiB.

The Program chain is about 469.58 MiB. Its SHA-256 is
`158f92abd96b902542bc6fe032c4ee897fd804cc15960d69c9a9aa625f2320f2`.
Original source BLAKE3 pins are:

| File | Raw BLAKE3 |
| --- | --- |
| Program | `96ed4322c7e4db289b876848e885d02afd2958f829135d5108b565ce9d493c05` |
| Input | `e0e8fbc9e0c68246b93ce8128c4ed3229029e5b06fc6185fe8a18d48f1018769` |
| Output | `efafe68f5f11d9701e88d02b0cf78de1a3c116d33a3ca8fedd82ae2eb6d90bcf` |

Local artifacts and logs are under `/tmp/ixby-cslib-stream.MfwAc6/`, with
transport chains and joint verification logs under `transport/`. These scratch
files are not repository fixtures. Original source paths and SHA-256 identities
are recorded in [the CSLib target record](IxbyStage2CSLib.md).

## From this chain to one Flock proof

Compressing the existing batch proofs requires a recursive composition
relation. One parent proves both child verifiers accepted, binds their exact
approved setups and original-file identities, and constrains the left final
state to equal the right initial state. It publishes the combined range and
endpoints. Repetition produces roughly eleven binary merge levels for 1,217
leaves. Explicit coverage/count and padding rules must prevent omitted,
duplicated or substituted ranges. The root requires genuine Start and complete
Done, with transport metadata bound to the verified Program.

The pinned Flock revision already contains a recursion tower under
`crates/flock-prover/src/tower/`. Its first-level builder `build_fl_node_k`
takes exactly two `ChainProof` children and asserts one Boolean BLAKE3 table.
Its application block is an eight-word hash-chain span. It cannot directly
consume this 35-table, 63-word parser statement. Required work includes a
general child verifier, the parser boundary/context relation, an expanded
accumulator layout and measured recursion geometry. Existing generic verifier
replay in [Stage 4](IxbyStage4Replay.md) provides related components, but is
not an implemented parser-to-Flock recursion adapter.

Flock defers matrix, wiring and jagged-layout evaluations into accumulators.
Their claims must be bound to actual child-verifier outputs, folded inside
the parent relation and discharged against every approved table at the root.
Calling the native accumulator helper or checking endpoint hashes alone does
not compress proof validity. The recursive artifact must include all root
data its verifier needs; leaf proofs can then remain prover-side.

The next aggregation milestone is one two-batch parent proof verified in a
fresh process, rejecting a changed source, substituted child, broken boundary
and forged accumulator. Then measure proof bytes, peak memory, the exact
table/PCS configuration and another recursion level before choosing the full
tree's envelope. The final size and cost are not yet measured.

An alternative is to re-prove every parser batch inside one larger direct
Flock circuit, with intermediate states wired internally. That avoids recursive
verifier work but combines the trace and wiring allocation. It needs a
count-only resource census first and does not compress existing proof files.
Full guest execution has billions of transitions and requires separate
scalable execution/composition work in either case.

## Reproduction entrypoints

All tests below are in `ixby::ixbf_decode::stream::proof_tests` and are opt-in:

- `batches_and_chains_verify_in_isolation_and_reject_substitutions` runs the
  self-contained cryptographic conformance corpus.
- `cslib_tests::retained_cslib_batches_match_reference_and_prove_transports`
  takes `IXBY_STREAM_PROGRAM`, `IXBY_STREAM_INPUT`, `IXBY_STREAM_OUTPUT`.
- `cslib_tests::retained_cslib_program_proof_shard` takes the Program path,
  fresh `IXBY_STREAM_PROOF_DIR`, `IXBY_STREAM_SHARDS` and `IXBY_STREAM_SHARD`.
  Each worker writes only its disjoint numbered frames with create-new files.
  Assemble frames in order after `IXFSTC00`, followed by a zero u32.
- `cslib_tests::retained_cslib_program_chain_verifies_without_original_artifacts`
  takes only `IXBY_STREAM_CHAIN`.
- `cslib_tests::retained_cslib_transport_proofs_from_program_boundary_advice`
  takes that chain, the two original transport paths and a fresh proof directory.
- `cslib_tests::retained_cslib_all_grammars_verify_with_program_bound_context`
  takes only `IXBY_STREAM_CHAIN`, `IXBY_STREAM_INPUT_CHAIN` and
  `IXBY_STREAM_OUTPUT_CHAIN`; original identities are fixed in this retained
  workload test. Run the built executable from `/tmp` with a cleared environment
  and those three paths, plus `RAYON_NUM_THREADS=4`.

Measured runs used a 32 GiB virtual-address cap per process. Original files are
required only for proving/native differentials. Verification needs the approved
setup, expected identities and complete proofs.
