# Source-bound instruction and reference checks

`flock-stage3/host/src/ixby/ixbf_decode/references/` connects every actual
Program dispatcher event to the completed
[declaration/header registry](IxbyFunctionalRegistry.md). It checks direct
and self calls, closures, constructor arities, all successor frames, and
duplicate constructor alternatives, including forward references and dead code.

This completes the instruction/reference part of bounded original-wire program
admission. It does not materialize executable bodies or typed input/output
arenas, establish native constraint-to-reference refinement, or admit IXBF to
an Exec factory. The source reader must authenticate the dispatcher's exact
requests to one externally expected file; the proof class below supplies that
link for a 1 KiB file. Full Init execution and terminal compression remain
separate gates in the [scaling plan](IxbyStage3ScalePlan.md).

## Complete event coverage and forward references

`ProgramReferenceSlots` owns a `ProgramRegistrySlots` and a private state type.
Initialization creates the actual zero-offset grammar and empty registry.
Every `step` retains the old grammar and the actual returned dispatcher event.
The retained list contains circuit wires, not a prover-supplied event schedule,
lookup request, decoded AST, or acceptance bit.

`finish` first completes the genuine grammar/EOF and header registry. It then
checks every retained step against that same final immutable bank. This makes
later-declared callees and successor blocks available without a second parse
or a prover-selected registry. Unreachable blocks and unused functions follow
the same path. The wrapper exposes no operation to omit a retained event.

Each step emits one request row, all three typed registry reads, and one check
row. The circuit topology depends on setup capacities and the number of
steps. Tags, indices, owners, read enables and argument counts derive from
actual event/state wires. Disabled reads have zero requests and results.

The three carried words are the current instruction, the saved direct-tail-call
callee, and a bitmap of constructor alternatives already seen in this block.
Every block header resets the callee and bitmap. Only the actual function-index
event saves a tail callee. Intermediate UTF-8 rows and Done padding carry state;
they cannot create, skip or reset a semantic event.

## Checked relations

| Event | Registry read and required relation |
| --- | --- |
| Construct operation | Selected constructor's field count equals argument count |
| Closure operation | Selected function's arity strictly exceeds captured argument count |
| Direct call | Selected function's arity equals argument count |
| Self call | Current function's registered arity equals argument count |
| Direct tail call | Saved actual callee's arity equals the subsequent argument-count event |
| Self tail call | Current function's registered arity equals the argument-count event |
| Let successor | Owned target frame has current locals plus one |
| Nat case | Zero target preserves locals; successor target adds one |
| Boolean branch | Both owned target frames preserve locals |
| Constructor alternative | Owned target frame adds the selected constructor's fields; its constructor index has not appeared earlier in this block |

Owner selection uses exact `next_function_index - 1` with underflow rejection.
All indices, arities, counts and frame arithmetic preserve all 128 bits.
Successor addition rejects overflow and checks the original declared local
limit. Full constructor uniqueness is already enforced by registry completion,
so distinct alternative indices identify distinct constructors.

The existing decoder and grammar constraints continue to check local operand
bounds, all 45 primitive tags and their arities, operation/operand counts,
canonical scalars, Nat limits and UTF-8. Copy, projection, application and
return add no static registry-arity check beyond their existing operand checks.
Runtime operand types and dynamic application behavior belong to execution.

## Tables and bounded setup

The new component uses two setup-owned Boolean tables:

| Table | Input words | Output words | Inner `k_log` |
| --- | ---: | ---: | ---: |
| Request | 46 | 18 | 16 |
| Check | 29 | 1 | 16 |

Request inputs are old grammar (28), committed flag, event tag, thirteen fields,
and the three carried words. Outputs are next carried state, seven typed-read
request words, seven semantic facts and a validity residual. Check consumes
those fourteen actual request/fact wires plus the three five-word registry
results. Its sole output is the validity residual. Both residuals connect to
a verifier-owned zero distinct from initialization constants.

The row domain remains bounded from three through twenty. Count-only emission
does not build Boolean plans or evaluate witnesses. Constructor capacity stays
within the existing registry's zero-to-four bound; the bitmap introduces no
new guest limit. This dense per-step bank/read construction is a small-class
prototype and cannot scale to Init by increasing constants alone.

The test proof class fixes the existing `(C,F,B)=(2,2,2)` registry, 1,024 private
bytes, 32 steps, 4,096 Nat bits, and outer `nu=7`. It has 37 tables and uses
the unchanged pinned Flock revision, legacy BLAKE3 and Fast128 with `M=25`.
The shared source buffer is hashed once with seventeen compression rows.

There are 65 private words: file length and 64 packed buffer words. The 30
externally expected public words are the two raw file-digest limbs and complete
final grammar. No lookup queries or registry results are supplied by the verifier.
The raw digest is still not the Exec commitment chain.

Envelope `IXFREF00`, revision zero, has the distinct domain
`ix:ixby:ixbf-program-references:bytes1024:steps32:nat4096:c2:f2:b2:v0`.
Encoding is canonical fixed-integer little-endian, with no trailing bytes and
an 8 MiB transport cap. Earlier registry, dispatcher and Exec envelopes are
not accepted through fallback decoding. Existing production Exec setups,
keys, envelopes and security settings are unchanged.

## Verification

The ordinary tests cover all eight instruction forms and all eight operation
forms under one setup. Fixtures include forward calls, different block owners,
nonzero entry blocks, unused blocks, split UTF-8, a 4,096-bit Nat, full-width
arities and a valid successor addition reaching u128-max. Independent native
loading and exact re-encoding agree on every honest original-wire fixture.

Fifteen malformed programs remain complete canonical grammars and pass the
unchanged source-bound header registry. The new checks and the independent
native validator reject their wrong call/closure/constructor arities, self/tail
calls, Let/case/branch frames, duplicate alternatives, dead bad code and
high-limb arity mismatch. Unit differentials cover every control byte, high
and reserved bits, ownership underflow, full-width saved callees and constructor
indices, duplicate/reset behavior, arithmetic overflow and disabled advice.
Output-bit, unused-column, poisoned-padding and lazy count/shape tests also run.

The opt-in proof regression verifies 24 original-wire fixtures in fresh
environment-cleared processes outside the worktree. Children receive only
externally expected public words and proof bytes through stdin, reconstruct
the approved setup, and run no native parser, hash, loader or semantic predicate.
Each complete serialized proof is 424,156 bytes, excluding the expected public
words. Nine recomputed forgeries target:

1. A decoded call target.
2. The saved direct-tail-call callee.
3. The current block's function owner.
4. Source and target local counts inside the successor check.
5. Constructor field and argument counts inside their check.
6. Callee arity and argument count inside their check.
7. The carried alternative bitmap.
8. Unused grammar metadata inside a Done request.
9. A source-buffer byte outside the current requested window.

Each reference forgery recomputes a locally valid Boolean row and checks its
actual R1CS before proving. The semantic-check and unused-metadata attacks
preserve every local output. Fresh verification rejects all nine at `Wiring`.
Changed expected digest/state, proof transport, or the old registry domain also
reject. These proofs establish this bounded native relation, not a formal
source/refinement theorem or a full Stage 2 execution proof.

The final 2026-09-15 workspace run passes 237 ordinary tests (40 opt-in),
formatting and release Clippy on all targets with warnings denied. The existing
AST-free parser differential also passes all 81 compiler-corpus programs and
the exact retained Init image/input/output. This is a parser regression; the
new bounded registry/reference class does not admit the full Init artifacts.

The proof regression takes 272.69 seconds in the body, 290.04 seconds wall
including compilation, with 5,632,232 KiB maximum RSS. The workspace run takes
246.18 seconds wall and 18,941,072 KiB maximum RSS using four test workers.
The retained-artifact differential takes 272.73 seconds wall and 602,108 KiB
maximum RSS. All three jobs overlap, use four Rayon workers, and retain the
32 GiB virtual-address cap. These are per-command regression measurements,
not isolated single-proof costs or Init proving estimates. Logs and timing
files are retained under `/tmp/ixby-references-*-final.{log,time}`.

```sh
ulimit -c 0
ulimit -v 33554432
RAYON_NUM_THREADS=4 cargo test --release --locked \
  --manifest-path flock-stage3/Cargo.toml ixby::ixbf_decode::references:: \
  -- --test-threads=1
RAYON_NUM_THREADS=4 cargo test --release --locked \
  --manifest-path flock-stage3/Cargo.toml ixby::ixbf_decode::references:: \
  -- --ignored --test-threads=1 --nocapture
```

## Remaining work

The [typed value layer](IxbyFunctionalValues.md) now consumes this completed
program object for IXFI/IXFO constructor identities, PAP arities and transport
context. It preserves scalar payloads/ranges and derives ownership, child order,
depth and complete subtree spans under explicit physical bounds. This
Program-only component still does not materialize executable bodies. Their
ordered coverage, ownership and execution consumers remain required, as do
larger-class native loader depth/allocation obligations.

Larger files need shared chunk authentication and scalable registry/code/memory
access. The raw-byte/Exec commitment bridge, streaming witnesses, VM-derived
global fuel, complete execution segments, sound composition and pinned Init
proving remain ahead of terminal compression.
