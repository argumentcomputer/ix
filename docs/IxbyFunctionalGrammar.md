# Constrained original-wire grammar control

> Current contract: [runtime revision 2](CompilatrixRuntimeV2Handoff.md), with format-1/semantics-2 headers, 58 opcodes, and five wire-value kinds. This report preserves component milestone measurements and their original setup identities; its remaining-work sections describe that milestone. Current complete admission and execution are documented in [paged execution](IxbyFlockPagedExecution.md).

`GrammarStepGate` adds the control relation for the complete IXBF program
grammar and IXFI/IXFO preorder value forests. It selects the required decoder
event and bounds, threads all parser state, accounts for outstanding records
and children, and requires exact EOF on completion. It covers all eight
instruction forms and all eight operation forms, including their nested
operand/scalar bodies and post-operand fields.

This is a component of [binary correspondence](IxbyStage3ScalePlan.md), not
whole-image admission, an IXBF Exec factory, or a full Init execution proof.
The distinction is important: a correct control trace over typed decoder
events does not authenticate those events' original source windows or their
registry lookups. The existing [record relations](IxbyFunctionalRecords.md)
and [payload codecs](IxbyFunctionalCodec.md) remain separate components.

## Exact row and state ABI

The setup owns `GrammarKind::{Program, Input, Output}`. A row has 46 input
F128 words and 29 outputs. F128 is used as a container for exact bits;
counters use Boolean u128 addition/subtraction with explicit carry/borrow.

| Input words | Meaning |
| --- | --- |
| 0–27 | Complete previous parser state |
| 28 | Setup-owned decoder event tag |
| 29–31 | The actual decoder's three bound inputs |
| 32–44 | Thirteen decoder fields; ordinary records use six, with the rest zero |
| 45 | The actual decoder's next cursor |

Outputs 0–27 are the next state. Output 28 is the validity residual;
`GrammarStepSlot` fixes it to a verifier-owned zero.

| State words | Meaning |
| --- | --- |
| 0 | `(byte offset, file length)` in exact u64 lanes |
| 1 | Five bytes: phase, after-operand, after-vector, after-scalar, targets-left; remaining bits zero |
| 2–3 | Total constructor and function counts |
| 4 | Functions remaining |
| 5–6 | Current function's block count and blocks remaining |
| 7 | Constructors remaining |
| 8 | Next function ordinal; current ordinal is one less after its header |
| 9 | Current local-frame size |
| 10 | Remaining operands or alternatives |
| 11 | Pending String/ByteArray payload length |
| 12–13 | Pending value positions and values already seen |
| 14–23 | The ten original declared limits, in wire order |
| 24–25 | Entry function and its arity |
| 26–27 | Current function arity and original fuel budget |

Every state word is carried, including unused-looking continuation/context
words. Program initialization requires offset zero and zero in every other
state word except the file-length lane. The decoded header initializes its
limits, fuel, entry and constructor count. The function-count event checks
the entry index, and the ordered function walk derives the entry arity.

Transport initialization also requires offset zero and zero working state.
Its constructor/function counts, limits, entry/arity and fuel are supplied
context that must ultimately be bound to the admitted program. Allowing that
context is not an authenticated registry or an entry-function lookup proof.

Ordinary phases have codes 0–20. Temporary FinishBlock, FinishValue and
NextArgument continuations are resolved within a row; they cannot be an
input/output phase of a successful row. Continuation bytes have checked
ranges and targets-left is at most two. Program and transport phase domains
are distinct. Every instruction/operation/scalar/value selector is derived
from its decoded tag, not from free one-hot advice.

## Events and ordered completion

Event tags 0–12 are the existing `RecordKind` tags. Tags 13–17 are Header,
Natural, StringPayload, BytesPayload and Done. The grammar constrains the
supplied tag and bounds to the current phase and carried limits/counts.

Header uses all thirteen fields, bounds `[file_length, 0, 0]`, and the header
codec's narrow offset output. Its offset's high lane must be zero and its
file length must equal the state's length lane. Other events use packed
cursor/file-length pairs and preserve that length exactly. An active event
must advance strictly, without wrapping or exceeding EOF. Done preserves
the entire state and cursor, requires zero event fields/bounds, exact EOF,
and no outstanding constructor/function/block/item/payload/value work.

Function and block headers consume their declared counts exactly. Operand
vectors return to the correct enclosing operation/instruction; literal
operands finish their scalars first. Projection metadata, let successors,
both branch/case-Nat targets, alternative vectors and tail-call arguments
cannot be omitted by changing the next record kind. Each slot must receive
the preceding slot's complete state and its actual decoder output cursor.

For a value prefix the relation enforces:

```text
seen'    = seen + 1
pending' = pending - 1 + decoded_children
seen' + pending' <= declared_input_nodes
decoder_child_budget = declared_input_nodes - seen'
```

All arithmetic is checked at 128 bits, including pending underflow and both
additions. Roots initialize pending. A scalar node cannot finish until its
scalar/payload finishes; other node prefixes continue to the next pending
position. No additional node may follow completion. In preorder, the root
count and child degrees determine a unique ordered forest; an independent
stack differential checks that characterization. This relation does not
yet materialize authenticated parent/child addresses for the interpreter.

String and ByteArray counts are decoded against their distinct limits. A
nonempty payload advances by exactly the saved count; an empty one resumes
immediately. Natural events use field 0 for the exact encoded length checked
by the natural decoder, require 1–586 bytes, and advance by that length.
That length must be connected through checked packing to the natural
decoder's `(length, enable)` control word, not supplied as an unrelated hint.
The later [scalar payload components](IxbyFunctionalScalars.md) supply that
checked packing, UTF-8 and the guest Nat-bit limit, including small actual
decoder/control chains. They are not checks performed by this control gate
alone; generic whole-file payload dispatch remains required.

## Integration contract and proof scope

A caller must enforce all of the following together:

1. A genuine initial state and a final Done row, not arbitrary public endpoints.
2. Exact equality of **all 28** adjacent state words, in order.
3. The decoder's setup-owned event tag and actual bounds, fields and cursor;
   active record enables must not become independent acceptance hints.
4. Exact source identity, offset, lookahead and payload-range authentication.
5. The complete semantic/registry checks required by the parsed records.

The component's row geometry depends only on the setup-owned grammar kind.
A generic whole-file dispatcher/schedule and authenticated lookup construction
are still needed; deriving a different circuit shape from each host AST would
not establish an image-independent Exec setup.

Two fixed, image-independent *conformance schedules* exercise the actual
cross-component wiring: a complete one-function/one-block return program and
a complete two-root input forest containing a PAP with one erased child and
a second erased root. The first wires a real header, four body records and
six grammar rows. The second wires an input record, three value prefixes and
five grammar rows. Bounds come from the carried context; the supplied child
budget is checked exactly by the grammar. Tags/enables are verifier-owned
constants. These schedules are deliberately limited examples, not a generic
whole-file admission factory or a registry-membership proof.

## Original grammar milestone evidence

The following measurements describe the original grammar milestone. The later
[scalar evidence](IxbyFunctionalScalars.md) extends the same original-source
tests with checked payload/limit/UTF-8 rows and adds two decoder/control chains.

Six new ordinary tests cover all productions, complete independent endpoint
states, every output bit, unused columns, recycled buffers, count/emission
parity, full-width carries, exhaustion and EOF. The checked-integer model
agrees on 14,430 structured/mutated rows: 8,949 locally valid and 5,481 invalid.
An independent explicit stack agrees on all 484 forests with 0–3 roots,
0–4 nodes and child degrees 0–2: 21 complete and 463 rejected.

The AST-guided original-source differentials now feed each event through
both the integer model and the Boolean control constraints. They retain
original block-boundary assertions and additionally require the constrained
terminal state. Program ByteArrays now also exercise their separate count
events; therefore their record census is slightly larger than the earlier
record-only milestone.

| Original artifacts | Record events | Grammar rows, including final Done |
| --- | ---: | ---: |
| 81 independent compiler-corpus programs | 3,268 | 3,536 |
| Exact Init program: 146 constructors, 681 functions, 6,763 blocks | 37,266 | 37,879 |
| Structured identity and retained Init I/O: eleven value nodes | 27 | 38 |

These are constrained-row differentials, not a full Init parsing proof. The
AST is untrusted test preparation and never a verifier acceptance oracle.

Five new honest Flock proofs verify in fresh, environment-cleared processes.
Five fully recomputed, locally valid substitutions reject at global wiring:
the chained cases alter a carried context word in an interior row while both
endpoint rows and external source words stay unchanged. Accepting the isolated
transition cannot bypass the adjacent-state connection. The
tests also reject changed fixed constants, public words, component/domain,
truncation and trailing proof bytes.

| Conformance relation | Inner `k_log` | Complete bundle bytes |
| --- | ---: | ---: |
| Single Program/Input/Output grammar row | 17 | 112,396 |
| Header/body/complete return-program control chain | mixed | 146,300 |
| Input/value/complete PAP forest control chain | mixed | 136,588 |

The Program plan uses 73,053 columns; Input and Output each use 69,096.
All new proof schedules use `nu = 5`. No Flock pin, admitted Fast128 profile,
existing Exec factory/key, primitive meaning or security/resource cap changes.
The private test envelope remains `IXFCOD00` with distinct new tags/domains.
Expected public vectors contain exact windows/context, not full-file BLAKE3
commitments or Exec digests. Verifier children receive only the approved
component selector, externally expected words and proof bytes; they neither
receive artifact files nor invoke the host reader.

Reproduce ordinary and opt-in checks with the commands and four fixture
variables in [the record document](IxbyFunctionalRecords.md). Proof bytes are
generated and verified by tests, not retained as standalone artifact files.
Measurements of these components do not estimate full Init proving capacity.

The final complete codec suite passes all twelve opt-in tests: forty-one
honest proofs and thirty-two recomputed forgeries, including the stronger
interior-row attacks above. On 2026-09-14 its warm run took 43.38 seconds wall
time (43.25 seconds in the test body) and reported 488,560 KiB maximum RSS.
It used four Rayon workers, one test thread, a 32 GiB virtual-address limit
and a 600-second timeout, without overlapping workspace tests. This measures
the combined external differentials, proof generation and isolated verifier
children, not a single proof. Full release workspace regressions also pass:
203 Stage 3 tests and 266 Stage 4 tests; both workspaces pass strict Clippy
and formatting. The only test-code change after those ordinary runs was
strengthening the opt-in forger to preserve both endpoints; the final full
opt-in suite and strict Stage 3 Clippy were rerun after that change.

## Still required

The later [generic dispatcher](IxbyFunctionalDispatch.md) integrates source
requests, decoder selection and UTF-8/payload checks at actual grammar cursors,
with source-bound whole-grammar proofs for an explicit small-file class.
Scalable shared chunk authentication for larger files, authenticated typed
constructor/function/block ownership and references, and duplicate-alternative
checks remain. Native loader syntax-allocation/depth limits are not new
semantic circuit claims. Execution additionally needs authenticated value
addresses, streaming witnesses, scalable code/memory access, full-state
segments, global fuel wired to actual VM transitions, and sound composition.
Source/native refinement is separate. The work remains local and uncommitted;
EC2 has not been restarted.
