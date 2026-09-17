# Constrained functional scalar payloads

> Current contract: [runtime revision 2](CompilatrixRuntimeV2Handoff.md), with format-1/semantics-2 headers, 58 opcodes, and five wire-value kinds. This report preserves component milestone measurements and their original setup identities; its remaining-work sections describe that milestone. Current complete admission and execution are documented in [paged execution](IxbyFlockPagedExecution.md).

Three components extend the [original-wire codecs](IxbyFunctionalCodec.md)
and [grammar control](IxbyFunctionalGrammar.md): checked payload cursor/control
packing, the program's declared Nat-bit limit, and streaming strict UTF-8.
Small Flock conformance chains share their actual decoder and state wires.
They do not yet implement generic whole-file dispatch, source authentication,
an IXBF Exec factory, or a proof of the Init execution.

## Exact component relations

All words below are F128 bit containers, not binary-field integer arithmetic.
Each slot pins its validity residual to verifier-owned zero. Inputs and output
padding bits are constrained; additions and comparisons retain carries and
borrows. Every gate has setup-owned `nu` in 3–20 and lazy count/emit parity.

| Component | Input words | Output words | `k_log` / used columns |
| --- | --- | --- | --- |
| `PayloadCursorGate` | cursor, narrow length, Boolean enable | Nat control, range, next cursor, residual | 12 / 1,935 |
| `NaturalLimitGate`, 4,096-bit capacity | u128 declared limit, Boolean enable, 32 magnitude limbs | narrow bit length, residual | 15 / 17,562 |
| `Utf8ChunkGate` | cursor, remaining/DFA state, Boolean enable, two source words | next cursor, next state, residual | 14 / 9,240 |

### Cursor and Nat-control packing

The cursor is `(offset, file length)` in u64 lanes. Length is a narrow u64
with a zero high lane; enable is exactly 0 or 1 with all other bits zero.
The relation checks `offset <= file length` and the nonwrapping sum
`offset + length <= file length`. Its outputs are exactly:

```text
natural_control = (length, enable)
range           = (offset, length)
next            = (offset + length, file length)
```

A disabled row requires length zero and preserves the cursor. An enabled
empty payload is valid; the separate Nat decoder requires a nonempty encoding
when enabled. The length wire can feed both the grammar event and this packer;
the packed control feeds `NaturalDecodeGate` directly. For String/ByteArray,
length must be the actual Count decoder output. The range is not an artifact
identity or a payload membership proof.

### Declared Nat-bit limit

Capacity is the existing setup-owned `NaturalCapacity`, from 0 to 4,096 bits.
Magnitude input limbs must be the actual Nat decoder outputs. A descending
scan derives a mutually exclusive highest-set-bit flag from every magnitude
bit; zero has length zero. The resulting exact bit length is compared with
the entire u128 declared limit, including its high lane. No host-supplied
length or truncated limit can stand in for that comparison.

Unused physical magnitude bits must be zero. Disabled rows require a zero
magnitude and therefore produce bit length zero. A declared limit above the
physical capacity is permitted, but does not expand that capacity. The
program's header limit must be wired into this consumer; an unrelated copy
is not sufficient. This component does not change the physical codec class,
guest limits, or existing Exec profile.

### Streaming strict UTF-8

State packs remaining payload bytes in the low u64 lane and the DFA in the
high lane; all unused DFA bits are zero. Cursor packs offset/file length.
An enabled row consumes exactly `min(32, remaining)` bytes. Remaining must
fit the file suffix even on a disabled row. Source bytes beyond EOF are zero;
bytes after the payload but before EOF are ignored, not incorrectly treated
as padding. Disabled or empty rows have all-zero byte inputs.

| DFA | Meaning | Valid continuation and next state |
| --- | --- | --- |
| 0 | Ground | ASCII stays 0; C2–DF → 1; E1–EC/EE–EF → 2; F1–F3 → 3; E0/ED/F0/F4 → 4/5/6/7 |
| 1, 2, 3 | One, two or three continuations remaining | 80–BF → state minus one |
| 4 | Immediately after E0 | A0–BF → 1 |
| 5 | Immediately after ED | 80–9F → 1 |
| 6 | Immediately after F0 | 90–BF → 2 |
| 7 | Immediately after F4 | 80–8F → 2 |

This rejects overlong encodings, lone continuation bytes, surrogate code
points, values above U+10FFFF, invalid leads and incomplete final characters.
NUL is valid. State may cross a chunk boundary inside a character. Whenever
remaining becomes zero, DFA must also be zero, even on disabled padding.
Disabled rows preserve valid cursor/state and cannot finish outstanding work.

A complete chain must start from the actual decoded narrow length, whose
zero high lane establishes ground DFA; share both complete cursor/state wires
between chunks; and pin the final state to zero. Its final cursor must equal
the packer's checked endpoint and feed the grammar payload event. Every
nonempty active source window still needs separate authentication at its
actual cursor. Empty padding is not a claim about later source bytes.

## Actual decoder-to-consumer proof chains

The private test envelope remains `IXFCOD00`, with distinct tags/domains for
the new relations. Old tags, domains, Fast128 admission, Flock pin, security
parameters, factories and keys are unchanged. No new production Exec profile
is introduced. The fixed conformance schedules are:

- A single output Nat: decoded program header → initial output context →
  Output/Value/Scalar records → checked length packing → canonical Nat
  magnitude → declared-limit check → Natural grammar event → Done.
  The same length feeds the packer and grammar; actual magnitude limbs and
  the carried header limit feed the limit check. The fixture has a 65-bit Nat
  and a declared limit of 65, with physical codec capacity still 4,096.
- A single nonempty output String, at most 64 bytes: the same header/output
  prefix path → Count record → checked range and initial UTF-8 state → two
  fully chained chunks → StringPayload grammar event → Done. The fixture is
  36 bytes, with F0 at the end of the first chunk and its three continuations
  in the second. Final UTF-8 state is fixed zero, and its cursor is connected
  to the checked range endpoint. Empty strings are covered by component and
  original-source tests, not this particular fixed grammar schedule.

These schedules have genuine initial working state and terminal grammar
completion, but decode only the supplied program header, not its whole body.
Function count and entry arity remain externally expected context, not
authenticated registry lookups. Public vectors contain expected source
windows, not full-file commitments or Exec digests. The general image-
independent dispatcher and byte/registry authentication remain open.

Five new honest proofs verify in environment-cleared child processes given
only the component selector, expected public words and proof bytes. Five
locally valid, fully recomputed substitutions reject at global wiring. In the
Nat chain a different declared limit leaves all outputs unchanged. In the
String chain, only the second chunk's incoming DFA is substituted: state 3
can locally consume the same bytes as the required state 6, but cannot replace
the first chunk's actual output wire. The first chunk, source words and final
outputs remain unchanged. Fixed/public words, domains, proof kinds, truncation
and trailing data are also checked.

| Conformance relation | Public words, including fixed pins | Complete bundle bytes |
| --- | ---: | ---: |
| Payload cursor | 7 | 107,772 |
| Declared Nat limit | 36 | 108,356 |
| UTF-8 chunk | 8 | 107,300 |
| Header/decoded Nat/grammar chain | 123 | 148,508 |
| Header/decoded String/UTF-8/grammar chain | 96 | 146,620 |

Sizes exclude expected public words. Single-component schedules use
`nu = 10, 7, 8` respectively; mixed chains use `nu = 5`. These are component
measurements, not full Init proving estimates or retained standalone proofs.

## Differential and regression evidence

Six new ordinary tests cover exact independent endpoints, all 4,096 Nat basis
bits at their valid and one-bit-too-small limits, zero/partial capacities,
full-width limits and carries, every output bit, unused columns, recycled
buffers, fixed templates and lazy counting. UTF-8 checks include:

- Every one of the 2,048 DFA-state/byte transitions against an independent
  integer evaluator and the Boolean R1CS, including post-byte state on errors.
- All 65,792 one- and two-byte sequences against `std::str::from_utf8`, and
  all 1,112,064 Unicode scalar values through the independent native evaluator.
- R1CS checks for restricted three/four-byte boundaries, split and incomplete
  characters, following records versus EOF padding, disabled state, malicious
  remaining/DFA lanes, and 1,024 deterministic structured fuzz strings.

The original AST-guided differentials now feed actual decoded Count fields,
Nat magnitudes and carried limits into these checks. They still use the
original source windows and retain all prior record, reference and grammar
checks; the host AST is untrusted test preparation, never verifier admission.

| Original artifacts | Checked payload cursors | Declared Nat limits | UTF-8 chunks |
| --- | ---: | ---: | ---: |
| 81 compiler-corpus programs | 108 | 89 | 7 |
| Exact Init program | 614 | 608 | 0 |
| Structured identity and retained Init transports | 7 | 2 | 2 |

All 699 Nat checks, 729 payload cursors and nine UTF-8 chunks pass. Init has
no String literals; split-character evidence comes from the independent
synthetic tests and proof fixture, not a claim about Init's contents.
The complete codec suite passes thirteen opt-in tests, with forty-six honest
proofs verified and thirty-seven recomputed negative proofs rejected.
Full release workspace regressions pass 209 Stage 3 tests and 266 Stage 4
tests, with zero failures; both workspaces pass strict Clippy and formatting.

On 2026-09-14, the final warm thirteen-test codec run took 76.68 seconds wall
time (76.49 seconds in the test body) and reported 624,004 KiB maximum RSS.
It used four Rayon workers, one test thread, a 32 GiB virtual-address limit
and a 600-second timeout, without overlapping workspace tests or rebuilds.
This includes original-artifact differentials, all proofs and isolated
verifier children; it is not a single-proof timing or a full Init estimate.

Use the ordinary and opt-in commands, including the four retained-fixture
variables, in [the record document](IxbyFunctionalRecords.md). No cloud
machine is needed for these checks.

## Still required

The later [generic dispatcher](IxbyFunctionalDispatch.md) links these scalar
checks to state-selected byte requests and proves complete small-file grammars
with one authenticated shared buffer. Remaining work includes authenticated
typed payload/record materialization, scalable shared chunk authentication for
larger files, registry ownership/coverage and forward references, and complete duplicate-
alternative checks. Native loader depth/allocation limits and source/native
refinement remain separate obligations. Then the execution path needs
streaming witnesses, scalable code/memory access, full-state segments with
actual VM-derived global fuel, sound composition and the full pinned Init
proof. The [scaling plan](IxbyStage3ScalePlan.md) is unchanged in scope.
Work remains local and uncommitted; EC2 has not been restarted.
