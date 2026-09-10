# IxBy: first Aiur execution proofs

The experimental scalar interpreter produces real Aiur/FRI execution proofs
for a strict subset of [crypto semantic revision 0](IxbyEncoding.md). It is
program-independent within that subset: the current tests execute and prove
39 cases across 26 distinct guest images using one interpreter key.

This is not the complete functional machine, a certified compiler target, a
production `Claim` format, or a reviewed deployment/security profile. The
general circuit-to-Lean refinement theorem is still outstanding.

A separate [scalar CEK control backend](IxbyControl.md) now adds authenticated
whole-image tables, branches, direct/tail calls, and explicit continuations.
The [object backend](IxbyObjects.md) adds immutable constructors, projections,
and pattern matching, with a conditional ranked-heap representation contract.
This document retains the original straight-line subset and its measurements;
the three fixed profiles have different interpreter keys.

## Supported fragment

`Ix/Ixby/Aiur/Fragment.lean` records the host-side fragment check and fixed
experimental profile. `Aiur/Scalar.lean` independently enforces the fragment
inside the circuit; host acceptance is not a trusted input to proving.

- One function, entry function and entry block both zero, no constructor table.
- Straight-line blocks: every `letOp` names the next block, and only the final
  block may return. Each block declares exactly its incoming local count.
- Immutable absolute locals, scalar literals, erased operands, `copy`, and the
  selected primitives below. The internal reverse list implements append-only
  locals by translating index `i` to `count - (i + 1)`.
- Bool, Word32, canonical Goldilocks, canonical quadratic extension elements,
  and erased input/output values. No structured guest values or byte scalars.

The 20 supported primitive names use their existing wire opcodes:

| Family | Supported operations |
| --- | --- |
| Word32 | Add, And, Or, Xor, Eq, Lt, ToField |
| Goldilocks | Add, Sub, Mul, Inverse, Eq |
| Extension | Add, Sub, Mul, Inverse, Eq, Pack, Fst, Snd |

Calls, tail calls, closures/PAPs, constructor operations, branching, loops, and
the other 15 crypto primitives are rejected. BLAKE3 is used for artifact
authentication, but the guest `blake3` instruction is not yet supported. Nat
and String remain excluded by the crypto profile itself. These exclusions
restrict backend coverage; they do not change the reference machine's meaning.

The exact fixed profile capacities are:

| Parameter | Bound |
| --- | --- |
| Functions / constructors | 1 / 0 |
| Blocks per function / locals | 64 / 64 |
| Operands, entry arguments, total input nodes | 16 each |
| Continuations / value depth | 0 / 1 |
| Complete program bytes | 4,096 |
| Complete input bytes / complete output bytes | 1,024 each |
| Maximum reference steps | 65 |
| Nat bits / string bytes / individual byte-array bytes | 0 / 0 / 0 |

All parameters are included in the existing profile commitment. The circuit's
limits and profile hash are generated from that same Lean profile, not supplied
as witness metadata. A scalar or erased result consumes one output node and
one depth level. A run with `n` blocks takes `n + 1` reference transitions,
including the terminal return; the circuit checks that bound. This slice
admits no unused blocks or functions, rather than silently skipping them.

## What the proof checks

The public input is the existing statement `(P, B, I, O)`. Each digest is eight
little-endian 32-bit limbs embedded injectively in Goldilocks: 32 public field
elements in total, plus Aiur's function-channel and entry-index claim fields.
There is no separate public output vector or prover-selected claim acceptance bit.

The circuit performs the following work:

1. Check the expected profile digest against its fixed profile constant.
2. Read raw program advice from channel 0 and input advice from channel 1, key
   `[0]` on each. Check lengths before iteration and range-check every byte
   before placing it in the immutable memory tables.
3. Recompute `B = H_1(P || programBytes)` and
   `I = H_2(B || inputBytes)` using the specified domain-separated BLAKE3 gadget.
4. Parse and execute the entire straight-line image. Check exact headers,
   revisions, counts, scalar tags/ranges, local indices, arities, types,
   successor/frame contracts, and terminal/full-consumption conditions.
5. Encode the computed result as canonical `IXBO` bytes, check its size, and
   recompute `O = H_3(B || outputBytes)` against the expected output digest.

The parser and executor are fused for this subset. There is no host-decoded
program, supplied instruction transcript, or supplied output substituted for
these constraints. Byte-list and local-list pointers are internal to the
backend; guest equality never depends on physical pointer identity.

Field ingestion checks the eight-byte integer is below the modulus before
packing. Field egress uses a byte-decomposition hint with byte ranges,
recomposition, and canonicality constrained. Inverse hints are constrained,
including the zero case. Word addition constrains its wrapping result and
carry. The implementation reuses the existing IxVM BLAKE3/word gadgets and
MultiStark native Goldilocks/extension gadgets; no new Rust primitive was added.

## Host interface and key policy

`Ix/Ixby/Aiur.lean` exports `ScalarSystem.build`, `execute`, `prove`, `verify`,
and `verifyBytes`. It is deliberately a separate import from `Ix.Ixby`, so the
logical execution specification does not acquire a proving FFI dependency.

The builder takes explicit commitment/FRI parameters. Construct the verifier
from the approved interpreter and parameters; do not accept a prover-selected
system merely because it verifies a proof. `verify` reconstructs the claim
from the caller's expected statement and needs no program/input/output advice
and no reference evaluation. A valid proof still does not authorize its guest
program as an application's verifier or establish any source-level assertion.

`prove` preflights execution because the existing native proving FFI can abort
on a non-accepting execution. This host check provides ordinary error handling,
not cryptographic evidence; all defining checks remain in the circuit.
`verifyBytes` uses checked native proof decoding and exact canonical
reserialization, rejecting trailing bytes accepted by the underlying decoder.
Its 64 MiB cap is local transport policy, not an Exec semantic parameter.
These measures are not a complete untrusted-service denial-of-service audit.

Guest images and inputs can change without rebuilding this interpreter key.
The current capacities are compiled constants, so changing the profile changes
the key and profile/program commitments. Extending backend coverage or changing
the compiler/gadgets or proof parameters may also change the key. Supporting
more of the already-defined semantics need not itself change wire revision 0;
changing encoding or meaning does require the revisions described in the
encoding specification. The builder rejects codec revisions it does not implement.
No permanent key freeze or production activation has occurred.

## Checks and initial measurements

Build and run the isolated runner without unrelated integration suites:

```sh
lake build --wfail IxbyAiurTests
RAYON_NUM_THREADS=8 .lake/build/bin/IxbyAiurTests
RAYON_NUM_THREADS=8 .lake/build/bin/IxbyAiurTests --execute-only
RAYON_NUM_THREADS=8 .lake/build/bin/IxbyAiurTests --stats
```

The regular `IxTests` runner also exposes `ixby-aiur` for execution checks and
`--ignored ixby-aiur-prove` for the full proving suite. This backend suite runs
at runtime, not through the logical suites' elaboration-time `#guard` checks.

The current full suite passes 209 checks. It includes 39 successful proof
cases covering all 20 primitives, zero/nonzero inverses, comparison outcomes,
word overflow, immutable locals, and capacity boundaries. A fresh verifier
rebuilds the same key and verifies serialized proofs without execution advice.
Two cases additionally run through the Aiur source interpreter.

The 115 malformed/excluded artifact cases use matching raw commitments and
bypass host admission, exercising circuit execution rejection rather than
merely a host parser or stale hash. Additional checks reject out-of-range
field-valued advice, all four altered statement commitments, malformed proof
bytes, and an altered activation vector. These are not an exhaustive malicious
witness campaign or a formal constraint-soundness proof.

Initial local run on 2026-09-10: AMD Ryzen 9 7950X3D, 32 logical CPUs available,
eight Rayon threads, release build. Test parameters: `logBlowup = 2`,
`capHeight = 0`, `logFinalPolyLen = 0`, `maxLogArity = 1`, 64 FRI queries,
and zero commit/query proof-of-work bits. **These are test parameters, not a
reviewed security recommendation.**

- Full `--stats` suite: 7.16 seconds wall time, peak RSS 1,520,116 KiB
  (about 1.45 GiB), including both backend constructions and all checks.
- Per-case measured combined path: 128–162 ms. This includes fixture/reference
  evaluation, preflight, proving, serialization, decoding, and verification;
  it is not isolated prover or verifier latency.
- Serialized proof sizes: 2,003,486–2,217,860 bytes for this corpus.
- The system has 29 function circuits, five memory tables, and two fixed byte
  gadget tables. `--stats` prints per-table raw/padded rows, committed width,
  and cache hits. Its FFT-work estimate is a surrogate, not measured time.

Selected trace rows show both the fixed overhead and the changing workload:

| Table | Identity raw / padded rows | 64-block copy raw / padded rows | Committed width |
| --- | --- | --- | --- |
| `Bytes2` | 65,536 / 65,536 | 65,536 / 65,536 | 24 |
| `Bytes1` | 256 / 256 | 256 / 256 | 11 |
| `blake3_compress` | 40 / 64 | 168 / 256 | 925 |
| `memory[3]` | 500 / 512 | 2,338 / 4,096 | 12 |
| `ib_blocks` | 1 / 1 | 64 / 64 | 97 |

The identity image is 42 bytes; the copy-chain image is 987 bytes. Both use
18-byte inputs and 14-byte outputs. The latter's program-commitment preimage
is 1,035 bytes after framing and the profile digest, so it crosses a BLAKE3
chunk boundary. The fixed byte tables dominate this small corpus's FFT-work
estimate. These numbers do not compare CEK against a word machine, establish
full-program throughput, or estimate Flock's non-native field cost.

## Remaining backend work

Constrained whole-image tables, scalar branches, calls/returns, and bounded
continuations are now implemented by the separate [control slice](IxbyControl.md).
The [object slice](IxbyObjects.md) now implements constructors, projections,
and constructor cases. Closures/PAPs, general application, remaining primitives,
and byte values are still next. Unsupported features must keep failing closed.

The connection from accepted Aiur constraints to `Codec.Evaluates` still needs
a circuit representation/transition refinement theorem. The control slice's
logical frame/continuation lemmas, the object slice's conditional heap/rank
contract, and the existing reference byte-execution theorem do not supply that
circuit theorem. The shared compiler hoisting issue found in object testing
has a [tested hygiene/order repair](IxbyObjects.md#compiler-issue-found-and-repaired),
but no general compiler correctness proof. Compiler correctness,
lookup/memory arguments, field/hash
gadgets, and cryptographic assumptions must remain explicit in that work.
Security and privacy properties need review before deployment. Full verifier
workloads, Flock measurements, source-to-IxBy compilation certification, and
Stages 3/4 remain separate milestones. Compilatrix has not been modified here.
