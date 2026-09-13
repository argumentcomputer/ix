# Direct scalar IxBy execution in Flock

Status: a native, fixed-capacity scalar/control interpreter is connected to
canonical byte admission, all four commitments, and real direct Flock proofs.
The native constraint-to-reference refinement is unfinished. This is neither
a certified Stage 2 guest nor a closed Stage 4/compact proof.

## Setup and statement

`flock-stage3/host/src/ixby/exec::compile_exec_profile` accepts only a typed
`SemanticProfile`, `MachineCapacities`, and `PrimitiveSet`. It accepts no guest
image, proof, Stage 2 key/AIR, trace, or witness-dependent dimensions. A count
pass fixes the row domain and admits the pinned baseline PCS geometry before
the physical wiring is allocated. Compilation checks exact count/emit matrix
and I/O-layout agreement, with complete, unique prover-driver coverage.

`SemanticProfile` encodes the existing 68-byte `IXBP` envelope: zero wire and
semantic revisions, followed by the fourteen little-endian u32 parameters in
`Profile.parameters` order. The scalar adapter requires matching semantic and
physical bounds, zero constructor/Nat/String/byte-array bounds, value depth
one, and equal input/output byte capacities. This does not admit every value
or instruction of the broader crypto profile: the supported class explicitly
excludes byte scalars, constructors, closures/PAPs, and application. Those are
M4 work, not silently assumed compiler coverage.

The first proof corpus uses this fixed capacity:

| Parameter | Value |
| --- | ---: |
| Program bytes / functions / blocks per function / operands | 256 / 2 / 4 / 2 |
| Locals / saved continuations / call arguments | 4 / 2 / 2 |
| Input bytes / input values / output bytes | 64 / 2 / 64 |
| Physical transitions and initial semantic fuel | 24 |
| Outer row exponent / effective PCS exponent | 8 / 23 |
| Unique Boolean tables | 23 |

The canonical semantic parameters are
`[2,0,4,4,2,2,2,0,0,0,256,64,1,24]`.
Its approved native setup digest is
`41163b87f03675917ac93824d8b1c11ab0c489c2fc2e03abece34d11fa3255f7`.
This identity is regression-pinned, experimental, and not a security approval.

Protocol, backend implementation, semantic profile, physical capacity,
primitive registry, actual R1CS registry, circuit wiring, public template, and
private-input layout have separate identities, combined in an ordered setup
digest. The transcript domain is `ix:ixby:scalar-exec:v0`, further bound to
that setup digest. The Flock verifier also binds its registry, circuit, fixed
public words, and expected statement before deriving challenges. The upstream
pin remains `b310f35f35f68095537150a1c8c0a43caca9a29e`, without m37 patches.

## The constrained path

The only free artifact inputs are the program and input byte lengths and
their fixed padded banks. No output, state trace, or resolved action is free.

```text
canonical program bytes → whole-image decoder → fixed instruction table
canonical input bytes   → input decoder       → initial frame and fuel
                                                   ↓
  fetch → resolve operands → scalar dispatch → assemble action → control step
    ↑                                                              │
    └──────────── fixed count, constrained next state ────────────────┘
                                                   ↓
                      genuine terminal state → canonical output bytes
                                                   ↓
       profile + original program/input + derived output → P,B,I,O → S
```

The dynamic-access construction is bounded unrolling with full-width derived
selectors, not trace-specialized wiring or a scalable memory argument.
Every function, block, operand, local, frame and transition slot is emitted
from setup capacities. Actual indices/counts use all 32 bits. Unused data,
reserved metadata, inner columns and absent rows must be zero.

The whole-image decoder checks the canonical `IXBY` format, full byte
consumption, all declarations including unreachable blocks, function/entry
bounds, local/operand references, call arities, primitive registry/arity, and
destination local-count contracts. Self calls resolve to the containing
function. Scalar literals and `IXBI` values have exact tags, canonical
Goldilocks coefficients, bounded payload bits, and zero unused cells. The
byte reader constrains bank selection and offset advancement; a host parser's
acceptance bit is never an input.

Fetch reads the authenticated table using the current function/block and
checks its declared local count. Operand resolution selects oldest-first
locals or decoded constants and validates even unread live local cells.
The initializer checks the actual entry function/arity and starts with an
empty continuation bank. The control network checks every transition,
positive active fuel, exact decrement, branch Bool, call/return order,
continuation/local capacity, and absorbing terminal padding. A return
instruction is not itself a halt; empty-stack return takes another transition.
The output encoder requires a genuine halted state with an empty stack and
serializes its canonical scalar/erased value as `IXBO`.

The enabled existing crypto-v0 opcodes are
`0,3,4,5,9,10,13,14,15,16,17,18,21,22,23,24,25,26,27,28`.
They implement Word32 add/bitwise/compare/conversion, canonical base/extension
add/subtract/multiply/inverse/equality, and extension pack/projections. All
instructions execute the same dispatch/arithmetic network, including inactive
padding. Inverse candidates are the only additional free arithmetic advice:
canonicality, the full multiplication equation, and inverse-zero behavior
constrain them. No host inverse or privileged Stage 2 opcode is trusted.

The 14 machine tables share four canonical arithmetic tables internally.
Nine additional commitment tables share BLAKE3 compression, selection and
ROOT processing. The exact domain chain is unchanged:
`P=H(0,profile)`, `B=H(1,P||program)`, `I=H(2,B||input)`,
`O=H(3,B||output)`, `S=H(4,P||B||I||O)`.
Only the two F128 limbs of S vary publicly; the rest of the public template
is setup-owned. Neither output bytes nor an execution oracle are needed by
verification. This private-witness ABI is not a reviewed zero-knowledge claim.

## Proof API and hostile-advice evidence

`CompiledExec.prove(expectedS, programBytes, inputBytes)` generates a direct
Flock proof. `CompiledExec.verify(expectedS, proofBytes)` consumes only approved
setup, the externally expected full digest, and the proof. The native
`expected_statement` helper computes commitments; it does not establish
admission or execution. The final Ixon public-claim application API still
requires the composition described in [IxbyExec](IxbyExec.md).

The strict experimental proof envelope is `IXBYEX00`, the 32-byte setup
digest, and fixed-integer little-endian bincode encoding of the complete Flock
commitment/proof bundle. It admits at most 16 MiB, rejects trailing bytes,
requires exact re-encoding, checks the caller-approved setup before decoding
the proof fields, and has no legacy V1/V2 or gadget-proof fallback.

The real regression proved 39 executions under one setup: six scalar/erased
identities, both branches, calls/tail calls/self calls, mutual recursion with
different iteration counts, retained continuation depths 0/1/2, empty input,
and every enabled scalar opcode against the independent P3 arithmetic oracle.
Every fresh child verifier received only 32 bytes of expected S and the proof
on stdin, with a cleared environment and working directory outside the repo.
That branch neither constructs a guest nor hashes, decodes, or executes
private artifacts. Each complete proof was **296,091 bytes**; expected S and
reusable setup are separate. First proving took 0.597 seconds, subsequent
cases about 0.37–0.39 seconds, and cold child verification including setup
about 5.6–5.9 seconds on this local four-worker run. These are regression
timings, not a production benchmark or measured peak-RSS claim.

Changed profile/program/input/output commitments, setup/primitive changes,
rewritten setup headers, proof mutations, truncation, extra bytes and legacy
domains reject. Two additional proofs substituted fully recomputed, locally
valid decoder rows for different program/input bytes while retaining the
original surrounding circuit. Both fresh verifiers rejected with
`Wiring(Gkr(ProductMismatch))`. This checks real cross-table connections,
not only stale local outputs or host admission.

Ordinary tests also force validity outputs to zero after recomputing malformed
advice, mutate output/padding bits, and compare table matrices and poisoned
in-place buffers under both padding-elision hints. Every production driver
overwrites all inactive rows and columns, including recycled arithmetic and
hash buffers.

## Remaining proof boundary

`Flock/Control.lean` and `Flock/Trace.lean` prove decoded instruction/control
rules refine reference steps and finite canonical byte execution. They do
not yet derive those rules from the native matrices. The still-required
bridge includes bit/word/value representations, canonical byte parsing and
whole-image admission, fetch/operand/action/control constraints, fixed wiring,
primitive correspondence, output serialization, and commitment composition.
Real Flock acceptance is not a replacement for these theorems. Flock and hash
security assumptions remain explicit, as do compiler reflection and complete
terminal root discharge. M3 is not marked complete by this native slice.

```sh
cargo test --release --locked --manifest-path flock-stage3/Cargo.toml --workspace
RAYON_NUM_THREADS=4 cargo test --release --locked --manifest-path flock-stage3/Cargo.toml \
  --workspace ixby::exec::proof_tests:: -- --ignored --test-threads=1
```

The recorded real-proof run used a 32 GiB virtual-address limit and a
1,500-second timeout, completing in 258 seconds. The merge/manual CI tier
uses a separate 600-second timeout for this corpus; ordinary PR tests do not
start a prover. The six retained component proof tests remain separately
labelled and bounded.
