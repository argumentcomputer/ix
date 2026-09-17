# IxBy runtime and proof boundary

IxBy is a strict functional execution language with a pure Lean reference
interpreter and a native paged Flock proof backend. The current artifact
contract is **IXBF/IXFI/IXFO format 1, semantics 2**. There is one current
semantic profile. Older revisions and the retired IXBY/IXBP formats reject.

Start with the [compiler handoff](CompilatrixRuntimeV2Handoff.md) for migration
and [canonical encoding](IxbyEncoding.md) for exact bytes.

## Language

Values are Nat, String, Bool, Word32, Goldilocks Field, its quadratic extension,
Bytes, immutable constructor values, closures/PAPs, erased values, persistent
arrays, and internal immutable byte builders. Scalars are unboxed values;
numeric conversion is explicit. Builders must be frozen before serialization.

Programs contain ordered constructor and function tables. A function contains
basic blocks with declared incoming local counts. Operations append a result
to the immutable local frame. Calls, tail calls, closure application, constructor
cases, Nat cases, and Boolean branches have explicit frame contracts. A Nat
successor case appends the predecessor; a zero case appends nothing.

Whole-image validation checks unreachable code as well as reachable code:
references, frame sizes, arities, unique constructor identities, and unique
case alternatives. Dynamic operand types and execution success remain runtime
checks. Function and block order is part of the committed artifact.

The reference interpreter executes `Eval`, `Apply`, `Return`, and `Halt` states.
Fuel counts logical transitions, including return/halt work. Native internal
microsteps implement a transition without changing its guest fuel charge.

## Current scalar primitives

The [58-opcode table](IxbyEncoding.md#primitive-opcodes) is explicit and stable
within revision 2. Nat arithmetic is exact within the declared bit limit;
subtraction saturates, division by zero returns zero, and remainder by zero
returns the dividend. Word32 arithmetic wraps at 32 bits. Field coefficients
are canonical modulo `2^64 - 2^32 + 1`. Byte conversions have exact lengths and
reject noncanonical field encodings. BLAKE3 operates on the complete byte value.

Conversions connect Nat, Word32, and Field without wrapper constructors.
Persistent array updates share unchanged paths. Builder append shares chunks;
freeze copies each output byte once. Byte slices share checked source ranges.
See the handoff for types, failure behavior, capacity checks, and native costs.

## Implementation map

| Area | Sources |
| --- | --- |
| Values and syntax | [Basic.lean](../Ix/Ixby/Basic.lean) |
| Primitive semantics | [Primitive.lean](../Ix/Ixby/Primitive.lean) |
| Whole-image and input validation | [Validate.lean](../Ix/Ixby/Validate.lean) |
| Functional machine | [Eval.lean](../Ix/Ixby/Eval.lean) |
| Current semantic limits and admission | [Profile.lean](../Ix/Ixby/Profile.lean) |
| Canonical byte boundary | [Codec/](../Ix/Ixby/Codec/) |
| Commitments and conditional composition | [Commitment.lean](../Ix/Ixby/Commitment.lean), [Claim/](../Ix/Ixby/Claim/), [Composition.lean](../Ix/Ixby/Composition.lean) |
| Trust gate | [Audit.lean](../Ix/Ixby/Audit.lean) |
| Rust functional reader | [ixbf/](../flock-stage3/host/src/ixby/ixbf/) |
| Constrained byte admission | [ixbf_decode/](../flock-stage3/host/src/ixby/ixbf_decode/) |
| Paged execution and collections | [paged_exec/](../flock-stage3/host/src/ixby/paged_exec/) |
| Complete recursive proof | [execution_tree/](../flock-stage4/recursive/src/execution_tree/) |

The trust gate checks 19 current theorem roots and a 711-theorem source frontier.
The reference suites run from [Tests/Ixby/Main.lean](../Tests/Ixby/Main.lean).
Three collection equations and the exhaustive opcode inverse theorem are
kernel checked; the runtime suites check the larger set of examples.

## Native proof boundary

The complete path proves original program/input byte commitments, constrained
parsing and code capture, references and constructor identities, input capture,
paged execution, Bytes output serialization, and the final commitment digest.
The receiver uses an approved profile, batch class, and tree geometry, then
accepts only the expected 32-byte statement digest and one root proof.
Native execution supplies untrusted advice.

The native backend has physical bounds beyond reference semantics: Nat128,
finite addresses and stack/frame limits, and a Bytes terminal result.
String primitive execution and structured terminal output are not implemented
by the complete proof path. The handoff lists exact current limits. Host
decoder acceptance alone does not establish proof admission.

Kernel-checked refinement from every native circuit to the reference machine
and the compiler's source-to-runtime representation certificates remain open
obligations. The [Exec contract](IxbyExec.md) keeps those assumptions explicit.
A successful execution proof does not itself prove compiler correctness.

## Retired implementations and measurements

The fixed-arena IXBY/IXBP profiles, Lean IxBy Aiur adapters, and native
`CompiledExec` adapters were removed in revision 2. Their sources and proof
measurements remain available at
[the final revision-1 commit](https://github.com/argumentcomputer/ix/tree/d4405b3ceb82e6d4cce19e48186f3272f8482e04).
General Flock proof algorithms, memory arguments, verifier replay, and the
paged backend remain active.

Historical measurements in the paged-execution and performance reports retain
their original artifact and setup identities. They do not measure revision-2
CSLib: that requires integrating the compiler changes, rebuilding CSLib, and
measuring the resulting image.
