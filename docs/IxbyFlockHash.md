# IxBy Flock byte-authentication component

Status: implemented native constraints and conformance proofs; **not generic
execution**, not a Stage 2 verifier, and not a terminal compact proof.
This is part of M3's authenticated-byte boundary. The reference remains
`Ix/Ixby/Commitment.lean`; no logical instruction or commitment domain changed.

## Fixed setup, private contents

`BoundedBlake3::declare` takes a row domain and byte capacity. Hash emission
takes one canonical u32 length wire and the entire physical padded buffer.
Neither the length, bytes, nor a witness execution selects the wiring graph.
The current component supports capacities through 16 MiB. This synthesis
ceiling is not a production memory/security admission promise: the caller must
count rows and admit the resulting complete Flock geometry before compiling.

For capacity C, let B = max(1, ceil(C / 64)) and K = ceil(B / 16). One invocation
emits exactly B length/padding controls, B + K BLAKE3 compressions,
B + K - 1 nine-word selectors, and one ROOT-parameter conversion. Empty input
still has an active first block. Counting and compilation run the same emitter.

The control table computes the block position/counter, min(64, remaining)
length, CHUNK_START/CHUNK_END flags, and activity from constrained input bits.
All high metadata bits, length > capacity, out-of-range block positions and
nonzero bytes outside the live prefix produce a residual wired to a fixed
zero. An invalid wide position cannot exploit a wrapped 32-bit byte offset.
The fixed schedule supplies each position as a verifier-owned constant.

Each chunk retains a nine-word record: the seven inputs of its last active
compression and that compression's two-word chaining value. A Boolean
selector updates the record only for active blocks. It constrains every
selector bit: the full F128 selector must be exactly 0 or 1. No one-hot advice
or native branch selects the accepted output.

Adjacent physical subtrees are merged using ordinary BLAKE3 PARENT
compressions. If the right subtree is absent, a constrained selector carries
the left record. Odd physical subtrees are carried rather than duplicated.
The active chunks form a prefix, so this produces the normal BLAKE3 tree for
every admitted length, including non-power-of-two chunk counts. The final
compression uses the retained root Output, a constrained ROOT flag, and a
zero output counter. A chunk counter is never reused as a ROOT output counter.

## Exact statement chain

`ByteCommitmentSlots` accepts fixed profile bytes and program/input/output byte
capacities at setup. It does not accept those three artifacts or their hashes.
Its circuit computes:

```text
P = H(0, profile)
B = H(1, P || program)
I = H(2, B || input)
O = H(3, B || output)
S = H(4, P || B || I || O)
H(tag, payload) = BLAKE3("IxBy/commit/v0" || 00 || tag || payload)
```

The prefix is exactly 16 bytes, so digest and artifact concatenation is
word-aligned. Artifact lengths gain 48 bytes through a checked, constrained
u32 addition, not a host-computed length or modular wrapping. The source
length's high bits and carry overflow are rejected. The P/S lengths are setup
constants. Every final-block byte after the actual length is constrained zero.

All domains share the compression, nine-word selection and ROOT slots. Each
domain has its own capacity-specific block-control table; the three variable
artifact lengths share one add-48 table. The identity-program vector checks
every P/B/I/O/S limb in both `Tests/Ixby/Codec.lean` and native circuit tests.

The general `InputLayout` records fixed constants separately from ordered
private advice. `PublicLayout` records fixed constants and expected output
positions. Neither layout is artifact-decoded or computed by evaluating a
witness. The byte-chain proof tests publish only S's two F128 limbs. These
general layouts do not, by themselves, instantiate the approved Exec ABI or
its setup/claim admission checks.

## Constraint and proof evidence

The component tests cover every small byte length, full/partial blocks,
chunk boundaries, odd trees through eight physical chunks, and count/emit
identity. Direct R1CS tests recompute internal advice after hostile metadata or
padding changes before forcing the residual to zero. They test every relevant
metadata/padding bit, forged output/flag bits, prefix carry overflow and
unused table columns. Every new driver clears poisoned/recycled z/Az/Bz
buffers and lincheck stripes, including empty and partial active-row counts,
under both values of the upstream padding-elision hint.

At this component's original checkpoint, the native workspace had 53 ordinary
tests and five opt-in conformance tests. These real Flock proofs use the pinned
baseline Fast128/BLAKE3 path, nu = 8, with these component-only measurements:

| Relation | Fixed byte capacities | Flock bundle bytes |
| --- | --- | ---: |
| Unkeyed bounded BLAKE3 | 3,073 | 167,915 |
| Full byte-commitment chain | program 130, input 1,100, output 67 | 146,043 |

The hash proof reuses one setup for lengths 0, 1,024, 1,025, 2,049 and 3,073.
It rejects a proof whose first compression row is locally valid but uses a
different chaining value from its fixed circuit wiring. The byte-chain proof
reuses one setup for the golden identity bytes, empty buffers and full buffers.
It also rejects changed public digest limbs, changed fixed profile bytes,
changed capacity with the same rounded buffer geometry, wrong domains,
modified proof bytes, truncation and trailing bytes.

The byte-chain's isolated verifier child receives only the expected 32-byte S
and proof on stdin, has no inherited environment, and runs outside the source
worktree. It rebuilds the fixed setup/public template and never executes gates,
receives private artifacts, runs IxBy, or calls the prover. A changed expected
digest is also rejected in a fresh child. This is isolation evidence for the
byte-binding component. The separately integrated scalar Exec relation has its
own [execution proof evidence](IxbyFlockScalar.md).

Proof sizes exclude the independently supplied 32-byte expected digest and
reusable setup. Fixed public constants are reconstructed, not transported by
the prover. These are full Flock component bundles, not FFLONK body sizes or
evidence for the 1,024-byte terminal target. Tests use four Rayon workers,
a 32 GiB virtual-address limit, and bounded timeouts. No peak-RSS, large-profile
capacity, production cryptographic-parameter or setup claim follows.

## Explicit packed-word compression backend

The `flock-stage3/host/src/packed_blake3` component implements the explicitly
selected `Blake3Backend::PackedWordsV0`, not a silent replacement of the
default compression slot above. Its raw inputs and sixteen u32 outputs have
exactly the same semantics as the pinned compression gate. Counter, length and
flags are raw words here;
the surrounding bounded-hash construction must supply hash-mode constraints.

State columns `[v0..3]`, `[v4..7]`, `[v8..11]`, `[v12..15]` each occupy one
F128 word. Four G operations execute in parallel across independent u32
lanes. Fixed lane permutations switch between column and diagonal rounds.
One setup-owned linear table routes the original sixteen message words to
all seven rounds. Every invocation emits exactly 84 additions, 60 XOR/rotate
operations, 42 lane permutations and one schedule row, independent of values.

The addition table uses `c_i = XOR(p_0,...,p_(i-1))` and
`p_i = (x_i+c_i)*(y_i+c_i)`. Over Boolean GF(2) witnesses,
`c_(i+1) = c_i+p_i = x_i*y_i + c_i*(x_i+y_i)`, the full-adder carry.
Output is `x_i+y_i+c_i`; dropping the final carry gives wrapping u32
addition. Each lane starts with an empty carry. Linear rows use `f*f=f`
for Boolean linear forms, avoiding a constant-one pin. Padding still has
zero A/B rows and C=I, hence must be zero. This mathematical explanation and
native differential tests are not an extracted-table Lean refinement proof.

The ten tables have a padded combined width of 8,192 bits. Standalone proving
uses explicit `nu=9` to admit the pinned Fast128/m22 floor; it does not switch
to a development query schedule. Poisoned-buffer tests compare the in-place
driver against complete matrices for empty, partial and full counts.
Every bit of each table row is mutation-tested, including carries and padding.
Complete composition tests cover 64 arbitrary private CV/message/parameter
vectors and independent hashes for every single-block length 0–64.

Two real compression proofs use identical setup and verify in fresh child
processes receiving only the four expected F128 output words and the bundle.
Each bundle is 114,027 bytes; the separately supplied output is 64 bytes.
Expected-word, transcript-domain and canonical transport mutations reject;
a recomputed valid addition row substituted into the wrong wiring fails
Product-GKR. The child rebuilds only the fixed component setup, not any
message or native hash evaluation. This establishes component conformance,
not an execution statement, full multi-block hash proof or compact terminal
proof. Formal primitive/composition refinement remains outstanding.

The [original paired terminal measurements](../flock-stage4/census/packed-blake3-components-v0.json)
show much smaller matrix-root evaluation components, but dense witness width
rises from 92 to 632 words per compression. Nineteen shared invocations need
`nu=11`. Component savings alone do not measure total wiring/PCS/fold costs.

`BoundedBlake3::declare_with_backend` and
`ByteCommitmentSlots::declare_with_backend` now use this compression choice
through the complete fixed block/tree schedule. The five commitment domains
share all ten word-table slots and the exact same fixed IV wire. Their default
constructors remain legacy-compatible. Generic drivers inspect the explicit
compression variant and cover every declared slot; the old single-slot getter
is legacy-only and rejects use with the packed variant.

New count/native-hash differentials cover capacities 0, 65, 1,025, 3,073 and
7,169, with private lengths around block/chunk/odd-tree boundaries. Count and
compiled registries/layouts agree. All 39 scalar/control Exec corpus cases
also have direct packed-backend Flock proofs under one setup, each with a
339,563-byte bundle; fresh verification needs only approved setup, externally
expected S and proof. A locally valid packed addition with broken global wiring
is rejected. This is integration/native proof evidence, not the still-missing
formal hash/machine refinement or a terminal FFLONK proof. The opt-in compiler
binds a new backend/key identity; the existing default setup and exact commitment
function are unchanged. Whole Stage 4 sizing is recorded separately in the
[integrated report](../flock-stage4/census/exec-packed-blake3-root-closed-v0.json).

## Missing correctness and execution obligations

The native gates use one Boolean synthesis description for matrices and row
generation. That helps conformance, but is not a Lean proof of the generated
tables. The BLAKE3 compression primitive, Boolean selector/length/control
refinements, tree construction and native-to-Lean extraction still need their
explicit constraint-semantics proofs. Cryptographic Flock soundness and BLAKE3
binding remain distinct assumptions; no finite-hash injectivity axiom is used.

Byte commitment alone accepts a matching commitment to malformed bytes. The
interpreter must still constrain canonical decoding and admission of all
functions/blocks, instruction fetch, operands/types, local/frame transitions,
calls/returns, branch conditions, exact fuel, terminal state and canonical
output serialization. Only then can the finite constrained run connect to
`Codec.Evaluates`. The final application verifier must still receive and bind
the explicit canonical Ixon claim; a prover-selected S is not its replacement.
Stage 4 replay/root closure and the compiler-reflection handoff are unchanged
remaining milestones.
