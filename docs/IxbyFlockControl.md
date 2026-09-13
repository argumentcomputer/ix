# Fixed-capacity Flock control component

Status: constrained ordered-frame control updates and real component proofs,
with a Lean decoded-control refinement and finite-trace theorem. The component
proofs described here are not Exec proofs. The newer
[scalar Exec network](IxbyFlockScalar.md) now connects this gate to canonical
bytes and constrained instruction/operand/primitive resolution and has direct
Flock proofs. The packing/table-to-decoded-rule proof remains unfinished.

## Representation and capacity

`flock-stage3/host/src/ixby/control` uses setup-owned capacities `L` locals,
`D` saved continuations and `A` arguments. The prototype admits `1 ≤ L ≤ 16`,
`0 ≤ D ≤ 8`, `0 ≤ A ≤ L`, with outer row exponent `3 ≤ nu ≤ 20`. These are
component factory bounds, not whole-pipeline resource or security approval.
They do not depend on a guest image, trace, branch, or Stage 2 configuration.

Each physical value has two F128 words: tag and payload. The reserved tags
are Bool=1, Word32=2, Goldilocks=3, extension=4 and erased=5. Physical zero
padding is distinct from both erased and Bool false. These are not the
canonical byte codec's tags. Apart from typed branch conditions, this control
component transports **opaque live cells**; it does not yet prove their scalar
canonicality or their correspondence to logical values.

Metadata uses four little-endian u32 lanes in one F128 word. A frame occupies
`F = 1 + 2L` words; a state occupies `N = 3 + (D + 1)F` words.

| State region | Contents |
| --- | --- |
| Word 0 | `(kind, remaining fuel, stack depth, 0)` |
| Next F words | Current frame: `(function, block, local count, 0)` and L value cells |
| Next two words | Returned value, or zero in an eval state |
| Last D frames | Live-prefix continuation bank, oldest first; last live frame is top |

Kinds are eval=0, ret=1 and absorbing halted=2. Ret/halted states require a
zero current frame. Every unused frame, header lane and value cell is zero.
All live counts use their full 32 bits and are bounded; high-bit aliases and
nonzero inactive data cannot bypass admission. Function/block bounds are not
checked by this component: authenticating them is part of instruction fetch
and whole-image admission.

An action occupies `4 + 2A` words. Its headers are
`(mode, target, alternative, callee)` and `(entry, arity, argument count, 0)`,
followed by a value cell and argument bank. Modes 1–5 mean resolved bind, call,
return instruction, tail call and branch. These describe control effects of
existing IxBy instructions; they are not new guest opcodes or trusted calls.
Unused fields and arguments are zero. Non-eval states require an entirely
zero action. Calls and tail calls require argument count equal to arity.

## Constrained transitions

The Boolean plan derives all selectors from constrained metadata. No free
one-hot selection or host-chosen wiring determines the current frame or stack
top. The slot wrapper connects the entire validity word to setup-owned zero.

- Bind appends one value and changes the current block, preserving old locals.
- Branch accepts only the exact Bool tag and payload 0 or 1. It changes the
  block and preserves the complete local frame.
- Call saves the current frame with the return block, pushes once and enters
  the claimed callee with the argument vector in original order.
- Tail call enters without pushing; a full continuation bank is allowed.
- A return instruction produces a ret state without popping or halting.
- Ret with a saved frame pops the last live frame and appends the return value.
- Ret with an empty bank performs the genuine terminal transition.
- Halted padding freezes the result, empty stack and remaining fuel.

Each non-padding transition requires positive fuel and decrements it exactly
once. Fuel exhaustion is rejection, not successful termination. Bind and
resume require room for the appended local; call requires continuation room.
A full caller local frame can take the call step, but cannot later resume by
appending a result. Whole-program block-contract admission must additionally
exclude such invalid return destinations, including unreachable ones.

Native row evaluation is total even for malformed advice. Tests bypass typed
witness helpers and recompute every internal/output bit before forcing a zero
validity word. The Boolean plan rejects that forgery. The native evaluator is
only an untrusted witness builder; it is never the verifier's acceptance rule.

The count pass materializes no table. Count/emit regressions compare counts,
I/O schemas, A/B matrices and repeated circuit identities. Maximum admitted
capacity synthesis is tested. Witness generation explicitly overwrites all
padding, including recycled buffers and absent rows with either elision hint.

## Logical proof boundary

`Ix/Ixby/Flock/Control.lean` models decoded frames in the same oldest-first
array order. `Resolves` checks actual copy/primitive/call/self-call operands,
constructor declarations/fields, and constructor/Erased projections;
`Entry` requires a real callee declaration, matching arity and checked entry
frame. `Step` additionally checks the current instruction and destination
block, including full-identity constructor cases and ordered field appends.
`Step.caseNatZero` and `Step.caseNatSucc` additionally model exact Nat cases,
preserving the old frame or appending the exact predecessor, respectively.
Primitive evaluation is an explicit semantic premise. The proved
`Step.reference` reaches the existing `Ix.Ixby.step` from those local premises,
without assuming correctness of a whole reference step or native evaluator.

`Trace.lean` adds fuel-indexed active transitions and genuine terminal padding.
It proves zero-fuel rejection, active fuel decrement, frozen halting states,
and finite-trace reference execution. `Trace.byte_execution` reaches the
existing `Codec.Evaluates` using exact program/input decoder equations,
initial-state admission, a bounded fuel value and exact output encoding. It
recovers program/input/output validation from the canonical encoder evidence.

These are decoded-rule theorems, **not native R1CS soundness theorems**. In
particular, the still-missing bridge must prove the physical tag/payload and
u32/padding representation, every table equation and inter-step connection,
and the instruction/operand/callee premises. Unauthenticated resolved actions
cannot supply `Step`. Native scalar/primitive correspondence and the complete
byte/commitment-to-trace connection remain required.

The exact IxBy audit now covers 333 public roots and scans 3,238 theorem
declarations, permitting only the existing standard Lean axioms. A concrete
six-transition call/Word32-add/return example is kernel proved; runtime tests
also check its canonical byte execution and the five-transition exhaustion.
Kernel-checked zero/successor Nat traces in `Tests/Ixby/Flock/Nats.lean` use
three transitions and reject two-step fuel. See the
[native Nat guide](IxbyFlockNats.md) for its separate physical implementation.

## Native evidence

Nine ordinary control tests cover positive updates, high metadata bits,
invalid modes/counts, live-prefix padding, reserved lanes, full banks,
noncanonical Bool conditions, modified next-state words, and unused columns.
They also cover count/emit equivalence and poisoned witness buffers.

The opt-in conformance setup fixes eight transitions, L=3, D=2, A=1 and nu=8.
Five different traces cover both branch outcomes, zero/one/two nested calls,
tail calls, and different amounts of halting padding. Each produced a
117,107-byte Flock bundle under the same compiled setup. The 768 bytes of
externally expected initial/final state are separate test public inputs, not
an Exec statement ABI or terminal proof-size claim.

Fresh child processes inherit no environment, run outside the worktree, and
receive only the expected endpoints and proof on stdin. They rebuild setup
and never receive actions or call the native evaluator. Mutated endpoints,
proof bytes, framing and domains reject. A recomputed, locally valid second
step with a changed current function is rejected by fresh verification with
`Wiring(Gkr(ProductMismatch))`, testing the actual inter-step connections.

The original scalar/control milestone passed 88 ordinary and seven opt-in
real-proof tests, including the separately documented scalar Exec corpus.
The merge-queue/manual CI tier runs those seven; ordinary PR tests do not start
a prover. The [workspace guide](../flock-stage3/README.md) records the expanded
byte/constructor/Nat suites and their separate opt-in proof tests.
All are bounded regressions, not production security review,
peak-resource measurements, or completion of the M3 execution gate.

```sh
cargo test --release --locked --manifest-path flock-stage3/Cargo.toml \
  --workspace ixby::control::tests::
RAYON_NUM_THREADS=4 cargo test --release --locked --manifest-path flock-stage3/Cargo.toml \
  --workspace ixby::control::proof_tests:: -- --ignored --test-threads=1
lake test --wfail -- ixby-flock-control ixby-flock-contract ixby-codec ixby-claim
lake build --wfail Ix.Ixby.Audit Tests.Ixby.Audit
```
