# Native bounded closure and application execution

Status: the explicit application setup implements immutable closures/PAPs,
let/tail application, under/exact/over-application, and mixed resume/apply-rest
continuations. Canonical I/O, all existing crypto primitives, constructors and
optional exact Nats compose with this path. This is a bounded native Stage 3
implementation, not a compiled Stage 2 guest, native refinement theorem, or
terminal SNARK.

## Explicit setup boundary

`compile_exec_application_profile(profile, capacity, values, primitives, backend)`
accepts `values: (ByteCapacity, ObjectCapacity, Option<NatCapacity>)`.
It accepts no guest image, input, trace, heap, or proof. The approving verifier
chooses the capacities and implementation. `CompiledExec::applications()`
reports that choice; a proof cannot enable it.

Without Nat, use `SemanticProfile::objects`; with Nat, use
`SemanticProfile::nat` with the matching `Some(objects)` and magnitude bound.
The existing semantic v0/v1 wire formats already define closures and PAPs:
this upgrade introduces no guest opcode, wire tag, primitive, or revision.
Strings remain excluded. The native application, constructor, byte, scalar and
Nat factories remain distinct approved setup classes. Existing factories still
reject application instructions and PAP values, with their prior keys unchanged.

This setup requires equal argument and operand capacities `A`, with
`1 ≤ A ≤ 4` and `A ≤ locals ≤ 16`. The existing prototype bounds also apply:
up to four functions, eight blocks per function, eight continuations, 64
transitions, and 512-byte program/I/O buffers. The explicit object bounds permit
up to four constructor declarations, depth three and 32 forest nodes; expanded
input-tree slots must fit 64 and object allocations 128. These are factory
limits, **not measured full-pipeline resource or security approvals**. A declared
primitive still needs enough operand capacity for its arity.

The program table has a separate final slot for an application's function
operand, in addition to its `A` arguments. That operand is decoded in its actual
wire position, before the argument vector, and has a distinct fixed byte-literal
allocation. It does not consume an argument slot or alias another literal.
Whole-image admission checks every closure's function and capture count,
every function operand and every let destination, including unreachable code.

## Immutable values and authenticated dispatch

PAPs share the setup-fixed immutable object arena with constructors. A physical
PAP cell has tag 9 and a canonical u32 arena index, not a host pointer or digest.
This physical tag is distinct from the canonical value-wire tag 2.

| Record kind | Header fields |
| --- | --- |
| Constructor | declaration index, field count, presence bit 64, bit 65 = 0 |
| PAP | function index, capture count, presence bit 64, bit 65 = 1 |

All remaining header bits and inactive fields are zero. A PAP names an existing
function and captures strictly fewer values than its arity. Function headers
are wired from canonical program decoding into input validation, dispatch and
output serialization. This validates PAPs even when they are unused inputs or
nested inside constructors/captures.

Input trees use finite decoder-owned preorder allocations. Runtime constructor
and PAP records may reference only earlier object allocations, preventing cycles.
Their fields retain canonical typed values, including bytes, Nats and other
objects. A step owns one fixed object allocation; non-allocating steps preserve
the constructor dispatcher’s record, and a new PAP supplies a constrained
replacement. No arena record is free host advice.

Output traverses the authenticated arenas in preorder and emits the existing
inline tree wire format. Shared values are serialized once per occurrence.
Depth, total nodes and output bytes are checked across constructors and PAP
captures together; returning an oversized tree is not successful execution.

## Control and exact fuel

The existing physical state width is unchanged. The explicit application table
adds control kind 3: an apply state uses the current frame's value bank for
arguments and the return-value cell for the function. Its function/block
positions are zero. Saved frame metadata distinguishes ordinary resume frames
from nonempty apply-rest argument vectors. Counts, reserved bits and padding
are constrained in both forms.

- A closure binds an immutable PAP immediately.
- Let-application saves the caller's resume frame; tail-application does not.
  Both enter a distinct apply state and consume one transition.
- Empty application returns its value unchanged, including non-functions.
  Erased absorbs nonempty application; other non-PAP values reject.
- Under-application captures the old values followed by the new arguments and
  returns a new PAP.
- Saturation enters the authenticated callee with its exact arity. Excess
  arguments become an apply-rest continuation.
- Return pops the top continuation. Apply-rest runs before any older caller
  resume; a resume appends the result after the saved oldest-first locals.
- Only a return with an empty continuation stack halts. Every active step,
  including apply and terminal return, consumes exactly one fuel. Absorbing
  halted padding preserves fuel; exhaustion is rejection.

The action table uses additional internal modes 6–9 and a bounded rest-vector
bank. These are constrained transport between instruction/application
resolution and control, not new guest instructions or prover-supplied actions.

## Regression evidence

Nine ordinary tests cover the new dispatch and control matrices, recomputed
malformed metadata, reserved bits, full indices, capture/argument order,
backedges, forged outputs, overflow, and poisoned/recycled witness padding.
The execution corpus has 27 cases under one setup, with exact remaining-fuel
assertions, canonical closure/object/byte results, repeated under-application,
and nested direct-call/resume/apply-rest interactions. Additional execution
negatives cover unread PAPs, unreachable closures, wrong types and bounds,
non-callables, oversized output trees, and old-factory rejection.

Separate revision-1 execution checks transport a 96-bit Nat through a PAP into
exact addition, preserve an empty-application Nat literal, and reject Word32
substitution. They do not establish a whole application-capable Nat proof corpus.

`Tests/Ixby/Flock/Applications.lean` independently encodes and executes all 27
cases and checks their minimal fuel. Three whole-statement goldens are shared
with Rust: closure creation, over-application with a saved caller, and an empty
byte-literal application. Its 31 checks include a fixture-count check.
Four kernel-checked examples pin over-application's
8/10-step successes and 7/9-step exhaustion.

The full ordinary Rust regressions passed: 149 Stage 3 tests and 266 Stage 4
tests, with 18 and 39 opt-in tests respectively. Formatting and strict Clippy
passed in both workspaces. All 12 named IxBy Lean suites passed, as did the
warning-as-error build and the existing 333-root production audit.

The proof fixture fixes three functions, three blocks each, four locals,
three continuations, two arguments, 12 steps, 256 program bytes, 192 I/O bytes,
33-byte arrays, and object bounds `(2, 3, 7)`. Its setup is
`9ef161680676f2929322a59c5804f6c7cf3d3f8e3e36e61960c7d3f85df42953`,
with `nu=12`, PCS `m=24`, 38 tables and largest table `log_k=22`.
The application transcript domain is `ix:ixby:application-exec:v0`;
protocol, implementation, capacities, registry, circuit and public layout
are bound into the setup identity.

The opt-in proof test passed all 27 cases with fresh isolated digest-only
verifiers. It also recomputed locally valid rows with changed captures, excess
arguments and popped apply-rest values, then checked cross-table wiring
rejection: all three were rejected with `Wiring(Gkr(ProductMismatch))`.
Proof-byte/digest mutations and old-key substitution, including a renamed
setup header, also rejected.

Every complete serialized Exec proof was 405,243 bytes. With four Rayon
workers, the unchanged 64 GiB virtual-address cap and a 1,800-second timeout,
the full run completed successfully in 771.06 seconds. GNU `time` reported
30,121,140 KiB maximum RSS (about 28.73 GiB); this is not aggregate simultaneous
prover-plus-verifier memory. Per-case proving took 4.223–15.580 seconds and
fresh-process verification 10.223–38.922 seconds. Builds and ordinary
regressions overlapped part of this run, so these are observed regression
measurements, not dedicated performance benchmarks or guest-size estimates.

The earlier decoded-control/trace theorems cover the first-order fragment,
not these new application continuations. A native constraint-to-reference
bridge, higher-order logical trace extension, source compiler certification,
full Stage 2 guest sizing and complete terminal closure remain open. Native
proof acceptance and independent reference agreement do not close those gaps.
No paid CI tier or resource budget was expanded.

```sh
cargo test --release --locked --manifest-path flock-stage3/Cargo.toml \
  --workspace application -- --test-threads=1
RAYON_NUM_THREADS=4 cargo test --release --locked --manifest-path flock-stage3/Cargo.toml \
  --workspace ixby::exec::application_proof_tests:: -- --ignored --test-threads=1 --nocapture
lake test --wfail -- ixby-flock-applications
```
