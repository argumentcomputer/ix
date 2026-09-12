# IxBy: functional bytecode and execution semantics

IxBy is an experimental functional bytecode execution layer with CEK-family
control, a pure Lean reference model, and three bounded Aiur/FRI interpreters.
Its intended role includes certified execution of Ixon programs, but no
Compilatrix lowering or source-to-IxBy certification is implemented here.
The ISA, profiles, wire format, and proof parameters remain provisional.

Existing production claims, Stage 1/2 keys, Flock relations, and deployment
policies are unchanged. There is no new Flock interpreter or terminal SNARK.
This document describes the current architecture and semantic boundaries;
the [design roadmap](../plans/ixby-plan.md) records longer-term integration work.

## Implementation map

- [Basic.lean](../Ix/Ixby/Basic.lean), [Validate.lean](../Ix/Ixby/Validate.lean),
  and [Eval.lean](../Ix/Ixby/Eval.lean): immutable values and locals, indexed
  operands, whole-image admission, explicit continuations, and total
  fuel-bounded execution with determinism and fuel-extension theorems.
- [Primitive.lean](../Ix/Ixby/Primitive.lean), [Goldilocks.lean](../Ix/Ixby/Goldilocks.lean),
  and [Blake3.lean](../Ix/Ixby/Blake3.lean): closed, typed reference primitives.
  Field arithmetic and hashing remain pure, without importing an FFI oracle.
- [Profile.lean](../Ix/Ixby/Profile.lean), [Codec/](../Ix/Ixby/Codec/), and
  [Commitment.lean](../Ix/Ixby/Commitment.lean): bounded crypto-profile admission,
  strict canonical artifacts, checked byte execution, and domain-separated
  commitments. See the [encoding specification](IxbyEncoding.md).
- [Composition.lean](../Ix/Ixby/Composition.lean): conditional source/target
  refinement and composition. Its concrete example is not an IxIR₀ lowering
  theorem or general compiler certification.
- [Aiur.lean](../Ix/Ixby/Aiur.lean): the host adapter for
  [scalar](IxbyAiur.md), [control](IxbyControl.md), and
  [object](IxbyObjects.md) interpreters. It is a separate import from the pure
  `Ix.Ixby` specification.
- [Aiur/Refinement.lean](../Ix/Ixby/Aiur/Refinement.lean) and
  [Aiur/Objects/](../Ix/Ixby/Aiur/Objects/): kernel-checked frame, heap, memory,
  store, and parser-component contracts. The
  [object proof guide](IxbyObjects.md#formal-contract-and-remaining-bridge)
  owns the detailed premises and remaining boundaries.
- [Audit.lean](../Ix/Ixby/Audit.lean): exact standard-axiom allowances for 314
  public theorems, plus a source-module scan of private/generated theorems and
  global axioms. CI builds the audit and its negative regression tests.

Tests mirror the implementation under `Tests/Ixby/`: reference, crypto, and
codec suites at the root; backend suites under `Aiur/`; object conformance
tests under `Aiur/Objects/`. The parser suite delegates to focused reader,
identity, uniqueness, declaration, loader, program-prefix, code-header, and
operand modules under `Aiur/Objects/Parser/`, sharing one full and one pruned
compilation per run.

`Tests/Ixby.lean` collects the suites. Each standalone backend runner has a
`Main.lean` module; executable names and `IxTests` selectors remain stable.
All runtime suites use LSpec. Fixture compilation and check construction are
deferred IO actions, so unrelated suite selection does not run IxBy checks.
`Tests/Ixby/Aiur/Common.lean` shares artifact/proof helpers and reuses the
repository's Aiur test parameters, while preserving backend-specific admission
and rejection-stage checks.

Cryptographic execution uses hand-authored guest programs. Actual IxIR₀
lowering and source-to-IxBy refinement belong in a later Compilatrix companion
change; target execution proofs alone do not claim source correctness. IxIR₀
remains the semantic anchor, and no native ownership/compiler refactor is
required for this model. Extracting a shared pure lowering phase requires its
own interface and preservation proofs.

## Eval and Exec are different claims

Keep `Eval` for source-level interpretation and introduce a separate,
versioned `Exec` for successful Ixby execution. The existing `Claim.eval`
encoding must not silently acquire machine-execution semantics. In particular,
`#ixeval` currently computes output using kernel-style `Meta.reduce`;
Compilatrix's source runtime is weak call-by-value, not full normalization.
Relating those observations requires an explicit theorem and a stated domain.

A proposed Exec statement names:

- the Ixby semantic profile, including primitive semantics;
- the closed program image, including entry point, code, immutable data,
  imports/dependency closure, and representation-sensitive ABI information;
- the canonical input and output commitments;
- the input/output ABI when it is not already uniquely fixed by the image.

These are semantic identities, not FRI/Flock/curve identities. Backend and
security-parameter authorization belongs to the proof wrapper and verifier
policy. Different sound backends should establish the same Exec proposition.
An opcode schema, canonical encoding, hash domains, claim tag, and migration
must be specified together before any production claim format changes.

Exec proves an execution, not that the selected program means what an
application wants. Application verification must check the expected program,
inputs and result; Stage 3 must additionally bind the approved Stage 2
key/allowed-key policy. An arbitrary valid Exec proof is not a certificate of
an arbitrary source assertion.

## Composition and compiler certification

The desired derivation is conceptually:

```text
Compile(C, source S, options O) = bytecode B
Check(exact compiler-correctness theorem for C, O, ABI, semantics)
Exec(B, encode(input), encodedOutput)
decode(encodedOutput) = output
----------------------------------------------------------------
SourceEval(S, input, output)
```

All occurrences of C, S, O, B, input, output, and ABI must refer to exactly
the same committed objects. A Check claim that merely establishes that some
declaration is well-typed is insufficient: bind its actual theorem type and
all hypotheses to this derivation. Permitted axioms and assumptions must be
explicit; unrelated Check claims cannot discharge them. The final transition
to the existing kernel-oriented Eval meaning also needs its semantic bridge.

`ExecutionRefinement` states the direction needed here: a successful target
execution has a decodable result and implies a source execution with that
result. Existing forward-simulation theorems typically start with a source
execution and construct a target execution. Reversing that implication needs
more evidence. `refinement_of_forward_and_termination` gives one route, with
source termination, target resource adequacy through a successful forward run,
and target determinism all explicit. It does not discharge these obligations
for Compilatrix.

There are two useful certification routes:

1. A theorem about a fixed compiler, plus a proof of its exact compilation
   result. If the compiler itself runs as Ixby, its image must be connected to
   the certified source compiler by an already established bridge.
2. A per-artifact theorem `Refines(S, B, ABI)`. In this case proving the
   compiler's execution is optional for semantic correctness: the checked
   artifact theorem already binds source to target. Compiler execution can
   still be proven for provenance or reproducibility.

Compilation evidence can be reused for multiple executions of B. Bootstrap
must be finite and non-circular: pin/independently certify the first compiler
image or start with per-artifact checking. Do not use an Exec proof to justify
the very compiler-image certificate on which that proof's source meaning
depends.

Current aggregation folds CheckEnv claims. It does not automatically implement
this mixed Eval/Exec/Check inference merely by placing proofs in one list.
A dedicated, reviewed composition relation is a separate implementation gate.

## Execution-model rationale

The initial exploration considered the following models. The functional
direction is selected for planning; remaining measurements refine that design
rather than requiring full implementations of every candidate:

| Candidate | Potential benefit | Cost/risk to measure |
| --- | --- | --- |
| CEK or related reduction machine | Direct source correspondence, persistent environments and sharing | Environment/continuation traffic, application/recursor dispatch; whole-state CEK stepping does not automatically memoize subevaluations |
| Compiled functional bytecode | Direct calls, explicit local operands and data layout, preserved pure-function boundaries | Compiler proof obligations, closures/PAP fallback, lookup traffic for locals and objects |
| Word/register machine | Simple bounded-arity instructions and conventional control flow | Register read/write consistency, lowered calls and allocations, loss of memoization, field operations expanded into word operations |

Compilation, memory organization, and arithmetization are separate choices.
Compiled bytecode need not emulate a CPU or mutable RAM; a reduction machine
need not cryptographically hash every intermediate pointer. Aiur's executor
already memoizes function calls by arguments and interns stored values. If a
new interpreter includes a changing clock, continuation, output accumulator,
or irrelevant heap state in every memo key, shared pure computations may no
longer reuse queries. Neither a CEK label nor bytecode syntax guarantees reuse:
the evaluation relation and lookup keys must expose it correctly.

The current logical target is a compiled functional machine: immutable
objects, local SSA-like operands, saturated direct calls, explicit case
dispatch, and closure/PAP operations only where needed. Compilatrix's IxIR1
is a relevant starting point. A new pure intermediate phase or a distinct zk
pipeline may separate its computational features from ownership lowering;
IxIR₀ remains the semantic anchor. Native reference counting, reuse credits,
byte layouts, and calling conventions should not become proof-machine obligations
without a measured benefit. Erasing such operations still needs an explicit
representation/observation refinement; it is not justified for arbitrary
extern effects or observable pointer identity.

### Logical bytecode and machine

`Program` contains an entry function, a function table, and a constructor table.
Each function declares its arity and entry block. Each block contains one
instruction and the exact number of incoming local slots. Indices are `Nat`;
there is no implicit word truncation. Constructor identity is a logical
256-bit declaration/block name plus an inductive member and constructor tag;
it is not a runtime pointer or a hash computed by this model.

| Operation | Semantics |
| --- | --- |
| `letOp` | Evaluate an operation and append its result as the next local slot; then enter the named successor block. |
| `copy`, `primitive`, `construct`, `project` | Pure value operations; constructor fields preserve their declared order. |
| `call`, `callSelf` | Exactly saturated calls, saving the caller's function, successor block, and locals. |
| `closure`, `apply` | An immutable PAP holds a function and fewer arguments than its arity. Application may return a larger PAP, enter the function, or apply remaining arguments to its result. |
| `ret` | Return through the current continuation; an empty continuation terminates with one structured value. |
| `tailCall`, `tailCallSelf`, `tailApply` | Transfer without adding a caller-resume frame. Over-application may still need a continuation for remaining arguments. |
| `caseCtor` | Match the full constructor identity and append its fields to existing locals. Missing alternatives fail. |
| `caseNat` | Match a Nat scalar; the successor branch appends its predecessor. |
| `branch` | Branch on a Bool scalar, not arbitrary numeric truthiness. |

Local frames, fields, captures, and the continuation stack use arrays in the
reference implementation. Locals are absolute, append-only slots: binding does
not renumber existing locals. There is no linked-list variable-name search,
guest reference counting, mutable heap, pointer comparison, or output-word stream.
Constructor/PAP values are finite logical trees. The experimental object
backend now uses immutable field lists with checked ranks for constructors;
PAP storage and the complete constrained-representation proof remain open.

Calls are not recursively evaluated by an unmetered host evaluator. `Control`
explicitly alternates between block evaluation, application, and returning.
A normal return instruction and the subsequent terminal return transition each
consume fuel. All recursive calls, continuation handling, and over-application
therefore participate in `run`'s fuel budget. Only a finite run reaching a
terminal return establishes `Evaluates`; exhaustion never accepts.

Whole-image admission checks unused functions and unreachable blocks too:
entry arities, local bounds, successor frame sizes, call/capture counts,
constructor identities/field counts, and unambiguous alternatives. Runtime
checks reject primitive type errors, invalid projections, missing constructor
cases, and application of non-functions. Empty application is identity;
erased values absorb nonempty application and projection. Bool unboxing and
Nat literal/constructor coherence require explicit source refinement; the
machine does not silently equate these representations.

`Limits` bounds functions, constructors, blocks per function, local and operand
counts, continuation depth, total input nodes, Nat bit lengths, UTF-8 string
bytes, and byte-array lengths. Input validation shares one node budget across the entire forest,
including nested fields and captures. Scalar caps also apply to literals and
primitive results. Generated object counts, tree readback costs, and prover
allocation peaks are not covered by a complete RAM model. Limits are explicit
execution parameters, not permanent wire widths or production recommendations.

These are logical transitions, not constant-cost circuit instructions. Operand
vectors, case selection, arbitrary-precision arithmetic, string operations,
program admission, and object representation have additional costs. Program
and constructor lookup implementations remain reference code, not optimized
or cryptographically authenticated ROM tables.

### Current scalar primitives

Nat addition/multiplication are exact, subtraction truncates at zero, division
by zero returns zero, and modulus by zero returns the dividend. Nat equality
and ordering produce Bool scalars. String append and equality use Lean strings;
string length counts Unicode scalar values, whereas capacity counts UTF-8
bytes. Primitives check arity, operand tags, and input/result scalar limits.

Word32 is a separate scalar tag, with arithmetic modulo `2^32`, bitwise
operations, unsigned comparisons, and explicit little-endian byte conversions.
Logical shifts by at least 32 produce zero; rotations use the count modulo 32.
Byte operations check indexing and slicing bounds without wrapping or silent
truncation. There are no IO or arbitrary extern primitives.

Word32 does not change the execution architecture: a primitive returns a new
value into an immutable local frame; it does not mutate a machine register.
Calls, closures, constructors, and continuations remain functional. Function,
block, and local identities are still distinct logical indices, not Word32
guest values. Nat semantics are unchanged. Bounded parsing, bit manipulation,
and verifier counters motivate this scalar family; the exact exposed operation
set is provisional, not a requirement of CEK control. Field/hash work need not
be decomposed into guest word operations.

### Cryptographic primitives

The reference layer now includes canonical Goldilocks elements modulo
`18446744069414584321` and quadratic extension elements `c0 + c1*X`, `X² = 7`,
matching the existing verifier's basis. Arithmetic reduces before narrowing;
base and extension inverses map zero to zero. Field byte decoding requires
exactly eight little-endian bytes representing an integer strictly below the
modulus: noncanonical values are rejected, not silently reduced. Word-to-field
conversion is explicit and injective over Word32.

The BLAKE3 primitive takes bytes and returns 32 bytes, with unkeyed hashing only.
Its reference implementation is kernel-reducible and uses no host hash oracle.
Tests compare it against the Rust library across all lengths 0–129 and larger
block/chunk/tree boundaries through 65,536 bytes. This is conformance evidence,
not a proof of collision resistance or constraint soundness. Hashing and other
variable-size operations still require bounded work in the proving backend.

The first scalar backend reuses the existing Aiur gadgets in
`Ix/MultiStark/Goldilocks.lean` and `Ix/IxVM/Blake3.lean` for field operations
and artifact authentication. Guest byte/hash instructions remain unsupported
by that slice. Any focused comparison must equalize those primitives. A CEK
machine with native field primitives versus a word machine synthesizing them
is not a comparison of control models.
Goldilocks still needs non-native constraints under Flock's F128 backend.

Primitive semantics, operand encoding, output encoding, failure cases, and
memory access must be exact. Hints may supply values, but accepted execution
must check their defining relations. No arbitrary host or compiler oracle
may produce trusted outputs. Defining the reference primitive does not implement
or certify its accelerator, so this baseline cannot establish proving efficiency.

### Experimental crypto profile

`Profile` admits the same functional control with Bool, Word32, canonical base
and extension fields, and bounded bytes. It explicitly rejects Nat/String
operations, literals, and nested runtime values, and rejects `caseNat`, even in
unused code. The broader reference evaluator still supports those operations;
their exclusion is an initial proving-fragment choice, not their removal from
the permanent execution plan. Raising a capacity cannot re-enable them.

Profile execution checks the reference admission rules, a step bound, and
shared node/depth limits on inputs and outputs. Numeric profile parameters
must fit 32 bits; this is an experimental metadata constraint, not Word32-based
control. `programBytes` and `valueBytes` are enforced by the codecs, including
artifact headers, but not by logical `Profile.execute` alone. All fourteen
parameters are serialized and bound by the profile commitment. Decoding a
profile does not authorize its capacities or security policy.

### Canonical artifacts and byte execution

The [experimental encoding specification](IxbyEncoding.md) defines exact
little-endian widths, explicit instruction/primitive tags, raw byte scalars,
inline constructor/PAP trees, and separate profile/program/input/output
envelopes. It covers the entire program image, including unused functions and
unreachable blocks. Unknown tags, trailing data, noncanonical fields, invalid
references, oversized counts, and narrowing overflows are rejected. Input and
output trees share their respective node budgets across all nested values.

Successful decoders return a value with its checked exact re-encoding equation;
general encoder/decoder inverse and injectivity theorems remain outstanding.
`Codec.execute` additionally retains successful profile-execution and output
encoding equations. Its `Execution.reference_evaluates` theorem connects this
byte boundary to the original functional execution relation. This does not
assume an arbitrary host acceptance oracle.

Domain-separated BLAKE3 commitments bind profile, full program, input, and
output. Constructing a statement from well-formed artifacts does not establish
that its output was executed. `Commitment.executeAndCheck` performs reference
execution and checks all expected commitments; it is not a STARK verifier or
application program-authorization policy. Hash security, constrained admission,
authenticated lookup, and circuit/reference correspondence remain separate
obligations. Wire/semantic revision 0 and the commitment domain are experimental,
not changes to production claim encodings or permanent interpreter keys.

### Constrained execution backends

Each backend authenticates raw program/input bytes, admits the full image
including unused code, executes it, and checks the canonical terminal output
commitment. Unsupported operations are rejected in the interpreter, not merely
by the optional host admission helper.

| Backend | Supported execution | Proved workloads / guest images |
| --- | --- | ---: |
| [Scalar](IxbyAiur.md) | One straight-line function, immutable locals, 20 scalar primitives | 39 / 26 |
| [Control](IxbyControl.md) | Branches, direct/self/tail calls, recursion, explicit continuations | 50 / 40 |
| [Objects](IxbyObjects.md) | Immutable constructors, projection, constructor cases, shared values | 66 / 55 |

`System.buildScalar`, `System.buildControl`, and `System.buildObjects` select
separate fixed profiles and keys. Each key is reused across its guest images.
`System.verify` binds the caller's expected statement without rerunning
reference execution or receiving artifact advice. Proving retains native
preflight; `verifyBytes` checks bounded decoding and exact reserialization.

Kernel-checked contracts cover representation, immutable-store preservation,
concrete tables, byte/u32/identity readers, ID comparison and uniqueness,
bounded declarations and advice loading, program/function/block headers, and
complete scalar/leaf-operand readers. Structural certificates bind the relevant
actual bytecode shapes and same-toplevel callees. These are Lean evaluator
contracts with explicit range, metadata, allocation, and frame premises—not an
AIR-to-reference or compiler correctness theorem. See the
[remaining proof obligations](IxbyObjects.md#remaining-proof-obligations).

Object differential tests exposed a shared let-hoisting bug. The compiler
repair and all three regenerated native kernels landed upstream in
[PR #628](https://github.com/argumentcomputer/ix/pull/628); this branch depends on
that repair and retains additional regressions. See the
[compiler dependency](IxbyObjects.md#compiler-issue-found-and-repaired).
The fixed capacities and FRI test parameters are not security recommendations.

## Implementation sequence and acceptance gates

1. **Lean functional reference baseline (implemented).** The
   functional machine, reference execution, admission checks, and determinism
   are implemented. The current composition example is not an IxIR₀ lowering
   theorem; that proof and the source/output observation bridge belong in
   step 3. Freeze neither address widths nor wire tags yet.
2. **Aiur/FRI implementation and focused measurement (in progress, here).** The
   candidate profile, closed crypto reference primitives, canonical codecs,
   commitments, and checked byte-execution contract are implemented in Lean.
   Straight-line, scalar CEK control, and immutable-constructor slices have real
   proofs and local measurements; extend them to closures/PAPs, general
   application, and the remaining crypto operations. The upstream compiler repair is covered by
   regressions; prove circuit/reference correspondence and
   expand malicious witness coverage. Use hand-authored IxBy programs to measure
   code authentication, memory consistency and primitive constraints, not just
   unconstrained host evaluation.
   Require honest proofs, independent verification, and negatives for altered
   programs, inputs, outputs, control flow and memory accesses. Explicitly reject
   any reference operations outside the first supported proving profile.
3. **Compilatrix target (later companion PR).** Implement the selected
   computational lowering and zk target, initially for a declared fragment.
   Prove representation/lowering correctness and the execution-reflection
   contract (or its stated sufficient premises), including a real IxIR₀ example.
   Use the target codecs from step 2 and prove the source-value ABI bridge,
   primitive correspondence, and exact image/profile binding. Add differential
   source/target tests; validate the compiler boundary before permanent freeze.
   Compiler self-hosting and the first compiler-image certificate are separate
   gates, not consequences of a tiny compiled example.
4. **Flock Stage 3 interpreter.** Reuse the selected Ixby semantics and
   identities. Prove the same execution relation independently of guest code.
   Handle variable execution size through checked capacity padding or bounded
   segments with a reviewed recursive composition scheme. Fixed interpreter
   source alone does not fix the present exact-shape Flock circuit geometry.
5. **Terminal Stage 4.** Verify the stable Stage 3 proof interface and publish
   its bound statement. Compare KZG-FFLONK and Groth16 using actual verifier
   constraints, setup requirements and lifecycle, proving/verification costs,
   and security review. No backend or setup is selected or generated here.

The benchmark corpus must cover both proposed roles: cryptographic Stage 2
verification AND a permanent source execution layer. Include a BLAKE3/Merkle
workload, FRI fold/field arithmetic, AIR DAG evaluation, recursive lists and
closures, deliberately shared subcomputations, and a compiler/validator slice.
Do not use exponential recursive Fibonacci alone to select a machine.

Record per-table raw and padded heights, widths, lookup counts and distinct
queries; execution/trace generation time; total proof time and peak RSS;
proof size and verifier cost; compiler/code growth; and recursion/compression
costs. Equalize security parameters, inputs, primitive semantics and hardware.
An instruction count, CEK reduction count, or native runtime is not itself a
proof-cost metric. The chosen design must also be evaluated in Flock before
freeze; complete competing CEK and word provers are not a prerequisite.

## Checks

```sh
lake build --wfail Ix.Ixby.Audit Tests.Ixby.Audit IxTests
lake test --wfail -- ixby ixby-crypto ixby-codec \
  ixby-aiur ixby-control ixby-objects \
  ixby-objects-memory ixby-objects-table ixby-objects-parser
RAYON_NUM_THREADS=8 lake test --wfail -- --ignored \
  aiur-hoisting-prove ixby-aiur-prove ixby-control-prove ixby-objects-prove
```

Boolean regressions run only when their runtime suite is selected; kernel
theorems and the trust audit are checked at build time. The default test tier
covers execution and conformance. The merge-queue matrix explicitly selects
the slower IxBy proving and additional hoisting suites. Standalone runners and
statistics commands are documented with each backend.

The trust gate permits only `propext`, `Classical.choice`, and `Quot.sound`.
It rejects proof holes, native-decision/custom axioms, stale exact allowances,
and missing or duplicate roots. These logical checks do not replace native
differential tests, hostile-witness analysis, or the remaining soundness proofs.

Relevant existing boundaries: `Ix/Claim.lean`, `Ix/IxEval.lean`,
`Ix/Aggr/Circuit.lean`, and `crates/aiur/src/execute.rs`. Companion compiler
design and coverage live in Compilatrix's `docs/compiler-design.md` and
`docs/roadmap.md`; that repository has not been modified here.
