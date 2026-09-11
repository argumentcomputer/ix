# IxBy: functional bytecode and execution semantics

Ixby is proposed as IxVM's permanent bytecode execution layer, with certified
compilation from Ixon and multiple proving backends. The implementation
direction is now **functional bytecode with CEK-family control**, potentially
factoring Compilatrix's IxIR₁ computational lowering away from its ownership
and store operations. The exact IR split, ISA, representation, and wire format
remain unfrozen; no proof-performance winner has been established.

The [IxBy implementation plan](../plans/ixby-plan.md) owns the current direction
and work packages. It supersedes the initial requirement to build complete
competing provers before choosing an architecture. This document records the
current executable model and the shared semantic boundaries. The plan is
tracked on `jcb/ixby`, but is not a frozen protocol document.

The local `jcb/ixby` bookmark starts this work. Existing claim encodings,
Stage 1/2 keys, Flock relations, and deployment policies are unchanged.

## Current implementation

- `Ix/Ixby/Basic.lean`: functional values, indexed operands, calls, constructors,
  branches, immutable local frames, and explicit continuations.
- `Ix/Ixby/Primitive.lean`: closed, typed scalar/byte reference primitives.
- `Ix/Ixby/Goldilocks.lean` and `Blake3.lean`: pure base/extension arithmetic
  and unkeyed 32-byte BLAKE3, without importing an FFI oracle.
- `Ix/Ixby/Profile.lean`: experimental crypto-profile admission and execution;
  functional control over Bool, Word32, field/extension elements, and bytes.
- `Ix/Ixby/Codec.lean` and `Codec/`: bounded, strict profile/program/value
  encodings and byte execution carrying encoding and evaluation equations.
- `Ix/Ixby/Commitment.lean`: domain-separated profile/program/input/output
  commitments and reference execution against an expected statement.
- `Ix/Ixby/Aiur.lean` and `Aiur/`: constrained straight-line, scalar CEK, and object
  interpreters, with raw artifact authentication and real Aiur/FRI proofs.
- `Aiur/Refinement.lean`: logical reversed-frame and continuation contracts,
  with kernel-checked representation/transition lemmas, not an AIR theorem.
- `Aiur/ObjectsRefinement.lean`: conditional ranked-heap finiteness, field-order,
  constructor/case, and field-counter bridges; the full circuit proof remains open.
- `Aiur/ObjectsMemory.lean`: checked reconstruction of concrete bytecode memory,
  with a proof that success yields the logical object representation. Execution
  establishing reconstruction success and the declaration table remains open.
- `Aiur/ObjectsStore.lean` and `ObjectsTable.lean`: actual bytecode-store
  preservation and checked concrete-table binding to canonical program bytes.
  Admission, complete interpreter transitions, and AIR links remain open.
- `Aiur/ObjectsParser.lean`: structurally checked byte/u32 reader contracts,
  byte-prefix preservation, and the zero-count declaration parser proof.
  The authenticated byte-stream invariant remains open.
- `Aiur/ObjectsIdentity.lean`: compositional inlined-word and compiled ten-limb
  identity-reader proofs, including exact digest/member/tag, suffix preservation,
  and actual Call semantics. Authenticated whole-program binding remains open.
- `Aiur/ObjectsEquality.lean` and `ObjectsUnique.lean`: exact compiled ID
  comparison and bounded duplicate traversal, tied to semantic table decoding
  and preserving caller state.
- `Aiur/ObjectsDeclarations.lean`: complete bounded declaration-parser and Call
  contracts, including exact byte-codec identities, field-limit/duplicate
  rejection, table construction, and state preservation.
- `Aiur/ObjectsAdmission.lean`: checked raw-advice reader and loader contracts,
  genuine-byte stream construction, allocation/frame bounds, and composition
  with a declaration prefix. Metadata/address and initial storage bounds are
  explicit; authenticated whole-program admission remains open.
- `Aiur/ObjectsProgramPrefix.lean`: actual `is_run` magic/revision, entry/count,
  and declaration-call contracts, with a derived constructor bound, exact
  continuation state, and checked loader composition. The suffix/function-table
  code and whole-program binding are not certified by this prefix check.
- `Aiur/ObjectsCodeHeaders.lean`: checked function-count, function-header, and
  block-header guards, exact zero-count Nil stores, and continuation/loader
  composition. Instruction decoding and complete function-table admission remain open.
- `Aiur/ObjectsScalars.lean`: complete checked field and scalar-literal readers,
  exact canonical Goldilocks packing, Boolean rejection, concrete value layouts,
  and same-toplevel Call contracts.
- `Aiur/ObjectsOperands.lean`: complete checked local/literal/erased leaf readers,
  exact local-index bounds and six-field layouts, caller-state preservation,
  and composition with the actual checked loader. Lists and instructions remain open.
- `Ix/Ixby/Validate.lean`: whole-image admission and bounded input validation.
- `Ix/Ixby/Eval.lean`: total call/evaluate/return execution, fuel
  monotonicity, and uniqueness of successful results across fuel witnesses.
- `Ix/Ixby/Composition.lean`: the required source/target refinement interface
  and a generic theorem composing compilation certification with execution.
- `Tests/Ixby.lean`: 100 executable regressions and a kernel-checked example
  with a runtime argument, direct call, branch, and constructed result, plus
  a counterexample to forward simulation alone.
- `Tests/IxbyCrypto.lean`: crypto primitive/profile tests, BLAKE3 comparison
  against the Rust implementation, and a functional-call/Word32 example.
- `Tests/IxbyCodec.lean`: golden artifact bytes, canonical decoding, malformed
  inputs, resource bounds, byte execution, and commitment mismatch tests.
- `Tests/IxbyAiur.lean`: scalar-slice execution/proving, malformed advice,
  changed statements/proofs, fresh-verifier checks, and trace measurements.
- `Tests/IxbyControl.lean`: authenticated code tables, branches, call/return
  restoration, tail/self/mutual recursion, resource boundaries, and proofs.
- `Tests/IxbyObjects.lean`: recursive list map/fold, constructor identity and
  field order, shared objects, I/O budgets, malformed artifacts, and proofs.
- `Tests/IxbyObjectsMemory.lean`: 126 concrete-layout, compiled-helper,
  native-output parity, and malformed-memory checks, without new proof workloads.
- `Tests/IxbyObjectsTable.lean`: 191 table-layout, compiled parser/runner,
  store-preservation, and checked program/table-binding tests.
- `Tests/IxbyObjectsParser.lean`: 23,832 checks covering full/pruned compilation
  certificates, byte/u32/identity execution, exact codec agreement, malformed
  cells, forged ranges/metadata, actual Call boundaries, the zero-count parser,
  exact ID comparison/duplicate traversal, complete bounded declaration parsing,
  raw-advice loading, program/header count guards, and function/block headers
  with exact allocation, continuation-state, and loader-composition checks;
  complete scalar/leaf-operand certificates, canonical field/Boolean rejection,
  local bounds, flat layouts, codec agreement, and per-byte failure cases.

The earlier mutable-register/word-stream prototype and its tests have been
replaced, rather than maintained as a second ISA. The composition contract is
retained with a structured-value ABI. The logical bytecode now has an
[experimental crypto-profile encoding](IxbyEncoding.md) with explicit tags and
domain-separated commitments, but is not a frozen permanent ISA. A
[straight-line scalar Aiur slice](IxbyAiur.md) and a
[scalar CEK control slice](IxbyControl.md), and
[immutable-object slice](IxbyObjects.md) now have real execution proofs and
initial measurements, not complete functional-machine coverage. There is
no Compilatrix backend, new production claim variant, Flock Ixby interpreter,
or terminal SNARK yet. The composition interface is not itself a proof of
Compilatrix's correctness or of an Ixon semantic bridge. The checked
example covers both inputs of a small Boolean-to-pair source observation;
it is not an IxIR₀ lowering theorem or general compiler certification.

For the first integration, use the plan's incremental distinct-zk-pipeline
route: IxIR₀ remains the anchor and the logical IxBy vocabulary is the initial
pure computational target. No separate IxIR-F module or native compiler
refactor is required by this first model. Extract a shared pure phase when its
interfaces and preservation obligations are established. Compilatrix itself
has not been modified here.

Cryptographic execution work proceeds here first; actual IxIR₀ lowering and
source-to-IxBy refinement belong in a later Compilatrix companion PR. Target
execution proofs can use hand-authored programs without claiming source
correctness. The compiler-facing representations and primitive contracts remain
provisional until that integration is checked.

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

### First constrained execution slice

The [scalar Aiur backend](IxbyAiur.md) admits one straight-line function with
immutable locals, copies, and 20 word/base-field/extension primitives. The
circuit authenticates and parses raw program/input bytes, executes the admitted
image, and binds the canonical computed output. It rejects unsupported code
and values inside the circuit; it does not rely on host fragment admission.
The same interpreter key proves 39 test cases over 26 guest images, including
the 64-block limit. This original subset remains a regression baseline.

The separate [control slice](IxbyControl.md) now decodes and admits the whole
image into immutable tables before execution. It supports scalar branches,
direct/self calls, tail calls, and explicit caller-resume continuations. Its
50 proved workloads cover 40 guest images under one control interpreter key,
including mutual recursion, backward successors, exact 256-transition runs,
and tail calls at the 16-frame continuation limit. Its fixed profile has a
different key from the straight-line backend; no wire or semantic revision
changed.

The [object slice](IxbyObjects.md) adds immutable constructors, projections,
and constructor cases under another fixed profile/key. Its 66 proved workloads
span 55 guest images, including recursive list map, shared objects, and separate
intermediate-rank and I/O bounds. Closures/PAPs, general application, byte values,
and the other crypto primitives remain pending.

`ScalarSystem.verify` verifies the caller's expected commitment statement
without rerunning reference execution or receiving execution advice. The
backend is a separate import from the pure `Ix.Ixby` specification. Its actual
proofs and differential/negative tests are not a formal AIR-to-reference
refinement theorem, a complete hostile-witness audit, or production activation.
The representation modules prove 27 frame/stack/transition lemmas and 25
object/heap/field-counter lemmas. The latter derive finite values from a
functional memory view and closed local rank constraints. Ten additional
concrete-memory lemmas establish checked reconstruction into that representation
and its connection to the Lean bytecode evaluator's width-bucketed loads.
A further 24 lemmas establish immutable-store preservation—including an
actual bytecode Store instruction—and checked declaration-table binding to
canonical program bytes. Another 22 prove byte-prefix/store, actual byte/u32
reader, and zero-count parser contracts, with executable structural certificates
for the corresponding bytecode. Twenty more compose the actual inlined word
operations through the ten-limb identity reader, prove exact natural-byte packing
and semantic-name decoding, and preserve the suffix, memory/I/O, and caller
registers. Another 37 prove full-field ID comparison, range-checked semantic
equality, and bounded duplicate traversal through actual Call boundaries.
Successful table decoding supplies the concrete-spine premise; the traversal
preserves memory and I/O and succeeds exactly for an absent semantic ID.
Another 25 lemmas establish store-allocation bounds and the complete bounded
declaration-parser composition. Byte-derived prefixes of up to sixteen records
are accepted exactly when their full IDs are distinct and field counts are
supported. Success establishes the concrete semantic table in wire order,
returns the exact suffix, and preserves prior reads, caller registers, and I/O.
Allocation bounds prevent field-pointer wrap without assuming fresh cells.
Another 29 lemmas certify the actual recursive advice reader and complete loader,
prove exact limit/range-check behavior under explicit metadata bounds, and derive
a genuine-byte stream from success. Actual loading preserves prior reads/I/O,
adds at most one width-3 cell per byte plus Nil, and leaves other width buckets
unchanged. This discharges the declaration parser's byte premise at an identified
loaded prefix and preserves its table-capacity bound. Another 18 lemmas certify
the actual `is_run` header and declaration-call prefix: exact magic and revision,
the full u32 entry, a constructor bound derived from the executed check, and
the ordered table at its actual output pointer. The precise 73-register state
passes to the original suffix/control, whose success is not assumed. A loader
composition supplies the genuine-byte premise and preserves the suffix stream.
Another 27 lemmas extend the actual program prefix through the nonzero function
count bounded by eight, and certify function arity/block-count and block-local
headers. They preserve exact live state, prove both zero-count Nil stores, and
bind the next Calls while leaving their remaining behavior unrestricted.
Another 40 lemmas certify complete field/scalar/leaf-operand readers. The actual
field guard accepts exactly the eight-byte encodings below the Goldilocks modulus;
packing then agrees with the natural little-endian codec value without reduction.
Boolean, Word32, field, and extension literals have exact five-field layouts;
local, literal, and erased operands have exact six-field layouts. Under a genuine
u32 frame count, the executed local-index comparison is exact. Same-toplevel Calls
preserve caller registers, memory, and I/O; actual successful loading supplies
genuine bytes at an identified operand prefix and preserves the suffix stream.
Operand-list/instruction decoding, complete block/function-table admission and validation,
canonical whole-program binding, remaining resource bounds,
initialization/full transitions, commitment agreement, and actual circuit/gadget
refinement remain outstanding; checked representation alone is not execution verification.
Object tests also found a shared let-hoisting capture bug; the
shared normalizer now has a tested scope/evaluation-order repair, and the
original shadowed entry passes its negative regressions without the workaround.
This is not a compiler correctness proof; compiled artifacts/keys need rebuilding.
The three checked-in generated Rust kernels have also been regenerated;
the [reproduction steps](IxbyObjects.md#compiler-issue-found-and-repaired) include
the CI content check and rebuilt native/interpreter parity tests.
The fixed test capacities and FRI parameters are not security recommendations.

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
   application, and the remaining crypto operations. Compiler hoisting has a
   tested repair; prove circuit/reference correspondence and
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
lake build --wfail Ix.Ixby Tests.Ixby Tests.IxbyCrypto Tests.IxbyCodec
lake build --wfail Ix.Ixby.Aiur.Refinement IxbyAiurTests IxbyControlTests
RAYON_NUM_THREADS=8 .lake/build/bin/IxbyAiurTests
RAYON_NUM_THREADS=8 .lake/build/bin/IxbyControlTests
lake build IxTests
.lake/build/bin/IxTests ixby
.lake/build/bin/IxTests ixby-crypto
.lake/build/bin/IxTests ixby-codec
```

The reference, crypto, and codec test modules also run their Boolean regression
collections at elaboration; the Aiur backend tests require the runtime/FFI.
Formal composition examples use the real reference semantics, not an assumed
host acceptance bit. They introduce no `sorry`, custom axioms, or
`native_decide`. The checked execution/composition and byte-reference bridge
theorems report only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound`; no custom axiom was added for decoding or commitment binding.

Relevant existing boundaries: `Ix/Claim.lean`, `Ix/IxEval.lean`,
`Ix/Aggr/Circuit.lean`, and `crates/aiur/src/execute.rs`. Companion compiler
design and coverage live in Compilatrix's `docs/compiler-design.md` and
`docs/roadmap.md`; that repository has not been modified by this first step.
