# IxBy: certified functional bytecode and universal execution

Date: 2026-09-10. Status: functional Lean reference baseline implemented;
crypto reference primitives, canonical codecs, commitments, and checked byte
execution implemented; straight-line, scalar CEK control, and immutable-object
slices now produce real Aiur/FRI proofs. Closures/PAPs and general application remain pending,
with certified compilation in a later Compilatrix companion PR. No certified
compiler target or frozen protocol yet.
Branch: `jcb/ixby`. This plan is tracked with the isolated IxBy implementation.

The branch is based directly on `origin/main` at `5430a5d9`. The shared Aiur
hoisting repair is a separate prerequisite commit. Existing main-branch Aiur
interfaces suffice for the IxBy backends, so the mixed workspace's Flock
implementation, CLI, fixtures, dependencies, and protocol changes are not
included. See the [hoisting plan](aiur-hoisting-fix.md#isolated-ixby-branch-validation)
for the isolated build and regression results.

This plan selects a functional direction for IxBy: retain a close connection
to Compilatrix's IxIR₀ semantics while extracting the useful computational
structure of IxIR₁ independently of its native memory-management operations.
The exact intermediate phase, instruction set, runtime representation, and
proof layout remain to be designed. No claim of superior proving throughput
over a word machine has been established.

This supersedes the requirement in the initial exploration to build complete
CEK and word-machine provers before choosing a direction. The initial word
prototype has been replaced by the functional model rather than maintained
as a second ISA. See
[implementation status and semantic boundaries](../docs/Ixby.md).

### Implementation checkpoint

- Functional values, indexed locals, constructor cases, direct/tail calls,
  PAPs, and under-/over-application are defined in `Ix/Ixby/Basic.lean`.
- `Primitive.lean`, `Validate.lean`, and `Eval.lean` provide closed scalar
  operations, whole-image/input admission, explicit continuations, total fueled
  execution, fuel extension, and deterministic successful results.
- The structured-value composition contract and 100 executable regressions
  replace the word-stream API/tests. A kernel-checked call/branch/constructor
  example covers both Boolean runtime inputs, but is not an IxIR₀ theorem.
- `Goldilocks.lean`, `Blake3.lean`, and the expanded `Primitive.lean` define
  pure word/byte/field/extension/hash operations. `Profile.lean` defines the
  candidate crypto fragment and node/depth/step admission, with Nat/String
  explicitly excluded from that profile but retained in the reference machine.
  BLAKE3 is differentially tested against Rust; these are not IxBy circuit proofs.
- `Codec/`, `Codec.lean`, and `Commitment.lean` implement experimental wire and
  semantic revision 0: strict bounded artifacts, exact checked re-encoding,
  whole-image/profile/input/output binding, and byte execution connected by a
  Lean theorem to functional reference execution. The
  [encoding specification](../docs/IxbyEncoding.md) records widths, tags,
  resource policy, and hash domains. This is not a production claim format.
- The 89 codec/commitment checks supplement 100 functional and 74 crypto checks.
  General codec inverse/injectivity proofs, circuit soundness, and source ABI
  correctness are not inferred from the checked equations or tests.
- `Aiur/Fragment.lean`, `Aiur/Scalar.lean`, and `Aiur.lean` implement the first
  constrained backend subset: one straight-line scalar function, immutable
  locals, copies, and 20 primitives. Raw program/input bytes are authenticated,
  parsed, executed, and output-bound in the circuit. Host admission is not a
  proof input. Unsupported instructions and values are explicitly rejected.
- `Tests/IxbyAiur.lean` passes 209 checks, including 39 proof cases over 26 guest
  images under the same interpreter key, fresh-verifier checks, 115 malformed
  or excluded raw-artifact cases, and commitment/proof mutations. The
  [backend notes and measurements](../docs/IxbyAiur.md) record the exact fixed
  profile, test-only FRI parameters, timings, peak RSS, and trace-table costs.
  This is neither full functional control nor a formal AIR/refinement proof.
- `Aiur/Control.lean` adds constrained whole-image tables and admission,
  scalar branches, direct/self calls, tail calls, recursion, and immutable
  caller-resume continuations. Only raw artifact bytes are advice. The fixed
  control profile admits 8 functions, 64 blocks/function and locals/frame,
  16 saved continuations, and 256 reference transitions. It has its own key,
  with no wire/semantic revision change and no change to the scalar baseline.
- `Aiur/Refinement.lean` provides 27 pure kernel-checked logical frame/stack,
  lookup/argument-order, transition, and resource-accounting lemmas. Their
  reference fetch/read/primitive/entry premises are explicit. An actual
  circuit-memory representation and AIR-to-`Codec.Evaluates` theorem are still
  outstanding; these lemmas are not an end-to-end soundness certificate.
- `Tests/IxbyControl.lean` passes 232 checks: 50 proved workloads over 40 guest
  images under one control key, fresh verification, 115 malformed/excluded or
  nonterminal artifacts with matching raw commitments, and advice/proof
  mutations. Tests include exact capacities, full-stack tail calls, nested
  restoration, mutual recursion, and rejection of a callee result substituted
  for the caller's output. Together with the earlier suites, 704 targeted
  runtime checks pass. The [control notes](../docs/IxbyControl.md) record the
  supported fragment, open proof obligations, and measured trace costs.
- Word32 is an immutable scalar, not a return to mutable word-machine control.
  Its exact operation catalogue is provisional. Field and BLAKE3 primitives
  remain separate operations rather than mandatory guest word decompositions.
- `Aiur/Objects.lean` adds immutable constructors, projections, and constructor
  cases. Full 40-byte constructor names are admitted uniquely and mapped to
  logical table indices; ranks are computed, not advice. I/O forests/trees have
  shared 128-node and depth-32 limits, separate from the derived intermediate
  rank bound 288. The profile retains the control slice's 256 transitions and
  16 saved frames. Byte/semantic revisions are unchanged; circuit keys need
  rebuilding after the compiler repair below.
- `Aiur/ObjectsRefinement.lean` provides 25 kernel-checked conditional heap,
  finite-value, rank, field-order, constructor/case, and pure-Aiur-field bridge
  lemmas. Arbitrary physical pointers and duplicate cells are permitted in the
  memory view; closed local rank checks imply finite logical objects and rule
  out reachable object cycles. Actual trace/AIR discharge is still pending.
- `Aiur/ObjectsMemory.lean` adds executable concrete-layout decoding and
  reconstruction from the Lean bytecode evaluator's width-bucketed memory.
  Ten kernel-checked lemmas connect successful reconstruction to the logical
  representation, exact scalar interpretation, local bounds, and shared
  budgets. It does not assume a closed ranked heap, but does require successful
  reconstruction and a supplied declaration table; execution/trace establishment
  and authenticated table correspondence are still open.
- `Tests/IxbyObjectsMemory.lean` adds 126 checks, including 14 native flat-output
  comparisons, compiled object helpers, malformed memory, duplicate cells,
  cycles, exact shared budgets, and rank-288/larger-than-I/O intermediates.
  It checks the compiler's distinct nullary tag padding, and documents that
  local rank checks do not alone establish recursive child validity. No
  interpreter, semantic profile, wire format, or production key changes.
- `Aiur/ObjectsStore.lean` proves actual `memStore` readback and preservation
  from `IndexMap`'s invariants, including deduplication, existing logical values,
  exact successful reconstruction, stored field-list construction, and a real
  bytecode Store instruction. Field-address conversion retains an explicit
  canonical bound. `Aiur/ObjectsTable.lean` decodes width-13 declaration cells,
  preserves complete u32-limb identities, checks order/arity/uniqueness, and
  binds the entire table to the existing canonical program decoder. The two
  modules add 24 public kernel-checked lemmas, not a full parser/interpreter/AIR
  theorem or commitment-authentication proof.
- `Tests/IxbyObjectsTable.lean` adds 191 checks against concrete tables, the
  real compiled declaration parser, five complete `is_run` fixtures, and actual
  store operations. Tests distinguish checked representation from execution
  verification. All 1,551 targeted checks at that checkpoint passed; the existing
  interpreter profiles, proof workloads, wire format, and keys are unchanged.
- `Aiur/ObjectsParser.lean` adds 22 kernel-checked byte-prefix, actual byte/u32
  reader, range-check, and zero-count declaration-parser lemmas. Executable
  structural certificates are checked against full and pruned production-source
  compilations. Final Cons allocation extends a checked tail with a fresh name;
  the nonzero recursive parser, duplicate traversal, and input byte
  invariant still have to establish its premises. The initial 387 parser-component
  checks include forged-range and uncertified-nonzero-branch counterexamples.
  All 1,938 targeted IxBy checks at that checkpoint passed, including the existing
  scalar, control, and object proof workloads.
- `Aiur/ObjectsIdentity.lean` adds 20 kernel-checked lemmas for actual inlined
  u32 composition, the full compiled `is_read_id` body, semantic-name decoding,
  and its Call boundary. The forty-byte prefix yields ten exact u32 limbs with
  full 256-bit digest/member/tag agreement and unchanged suffix, memory, and I/O.
  All byte sequences of that length can be grouped into the proved word form.
  Structural certificates cover the actual full/pruned compilations and bind
  the byte callee; all axiom audits use only standard logical axioms. The 725
  added tests bring the parser suite to 1,112 checks and current targeted IxBy
  coverage to 2,663, without changing interpreter profiles, proof workloads,
  wire formats, or keys. Next are exact ID comparison/duplicate traversal,
  the nonzero parser induction, and establishing the byte invariant at admission.
- The shared hoisting repair also requires regenerating all three checked-in
  Rust kernels. That step was initially missed and caused the CI codegen check
  to fail. The generated snapshots are refreshed; content checks and native
  parity must run against rebuilt binaries after shared compiler changes.
- `Tests/IxbyObjects.lean` passes 530 checks, with 66 proved workloads over 55
  guest images under one object key. Coverage includes recursive map, tail fold,
  shared-object unfolding, all 20 primitives in objects, full ID limbs, and
  exact node/depth/local boundaries. All 704 previous checks pass (1,234 total).
  [Object notes and measurements](../docs/IxbyObjects.md) record the profile,
  proof boundary, test-only parameters, and deterministic trace costs.
- Object differential testing found caller-local capture in shared Aiur
  `Source.Term.hoistLets`: continuation lets can retarget an earlier assertion.
  The subsequent [compiler repair](aiur-hoisting-fix.md) freshens caller/callee
  scopes, preserves assertion/IO continuation boundaries, and sequences complete
  argument evaluations. The object entry again reuses `rest`; all 530 checks,
  including source/native trailing-byte regressions, pass without the workaround.
  Compiler refinement remains open. The repair changes shared Lean normalization,
  not Rust/protocol code or byte/semantic revisions; rebuild compiled artifacts/keys.
- Initial integration route: the distinct zk pipeline, retaining IxIR₀ as
  anchor and using logical IxBy as the first pure computational target. A
  separate IxIR-F module and native-pipeline migration have not been started;
  later extraction into a shared phase remains the structural direction.
- Constrained closures/PAPs, general application, byte values,
  remaining primitives, and the circuit/reference
  theorem remain outstanding in B. Actual IxIR₀ refinement, compiler integration,
  and Stages 3/4 are also pending. Source refinement belongs to C and is not a
  prerequisite for continuing the cryptographic execution backend in B.

## 1. Objectives and scope

IxBy should serve both as:

1. IxVM's permanent execution target for certified compilation from Ixon.
2. A universal Stage 3 execution layer that runs an authorized Stage 2
   verifier supplied as a program, followed by a stable terminal Stage 4.

The intended delivery sequence remains:

1. Define the functional IxBy semantics in Lean.
2. Implement an Aiur interpreter and measure actual FRI proving costs.
3. Add the certified Compilatrix target, including the required IR factoring.
4. Implement a program-independent Flock Stage 3 interpreter.
5. Implement a KZG-FFLONK or Groth16 Stage 4 for the stable Stage 3 interface.

The compiler-boundary design belongs in step 1, but the actual IxIR₀ lowering
and refinement proof belong in the later Compilatrix companion PR. A manually
produced test program must not be presented as a certified Compilatrix output.

### Repository split and compiler-driven changes

- **This repository:** own the Lean IxBy execution contract, target-value and
  image codecs, program/input/output commitments, closed cryptographic
  primitive semantics, and Aiur/FRI execution proving. Flock Stage 3 and
  terminal Stage 4 are subsequent cryptographic milestones here as well.
- **Later Compilatrix companion PR:** own the admitted source fragment,
  computational lowering or IR factoring, closure conversion, recursor
  lowering, source-value/ABI correspondence, primitive recognition proofs,
  and exact source-to-IxBy compilation certificates. Consume an identified
  IxBy specification revision; do not maintain an unverified second semantics.

The current vocabulary already accommodates indexed locals, direct and tail
calls, lifted functions/PAPs, constructors, and cases. Compiler integration is
expected to require representation and proof work, not a switch back to a
word machine. For example, source de Bruijn environments must map to absolute
target locals, and source closures or partially applied constructors/recursors
can lower to lifted functions and wrappers. These are compiler obligations;
they do not by themselves require new VM instructions.

This is an expectation, not a proof that the draft ISA will remain unchanged.
Review capture/argument order, currying and over-application, literal versus
constructor representations (especially Nat/String/Bool), constructor identity
transport, and the exact accelerated primitive contracts during integration.
The primitive set has expanded for the initial cryptographic workloads here.
Keep instruction encoding and backend layouts separate from logical semantics;
prefer lowering or representation adapters when they preserve the contract.
If an actual semantic gap needs a VM change, change and revalidate the shared
specification explicitly. Once profiles/images are published, such changes
need a new bound semantic version rather than silently changing old claims.

Use hand-authored IxBy programs to establish target execution proofs and
measurements first. The backend statement is successful execution under an
exact IxBy program/profile, independently of how that program was produced.
Source Eval composition remains gated on the companion refinement evidence.
Flock/terminal backend development can also proceed without a compiler, but
an application-level Stage 3 result still needs the authorized verifier and
correctness policy in section 7. Defer permanent profile/key freeze until
compiler-boundary validation and backend measurements have both passed.

This plan does not authorize or perform a production cutover, a trusted setup,
changes to existing claim encodings, or a rewrite of Compilatrix's native
pipeline. Broad source-language coverage and compiler self-hosting are
separate milestones, not prerequisites for the first declared fragment.

## 2. Architectural direction

Keep four layers distinct:

| Layer | Responsibility |
| --- | --- |
| IxIR₀ semantics | Existing pure, eager, curried semantic anchor after checked erasure; applicable IxIR₀ˢ transformations still produce IxIR₀. |
| Pure computational IR | Proposed representation-independent calls, cases, locals, and functional objects, with a refinement to IxIR₀. |
| IxBy image and machine | Canonical executable representation and a CEK-family call/evaluate/return machine implementing that IR. |
| Proof backend | Aiur/FRI or Flock constraints establishing the same execution proposition. |

Here **CEK-family** means explicit control, environments/locals, and
continuations. It does not require interpreting every original syntax node,
using linked-list variable lookup, curried dispatch for statically known
calls, or cryptographic hashing of every intermediate object. IxBy can be
compiled functional bytecode with direct calls and efficient scalar primitives.

IxIR₀ remains the semantic anchor; it need not remain the exact runtime syntax.
The purpose of factoring Compilatrix is to obtain useful compilation without
first committing the proof machine to native heap and ownership semantics.

## 3. Factor the useful parts of IxIR₁

Use `IxIR-F` as a working label below, not a committed module name, numbered
IxIR stage, or new wire format.

The desired long-term structure is:

```text
validated Ixon
    |
checked erasure -> IxIR₀ -> applicable IxIR₀ˢ transformations
                                      |
                         pure computational lowering
                                      |
                                   IxIR-F
                                  /      \
                     IxBy encoding        ownership/store lowering
                           |                       |
                 functional execution            IxIR₁
                           |                       |
                    Aiur / Flock          IxIR₂ / native backends
```

The native branch in this diagram is a proposed factoring, not a description
of today's implementation. Keep the current native path usable until the new
path has its own preservation and regression evidence.

### Computational features to extract or adapt

- Let-normalization and explicit local operands.
- Lambda lifting or closure conversion, with explicit captured values.
- Saturated direct calls and content-addressing-safe recursive calls.
- Partial application and indirect application, including under- and
  over-application behavior.
- Recursor lowering into constructor cases and recursive calls.
- Constructor construction, field projection, literals, and erased values.
- Existing source-level specialization and later pure optimizations whose
  correctness can be established at this boundary.

### Native features not required in IxBy's default semantics

- Shared reference counts and `dup`/`drop` execution.
- Unique-node `free`, destructive `reuse`, and recursive reclamation.
- Borrowing credits, reuse-token pairing, and physical slot lifetimes.
- Machine register allocation, byte-addressed object layouts, and native ABI
  rules unless independently justified for the zk target.

Preserve source usage/ownership metadata and provenance wherever downstream
checking or native lowering needs them. A mode being operationally inert in
pure evaluation does not authorize removing source checks or changing source
identity. Any broader zk source acceptance needs its own proved coverage.

Do not implement this separation by deleting memory instructions from existing
IxIR₁ programs. For example, existing `apply` consumes its PAP, and case
lowering retains fields before releasing a scrutinee. The pure operations must
have their own semantics and a value/observation correspondence. Observable
pointer identity or effectful externs would require additional contracts.

### Two implementation routes

**Preferred structural route: a shared phase before ownership.** Factor the
current lowerer into IxIR₀-to-IxIR-F computational lowering and a separate
IxIR-F-to-IxIR₁ ownership/store pass. Reuse source analyses and proof lemmas
where their assumptions match. This gives native and zk backends a common
place for pure optimizations.

**Permitted incremental route: a distinct zk pipeline.** Add a direct
IxIR₀-to-IxIR-F/IxBy path with its own certificates, reusing independently
specified helpers and leaving native lowering unchanged. Prefer this initially
if splitting the existing stateful lowerer would make a broad native migration
a prerequisite for the first certified zk result. Record duplicated logic and
the intended shared interfaces; equivalence is not established by copying code.

The initial implementation takes the distinct zk route: existing `Lower.lean`
and its stateful proofs interleave ownership with captures, spines, and cases,
so the first model leaves them untouched. Logical IxBy currently serves as the
pure computational vocabulary as well as the instruction model. Do not create
a second identical IR solely to give it a name; factor an independently useful
shared boundary when its interfaces and proofs are established.

A complete native refactor is not an acceptance condition for
the first IxBy prover. An optional transformation may retain a previously
checked baseline only when such a baseline actually exists; unsupported source
must fail explicitly.

### Existing compiler entry points to inspect

In the companion `compilatrix` repository:

- `Compilatrix/IxIR0/Basic.lean` and `Eval.lean`: semantic anchor and values.
- `Compilatrix/IxIR1/Basic.lean` and `Eval.lean`: current mixed computational
  and ownership vocabulary.
- `Compilatrix/IxIR1/Lower.lean`: `lowerSpine`, `knownCall`, `lowerLam`,
  `lowerCaptures`, and `lowerRecursorRule` interleave computational structure
  with mode demands, ownership tracking, and release operations.
- `Compilatrix/IxIR1/LowerStateBase.lean`, `LowerSim.lean`, and `Sim.lean`:
  reusable traversal, environment, function-value, and heap correspondence
  boundaries; none automatically certify a new pure target.
- `Compilatrix/PipelineSound.lean` and the addressed-lowering modules: exact
  emitted-program equations, source assumptions, and namespace transport.
- `docs/compiler-design.md`, `docs/lowering-restrictions.md`, and
  `docs/roadmap.md`: architecture, accepted fragments, and remaining gates.

## 4. Functional machine and data model

Specify a small computational vocabulary before assigning opcode numbers:

- Indexed local operands, constants, and erased values.
- Direct call, recursive call, return, and tail-call behavior.
- Closure/PAP creation and application when a target is not statically known.
- Constructor creation, checked field access, and constructor dispatch.
- Calls to a closed set of precisely specified primitives.

Keep case selection, argument order, saturation, captures, and erased-value
behavior consistent with the source refinement. The specification may retain
functional closures even if the encoded target uses lifted functions plus
capture vectors.

Runtime objects should be immutable; physical object identifiers should not
be observable source values. This permits interning and alternate layouts
subject to the representation theorem. It does not require a mutable RAM heap
or reference counting in the proved guest trace. A word/register design could
also use immutable objects; this is not an exclusive property of CEK.

Choose and justify the local/environment representation. Avoid an accidental
linear walk for every deep variable access. Bounded frames, indexed immutable
slots, and tail-call frame behavior are design candidates, not free operations.
Variable-size constructors, argument lists, strings, and large Nats must be
decomposed into bounded, checked operations; a variable-size host operation
cannot count as one constant-cost circuit row without an argument for its work.

Separate semantic resource behavior from prover capacities. Any guest-visible
limit belongs in the semantic profile. Host memory limits and circuit padding
must not change a failed or exhausted execution into a successful result.
Do not inherit the experimental core's 32-bit addresses as a permanent bound.

### Sharing and execution soundness

Aiur already caches calls by callee/arguments and interns stored tuples. Design
query boundaries to expose useful pure subcomputations. Including a changing
continuation, clock, output accumulator, or unrelated heap state in every key
can defeat sharing; naming the machine CEK does not solve that problem.

Specify successful execution as a finite derivation from the authenticated
initial state to a terminal result. If memoized recursive evaluation replaces
sequential steps, establish well-founded dependencies: balanced call lookups
alone are not the specification of a terminating run. State/object encoding
must exclude malformed or cyclic witnesses wherever finite source values are
required. These are obligations for the new interpreter, not claims that the
current Aiur implementation already discharges them.

Track distinct objects and trace retention as well as live guest values.
Removing guest reclamation does not guarantee lower prover peak RSS.

## 5. Primitive semantics and stable identities

The initial candidate primitive set should cover the current verifier's
Goldilocks and extension-field arithmetic, BLAKE3, and the required byte/word
operations, range checks, and conversions. Decide the acceleration granularity
using actual constraints and source-correctness obligations. Native field
operations and word arithmetic are compatible with functional control.

For every primitive specify input/output representations, canonical ranges,
failure cases, variable-size work, and the source function it implements.
Check accelerators against their defining relations; hints are not trusted
answers. IxIR₀'s parameterized extern oracle is not by itself a certified
primitive implementation or an acceptable unrestricted execution boundary.

Arbitrary Nat semantics must not silently become arithmetic modulo a field or
machine word. Strings need a stated canonical encoding and source observation.
Compiler recognition of an accelerated function must bind the exact source
identity and theorem, not merely a familiar declaration name.

The program identity must cover the entry point, all encoded code and data,
dependency/import closure, primitive semantic profile, and ABI. Code-table
indices may replace content addresses internally only with a checked mapping
to the authenticated image. Handle recursive blocks without assuming a hash
fixpoint, and prove strict decoding, canonical encoding, and address transport.

The experimental reference codec now includes the full closed table image,
including unused entries, and binds every profile capacity. Its inline value
ABI has no physical pointers or observable sharing. Accepted decoding carries
an exact re-encoding equation; general inverse/injectivity theorems and the
constrained representation/authentication proofs remain future work. Computing
a commitment to an admitted output is not evidence that execution produced it.

Keep semantic identities separate from proof-backend versions and security
parameters. Freeze the supported primitive semantics before fixing universal
interpreter keys; adding a new accelerated primitive may require a circuit
upgrade. New guest algorithms can use existing primitives without that upgrade.

## 6. Certificates and Eval/Exec composition

Retain `Eval` for source interpretation and introduce a separately versioned
`Exec` meaning successful IxBy execution. Existing `Claim.eval` bytes must not
silently change meaning. In particular, the current `#ixeval` uses kernel-style
`Meta.reduce`, whereas Compilatrix's source execution is weak call-by-value.
State the admitted observation domain and prove that bridge explicitly.

The required artifact-level conclusion is conceptually:

```text
Check(exact Refines(source S, bytecode B, semantic profile P, ABI A))
Exec(P, B, encode_A(input), encodedOutput)
decode_A(encodedOutput) = output
-----------------------------------------------------------------
SourceEval(S, input, output)
```

`Refines` must justify source evaluation from successful target execution.
A forward simulation alone has the opposite premise. Either prove execution
reflection directly or supply the needed source termination, successful forward
target execution under the same resource conditions, and target determinism.
Do not infer those premises from tests or from compiler validation alone.

Proof obligations should compose across checked erasure, pure computational
lowering, IxBy representation, and execution. Function/capture correspondence
and output decoding must be instantiated, not left as arbitrary oracles.
Each pass binds its exact input/output images, policies, and dependencies;
changed bodies cannot retain their old content identities without a theorem.

Optionally prove the exact compiler execution as well. A per-artifact
refinement theorem already establishes semantic correspondence; compiler
execution adds provenance and is not mandatory for that route. Conversely, a
compiler execution proof plus an unrelated well-typed Check declaration is
insufficient. Bind the theorem type, its arguments, hypotheses, and permitted
axioms to the actual composition.

Reuse compilation evidence across runs. Bootstrap through independently
certified compiler images or per-artifact checking; do not justify the first
compiler image using the execution certificate that depends on that image.
Implement an explicit mixed-claim composition relation: the current CheckEnv
aggregator does not acquire this inference by aggregating a list of proofs.

## 7. Universal Stage 3 and terminal Stage 4

Stage 3 proves execution of an authorized verifier program, not merely that
some program accepts a claim. Bind the exact Stage 2 protocol/key policy,
claim, input proof, expected success result, and verifier program identity.
A trusted verifier-program identity or checked verifier-correctness evidence
must establish its application meaning; compilation correctness alone does
not establish that the source program is a valid proof verifier.

Move changes to Stage 1/2 verification logic into guest programs when supported
by the frozen semantics. Independently check image binding, program lookup,
object consistency, control transitions, and all primitive constraints in the
Flock interpreter; Aiur's implementation does not automatically provide them.

Program-independent interpreter source does not guarantee a fixed Flock
key: the current backend has exact circuit geometry. Select and prove a
capacity/padding policy, a bounded family of authorized shapes, or segment
composition before claiming stable keys. Any segments must bind matching
intermediate states, program/profile identity, and complete initial-to-terminal
execution. Estimate the continuation/object traffic and non-native Goldilocks
costs under Flock's F128 backend before freezing the machine.

Stage 4 should verify the stable Stage 3 proof interface and preserve its
public statement, not reimplement the changing Stage 2 verifier. Select
KZG-FFLONK or Groth16 only after evaluating that verifier circuit, setup and
upgrade requirements, and actual prover/verifier costs. Changing the interpreter
semantics, authorized shapes, or proof protocol remains an explicit versioned
upgrade even when guest-program changes no longer require one.

## 8. Work packages and exit criteria

Work package A's reference baseline is implemented as recorded above; B is in
progress with the crypto reference profile, canonical artifacts, commitments,
byte-execution contract, and real straight-line/scalar-control proofs; C through E are
pending. The real IxIR₀ refinement example previously assigned to A is
deliberately moved to C, not counted as accomplished. The executable model and
its small example do not establish an IxIR₀/compiler refinement, cryptographic
soundness, or proving performance.

### A. Select the computational boundary and define it in Lean

- Map the existing lowerer and proof dependencies; select the shared-phase or
  distinct-pipeline route and record the preservation/migration obligations.
- Define the functional target vocabulary, values, local representation, and
  closed reference primitive semantics; use logical IxBy as the initial pure
  computational target without requiring a separate IxIR-F module.
- Define executable IxBy states, transitions, failure behavior, and successful
  execution; prove determinism and fuel/step-budget extension properties.
- Exercise runtime inputs, calls, constructed data, closures, recursion, and
  malformed programs/values. Check the generic composition interface on a
  small reference example and state that it is not an IxIR₀ refinement.

Exit: a documented boundary, checked Lean semantics, explicit outstanding
proof assumptions, and executable target regressions. Source/target
differential tests and the real lowering proof are C's gate, not a dependency
of B. Native compiler behavior and production proof formats remain unchanged.

### B. Build one Aiur/FRI interpreter and evaluate its costs

Reference profile/codecs/commitments, straight-line and scalar CEK control, and
immutable constructors/projections/cases have independently verified proofs.
The interpreter separates whole-image admission from execution and uses
authenticated immutable tables and ranked object fields. This package remains
in progress. Concrete-memory reconstruction now proves representation on
successful decoding; checked tables bind to canonical program images, and
actual immutable Store preservation is proved. Byte/u32/ten-limb identity reader
contracts and the zero-count parser path now have structural bytecode certificates
and proofs. The next step is exact identity comparison and duplicate traversal,
then composition through the nonzero recursive declaration parser, while
establishing the input byte invariant from admission. Canonical program/table
agreement, initialization, and complete interpreter transition correctness
follow those obligations.
Actual circuit/trace refinement, closures/PAPs and general application, the
remaining crypto operations, broader malicious-witness testing, and
full-workload/Flock-oriented measurements are still needed.

- Specify the first constrained target profile, including value/image codecs,
  canonical decoding, resource bounds, domain-separated program/input/output
  commitments, and exact cryptographic primitive semantics. Any initially
  unsupported reference operation must be explicitly excluded at admission.
  Source-to-primitive correspondence is C's obligation; the primitive relation
  itself and its constrained implementation cannot be deferred to C.
- Implement constrained image admission, program fetch, local/object access,
  call/return transitions, terminal binding, and the initial primitives.
- Relate encoded states and constrained transitions to the Lean execution
  contract. Keep any remaining formal proof or cryptographic assumptions
  explicit; differential testing alone is not a soundness theorem.
- Produce and independently verify real proofs from the same interpreter for
  different hand-authored guest programs; identify any capacity-dependent key
  variation. Compiler-generated inputs are not required for this milestone.
- Test malicious witnesses and altered programs, input/output commitments,
  locals, constructors, calls/returns, primitive results, and nonterminal runs.
- Compare reference execution with trace generation and collect the metrics
  in section 9, including a Flock-oriented operation-cost estimate.

Exit: actual functional execution proofs and evidence that no identified
control, representation, or primitive bottleneck blocks the next milestone.
A complete word prover is not required. Change a local design if the evidence
shows a problem; reopen the architecture only for a concrete unresolved cost.

### C. Integrate certified compilation in the later Compilatrix companion PR

- Consume the IxBy specification/profile from B through an explicit dependency
  or identified shared artifact. Establish the first real IxIR₀-to-machine
  refinement example with a runtime input, a call, and constructed data.
- Implement the selected factoring or zk branch with exact lowering traces
  or checked artifacts, including generated functions and recursive blocks
  within the declared source fragment.
- Prove the pure lowering and machine representation contracts; instantiate
  primitive, closure/PAP, source-observation, and execution-reflection premises.
- Use the target codecs from B; implement and prove the source-value ABI bridge,
  content-address reconstruction, compilation evidence, and adversarial
  certificate/image mismatch tests. Bind the exact target profile and artifact.
- Differentially test source, IxIR₀, IxIR-F, and IxBy; test runtime arguments,
  captures, partial/over-application, constructors, and supported recursion.
- If native lowering is refactored, retain its source acceptance, ownership,
  reclamation, and output guarantees with appropriate regression coverage.

Exit: an actual Compilatrix-produced image with checked source-to-target
evidence and a verified execution implying the promised source result. Report
exact source coverage; a proof for a closed example is not universal input
correctness. Native migration and compiler self-hosting have separate gates.

### D. Implement universal Flock Stage 3

- Fix the bounded shape/segmentation policy and constrained interpreter.
- Verify real Stage 2 proofs through an authorized IxBy verifier program.
- Exercise distinct supported verifier programs without rebuilding the
  interpreter within the stated shape policy; reject wrong keys, programs,
  claims, proof data, intermediate states, and output assertions.
- Measure complete proof costs and peak RSS, including all non-native work.

Exit: independently verified, fully bound Stage 3 artifacts and an explicit
account of which guest, capacity, and protocol changes preserve existing keys.

### E. Add terminal Stage 4 and reviewed activation

- Implement the selected Stage 3 verifier in the chosen terminal system.
- Bind the complete terminal statement and approved Stage 3 key/profile.
- Review setup, security parameters, negative tests, versioning, and migration.
- Only then activate new claim/proof formats and production verification policy.

Exit: end-to-end verification from terminal proof to the intended application
claim, with documented trust assumptions and upgrade boundaries.

## 9. Validation without two complete competing implementations

Start with operation-level traces for the chosen design: deep local access,
direct and tail calls, closure capture, PAP saturation, constructor dispatch,
and representative field/hash work. These checks guide layout and instruction
granularity; raw step counts are not proof-cost measurements.

The proving corpus must cover both roles:

- BLAKE3/Merkle and FRI/field-arithmetic verifier slices.
- AIR/code DAG traversal and shared pure subcomputations.
- Recursive lists, closures, partial application, and deep environments.
- A realistic compiler or certificate-validator slice.
- A complete supported Stage 2 verifier when integration permits it.

Record raw and padded per-table heights, widths, lookup counts, distinct query
and object counts, trace-generation time, proof time, peak RSS, proof size,
verification cost, code/certificate growth, and Flock/terminal compression
costs. Include admission, code authentication, memory consistency, and primitive
work; label partial kernels and lower bounds. Keep parameters and workload
identities reproducible, and model allocation peaks before large runs.

Compare changes to the chosen implementation using matched primitives and
security parameters. Benchmark a competing control model only if a specific
uncertainty would change the architecture and a bounded experiment can resolve
it. Do not assume either pure execution or compiled words win from instruction
counts, native performance, or an unrelated system's benchmark.

## 10. Initial decisions still open

- Timing and interfaces of shared-phase extraction after the initially distinct
  zk route; whether a separate IR/module is needed.
- Minimal functional instruction set and which calls/cases become macrosteps.
- Environment/local layout, closure/PAP layout, and safe memoization boundaries.
- Scalar and address widths, Nat/string representation, and primitive granularity.
- Source fragment, input/output observations, and each certificate's premises.
- Permanent image/ABI/Exec encoding and hash domains after validating the
  experimental codec; application program-policy binding and activation.
- Flock capacities/segmentation and Stage 4 system/setup selection.

These are bounded design tasks within the functional direction, not a request
to implement every alternative before making progress.

## References

- [Current IxBy implementation and composition boundaries](../docs/Ixby.md).
- [Experimental crypto encoding and commitments](../docs/IxbyEncoding.md).
- [First scalar Aiur proofs, coverage, and measurements](../docs/IxbyAiur.md).
- [Authenticated scalar CEK control and representation contract](../docs/IxbyControl.md).
- [Immutable constructors, ranked heaps, recursive workloads, and compiler finding](../docs/IxbyObjects.md).
- [Composition interfaces](../Ix/Ixby/Composition.lean): structured-value ABI
  and execution-reflection contract, not yet an IxIR₀/compiler certificate.
- [Aiur executor](../crates/aiur/src/execute.rs) and
  [immutable memory tables](../crates/aiur/src/memory.rs).
- [Source Eval surface](../Ix/IxEval.lean) and
  [existing claim representation](../Ix/Claim.lean).
- [Jolt architecture](https://jolt.a16zcrypto.com/how/architecture/architecture.html)
  and [program-table design](https://jolt.a16zcrypto.com/how/architecture/bytecode.html):
  useful precedents for separating control, code, memory, and operation checks.
  Its Spartan/Twist/Shout costs do not transfer merely by copying a word ISA.
- [Lurk experience report](https://namin.seas.harvard.edu/pubs/icfp-lurk.pdf):
  precedent for CEK-family proving with dedicated primitive gadgets, not a
  matched performance comparison against our backends.
