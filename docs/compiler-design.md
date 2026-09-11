# Compiler design

This reference consolidates the enduring architecture and design constraints.
The [roadmap](roadmap.md) alone owns priorities, delivery state, and acceptance
gates. Normative wire, IR, ownership, and trust contracts remain in the focused
specifications linked below; the proposed extensions here do not change them.

## Architecture and proof boundaries

Compilatr.ix is a Lean compiler with Lean semantics and verified checkers,
bootstrapped from upstream Lean. Expensive analyses and profitability
heuristics may be untrusted. Their accepted artifacts must pass bounded Lean
checking; a cheap local decision can instead be a proved executable function
over an already-checked artifact.

The compilation unit is the addressed transitive closure of a root. The
intended pipeline keeps specialization and downstream representation separate:

```text
validated Ixon
  → erased IxIR₀
  → bounded IxIR₀ˢ specialization and recognized recursion recovery
  → IxIR₁ ownership lowering, HPT, and shrinking consumers
  → IxIR₂ CFG, liveness, and take/reset planning
  → checked borrowed ABI and RC normalization
  → reuse expansion, dead-control cleanup, and RC coalescing
  → representation lowering, instruction selection, allocation validation
  → native objects or a zk target with its own representation/cost refinement
```

This describes responsibility and dependency order, not a claim that every
stage is implemented.

| Layer | Responsibility and constraint |
| --- | --- |
| Ixon | Strictly decoded, content-addressed source contracts. Uses/Owned are identity-bearing data; sharing and erasure checks define the accepted source boundary. |
| IxIR₀ | Pure, curried, eager erased semantic anchor, with closures and recursors close to source. Types/proofs disappear but runtime mode information must survive. Evaluator fuel is a termination device, not a performance cost. |
| IxIR₀ˢ | Bounded source-level specialization: known targets, usage/world instantiations, arity absorption, and derived-recursion schemas. This is a transformation stage over IxIR₀, not an independently frozen wire format. |
| IxIR₁ | First-order explicit store, saturated calls/PAPs, ownership effects, exact heap/RC counters, HPT, and shrinking consumers. Structured `case` remains non-consuming. |
| IxIR₂ | CFG and block parameters, consuming destructure, affine credits, borrowing, control/RC optimization, and logical/physical small-step semantics. See the [IxIR₂ specification](ixir2-spec.md). |
| Target | Physical heap/credit interpretation, typed instructions, ABI, bytes, objects, and runtime/environment interface. Native and zk representations refine shared semantic observations but have separate target costs. |

IxIR₁ analysis results never feed backward into the same IxIR₀ˢ compilation.
If a downstream experiment suggests an earlier specialization, define its
required analysis at the earlier layer before making it a production input.
Physical layout changes driven by HPT/liveness/created-by belong in IxIR₂ or a
small following representation IR.

Source and IxIR₀/IxIR₁ semantics use fueled functional big-step evaluation;
IxIR₂ and x86 also expose executable small-step machines. The
[simulation strategy](simulation-strategy.md) explains the value, ownership,
heap-history, and compilation-trace relations. Direct structural passes use
local lemmas, sequence/block composition, declaration/SCC results, exact
address reconstruction, and public pipeline theorems.

Analysis-driven passes check conservatism and transfer obligations, not
leastness or optimality. A rejected optimization, unknown fact, or exhausted
analysis budget retains the last checked artifact. Invalid source is an
error. Every subsequent rewrite needs its own exact input/output equations;
a baseline lowering trace does not certify a later transformation.

IxIR₁ rewrites retain their declared same-fuel or one-way successful-run
contract. Recursive destruction and helper expansion can consume continuation
fuel, and shared destruction needs an RC-zero branch. These belong in
IxIR₂'s consuming/reset operations, with existential target fuel. Preserve
semantic, ownership, reclamation, and cost theorems as separate interfaces.

## Compiler entry points

These interfaces identify the existing checked artifacts without widening
their domains. The [roadmap's baseline](roadmap.md#delivered-baseline-and-continuing-limits)
and linked source-family documents give their current scope.

| Interface | Result and selection boundary |
| --- | --- |
| [`Pipeline.compileValidated`](../Compilatrix/Pipeline.lean) | Checked source erasure and owned IxIR₁. `Pipeline.compile` bypasses erasure certification and is not interchangeable for certified clients. |
| [`IxIR2.Pipeline.compileValidated`](../Compilatrix/IxIR2/Pipeline.lean) | Separate checked baseline CFG attachment with trace and provenance; exact logical/physical baseline composition uses the credit-free inventory. |
| [`Borrow.compileValidated`](../Compilatrix/Borrow/Pipeline.lean) / [`Borrow.select`](../Compilatrix/Borrow/Pipeline.lean) | [Closed borrowed-call certificates](source-borrow.md): owned wrappers, source/result agreement, RC improvement, reclamation/peak checks, and exact baseline fallback. |
| [`Borrow.Runtime.compileValidated`](../Compilatrix/Borrow/Runtime.lean) / [`Borrow.Runtime.select`](../Compilatrix/Borrow/Runtime.lean) | [Structural runtime borrowing](source-borrow-runtime.md): selection before arguments, lender preservation, owned-heap resource laws, and exact fallback. |
| [`Recursion.compileValidated`](../Compilatrix/Recursion/Pipeline.lean) | Optional checked recovery with generated artifacts, retaining original validated owned IxIR₁ on outer fallback. |
| [`CallReuse.compileValidated`](../Compilatrix/CallReuse/Pipeline.lean) / [`compileMap`](../Compilatrix/CallReuse/MapPipeline.lean) | v1 selection on a checked attachment; `compileMap` adds the optional closed-source map specialization and original-source fallback. |
| [`UniqueReuse.compile`](../Compilatrix/UniqueReuse/Pipeline.lean) | Opt-in `recursor-modes/1` closed-source schema, consuming IxIR₁, checked IxIR₂ translation, and optional static reuse with checked fallbacks. |
| [`X86.ValidatedScalar.compile`](../Compilatrix/X86/ValidatedScalar.lean) | The synthetic source scalar goes through the actual validated compiler and graph selector. |
| [`UniqueReuse.Native.select`](../Compilatrix/UniqueReuse/Native.lean) and [`Native.Output.emit`](../Compilatrix/UniqueReuse/NativeObject.lean) | Bounded exact-Word selection from the actual unique artifact, then main/release objects with real IxIR₁ and policy provenance. |
| [`UniqueReuse.Runtime.compile`](../Compilatrix/UniqueReuse/Runtime.lean) and [`Runtime.Native.Output.emit`](../Compilatrix/UniqueReuse/RuntimeNative.lean) | Checked one-argument unique reversal, exported consuming/static-reuse IxIR₂ function, and one native object pair for every admitted runtime list. The [runtime ABI](source-native-runtime.md) states input ownership, capacity, guards, and complete release. |
| [`X86.NatCalls`](../Compilatrix/X86/NatCalls.lean) | Structural closed Nat-call selection; [upstream contract](source-native-upstream.md) records source/object composition and supplied-state execution premises. |
| [`Scalar.Source.compile`](../Compilatrix/X86/ScalarSourceObject.lean) | Runtime scalar source-to-ELF compilation; [scalar contract](source-native-scalar.md) records arithmetic, control/calls, finite stack, and overflow behavior. |

## Contracts, analyses, and identity

Keep three kinds of information distinct:

- **Source contracts:** usage, ownership, and any future explicit locality
  affect Ixon identity.
- **Analyses:** HPT, liveness, borrow, created-by, escape, reuse, and register
  allocation are checked sidecars keyed by the input artifact.
- **Representations:** layouts and specialized definitions are compiler
  outputs whose identities include the evidence and policies selecting them.

An artifact key commits to exact input/dependency roots, checker/domain and
wire versions, resource limits, transformation/growth policy, and any
representation-sensitive target ABI. Key and store SCC artifacts atomically.
Transport across a rebuilt address namespace requires a theorem; inherited
keys do not become hashes of changed bodies.

The [IxIR addressing contract](ixir-content-addressing.md) and
[HPT certificate/cache discipline](hpt-certificates.md) are the model for
strict decoding, bounded checking, dependency invalidation, and local repair.
Until the roadmap's I2 gate closes, IxIR₂-scoped transient artifacts and
native provenance use the actual IxIR₁ root plus deterministic lowering/pass
policy. They do not advertise independent IxIR₂ persistence or body identity.
The initial IxIR₂ codec will commit to block order; renumbering is a separate
checked transform.

## Ownership, borrowing, and reuse

Usage, uniqueness, borrowing, locality, and layout are distinct concepts.
Using a value once does not by itself prove it has no aliases. The current
source contract deliberately bundles `linear` (exactly one use) and `affine`
(at most one) with unique ownership; `many` uses shared RC, and `erased`
has no runtime value. Arrow results additionally carry `Owned`. This adds no
definitional-equality rule; the theory-level conservativity proof remains
separate from operational compiler preservation.

Field worlds are currently homogeneous. Ordinary recursor lowering retains
its documented mode restrictions, while the checked unique-source schema
uses separately addressed recursor world vectors. That narrow instantiation
does not provide general usage polymorphism, mixed unique/shared fields, or
escaping unique recursor applications. See [lowering restrictions](lowering-restrictions.md)
and [source unique reuse](source-unique-reuse.md).

Both reuse lanes remain part of the design:

- `takeUnique` consumes a statically unique node and produces a required
  exact-layout credit without a runtime uniqueness test.
- `resetShared` consumes one shared owner. The RC=1 hot path moves fields
  and reserves the slot; the cold path preserves other aliases, retains the
  needed fields, and produces an absent optional credit.
- `allocWith` consumes a compatible present credit as a reuse; an absent
  optional credit requires fresh allocation. `discardCredit` releases a
  present reservation as a free. Taking/reserving alone is not a free.

Credits are affine and not ordinary heap values. v0 excludes them from calls;
the explicit v1 policy allows reservations in suspended non-tail direct-call
continuations. Tail calls, returns, PAPs, heap stores, and extern transfers
retain their restrictions. Callees cannot access caller-reserved slots, and
supported terminal runs discharge every reservation. Capacity-based reuse
requires a new compatibility policy and a specified header/alignment ABI;
exact `LayoutId` matching does not grant it.

Borrowed parameter syntax is already in IxIR₂. A borrow grants read/project
access tied to a lender; consuming or escaping it requires an explicit
ownership conversion allowed by the validator. Borrowed entries are
direct-call-only unless an owned wrapper supplies the required boundary.
A borrow rooted in a local owner cannot survive a tail call ending that
owner's lifetime.

Take/reset planning precedes borrow inference because those operations need
ownership. Checked borrow inference precedes final RC normalization because
it determines which caller/callee retains and releases can disappear.
Inference must validate that rewrite, not treat baseline's conservative
releases as evidence that every parameter inherently needs ownership.
The local projection-lowering `lowerBorrow` helper is not a whole-function
borrowed ABI.

The [closed borrowed-call contract](source-borrow.md) uses finite execution
certificates; [runtime borrowing](source-borrow-runtime.md) uses structural
function/continuation proofs. Their focused specifications define selection,
lender preservation, reclamation, cost laws, and current source restrictions.

RC coalescing needs ownership-flow and lifetime evidence. Moving a release
across an extern, reset, or allocation can change observations; delaying it
also needs a declared peak-space policy. Reuse the existing RC potential and
resource interfaces where their domains apply.

## Freeze, duplication, and mixed fields

There is no implicit unique→shared publication in the validated fragment.
Diagnose real `freezeNeeded` failures before selecting a representation:
preserving a lost let-bound mode and introducing deep freeze are different
changes.

An explicit freeze must decide uniform headers versus conversion/copying,
steal versus deep copy, recursive fields and PAP captures, and interactions
with externs and locality. It needs store, ownership, progress, reclamation,
and cost rules. Shared leaves under a unique spine are a separate possible
field-world extension: destruction would dispatch on child world, with no
implicit permission to put unique children under shared parents.

Duplication is explicit and cost-bearing: shared→shared retains; shared→unique
needs deep copy or checked steal/copy-on-write; producing two unique values
needs consuming duplication; region promotion needs an independently global
result. Denotational equality does not make these operations free or license
implicit contraction of unique values.

## Specialization and representation

Keep code growth separate from shrinking normalization. Run a bounded growth
stage once, normalize with a declared decreasing measure, and recompute
checked analyses on the new root when needed. Do not re-enter the same growth
stage under the same policy in an uncontrolled fixed point.

A normalized specialization key includes definition address, usage/world
instantiation, known higher-order targets, available scalar/layout facts, and
policy version. Include universes or erased arguments only when they affect
runtime code or representation. Cap variants per definition/SCC, normalized
argument size, and total code growth; order candidates deterministically and
retain generic fallbacks. Specialize recursive SCCs coherently.

The first recovery route is an IxIR₀ derived recursor, followed by ordinary
recursor lowering. A recognizer must show that demanded below-tuple
projections correspond to admitted recursive fields and do not escape.
Successful eager evaluation can justify the checked direct form, but
general `brecOn`, course-of-values, mutual/nested forms, and well-founded
erasure require their own proofs. Recognition generalization follows source
evidence, not a new frontend encoding of non-kernel recursion.

HPT answers possible shape; liveness answers which observations are needed;
created-by answers which producers can reach a consumer. HPT's
context-independent result summaries with parameter `top` do not supply
the other two. Prefer bounded explicit specialization over silently
introducing unlimited call-string sensitivity. A future contextual summary
must include normalized arguments, domain/budget version, and SCC widening
policy in its key, with a generic summary and a context cap.

Semantic `CtorId` survives physical layout changes. A representation identity
may refine `LayoutId` with a live-field mask, field layouts, and ABI version.
Deleting a field needs liveness plus complete producer/consumer lineage;
reuse must distinguish constructor identity from historical slot lineage.
Preserve eager and destruction effects unless separately proved removable.
Use a representation relation with ghost source information when deleted
payloads cannot be reconstructed from the target. Observable open roots
retain a conservative layout or an explicit versioned representation ABI.

Generalize the existing `HeapMap`, heap-history isomorphisms, and native arena
relation when another layout needs the shared interface. Valid accesses,
value correspondence, and non-overlap are useful obligations from
[CompCert memory injections](https://compcert.org/doc/html/compcert.common.Memory.html).
Reuse additionally needs historical names with injectivity on live objects
and separate reservation disjointness; global historical injectivity would
forbid legitimate slot reuse.

Broader PAP devirtualization requires captured payloads, not just a target
and arity. Heap-valued forwarding/CSE requires alias, ownership, and lifetime
evidence beyond scalar forwarding. These restrictions explain why the
[GRIN transformation inventory](https://github.com/grin-compiler/grin#optimising-transformations)
is a source of measured candidates rather than an implementation checklist.

## Native, runtime, and resource model

The first ISA is x86-64 System V. Typed selection targets physical IxIR₂:
reservations, reuse, and memory effects must be represented. Local ABI traps
for stack alignment, return discipline, or saved-register clobbers are
compiler-contract failures, not assertions about x86 hardware exceptions.
Top-level return defines the observation boundary to a native caller.

Keep the typed execution proof, E1 per-form encoding, E2 stream/object proof,
and S0–S2 reference bridge separate. The preferred reference architecture is
an independently maintained formal model, a reproducible Lean adapter, a
small proof-friendly local model, and an agreement theorem for the emitted
fragment. The [S0 readiness record](x86-reference-model.md) pins and maps the Sail x86
candidate; adapter and agreement proofs remain separate. The relation must
cover registers, RIP, relevant flags, memory, instruction lengths, and
normal/failure outcomes; generated syntax alone is not that theorem.

Add instruction forms from selected-program needs. Keep flags local to
justified compare/branch or arithmetic sequences until a consumer needs
general flag liveness. Division may use a named intrinsic with a trap
contract; SIMD, floats, atomics, signals, TLS, and dynamic linking need
separate models. Sequential reference agreement does not prove concurrency.

The physical IR fixes the allocator contract: reserved slots are unavailable
to other operations, reused slots have compatible layout, and discarded
reservations are released. The current arena is one implementation witness,
not a general allocation/RC runtime. Allocation failure, page acquisition,
header layout, fragmentation, and general shared destruction remain explicit
design decisions when those services are needed.

Distinguish live nodes, occupied slots (including reservations), layout bytes,
allocator capacity/overhead, and stack space. Evaluator fuel is none of these.
Native and zk implementations may use different representations and must
justify their own conversions from semantic counters.

Every persistent opaque interface belongs in the
[trusted-extern ledger](trusted-extern-ledger.md), with implementation source,
reachability, assumed behavior, integrity checks, and a retirement condition.
Hashing and durable-sync dependencies of the compiler host are not already an
ABI for effectful compiled programs. Define source/IR/target effects and
ownership before reopening the certified extern boundary.

Capability certificates can make runtime replacement non-circular: small
allocation-free helpers use a specified page/syscall boundary, bignums use
fixed-width limbs and unique buffers with erased mathematical specifications,
and drop/memcpy/reuse helpers compile in fragments whose runtime needs are
already discharged. Define rc-free, heap-free, alloc-free, and panic-free
precisely per root; they are not automatic implications between labels.

## Locality prototype

Locality is an escape property orthogonal to ownership. Shared but local
scratch graphs may have arbitrary internal aliases while avoiding per-object
RC and using bulk release. Its roadmap gate requires residual cost after
borrowing and reuse, then an IR experiment before source syntax changes.

A rank-2 `RegionM r` alone does not prevent a region pointer escaping.
Region-backed values must carry a marker such as `Local r α`, or an IR
certificate must prove equivalent nonescape. Constructors, containers,
projections, PAPs, and closures preserve that marker; there is no coercion to
a global value. Promotion produces an independently global value with a
specified copy/freeze cost.

The preferred experiment uses region entry, local allocation, and region
exit through the IxIR₂ block interface. Check all return, store, capture,
extern, and tail-call paths, distinguishing current, ancestor/caller, and
global regions. Tail calls end the current region; caller-region allocation
must not accumulate one region per loop iteration. A separate allocation
stack or arena need not share the machine call stack.

Reserved local slots die at region exit, so credit discharge is required per
region as well as per activation. Specify nested-region ordering, promotion,
growth/overflow, failure cleanup, and task ownership before extending the
prototype. A source locality bit would be deep by default, default to global
for ordinary Lean, and affect Ixon identity. Require a representative
shared-scratch workload, escape negatives, promoted-byte/high-water counts,
and native or zk improvement before that hash roll.

## Bootstrap and trust

Upstream Lean is the Gen-0 seed for the Lean compiler and checkers. Its
kernel, code generator, C/C++ runtime, host compiler, Nix inputs, and native
dependencies are recorded bootstrap provenance. Retire an execution
dependency only when the generated-program inventory shows it is absent;
replacing its implementation language alone does not discharge its behavior.

Gen 1 compiles the compiler's accepted source closure through the native
backend, enumerates its runtime dependencies, and rebuilds a successor.
Gen 2 compares a self-built successor at an explicitly defined artifact
layer, with an independently seeded comparison when practical. If raw object
bytes contain nondeterministic metadata, specify and check the comparison
layer; do not silently weaken “reproducible” to selected equal fields.

Keep four obligations distinct:

1. Theory adequacy and mode conservativity against public lean4ix and ix's
   checker-verification line.
2. Correctness of the executable checker/compiler, including its source
   representation and generated code; the small X1 witness precedes scaling
   this obligation to the compiler closure.
3. Remaining runtime, ISA, unchecked-emission, linker/loader assumptions and Gen-0
   provenance, each with its own inventory and evidence.
4. Statement faithfulness: what the user reads corresponds to the certified
   Ixon object. A sound checker alone does not establish this.

The eventual frontend retargets upstream parser/macro/elaborator behavior to
Ixon. Compatibility is complete environment/address equality. Start with
explicit mode annotations; infer them only after addressed contracts and
diagnostics stabilize. Structural and well-founded recursion arrive as
kernel terms; backend erasure/recovery must handle the required forms.

Before self-hosting, decide which recursion forms the compiler source may
use, the runtime subset, a practical rebuild budget, the attestation format,
and the exact artifact layer for comparison. Diverse compilation improves
seed evidence; it is not the executable-correctness or theory-adequacy
theorem. Interpreter-speed self-compilation is not the intended native exit.

## Measurement policy

Treat control flow, specialization, borrowing/reuse, and representation as
hypotheses to test on accepted programs. Record source origin, last accepted
stage, selected policy, runtime/resource observations, code growth, checker
cost, and evidence size. Keep hardware timing outside semantic certificates
and distinguish evaluator payload units from occupied bytes.

The [benchmark design](benchmark-plan.md) defines comparisons and expansion
criteria; the [implemented protocol](../benchmarks/protocol.md) defines the
runner. [Retained reports](performance/README.md) record results and limits.
A measured consumer activates further optimization or proof-engineering work
through the roadmap.
