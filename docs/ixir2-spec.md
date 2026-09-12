# IxIR₂ v0 specification

Editorial review: 2026-09-12. Syntax and execution-policy contracts are unchanged.

This document freezes the first IxIR₂ semantic data model. It is normative for
the v0 syntax, ownership-flow checker,
reuse-credit behavior, and IxIR₁→IxIR₂ simulation boundary. Forward-looking
pass ideas and acceptance gates live in the [roadmap](roadmap.md), with their
rationale in [compiler design](compiler-design.md). An implementation that
disagrees with this document must change the specification deliberately
rather than silently choosing a different contract.

The separately versioned [v1 call-credit extension](#v1-suspended-direct-call-credits)
below permits credits in suspended caller continuations. The original v0
entry points and their call rejection remain unchanged.

The in-memory syntax, bounded executable validator, and logical/physical
small-step machine are implemented in
[`IxIR2/Basic.lean`](../Compilatrix/IxIR2/Basic.lean),
[`IxIR2/Validate.lean`](../Compilatrix/IxIR2/Validate.lean), and
[`IxIR2/Eval.lean`](../Compilatrix/IxIR2/Eval.lean). Executable acceptance,
rejection, hot/cold reset, reuse/discard, PAP, and budget witnesses live in
[`IxIR2/ValidateExamples.lean`](../Compilatrix/IxIR2/ValidateExamples.lean) and
[`IxIR2/EvalExamples.lean`](../Compilatrix/IxIR2/EvalExamples.lean).
[`IxIR2/EvalCounter.lean`](../Compilatrix/IxIR2/EvalCounter.lean) supplies the
credit-local heap relation and proved local counter algebra.
[`IxIR2/Lower.lean`](../Compilatrix/IxIR2/Lower.lean) now supplies the
validator-gated structured baseline lowerer and its generated trace;
[`IxIR2/LowerExamples.lean`](../Compilatrix/IxIR2/LowerExamples.lean) executes
Nat and constructor branches against IxIR₁. The logical whole-main simulation
is attached in [`IxIR2/PipelineSim.lean`](../Compilatrix/IxIR2/PipelineSim.lean).
[`IxIR2/PipelinePhysical.lean`](../Compilatrix/IxIR2/PipelinePhysical.lean)
transports its exact execution to the physical baseline using the checked
absence of credit operations. The [general credit refinement](credit-refinement.md)
now covers both policies and the full instruction language, with explicit
logical root ownership for complete reclamation. The separately versioned
[canonical snapshot codec](ixir2-wire.md) now supplies strict bounded
decoding, exact full-body/context identity, and checked-source recovery.

This specification freezes the in-memory Lean model and proof interfaces.
The wire contract freezes numeric tags and complete preimages under
`ixir2-snapshot/1`, independently of semantic v0 and the two credit policies.
Diagnostic JSON has no wire identity role.

Read this specification in three parts: [syntax and capabilities](#program-and-identifier-model),
[ownership and execution](#ownership-flow-judgment), and
[checked lowering and simulation](#ixir₁ixir₂-lowering). The
[v1 call-credit policy](#v1-suspended-direct-call-credits) is an explicit extension
to the v0 rules.

## Scope and non-goals

IxIR₂ consumes the current fully addressed IxIR₁ graph plus checked sidecars
for source provenance, function-parameter worlds, constructor field worlds and
layout, exact HPT facts used by accepted projections and scalar-leaf frees, and—when
enabled—borrowed parameter ABIs. These facts are reconstructed from the
validated lowering trace and checked analyses; a bare IxIR₁ artifact without
them fails closed rather than guessing an ownership signature. IxIR₂
introduces the control and ownership structure needed by native and zk
backends:

- a CFG with explicit block parameters and tail transfers;
- block-local SSA value registers;
- explicit owned and borrowed capabilities;
- consuming unique destructure;
- dynamic shared reset with an observable hot/cold decision;
- affine, unforgeable reuse credits;
- a compositional simulation back to IxIR₁.

IxIR₂ v0 does not add source-level definitional equality, implicit
unique-to-shared freezing, region values, heap-valued externs, credit-passing
function ABIs, capacity-based reuse, or a new PAP representation. It also does
not send inferred facts backward into the same IxIR₀/IxIR₁ compilation.

The current certified pipeline rejects extern declarations. The generic IxIR₂
runtime retains IxIR₁'s scalar-only extern operation so unvalidated tooling can
translate the same engineering language, but certified IxIR₂ artifacts inherit
the closed extern boundary until a separate ownership ABI reopens it.

## Program and identifier model

Top-level declaration keys are logical symbols inherited from the addressed
IxIR₁ graph or introduced by checked specialization. They do not become
hashes of changed IxIR₂ bodies. The canonical snapshot root commits to all
actual bodies and their ordered finite context, including recursive logical
references. A function's blocks are local to that function.

The v0 model uses three disjoint natural-number namespaces:

```text
BlockId  := Nat
ValueId  := Nat
CreditId := Nat
```

Blocks are stored in an array and `BlockId` is its index. Block `0` is the
entry block. Value and credit identifiers are block-local definition ordinals:
block parameters occupy the initial ordinals, and each instruction appends its
results in the order specified below. Instructions carry no arbitrary result
names. The snapshot codec preserves these local ordinals and the given block
order. Renumbering blocks remains a separate checked transform.

Every cross-block value is transferred through an explicit block parameter.
An edge cannot refer directly to a register defined in another block.

The whole-program shape is:

```text
Decl    := function Function | extern Nat
Program := { declarations : addressed graph of Decl, main : Function }
```

The main function has no parameters and carries the pipeline's checked result
world. Extern declarations retain only their scalar arity and are absent from
validator-gated programs.

## Signatures and capabilities

Function parameters separate representation world from transfer behavior:

```text
ParamPassing := owned | borrowed

Param := {
  world   : Owned,       -- unique or shared
  passing : ParamPassing
}

Signature := {
  params : Array Param,
  result : Owned,
  papSafe : Bool
}
```

As in IxIR₁, a scalar dynamically satisfies either `Owned` result world.
`ParamPassing.owned` transfers one ownership root into the callee;
`ParamPassing.borrowed` leaves the root with the caller and gives the callee a
non-retaining view for the dynamic extent of the call.

Block parameters carry the checker-facing capability available at block
entry:

```text
BorrowLender := caller | value ValueId

ValueCap :=
  | scalar
  | owned    Owned
  | borrowed Owned BorrowLender

CreditCap :=
  | required LayoutId
  | optional LayoutId
```

`BorrowLender.caller` is legal only for a function parameter or a value
derived transitively from one. `BorrowLender.value i` names an owning value in
the same block. Serialized borrowed block parameters may name only another
owning parameter; instruction-derived borrows may name any prior live owning
value. The validator remaps lender identities across edges and rejects a
borrow whose lender is neither transferred nor caller-rooted.

The `scalar` capability is stronger information, not a third heap world. A
scalar may flow to any value parameter whose dynamic contract accepts
scalars. A possibly heap-bearing owned or borrowed value cannot flow to a
`scalar` parameter.

Credits occupy their own register file. They are not values, cannot occur in
constructor fields or PAPs, and cannot be returned or passed to a function or
extern.

## Layout boundary

Reuse compatibility is not constructor equality and is not guessed from field
count. A checked representation sidecar supplies:

```text
LayoutId := content-addressed identifier

CtorSchema := {
  layout : LayoutId,
  fields : Array Owned
}

SchemaEnv := Owned -> CtorId -> Option CtorSchema
```

Schemas are keyed by ownership world as well as constructor identity: the same
source constructor may have distinct unique and shared representations.

The sidecar may describe header class, payload capacity, alignment, and target
representation details behind `LayoutId`; those details remain parameterized
so native and zk backends can refine the same IxIR₂ semantics differently.
The schema and its ABI version are committed by the validation-certificate
root.

The only v0 compatibility relation is exact layout identity:

```text
compatibleV0 available requested := available == requested
```

Different constructors may therefore reuse one another when the checked
layout artifact gives them the same `LayoutId`. Capacity-based or
header-subtyping reuse requires a new compatibility-policy version.

Only constructor nodes produce credits in v0. PAP/closure slot reuse is
deferred with the ownership-aware callable representation.

## Block syntax

A function contains its signature, entry block `0`, and a nonempty block
array. A block contains value parameters, credit parameters, a sequence of
instructions, and exactly one terminator:

```text
Block := {
  valueParams  : Array ValueCap,
  creditParams : Array CreditCap,
  instructions : Array Instr,
  terminator   : Terminator
}

Function := {
  signature : Signature,
  blocks    : Array Block
}
```

The entry block has one value parameter per function parameter, in signature
order, and no credit parameters. Owned parameters become `ValueCap.owned`;
borrowed parameters become `ValueCap.borrowed _ caller`.

Atoms are value registers, literals, or erased values:

```text
Atom := reg ValueId | lit Literal | erased
```

Operands are resolved simultaneously from the pre-instruction register file.
Instruction results are appended only after all operands resolve.

### Instructions

The v0 instruction set is:

| Instruction | Results appended | Operational role |
| --- | --- | --- |
| `move value` | one value with the same capability | Translate IxIR₁ `pure` and explicit capability transfer. An owned token moves to the result; scalar/borrowed views may be copied. |
| `alloc world cid args` | one owned value | Fresh constructor allocation; consumes each heap-bearing field owner. |
| `allocWith credit world cid args` | one owned value | Consumes a required/optional credit. `some` reuses an exactly compatible slot; `none` allocates fresh. |
| `discardCredit credit` | none | Consumes a credit. A physical `some` slot becomes a free; `none` is inert. |
| `takeUnique target expectedCid` | schema fields, then one required credit | Consumes a live unique constructor, moves every field owner out, and reserves its slot. |
| `resetShared target expectedCid` | schema fields, then one optional credit | Consumes one shared owner. RC=1 moves fields and returns `some` credit; RC>1 retains fields, decrements the parent, and returns `none`. |
| `retainShared target` | one owned shared value | Adds one shared owner; scalars are inert. This is the explicit borrowed→owned adapter. |
| `releaseShared target` | none | Consumes one shared owner and performs deep RC-zero release. |
| `dropUnique target` | none | Consumes and deep-frees one unique value. |
| `freeUnique target expectedCid` | none | Shallow-frees a unique constructor. In v0 the checker requires a checked all-scalar field fact. |
| `fetch target expectedCid field` | one borrowed value | Non-consuming field access. The result loan is tied to the target's lender/root. |
| `call address args` | one result-world owner | Direct synchronous call under the addressed signature. |
| `callSelf args` | one result-world owner | Direct recursive call without an address cycle. |
| `papp address args` | one owned shared PAP | Existing IxIR₁ partial application, restricted to `papSafe` owned/shared signatures. |
| `apply function args` | one dynamically checked result owner | Existing consuming PAP application. Borrowed-ABI functions are not dynamically enterable in v0. |
| `extern address args` | one scalar | IxIR₁ scalar-only oracle call; absent from validator-gated artifacts. |

`takeUnique` and `resetShared` check the full `CtorId`, not only a constructor
index. A tag mismatch is stuck; a dead location, wrong world, malformed RC, or
layout mismatch is a memory error in the raw evaluator and impossible after
validation.

`takeUnique` returns fields in stored source order. The fields receive the
worlds in `CtorSchema.fields`; v0 unique schemas require every heap-bearing
field to be unique. `resetShared` has the same result order and requires every
heap-bearing field to be shared. Scalars remain ownership-polymorphic.

The optional credit returned by `resetShared` is the explicit RC-zero result.
Code can feed it directly to `allocWith` or inspect it with `branchCredit`.
There is no hidden optimizer-only branch and no attempt to encode the branch
as ordinary IxIR₁ code.

`freeUnique` exists only to translate the delivered all-scalar IxIR₁ leaf
specialization. A non-scalar shallow free rejects in v0. New consuming
transforms must prefer `takeUnique` followed by `allocWith` or
`discardCredit`; they may not synthesize raw shallow frees to bypass credit
accounting.

IxIR₁ `reuse` is outside the v0 translation input. The current production
baseline lowerer emits no reuse. The first post-lowering insertion slice
recognizes one exact compiler-emitted shared accumulator-reversal block and
introduces physical reuse only through IxIR₂'s credit path. Encountering a
pre-existing raw IxIR₁ `reuse` still fails closed until its own certified
translation rule is added.

### Edges and terminators

An edge names a target block and supplies complete value and credit argument
vectors:

```text
Edge := {
  target  : BlockId,
  values  : Array Atom,
  credits : Array CreditId
}
```

The v0 terminators are:

| Terminator | Behavior |
| --- | --- |
| `jump edge` | Transfer to one block. |
| `switchValue scrut constructors natPeel?` | Observe one dynamic scrutinee. Locations take the unique full-`CtorId` edge; when `natPeel?` is present, Nat literals take its zero/successor edge. The successor edge prepends the predecessor literal to its explicit value arguments. |
| `branchCredit credit some none` | Observe whether an optional credit is present and take the corresponding edge; the edge must still transfer or consume that credit on its path. |
| `return value` | Return one scalar or owned result and terminate the activation. |
| `tailCall address args` | Transfer directly to an addressed function. |
| `tailCallSelf args` | Transfer directly to the current function entry. |

`switchValue` deliberately does not bind constructor fields. A structured
IxIR₁ `case` lowers to tag edges followed by checked `fetch` instructions, or
to `takeUnique`/`resetShared` when the case is consuming. Keeping constructor
and optional Nat-literal dispatch in one terminator is necessary because one
IxIR₁ scrutinee may have either representation dynamically. Adapter blocks may
join a fetched constructor field and a peeled predecessor after giving them a
compatible parameter capability. This keeps ordinary block arguments explicit
and makes the lifetime of every field borrow visible to the ownership checker.

The combined constructor/Nat alternative set must be nonempty, and constructor
tags are unique. Missing tags retain the source stuck behavior. A Nat
successor target has one leading scalar parameter for the predecessor,
followed by its explicit edge parameters.

## Ownership-flow judgment

The executable checker reconstructs an instruction-by-instruction flow trace.
Its proof-facing form is a judgment of the shape

```text
schemas; signatures ⊢ block : entryCaps ⇒ terminatorCaps
```

where capabilities form a path-sensitive multiset. The following rules are
normative:

1. An owned capability represents one root token even in the shared world. It
   must be consumed exactly once on every terminating or outgoing path.
2. `retainShared` creates an additional shared root token. Merely mentioning a
   shared register twice does not duplicate ownership.
3. A unique root cannot be retained or copied. Observing it is permitted while
   no consuming transition has invalidated it.
4. A borrow may be read, fetched from, or passed to a borrowed parameter. It
   cannot be released, deep-dropped, reset, taken, stored, captured by a PAP,
   returned as a heap value, or passed to an owned parameter without an
   explicit `retainShared`/future clone.
5. Consuming a lender requires that every loan rooted at it is dead at that
   program point. Borrow death is determined by checked liveness; there is no
   runtime `endBorrow` instruction.
6. A borrow transferred across an edge must transfer its block-local lender on
   the same edge. Caller-rooted borrows may cross blocks without a local
   lender.
7. Constructor allocation consumes the owners for all heap-bearing fields.
   Field worlds must agree with the checked schema. Borrowed fields are
   rejected.
8. A normal call consumes owned arguments and merely observes borrowed
   arguments. The caller's lenders remain live until the call returns.
9. A tail call leaves no local owners or credits. A borrowed tail argument may
   be caller-rooted; a borrow rooted in a local owner is rejected in v0 rather
   than attempting an implicit lifetime extension.
10. Return consumes exactly the result owner (or a scalar) and leaves no other
    owned roots, live block-local loans, or credits.

At a conditional terminator, the same incoming capability may appear once on
each mutually exclusive edge. This is path sensitivity, not duplication.
Each individual edge must still use every linear owner and credit at most once.

PAP construction and dynamic apply retain IxIR₁'s current boundary: every
dynamically enterable compiler function has owned/shared parameters, a shared
result, and `papSafe`. Consequently `apply` appends one owned shared result
capability; a scalar extern result also satisfies that capability dynamically.
An extern PAP may capture only statically scalar arguments. A function with
any borrowed parameter is direct-call-only in v0.

## Reuse-credit discipline

A runtime credit is either absent or names one reserved constructor slot and
its `LayoutId`. There is no syntax for manufacturing a present credit.

The checker enforces:

- required credits are present; optional credits may be present or absent;
- a required `LayoutId` may widen to the same optional `LayoutId` at an edge;
- optional-to-required narrowing is forbidden;
- different layouts cannot join;
- each credit is consumed by exactly one `allocWith` or `discardCredit`, or is
  transferred exactly once on each outgoing path;
- credits may circulate through local loop backedges but may not cross a
  function call, tail call, return, PAP, heap store, or extern;
- terminal states contain no reserved slots.

`allocWith` never silently ignores an incompatible present credit. The raw
evaluator reports a memory error and the validator proves that branch
unreachable. A heuristic that proposes an incompatible pair is rejected by
the candidate checker; the optimizer may then select `alloc` or its unchanged
fallback and report the compatibility miss.

## Logical and physical semantics

IxIR₂ has one control semantics and two interpretations of credits.

### Logical interpretation

The logical semantics explains optimization against IxIR₁:

- successful `takeUnique` and hot `resetShared` shallow-free the old node
  immediately and return a layout-only credit;
- `allocWith`, whether its credit is present or absent, performs a fresh
  allocation;
- `discardCredit` has no store effect because the logical node was already
  freed.

### Physical interpretation

The physical semantics explains execution and native lowering:

- successful `takeUnique` and hot `resetShared` remove the node from the live
  heap but reserve its slot without incrementing `frees`;
- `allocWith some` writes the compatible node into that reserved slot and
  increments `reuses` rather than `allocs`;
- `allocWith none` allocates fresh;
- `discardCredit some` releases the reservation and increments `frees`;
- `discardCredit none` is inert.

Both interpretations make the whole consuming/reset transition one CFG step.
Moving fields, constructing a credit, and selecting RC=1 do not invoke a
recursive helper or steal transition fuel from the continuation. Cold shared
reset may perform one parent decrement and one retain per heap-bearing field;
those actions are atomic for control fuel but remain visible in RC and reset
cost observations.

The primary semantics is an unfueled small-step relation. Its total executable
runner has separate control and heap-traversal budgets. Control fuel decrements
once per instruction or terminator transition. Heap fuel is consumed only by
recursive primitives such as shared RC-zero release and `dropUnique`; it never
reduces the control fuel available to the continuation. Shallow
`takeUnique`/`resetShared` uses no heap fuel.

For compositional simulation, a successful recursive release/drop run that
ends with zero heap fuel can be replayed with any additive suffix: the same
store is produced and the suffix remains. Consequently the proof chooses heap
fuel backward from the continuation, reserving `local traversal cost + tail
budget` at each destructive instruction.

The public finite-step closure admits only transitions whose source control is
running, excluding the evaluator's inert halted self-step. Its composition law
adds exact step counts, and its runner adequacy theorem removes exactly that
count from the control budget. A finite execution ending in a halt therefore
constructs a successful `runMachine` witness with zero unused control fuel.
The same public reduction layer exposes baseline credit-free edge transfer,
ordinary jumps, exact constructor dispatch, both literal-Nat branches, and
direct/self call and tail-call entry, plus resumed and outermost return without
requiring clients to unfold the private instruction or terminator dispatcher.

IxIR₁→IxIR₂ correctness does not assert equal budgets: one source transition
may match zero or more target transitions, and successful-run wrappers
existentially choose both target budgets. This avoids the exact-fuel
obstruction that correctly blocked recursive destruction as an in-place
IxIR₁ rewrite while keeping executable totality explicit.

## State relation and counter laws

The physical/logical proof uses a live-location bijection extending the
existing IxIR₁ `HeapIso`. A physical reserved slot has no live logical
counterpart. A present physical credit records which logical free may later be
matched by either a fresh logical allocation/physical reuse pair or a physical
free.

Let `k` be the number of present physical credits. At every related state:

```text
logical.allocs = physical.allocs + physical.reuses
logical.frees  = physical.frees  + physical.reuses + k
logical.rcops  = physical.rcops
logical.live   = physical.live
```

At a validated terminal state `k = 0`, so each physical reuse accounts for
exactly one avoided logical free and one avoided logical allocation.

The shared observation record additionally contains:

- reset attempts;
- hot resets;
- cold resets;
- reused payload units;
- peak live nodes and, once a representation supplies it, peak live bytes.

Logical and physical executions agree on attempts and hot/cold decisions.
Compatibility rejections and unchanged fallbacks belong to the optimizer
report, not successful runtime counters.

The current implementation establishes this interface and the local counter
updates for take, hot/cold reset, reuse, discard, and fresh allocation, plus
the terminal free equation. `HeapContentsEq` isolates exact live-node-array
equality from observation counters. On the cold branch, the parent decrement
commutes with an arbitrary successful batch of field retains, including
repeated fields and a field equal to the parent. On the hot branch, exact root
ownership rules out a self-field; the baseline retain/deep-release prefix then
cancels to the logical shallow reset. Physical in-place replacement is related
to a fresh allocation after that concrete baseline prefix by a live-location
bijection mapping the reused slot to the fresh slot. A linked-node proof
fixture exercises the complete hot prefix, while executable non-degenerate
runs pin the intermediate and terminal counter laws. The later
[general credit theorem](credit-refinement.md) composes the actual primitive,
frame, continuation, and policy-step relations through whole-machine execution,
independently of a compiler rewrite template.

## IxIR₁→IxIR₂ lowering

### Baseline translation

[`Lower.lean`](../Compilatrix/IxIR2/Lower.lean) performs syntax-directed
translation of the no-`reuse` IxIR₁ subset:

1. Split structured code at cases and tail positions. Entry is block `0`;
   every cross-block value becomes an explicit parameter.
2. Translate operations in order. `pure` becomes `move`; effect-only result
   binders map to the erased atom.
3. Translate non-consuming cases to `switchValue`. Constructor arms fetch the
   old field binders; a Nat-successor edge supplies its implicit predecessor.
4. Preserve ordinary calls and use tail transfers only at syntactic tail
   positions. Function/self lookup remains tied to the exact declaration.
5. Reject raw IxIR₁ `reuse` until its own certified rule exists. Generic scalar
   extern translation remains available, but the certified attachment rejects
   extern declarations.

[`Pipeline.lean`](../Compilatrix/IxIR2/Pipeline.lean) attaches this translation
to `ValidatedCompilation`. It reconstructs parameter worlds, owner/constructor
identities, homogeneous field-world schemas, and layout from checked source
provenance. Ownership-signature conflicts reject. HPT facts are produced and
checked for the same addressed graph and replayed at exact source sites:
fetch needs a singleton constructor, shallow free needs complete scalar-field
facts, and case selection uses precise facts or checked residual targets.
Missing facts fail closed.

### Checked trace and source provenance

The returned artifact retains its literal input, one-pass lowering equation,
selected depth bound, successful target-validation equation, and recursive
function traces. The trace is proof data tied to emitted code, not a trusted
optimizer assertion.

| Audit | Retained obligation |
| --- | --- |
| Program correspondence | Source declarations, emitted declarations, and function traces align in order, ending in the distinguished main trace. Extern rows consume no function trace. |
| Function entry | Exact source body, arity/result/PAP policy, entry block and PC, reversed parameter map, and register count |
| Operation coordinates | Actual instruction lookup, translated operands, input/successor maps, binder growth, safe forgetting, and continuation placement |
| CFG edges | One predecessor map determines explicit arguments and successor mapping; dead slots carry erased placeholders, and the implicit Nat prefix is counted separately. |
| Branches | Exact source alternative, target edge, child body/entry, and complete constructor-field fetch prologue |
| Ownership flow | Every recursive position has a matching producer capability vector. Live inherited parameters agree with source capabilities; allocations, moves, borrows, destruction, and calls have their exact consume/suspend/result-bind effects. |
| Allocation/PAP | Field worlds and sequential argument consumption agree with the schema; PAP creation consumes shared captures and installs a shared owner. |
| Calls and returns | Callee lookup and signatures are exact; all matching predecessor/continuation coordinates agree on suspended roots and result binding. |
| Sidecars | HPT fetch/free/case evidence and recursor mutual-block identity belong to the actual input and emitted coordinates. Raw reuse is absent and function PAPs target PAP-safe declarations. |

`CodeStateRel` relates the exact target definition, block, PC, registers, source
map, and environment. `TraceStateRel` additionally carries the literal source
suffix and held HPT environment. Their initial states and successor/child
states are derived from the checked trace. Public semantic interfaces therefore
recover operand translation, edge readiness, field worlds, constructor
selection, and return-world checks internally.

### Dynamic shared reuse

[`Reuse.lean`](../Compilatrix/IxIR2/Reuse.lean) recognizes the complete
compiler-emitted all-shared prefix:

```text
fetchⁿ; retainSharedⁿ; releaseShared; alloc; tailCallSelf
```

Constructor arity, source-parameter position, and allocation/tail argument
permutations are not fixed. Every candidate needs bounded block-local liveness,
exact no-later-use evidence, identical reset/allocation `LayoutId`s, and
consistent all-shared field worlds. Same-arity layout mismatches stay unchanged.
The producer appends required/optional-credit helper blocks while preserving
old block IDs and incoming ABIs, then validates the complete target. A second
pass is an unchanged fixed point.

The exhaustive decision trace records accepted shape, placement, schema,
operands, generated blocks, or the failed phase for every original block.
It materializes the exact target and report. Unsupported input or rejected
validation retains the checked baseline.

[`ReuseLiveSim.lean`](../Compilatrix/IxIR2/ReuseLiveSim.lean) proves preservation
through finite macros. A baseline site takes `2 * fieldCount + 3` steps;
each rewritten arm reaches its recursive call in four. Hot physical reuse
updates a live-location bijection; cold allocation extends allocation history.
The invariant relates future-live registers, pending application arguments,
and credits. Dead saved registers may contain stale locations, so they do not
impose false non-aliasing conditions on callee reuse.

Compiler trace coverage and ownership derive suspended-root support,
allocation field worlds, mapped operands, accepted-entry phase, and hot/cold
macro premises. Exhaustive instruction/control dispatch and guided successful
execution compose these with ordinary blocks, calls, returns, and repeated
`applyMore`. The public compiler theorem closes the accepted-site obligation;
it does not require a caller-supplied missing simulation callback.

## Required simulation interface

### 1. Structured-control simulation

[`PipelineSim.lean`](../Compilatrix/IxIR2/PipelineSim.lean) exposes
`Attached.successfulCanonicalMainSimulation`: successful evaluation of the
exact attached IxIR₁ input produces logical IxIR₂ execution with a related
result/store and independently chosen sufficient target budgets.

The proof uses source-output-indexed continuations. Ordinary calls install a
resume handler; tail calls preserve the enclosing handler. `ApplyMorePlan`
handles erased, under-, exact-, and recursively over-saturated application.
Constructor branches include the edge and generated field-fetch prologue;
Nat branches include their exact predecessor transfer. Recursive destruction
adds its local heap work to the continuation budget.

`SourceOwnershipAt` records active owners, suspended caller roots, and paths
from borrowed values to lenders. Checked capability transitions establish it
at every recursive position and derive call-entry/resumption ownership.
Constructor selection, scalar-leaf facts, field worlds, and return checks come
from the attachment and source evaluation, rather than extra caller premises.
The [simulation guide](simulation-strategy.md) describes the proof decomposition.

### 2. Credit implementation refinement

[`CreditRefinement.checked_runMain_refines`](../Compilatrix/IxIR2/CreditRefinement.lean)
relates successful logical execution of the same checked program to physical
execution under both policies, with the same or independently successful
budgets. Every physical prefix has a related logical prefix and the intermediate
counter law includes all suspended reservations.

`checked_runMain_owned` constructs the live-heap isomorphism, source-value
transport, and both complete releases from explicit logical `RootOwnership`.
It derives allocation order and release fuel internally. Validator acceptance
alone does not imply that semantic ownership premise. The
[R6 contract](credit-refinement.md) owns the full API and its error/effect/
capacity boundaries.

### 3. Pipeline composition

The [physical baseline bridge](../Compilatrix/IxIR2/PipelinePhysical.lean)
uses the checked absence of credit operations. Selected reuse adds its own
compiler refinement and exact fallback. Public composition retains successful
source preservation, target progress/memory safety at its stated domain,
owned results, complete reclamation, and separately named cost laws.

For [recovered shared mains](source-recursion.md), the selected endpoint is
`sourceRefinesSelectedWithCostLaws`. It includes both selection branches and
independent sufficient budgets, with:

```text
live + frees + presentCredits = allocs       -- every physical prefix
live + frees = allocs                        -- at halt
live = 0, allocs = frees                      -- after complete release
baseline.allocs = selected.allocs + selected.reuses
baseline.frees  = selected.frees  + selected.reuses
selected.rcops ≤ baseline.rcops
selected.peakLiveNodes ≤ baseline.peakLiveNodes
```

The comparative free/RC/peak laws also cover complete release. Selected-prefix
observations are bounded by the baseline's terminal costs, including internal
reset states. These claims use their explicit shared-main and source premises;
semantic heap relations omit counters. Outer source-recovery failure retains
the original owned IxIR₁ result and release.

[Reuse across calls](source-call-reuse.md) extends selected compilation to the
v1 policy below. Other CFG, recursion, borrow, or RC passes must supply their
own composed refinement or independently checked evidence. Optional failure
retains the last validated artifact.

## V1 suspended direct-call credits

`CreditPolicy.callLocalV0` has tag `call-local/0` and selects the original
contract above. `CreditPolicy.suspendedCallsV1` has tag
`suspended-direct-calls/1`. `Validate.validateWithPolicy` and
`Eval.Policy.runMain` require this policy explicitly. The old validator and
runner retain v0 behavior; `Policy.runMain_v0` proves exact compatibility.
This is an execution-policy version, not an IxIR₂ wire-format version.

V1 changes only non-tail direct `call` and `callSelf` at the credit boundary:

1. The caller's credits stay in its saved frame in the return continuation.
   No credit appears in a value argument or callee credit parameter.
2. The callee starts with an empty credit file. It can create its own credits;
   their ownership is disjoint from every suspended ancestor.
3. Callee return still requires all callee credits consumed. Resumption
   restores the caller's exact credit file, which may then be consumed by
   `allocWith`, discarded, or transferred once along an outgoing CFG edge.
4. Present required, present optional, and absent optional credits use this
   same suspension rule. Layout compatibility and required/optional edge
   rules are unchanged.
5. Return, tail calls, PAP construction, dynamic application, and extern
   invocation still require the active frame's credit file to be exhausted.
   An ancestor's suspended credits do not become accessible at those boundaries.

`Machine.ReservationOwnership` records all present physical reservation
locations in the active frame and continuation stack. The locations are
distinct and name existing empty heap slots. Every successful physical step
under either policy preserves this invariant. Actual main execution derives
it for every prefix, so a callee allocation cannot consume an ancestor slot.
The resource account is `live + frees + presentReservations = allocs`, with
all suspended frames included; halt yields `live + frees = allocs`.

The checked `shared-call-reuse/1` pass recognizes a shared consuming
fetch/retain/release prefix, a nonempty direct-call sequence, one compatible
allocation, and return. Exact source syntax, ownership, last use, and layout
are checked. Reset and register moves replace the prefix; `allocWith` consumes
the optional credit after the calls. The pass validates the complete v1
target and keeps its checked v0 baseline on unsupported input or target
rejection. General user-written credit programs are outside this compiler
refinement theorem, even when the validator accepts them.

`PipelineCallReuse.lean` derives actual selected physical execution with the
existing semantic value/heap relation and separate allocation/free/RC/peak
laws. It covers all selected prefixes and complete shared-result reclamation,
both selection branches, and independent sufficient execution budgets. The
source endpoints in `CallReuse/Sim.lean` and `CallReuse/MapSim.lean` need only
the original source sharing/oracle/success premises. The map endpoint checks
and specializes actual erased closed Nat-map source before ordinary lowering;
outer fallback retains original owned IxIR₁ execution and reclamation.

The [source-map gate](source-call-reuse.md) records the exact recognition
domain, nine hot/cold/mixed source executions, 35 policy/rejection checks,
complete fresh-process snapshots, and independent reservation/cost corruption
checks. Canonical provenance includes the addressed IxIR₁ graph, HPT roots,
source root, and lowering/pass/execution/specialization policies. Diagnostic
IxIR₂ JSON is not a persistent identity. The separate
[snapshot format](ixir2-wire.md) commits to the actual selected program and
context through the checked call-reuse adapter.

## Executable validation and resource limits

The validator checks at least:

- nonempty block arrays, entry block `0`, valid targets, and bounded counts;
- canonical block-local value/credit ordinals and use-before-definition;
- edge arity, capability compatibility, and lender remapping;
- addressed function existence, call arity, result world, and `papSafe` use;
- constructor existence, full identity, field count/worlds, and layout;
- unique constructor alternatives and exact optional Nat-successor shape;
- owned-root and borrow rules on every path and loop backedge;
- credit linearity, optionality, exact-layout compatibility, and empty
  terminal credit state;
- the closed extern policy when invoked by validator-gated compilation;
- a finite work budget for blocks, instructions, edges, dataflow iterations,
  schema lookups, and certificate bytes.

Recursive CFG validation is a bounded fixpoint over block-entry capabilities.
The candidate supplies proposed entry states; the checker verifies every edge
and requires a post-fixpoint. Leastness is not trusted or required. Resource
exhaustion is a named rejection, never host timeout behavior.

Before content addressing, accepted blocks are serialized in array order with
all signature, capability, layout-policy-version, instruction, and terminator
fields committed. A later canonical block-renumbering pass may improve address
reproducibility, but it must preserve this semantics and cannot make block
identity depend on allocation order or pointer identity.

## Regression coverage

Positive witnesses:

1. Structured lowering of an IxIR₁ case with two explicit successor blocks.
2. A loop carrying ordinary values through block parameters and ending in a
   tail self-transfer.
3. Unique constructor take followed by exact-layout `allocWith`, with physical
   reuse and the logical counter equations checked.
4. Unique take followed by `discardCredit` on one branch.
5. Shared reset whose RC=1 run takes the `some` branch and whose RC>1 run takes
   the `none` branch, with equal semantic results.
6. A diamond that transfers one optional credit through both mutually
   exclusive edges and consumes it after the join.

Negative witnesses:

1. credit duplication on one path;
2. return, call, tail call, PAP capture, or heap storage with a live credit;
3. use after `takeUnique`/`resetShared`;
4. consuming a lender while a field borrow is live;
5. borrow escape through return, owned call argument, or allocation;
6. incompatible-layout `allocWith`;
7. required/optional or layout mismatch at a join;
8. malformed block target, edge arity, result ordinal, switch tag, or schema;
9. borrowed-ABI dynamic PAP entry;
10. pre-existing raw IxIR₁ `reuse` at the v0 translation boundary.

The structured case fixture is producer-generated. Baseline whole-main
simulation and the source-family gates below provide theorem-backed coverage.
The v0 live-credit call negatives remain distinct from permitted v1 suspension.

## Static unique translation and selection

`UniqueLower.Translation` is a separate, fully validated translation of the
exact consuming IxIR₁ artifact produced by the checked closed-list reversal
schema. The source endpoint checks usage under `recursor-modes/1` and records
the source and specialized recursor worlds in canonical instance identities.
It does not broaden the ordinary v0 lowering interface.

Consuming extraction and shallow parent release translate to `takeUnique`
followed by `discardCredit`. The static pass checks last use and layout, then
replaces the cons discard and fresh allocation with `allocWith`. The nil
branch discards its final credit. Every tail or return boundary has no credit,
so both baseline and selected programs use the existing `call-local/0` policy.
The complete baseline and selected targets each cross the ordinary validator.
Optional reuse failure retains that exact checked baseline; target translation
failure retains the consuming IxIR₁ artifact.

`Translation.forwardSimulation` relates any successful execution of its indexed
IxIR₁ input to either target interpretation. Actual emitted-main proofs give
exact no-RC FIP counters for arbitrary accepted finite Nat lists and ownership
of every physical reservation prefix. Full release handles forward links
created by in-place reversal. The source endpoint derives these facts from
checked compilation and the established source evaluation premises. See
[source unique reuse](source-unique-reuse.md) for its domain, costs, independent
budgets, fallbacks, and artifact gate. The delivered [native subset](source-native-unique.md)
selects this actual artifact into a bounded arena ABI, with full byte-memory
main/release proofs and source-produced native objects. General unique lowering
and wider native heap selection remain separate extensions.

## Checked borrowed source calls

The optional [B1 pass](source-borrow.md) consumes the exact checked baseline,
infers unary shared borrowed entries, reconstructs every affected body and
call site, and validates the complete result. Original signatures remain
owned wrappers for dynamic/PAP entry. Root retains become borrowed moves;
root releases disappear; projected-field retains remain ownership adapters.
Tail borrows require caller lenders. Take/reset, credit effects, externs, and
self-call forms reject a candidate; conservative baseline releases alone do
not force an owned signature.

Selection additionally derives exact finite source and physical executions.
Only equal scalar results, complete reclamation, strict executed-RC reduction,
and no peak-live-node increase can select the candidate. This is a bounded
closed-program translation-validation contract, not an arbitrary-runtime-input
function simulation. Twelve ownership/resource negatives, field-retain
preservation, three checked source fallbacks, ten axiom fences, and an
independent full-prefix artifact gate pin the delivered boundary.

The [B2 attachment](source-borrow-runtime.md) checks a reusable structural
certificate for an accepted open shared tag-reading source function and every
inferred summary, callee, and owned wrapper. Selection has compiler/checker
limits but no runtime argument or replay fuel. `Open.Entry.steps` derives
actual function and continuation paths; `lenderLifetime` preserves the exact
store at every borrowed prefix. Later caller take/reset facts survive return.

`Open.Input` requires one external shared root owning the whole allocation-
ordered heap, balanced accounting, and a valid saved peak. Payload descendants
are unrestricted by size. Root ownership constructs release fuel and proves
empty final heaps, with exactly two fewer executed RC operations and unchanged
peak at the owned entry. Its wrapper adds one control transition. The source
composition consumes the actual erasure attachment and successful Ixon
application under the existing sharing/oracle premises. Fifteen axiom fences,
144 independent direct/PAP comparisons, aliased lenders, exact fallback, and
twenty corrupted artifacts pin this extension. General recursive SCCs and
native shared borrowing remain outside it.

## Extension policy

The [finite-storage resource semantics](finite-space.md) adds checked heap and
explicit control budgets to actual physical policy execution. Its versioned
Word-valued slot model distinguishes live/reserved occupancy from committed
backing storage and charges saved caller values and credits. It has its own
representation admission and capacity errors; evaluator fuel, the existing
peak-live results and native ABIs retain their separate meanings.

The in-memory syntax and semantics support static unique and dynamic shared
reuse with the same ownership/layout contracts. Extend them through separately
checked passes and explicit policy versions. The [roadmap](roadmap.md) owns
remaining work, including general native selection and modular certification;
this specification does not maintain a second implementation queue.
