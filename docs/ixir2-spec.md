# IxIR₂ v0 specification

Last reviewed 2026-09-07.

This document freezes the first IxIR₂ semantic data model. It is normative for
the v0 syntax, ownership-flow checker,
reuse-credit behavior, and IxIR₁→IxIR₂ simulation boundary. Forward-looking
pass ideas remain in the local plans; an implementation that disagrees with
this document must change the specification deliberately rather than silently
choosing a different contract.

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
absence of credit operations. General credit refinement and the codec remain
separate gates; the [roadmap](roadmap.md) records their state.

The freeze covers the in-memory Lean model and proof interfaces. Numeric wire
tags and a persistent codec are not frozen yet. No artifact may advertise a
stable `IxIR2/v0` wire version until the strict decoder, canonical encoder, and
content-address preimages are documented alongside their executable guards.

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

Top-level declaration identity continues to use ordinary declaration hashes
and cycle-safe mutual-block identities. A function's blocks are local to that
function and therefore do not create address cycles.

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
names. This makes alpha-equivalent blocks byte-identical once a codec lands.

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
runs pin the intermediate and terminal counter laws. Whole-machine
logical/physical refinement remains to be composed through the checked rewrite
and structured lowering; these local theorems do not claim that induction.

## IxIR₁→IxIR₂ lowering

Baseline lowering is syntax-directed and does not require an optimization
oracle:

1. Split each structured `Code` at cases and tail positions.
2. Make the function entry block `0` and pass every cross-block live value as
   an explicit parameter. The first implementation may conservatively pass
   more values; parameter reduction is a later checked optimization.
3. Translate `letOp` sequences in order; `pure` becomes `move`, while
   effect-only instructions map their erased IxIR₁ result binder directly to
   the erased atom.
4. Translate non-consuming cases to `switchValue`; materialize the old
   constructor-alternative field binders with checked `fetch` instructions and
   the literal-successor binder from the terminator's implicit predecessor.
5. Preserve `callSelf` unless it is syntactically tail-positioned, where it
   becomes `tailCallSelf`. Recognized direct-recursion recovery is a later
   candidate validated through the same block interface.
6. Translate the current no-reuse source subset. A raw IxIR₁ `reuse` rejects
   until its own certified rule exists.
7. Retain scalar-only extern behavior in the generic translator and reject it
   at the certified pipeline gate.

The lowering trace is a recursive derivation tree over the exact IxIR₁ code.
Every node retains its source site, source and successor environment maps,
generated block, and exact instruction coordinate where applicable; case
nodes retain their recursive alternatives. Successful function lowering
retains the literal IxIR₁ function definition and checks reconstructed source
code, arity, result world, and PAP policy alongside preorder block generation
and instruction placement against the emitted function. Entry block, entry
program counter, entry register count, canonical reversed-parameter map, every
instruction-to-continuation PC/register-count increment, binder-map head,
exact one-slot proof-map growth, and safe forgetting of older slots are
checked as part of the same certificate. A separate recursive audit checks
that every trace node beginning at target PC zero has exactly the value count
declared by its completed head block's parameter ABI. Descendant compiler
states can therefore derive an accepted entry's parameter count without a
caller premise.
The producer also checks each retained source operand against the emitted
instruction and every terminal source form against its emitted terminator.
Descendant lemmas therefore recover actual block/instruction lookup, operand
translation, map progression, and terminal syntax from trace membership
rather than taking those facts as semantic-theorem premises.

The simulation packages target definition, block, PC, register count,
source-environment/proof-map cardinality, and environment alignment in
`CodeStateRel`. The exact target `runMain` initial machine is proved to satisfy
this relation at the distinguished trace root.
The trace-facing `pure`→`move` theorem needs only that state, source operand
resolution, and machine control, and produces `CodeStateRel` for its recursive
continuation; operand translation and successor-map progression come from the
checked trace. The trace-facing outermost-return base similarly derives its
block, terminal PC, translated operand, and terminator from the certificate.
Generic checked instruction lookup, map forgetting, and successor-state
lemmas lift allocation, retain, scalar and recursive drop, shallow free,
fetch, and function-PAP cases to the same recursive-state interface. Function
entry is a `CodeStateRel` at any retained root; direct, self, and tail calls
enter that state, while a traced resumed return reconstructs the suspended
caller's exact continuation state.

The returned artifact itself retains the literal lowering input and a
distinguished main-function trace. A checked external match ties that trace to
the input's closed synthetic main and to the emitted program's actual main;
the resulting theorem exposes the exact root source code without replaying or
searching the compiler trace. A second fail-closed whole-program check aligns
source declarations, emitted declarations, and function traces in order
(externs consume no trace), ending in the sole main trace. Its reflected
relation resolves any source function occurrence to its exact emitted
definition and recursive trace, providing the callee-lookup boundary for the
semantic induction.

The trace also records the environment-to-parameter relation at every edge.
That proof map distinguishes live slots from consumed slots: live entries
name successor-local registers, dead entries are absent even though the
executable edge carries an `erased` placeholder, and an implicit Nat
predecessor is prepended explicitly. Each edge retains one predecessor input
map; its explicit operand vector and shifted successor map are computed
projections rather than independently supplied arrays. The branch certificate
also checks that target parameter count is the predecessor-map size plus the
implicit prefix. Consequently the complete `CodeStateRel` environment derives
successful edge-operand resolution and exact arity; semantic switch theorems
do not accept a caller-provided readiness witness. These witnesses are proof
data; they are not trusted claims from the optimizer.

The current executable tranche implements this baseline for the no-`reuse`
subset. Owner-keyed sidecars supply parameter worlds and exact constructor
identities at fetch, scalar-leaf free, and case sites—the facts IxIR₁ syntax
intentionally erased. The producer derives block IDs, SSA ordinals,
capability flow, conservative join parameters, leaf-fact target coordinates,
and the trace, then retains the exact successful validator equation. The
fuel-structural block worker is a public proof definition, and checked runs
retain its enclosing exact lowering equation without executing the compiler
twice. After validation, checked runs retain two recursive projections: every
traced ordinary allocation resolves an exact schema whose fields are
`replicate sourceOperandCount sourceWorld`, and its flat trace coordinate
retains the producer's exact pre-operation capability vector. The allocation
audit checks live/dead shape against the source input map, requires every field
operand to be scalar or an owner in the allocation world, and certifies the
exact continuation vector obtained by consuming those arguments sequentially
and prepending the fresh result owner. The same audit treats a function-PAP
allocation as shared capture consumption followed by a fresh shared PAP owner.
This keeps the later semantic proof independent of validator dataflow
internals. A separate
whole-trace audit requires every recursive node to have a matching flat
source/block/target coordinate with the exact capability/input-map shape, and
the checked API reflects such a position for any descendant. Nat and
constructor cases, fetched-field ownership, tail calls, missing facts, and
raw-reuse rejection have executable guards. For ordinary direct and self
calls, every matching predecessor/continuation pair must satisfy the same
argument-consumption, suspended-root, and result-bind transition. This
all-pairs check prevents duplicate flat coordinates from selecting
incompatible suspended caller frames.

`IxIR2/Reuse.lean` is the first post-baseline insertion checkpoint. Its public
entry validates the baseline program and recognizes the complete
compiler-emitted all-shared
`fetchⁿ; retainSharedⁿ; releaseShared; alloc; tailCallSelf` prefix without
fixing constructor arity, source-parameter position, or allocation/tail
argument permutations. Every candidate crosses the bounded block-local
liveness checker and retains an exact no-later-use witness. The reset and
allocation schemas must carry identical `LayoutId`s and consistent all-shared
field vectors. Separate required- and optional-credit successors are appended
under the same validation bounds. Old block IDs are preserved, so unrelated
CFG edges do not move. A same-arity allocation with a different layout remains
unchanged and is counted as a compatibility miss; a second run is an unchanged
fixed point. The traversal retains an exhaustive dependent decision for every
literal source block, including the exact failed phase for unchanged blocks.
Accepted decisions retain the recognized shape, checked placement, compatible
representation, and translated operands. Function-level accessors resolve the
replacement at the old block ID and both appended helper IDs; declaration
traces preserve order and map evaluator function lookup to the exact retained
function rewrite. The checked output proves that this trace materializes its
validated target and report.

The companion bounded benchmark begins at an IxIR₀ recursor and compares its
source observation with baseline IxIR₂ plus logical and physical rewritten
execution on both all-hot and all-cold inputs. This supplies the first
compiler-emitted performance witness, but not the required general rewrite
simulation: broadening the recognizer requires a checked liveness plan and a
compositional proof before dynamic shared reset/reuse is a delivered pass.

That proof no longer needs to unfold the evaluator's private instruction or
terminator dispatchers. The public small-step interface has exact rules for
logical/physical hot reset, common cold reset, all valid `allocWith` and
`discardCredit` modes, unique credit production, and present/absent credit
branches. Public credit lookup, linear take, batch take, constructor view,
no-live-credit, and general credit-carrying edge-transfer judgments supply the
premises needed to compose those rules. Every call, return, PAP, extern, and
dynamic-apply boundary also accepts a nonempty credit file once all slots are
consumed, matching states reachable after credit-producing rewrites. Their
axiom sets are pinned in the repository fence.
`IxIR2/ReuseSim.lean` proves the cold-prefix commutation, hot-prefix
retain/release cancellation, and the combined physical-reuse-to-concrete-
baseline-allocation heap isomorphism. Accepted-site inversion now exposes the
recognized source syntax, runtime schemas, generated blocks, and both
translated operand vectors. A canonical baseline/helper register relation
then proves exact branch-argument resolution and transports allocation and
tail operand resolution, including arbitrary location renaming. The recognized
baseline block now executes every fetch and retain followed by release,
allocation, and self tail call in exactly `2·fieldCount + 3` steps. Each
rewritten arm reaches the recursive call in four steps. Rewrite-aware
accepted-site theorems obtain the source/reset/helper lookups directly from
the retained decision trace: logical hot and cold preserve the exact recursive
argument vector and heap contents, while physical hot maps the reused result
to the baseline fresh result and transports preserved operands to an
isomorphic heap and related call vector. The logical-hot and cold theorems also
compose from distinct counter-divergent stores with equal semantic heap
contents and a dominating rewritten heap budget. Physical hot additionally
composes over an existing target-to-baseline live-location bijection: the
consumed pair is removed, the reused/fresh result pair is added, every other
old pair and both exact ownership states are preserved, and related suspended
stacks avoiding the consumed location are transported to the new relation.
The rewrite trace now also classifies
every original block as unchanged or accepted and proves that every replacement
retains its incoming value/credit ABI. A stable machine relation packages
exact-content or physical-isomorphic heaps, related frames and continuation
stacks, distinct evaluator contexts, and rewritten heap-fuel dominance.
Exact-content lockstep is proved for the ordinary heap and scalar operations;
self/direct calls, function- and extern-targeted PAP creation, and scalar
extern calls; return and tail-call boundaries; and all jump, constructor/Nat
switch, and optional-credit branch forms. The credit-bearing instruction cases
are branchwise too:
absent/logical/physical `allocWith`, all `discardCredit` modes, logical and
physical `takeUnique`, and hot-logical/hot-physical/cold `resetShared` transport
credit-file updates, reservations, counter-insensitive heap contents, and cold
field-retain loops. Together these lemmas cover every instruction and
terminator constructor on unchanged blocks. Public edge-transfer congruence
carries branches across the rewritten definition using the preserved target
ABI. Exact-content dynamic application covers erased argument release,
under-saturated PAP extension, saturated and over-saturated compiler PAP entry,
and exactly saturated scalar extern PAP entry. The branch proofs preserve
rewritten heap-fuel dominance and related resume/apply-more continuations, and
common wrappers lift them through both the `apply` instruction and return-time
`applyMore` boundary. Indexed evaluator relations classify every successful
application transfer, instruction worker, terminator worker, and public
`Step`. Trace-driven instruction and terminator theorems eliminate those
classifications across all runtime branches, selecting rewritten
function/extern declarations automatically; a final one-step theorem closes
the literally unchanged block arm. A positive finite-macro relation and
trace-driven block eliminator combine that arm with a full accepted macro;
direct logical-hot and cold constructors consume the corresponding ownership,
retain/release, and field-world runtime premises. Physical hot has the same
macro interface over a pre-existing live-location bijection. The cold macro is
also allocation-history aware: it transports distinct parameters and fields,
commutes the baseline retain/release prefix into reset order, extends the
history with corresponding fresh allocations, and rejoins with related call
arguments and continuations after an earlier reuse. The proof layer also
supplies relation-aware batch credit transfer and an exhaustive
allocation-history dispatcher for every instruction, dynamic-application
branch, terminator, and whole `Step`. Exact-content and history-isomorphic
states meet at one `StableHeapRel` macro dispatcher. Determinism and halted
prefix cancellation feed a strong induction over invariant-preserving macros;
the resulting finite-execution theorem and exact `runMachine` corollary already
handle variable source/target macro lengths. A call-boundary audit found that
whole-array stack non-aliasing cannot be that global invariant: the evaluator
suspends the complete append-only caller frame, so a transferred owner remains
in a dead register even though the callee may physically reuse its address.
`IxIR2/ReuseLiveSim.lean` therefore defines the compiler-facing relation in
terms of `Liveness.blockUses`. It relates only values used at or after a
suspended frame's current program counter, continues to relate every pending
`applyMore` argument, and transports a location-relation replacement using
avoidance of precisely those observable slots. The older all-register stable
relation embeds into this one. Declarative instruction, terminator, and edge
operand relations reflect into the executable liveness scan, and every scan
entry inverts back to an actual instruction or terminator operand. Local step
proofs can therefore recover operand liveness from syntax without accepting it
from their callers. Live frame primitives cover result pushes, vector appends,
operand resolution, credit lookup and consumption, and CFG edge transfer. The
unchanged layer covers moves and fetches plus every direct control boundary:
self/direct calls and tail calls, jumps, constructor/Nat switches, optional-
credit branches, resumed returns, and terminal returns. The remaining
ordinary instruction cases are live-indexed as well: allocation and free,
all credit-taking/discarding and reset modes, retain/release/drop, PAP
creation, scalar extern calls, and every erased/under-/saturated dynamic
application path, including return-time `applyMore`. Exhaustive live
instruction, terminator, and public `Step` dispatchers derive current operand
liveness from syntax and select rewritten declarations from the program
trace. A trace-driven live block eliminator packages unchanged steps and
leaves exactly one accepted-site macro callback. A positive macro relation,
invariant-preservation interface, finite-execution induction, and exact
`runMachine` corollary have also been lifted to the live relation. Logical hot,
cold, physical hot, and history-aware cold accepted macros now rejoin in that
live relation. In particular, physical hot reuse transports a suspended stack
using avoidance only for its future-live registers, pending `applyMore`
arguments, and credits. Observable suspended values now also carry semantic
support from the exact source roots framed around the active callee. At a
checked no-borrow position, environment correspondence, source ownership, and
coverage of every future-live target register by the trace input map establish
that support. Conversely, unit-refcount ownership of the consumed shared root
and an existing heap isomorphism turn supported related stacks directly into
the non-aliasing witness required by physical reuse. Checked trace structure
now proves that every future-live register in any related code state is covered
by its source input map, propagating through forgotten maps and all terminal and
switch forms. The concrete compiler running state therefore derives active-
frame coverage from its code-state relation and checked descendant, while it
records suspended-stack root support; both facts hold for the exact initial
main machine. At an ordinary addressed or self call, the audited capability
transition, surviving capability semantics, and no-borrow condition now turn
that derived successor coverage into root support for the newly suspended
caller frame. A typed `CompilerStackState` now runs in parallel with the target
resume stack and retains exactly the source caller trace, pre-call runtime and
ownership facts, surviving capabilities, live-stack support, and heap-image
provenance needed after return. Addressed/self ordinary-call entry pushes this
witness; exactly saturated dynamic PAP entry pushes a corresponding apply
witness derived from one common producer capability vector, while
over-saturation pushes an indexed `applyMore` witness whose shared residual
roots support both the exact target argument vector and the suspended caller.
Addressed/self tail-call entry preserves every form. Given the completed source
operation exposed by evaluator inversion, `CompilerStackReturn` aligns an
ordinary-call or exact-apply head witness with the callee's output store and
value, and `CompilerRunningState.returnResume` pops it in the same target step
while reconstructing every caller invariant. `CompilerApplyMoreReturn` instead
aligns the intermediate callee result with an `ApplyMorePlan` for the residual
arguments and the eventual original-apply result;
`CompilerRunningState.returnApplyMore` interprets all erased, under-, exact-,
and recursively over-saturated branches with additive heap budgeting and
rebuilds the original caller only after the entire chain resumes. This remains
valid when one or more tail calls changed the actively returning function: only
the returned root's world is adjusted to the original call signature.
Empty-stack return similarly produces a halted compiler state. The ordinary straight-line compiler-state
interface now also covers source `pure`/target `move`, HPT-certified shallow
unique free, scalar and heap-bearing shared retain, interpretation-polymorphic
checked allocation, function-PAP allocation, scalar shared/unique destruction,
recursive shared/unique destruction, and erased or under-saturated dynamic
application. Destructive operations and immediate dynamic application expose
their local heap costs additively and transport the compiler witness to both
the funded predecessor and any independently chosen suffix budget. Exact and
over-saturated PAP entry use that same framing while entering the matched
callee. The
validator-gated attachment makes a source extern trace impossible, so no
oracle contract is introduced. Nat-zero and Nat-successor switches advance in
one target step; constructor dispatch advances through its generated edge and
field-fetch prologue in exactly `1 + fieldCount` steps before rebuilding the
recursive child state. Evaluator determinism then identifies each reconstructed
one-step endpoint with the endpoint of a caller-supplied baseline step.
Consequently, the entire source-side prefix of an accepted reset block has the
same concrete preservation interface: HPT-certified fetch, shared retain,
recursive shared release, checked allocation, and self tail-call all advance
`CompilerRunningState`. The same module packages an exact successful reuse
optimization with its lowering
attachment, selects the current producer ownership vector, and proves the
paired allocation-history relation for the two initial machines. A
compiler-aware positive macro now carries the concrete `CompilerState` at its
baseline endpoint, and specialized finite-execution/`runMachine` theorems
preserve that paired state across variable-length synchronization. Its trace
dispatcher accepts either the ordinary compiler state at a literal one-step
successor or an already-paired positive macro. Constructor switching packages
its edge-plus-field-fetch execution as `CompilerMacroStep` and also retains the
exact parent runtime, edge-transfer, child-entry, and certified fetch-prologue
witnesses. The selected child then receives its own exhaustive rewrite
decision: a preserved child executes all `1 + fieldCount` steps in lockstep and
uses fixed-count determinism to attach the reconstructed compiler endpoint; an
accepted child delegates at entry and prefixes the related switch step to its
whole-site macro. Execution-guided variants of the finite and `runMachine`
inductions additionally pass the actual remaining baseline suffix and halted
endpoint to dispatch. This is necessary because the first fetch does not imply
enough heap fuel for a later recursive release; prefix cancellation against the
unique halted run still prevents the supplied suffix from acting as an oracle.
Accepted child/site macros remain the sole local obligation.
At any checked allocation coordinate,
`CompilerRunningState.allocationFieldWorlds` now converts the retained producer
ownership and successful source-operand resolution directly into the target
evaluator's `FieldWorlds` evidence; an accepted-prefix callback therefore does
not need to postulate that allocation premise once it has advanced the compiler
witness to the allocation instruction. Exact-content endpoints are no
longer a separate compositional gap: checked active-frame coverage and source
bounds, together with root-supported suspended stacks, re-index only
observable values by a canonical allocation history; a uniform
`StableHeapRel` dispatcher then covers both exact-content and history-related
states without constraining dead append-only registers. The paired invariant
now also carries `StableLiveAcceptedEntry`: whenever a synchronized frame is
selected by an accepted rewrite decision, its baseline program counter is
zero. This phase fact is kept out of the ordinary live-frame relation, whose
accepted-prefix proofs legitimately relate internal nonzero counters. The
accepted callback consequently receives both `pc = 0` and the entry
`LiveValuesIso` relation directly from the paired state. Accepted rewrite
metadata now proves that the replacement and recognized source block IDs are
distinct, and recognized source blocks exclude addressed calls, recursive
calls, dynamic application, moves, unique frees/drops, unique allocation, and
PAP creation.
Reusable constructors preserve the phase for zero-PC, halted,
unchanged-block, and source-block-excluded successors. The concrete compiler
transitions now return the phase for non-prefix move, unique-free,
unique-drop, PAP, and unique-allocation advances; all direct/self call and
tail-call entries; exact/over-saturated PAP entries; erased/under-saturated
application resumptions; both Nat-switch branches; ordinary call/self/apply
returns; recursively chained `applyMore` returns; and halt.

Planner transport and mapped-root obligations are restricted to registers
read by the recognized allocation or recursive tail call, and the physical-hot
theorem consumes entry `LiveValuesIso` rather than a complete parameter-vector
isomorphism. Dead forwarded ABI slots may therefore contain stale locations
without entering the heap relation. Scalar planner values no longer require
heap roots; only locations do. Static liveness at the allocation coordinate
turns borrow-free active-frame root support into the exact mapped-value premise,
and `CompilerRunningState` now exposes that bridge from its checked ownership
position. Borrow provenance remains intentionally weaker than direct root
membership. Checked lowering therefore audits exact agreement between every
live source capability and any inherited target block parameter it names.
At an accepted site, the compiler state combines this audit with release-site
liveness to recover the source parameter's exact shared owner, focus it at the
head of the root multiset, and retain all suspended-frame roots in the
remainder. Exact ownership also makes the complete field-retain batch
executable. The checked allocation transition exposes ownership of the new
field roots followed by every surviving capability and suspended-frame root;
after the successful hot retain/release prefix, address-bearing roots agree
exactly and inert scalar padding produces the root permutation required by
physical reuse. Unit refcount plus the existing heap isomorphism then
discharges the physical observable-stack avoidance premise without treating
borrows as roots. Accepted-prefix opcodes—fetch, shared retain/release, and shared
allocation—have a typed current-instruction witness and a dedicated compiler
advance arm. An unchanged enclosing block takes one related step and derives
phase from literal block identity; an accepted block bypasses its internal
successor and invokes the whole-site macro. Constructor-switch field prologues
now use the same independent child-decision split: preserved children advance
through the complete prologue, while accepted children take ownership at
`pc = 0` after the related switch. Exact ownership transport through the
incoming live heap isomorphism now preserves incoming multiplicities, root
and edge worlds, PAP sharing, and refcounts. Fixed-prefix preimage synthesis
and pointwise permutation transport carry the padded hot-prefix accounting to
the rewritten heap; entry-live planner support derives rewritten mapped
locations through that same root isomorphism. The physical-hot accounting
wrapper consequently reconstructs rewritten ownership, both root partitions,
and rewritten mapped support from baseline producer facts. Closed baseline
ownership now restricts an allocation history to an exact live-heap
isomorphism, while the checked parameter-capability audit proves that every
entry-live inherited register survives that restriction. Matching adapters
cover suspended continuations. The compiler-facing physical accepted-site
dispatcher uses those adapters, derives the rewritten source fields,
allocation resolution, field worlds, and observable-stack avoidance, and
selects either physical hot reuse or history-aware cold reset from the exact
baseline refcount. The complete accepted fetch/retain/release/allocation/
self-tail prefix now preserves `CompilerRunningState`. Its compiler endpoint
is joined to an indexed hot/cold semantic macro at the shared exact baseline
length, producing an `AttachedStableMacroStep` at recursive entry. The
recursive trace's zero-PC ABI audit now supplies the accepted parameter count
internally. The remaining trace-specific assembly is to invert the guided
baseline suffix for its release/allocation/tail witnesses and install that
result as the accepted child/site callback.

[`IxIR2/Pipeline.lean`](../Compilatrix/IxIR2/Pipeline.lean) now provides the
first fail-closed attachment to `ValidatedCompilation`. It transports source
parameter worlds through the final IxIR₁ address map, rejects ownership-
signature conflicts caused by erased identities, derives content-addressed
world/constructor layouts, and returns only an immediately validated IxIR₂
artifact while retaining the exact one-pass lowering equation. Exact
recursor-case identities are now recovered from certified addressed IxIR₀
mutual-block membership and transported through the final IxIR₁ owner map;
an executable same-tag/same-arity cross-block fixture pins that distinction.
The attachment also retains its selected depth bound and proves that the
lowering context is exactly the sidecar-produced context. Every successful
schema lookup in that context therefore exposes the baseline invariant that
all fields repeat the lookup ownership world. It additionally checks the
exact final source declarations and every retained trace for absence of
IxIR₁ `reuse`, and recursively verifies that every retained `papp` site
resolves to a function declaration marked PAP-safe. Both executable checks
have reflection theorems consumed directly by simulation.
The attachment now produces a checked HPT post-fixpoint for the same addressed
IxIR₁ graph and replays transfer along each exact `SourceSite` branch path and
offset. Fetch identities are selected only from singleton constructor facts;
shallow frees require the stronger exact-constructor fact with a complete
all-scalar field vector. Case target selection likewise prefers an exact
path-local constructor fact over global tag/arity lookup. All three uses are
checked against the retained schema table: global same-arity ambiguity no
longer blocks a locally precise allocation, while unresolved or incomplete
fetch/free facts reject.
[`IxIR2/PipelineSim.lean`](../Compilatrix/IxIR2/PipelineSim.lean) applies HPT
soundness to any held recovered environment. It proves the selected fetch
identity is the concrete operand constructor and proves both the constructor
identity and scalar-field condition required by `freeUnique`. The attachment
checks exact-constructor evidence across every recursive source-fetch trace,
scalar-leaf evidence across every recursive free trace, and the presence of
the exact emitted constructor target across every recursive case trace with
precise HPT evidence. It retains reflected coverage theorems for all three.
The attached fetch, free, and exact-HPT case adapters therefore have no
caller-supplied erased-identity, scalar-leaf, or constructor-selection premise.
Successful source inversions supply the remaining runtime equations.
The adapters share the sidecar-owned `SiteEnvironmentHolds` predicate. It is initialized at
each recoverable function root from top parameter facts and transported across
every successful linear source operation to `SourceSite.next`; the attachment
retains its exact input and rewrites the checked HPT post-fixpoint into that
same declaration environment.
Checked lowering additionally certifies that every function trace begins at
its owner's empty branch path and zero source offset. `TraceStateRel` combines
that literal source suffix, the held HPT environment, and target
`CodeStateRel`. It now initializes at every retained function root, including
synthetic main when its HPT analysis fails closed. Constructor and both Nat
alternatives transport it to the exact recursive child, and the public switch
simulations return the combined child state after their target reductions.
Attachment-facing steps for every non-call baseline operation—`pure`/`move`,
checked allocation, scalar/shared retain, scalar and recursive release/drop,
fetch, scalar-leaf free, and function-PAP allocation—likewise return the
combined continuation state from retained function membership. Direct and
self ordinary calls preserve the suspended caller while entering the matched
combined callee root; their tail forms enter without a continuation. A resumed
return restores the caller's exact combined continuation state, and an
outermost successful return supplies the attached one-step halt base.
Dynamic `apply` now advances the same combined continuation for erased and
under-saturated results, while exact and over-saturation enter a combined
retained callee root and retain a source-success-indexed caller-continuation
builder. Return-time `applyMore` has direct `applyGo` simulations for erased,
under-, exact-, and over-saturated results; exact/over results enter the next
combined callee root, and immediate results expose the exact resumed caller
machine and related store consumed by that builder.
The executable cyclic-pipeline witness exercises the attachment and target
covered `freeUnique` trace. The source evaluator now exposes exhaustive
successful inversions for every operation, known-address invocation, and all
three case outcomes. Case inversion retains the exact smaller-fuel branch run,
and the indexed-lookup bridge transports the evaluator's first match to the
source ordinal retained by the compiler trace. Recursive composition now uses
a source-output-indexed CPS boundary: a return handler distinguishes the
callee's exact returned store/value from the eventual enclosing computation's
store/value. Return handlers quantify over the retained function at a fixed
target stack, so an ordinary call installs a resume handler while a tail call
passes the enclosing handler through unchanged. The exact-fuel worker predicate
carries `SourceOwnershipAt` at every recursive position and has its zero-fuel
base, outermost-halt and ordinary-resume handlers, and
complete branches for `pure`/`move`, retain, fetch, shallow unique free, scalar
and recursive shared release, scalar and recursive unique drop, checked
ordinary allocation from the producer capability trace and a trace-indexed
source ownership invariant, strictly under-saturated addressed-function PAP
allocation, addressed/self
ordinary calls, and addressed/self tail calls. Its target reachability
conclusion existentially chooses entry heap fuel. Non-destructive steps replay
at the tail's budget; recursive release/drop uses additive work-list framing to
add its exact local traversal cost. Ordinary calls run the retained callee and
resume the source-indexed caller continuation; tail calls enter the retained
callee on the unchanged target stack. Checked `pure`/`move`,
`dup`/`retainShared`, `fetch`, ordinary allocation, addressed-function PAP
allocation, and `free`/`drop`/`dropU` capability flow discharge their ownership
transitions internally. Both allocation forms sequentially transfer
heap-bearing argument owners into the new node, preserve scalar arguments, and
install the fresh result owner. Every owned-boundary transition also retires
producer borrow capabilities rooted at the consumed SSA register. The dynamic
invariant records suspended caller roots and an exact semantic path from every
borrow to its local or caller lender. Destruction therefore transports every
unrelated surviving borrow across the restricted heap; shallow free also drops
the certified scalar children of its exact HPT leaf. An executable
fetch-then-drop witness pins the validator-dead loan shape. Ordinary and tail
calls now derive canonical callee-entry ownership from the current call-site
invariant and checked capability flow. Surviving caller owners become suspended
frame roots; ordinary return combines those roots with the checked result
owner and reconstructs the caller continuation. The public call CPS theorems
therefore take no preconstructed callee-entry or caller-resumption ownership
witness. Dynamic `apply` now consumes its function and argument roots through
an audited capability transition, excludes suspended borrows, and audits every
PAP-safe function root for the canonical all-owned/shared entry vector. Its
erased, under-saturated, and exact-saturated outcomes have complete CPS
adapters. Exact saturation constructs callee runtime and ownership from the
PAP retain/release prefix, frames the surviving caller roots, runs the callee,
and restores the caller through `.resume`; the same entry bridge splits an
over-saturated argument vector into callee roots and framed `applyMore` roots.
An evaluator-aligned `ApplyMorePlan` and structural interpreter now compose
that suffix through every immediate result and arbitrarily many
over-saturated function redispatches, using the strictly smaller source-fuel
worker at each call. Successful `applyGo` runs now select this plan
exhaustively. At interpretation time, trace ownership supplies shared-PAP
world evidence and the runtime `PAPsUnder` invariant supplies strict capture
under-saturation at every recursive redispatch.
Constructor, Nat-zero, and Nat-successor switch outcomes now also have
ownership-aware CPS adapters; constructor dispatch obtains its uniform field
schema from exact lowering-context provenance retained by the checked
attachment. The source evaluator's `runOwnedMain` entry installs the declared
main-result world in its synthetic current function and checks the final
value, so main-result soundness is no longer an external contract.
`SuccessfulSimulationContracts` now carries only the source and target context
identities, which canonical artifact contexts discharge definitionally.
Precise-HPT constructor cases recover their selection directly from the checked
attachment. At HPT-ambiguous sites, lowering emits every producer-known full
constructor identity matching the erased tag and arity; attachment audits both
that residual coverage and every constructor-producing operation in the source
and trace. Its source-store image carries a live-constructor invariant that the
worker preserves through ordinary evaluation, calls, reuse, PAP allocation,
and recursive application. Consequently,
`successfulCanonicalMainSimulation` takes the checked attachment alone and
supplies successful whole-main simulation without a caller semantic contract.
The exhaustive strong-fuel worker covers every recursive trace shape,
including dynamic constructor selection, all ordinary/self/tail calls, and
arbitrarily nested over-application.

The final-address application seam is closed for reachable compiled
executions. The validated
IxIR₁ compilation constructs `ApplyOwnershipContract` on its exact raw
lowerer context; the attachment proves that this context renames to the exact
emitted context used by the IxIR₂ simulation. `applyGo` is equivariant under
that renaming, and `RootOwnership` is invariant because declaration addresses
occur only as constructor/PAP metadata, not as ownership edges. Consequently,
`Attached.applyGo_exactImage` transports every successful raw application and
its output ownership to the emitted heap image. The rebuild audit also gives
every retained function and operation a raw syntax preimage, while evaluator
reflection preserves an exact raw-to-emitted `SourceStoreImage` through each
successful operation and through the retain/release stores used for PAP entry.
The exhaustive worker starts with the empty-heap image and carries this witness
through calls, returns, switches, and recursive `applyMore`. Its fixed-input
application rule can therefore instantiate the raw compiler theorem exactly
where needed. The stronger universal final-context contract remains false in
spirit for arbitrary heaps after declaration deduplication, but it is no longer
part of the simulation interface.

## Required simulation interface

The implementation must expose three compositional results rather than one
monolithic optimizer theorem.

### 1. Structured-control simulation

For every validated baseline lowering, each IxIR₁ code execution is simulated
by the corresponding logical IxIR₂ block execution. The whole-main wrapper has
the shape:

```text
IxIR1.runOwnedMain sourceCtx sourceResult sourceMain sourceFuel = ok sourceOut
  → ∃ controlFuel heapFuel logicalOut,
      IxIR2.runMain logicalCtx targetMain controlFuel heapFuel = ok logicalOut
      ∧ OutcomeRel sourceOut logicalOut
```

`OutcomeRel` includes the semantic result relation, exact root ownership, and
a live-heap relation. It does not require equal location numbers or equal
fuel.

[`IxIR2/LowerSim.lean`](../Compilatrix/IxIR2/LowerSim.lean) fixes this public
whole-main contract; proves scalar and vector operand resolution over partial
live-slot maps, value and erased environment extension, and safe forgetting of
consumed slots; defines the exact baseline store relation; closes the
canonical reversed-parameter relation at direct, self, and tail-call entry;
closes resumed and outermost-return block base cases (the latter through the
finite runner and through a trace-derived terminal theorem); composes an
instruction step or constructor/Nat dispatch with its continuation/branch
induction hypothesis; and closes the public
small-step cases for `pure`/`move` and ordinary constructor
allocation, both scalar and shared-node retain branches, scalar shared release,
nonunit shared-node release, scalar unique drop, checked scalar-leaf unique
free, fully recursive unique and shared destruction, checked non-consuming
fetch, function-targeted PAP allocation, and dynamic application control
transfer. Its baseline outcome currently
uses that stronger exact-heap relation. The trace layer additionally derives
generated-edge operand resolution from complete source/map cardinality and
converts the predecessor environment into the canonical successor environment,
including dead slots and the implicit Nat prefix; lifts every non-call baseline
case above to its exact recursive successor state; aligns all declared callee
traces; and composes call entry, callee return, and suspended-caller resumption.
Ordinary and self calls now expose their exact IxIR₁ `runOp` equations at
the same trace-facing target entry, while compiler-recognized addressed and
self tail-call shells reduce to the corresponding source invocation/body and
enter the matched target root without retaining a caller continuation. Thus
the recursive function proof need not unfold either evaluator at call entry.
The source half of that induction now has a single `SourceRuntimeInvariant`:
it combines append allocation order with bounded environment roots. Successful
reuse-free `runCode`, `runOp`, `invoke`, and `applyGo` executions preserve the
invariant and add their result root; argument resolution, constructor-field
entry, and Nat-successor entry transport it to the exact child environments.
In particular, allocation order directly discharges the positive shared-RC
premise of the existing recursive drop and PAP theorems.
Exact source/target heap correspondence additionally reflects source
`HasWorld` into the target evaluator's Boolean check. A
`SourceOwnershipInvariant` interprets one producer capability vector as
pointwise scalar/world facts, exact `RootOwnership` for its local owned slots
and suspended caller roots, and semantic lender paths for all local- and
caller-rooted borrows; `SourceOwnershipAt` selects that invariant by recursive
source, block,
target-position, and input-map coordinates. Together with uniform pipeline
schemas and successful source operand resolution, the checked allocation trace
now derives target `FieldWorlds` without an allocation-shaped root list from
its caller. `CodeStateRel` similarly turns a source function-result world fact
into the exact return-time check. Thus the recursive proof no longer needs
caller-invented dynamic world witnesses for either ordinary allocation or
return. Checked artifacts also audit a matching producer position at every
recursive code node, exact capability agreement for every live source slot
that still names an inherited target block parameter, and the exact
capability effect of every `pure`/`move`,
`dup`/`retainShared`, source `fetch`, allocation/PAP, destruction, and call
node. Ordinary-call auditing quantifies over every matching predecessor and
continuation position, fixing one unambiguous consume/suspend/result-bind
effect even when flat coordinates repeat.
Those effects have dynamic preservation theorems: scalar and borrowed moves
copy their facts, an owned move marks the old slot dead and moves the same root
to the new head by permutation, borrowed shared duplication gains an external
root, and owned shared duplication gains a second root across the exact RC
update. A successful fetch leaves the store and root multiset unchanged while
the parent capability proves the selected field inhabits the audited
constructor world; the result preserves the producer's exact lender. The
worker now requires `SourceOwnershipAt` recursively and every baseline branch
constructs its next witness. Direct/self ordinary and tail calls consume their
current ownership witness into the canonical reversed callee entry; surviving
caller roots are framed, and an ordinary return reconstructs continuation
ownership from the returned root plus that exact frame. Its base is
constructive: the
checked synthetic main's empty source and certified empty input map establish
the exact initial trace-indexed ownership state.
A public `ApplyTransfer` relation now exposes the evaluator's single dynamic
dispatcher to both an `apply` instruction and an `applyMore` return
continuation. Its under-saturated PAP theorem derives the target capture-retain
loop, old-PAP release, exact fresh location, and longer-PAP allocation from the
corresponding IxIR₁ `dupVals`/`dropVal` run while preserving the exact store
relation. The trace-facing entry derives the emitted instruction and both
operand families from the certificate and restores the exact recursive
continuation state for every successful dispatcher result. Exact saturation
is exposed from the IxIR₁ source `invoke` equation through the same derived
heap preparation to the matched callee root under a `resume` continuation.
Over-application is exposed from its source `invoke`-then-`applyGo` equation to
the matched first-callee root under `applyMore`, with the residual source and
target argument suffixes proved identical. A trace-facing return theorem then
executes that `applyMore` continuation through the shared dispatcher. Direct
`applyGo` theorems cover erased application and all three PAP saturation
shapes, so return-time exact/over redispatch enters the next combined callee
root and immediate erased/under redispatch exposes the exact resumed caller
and related store. These theorems close the local source/target seams for every
successful dynamic-application shape. An indexed recursive application plan
now composes those seams into the universal `applyMore` return handler, and a
successful source application constructs that plan inside the exhaustive
compiler-worker induction.
A recursive fail-closed switch
certificate now aligns every emitted constructor/Nat target with its exact
edge, source alternative, child body, successor map, and child entry state;
constructor arms additionally certify every generated field-fetch in their
prologue. Certificate-driven semantic theorems now execute both Nat branches
into their exact recursive child `CodeStateRel` (including the successor's
implicit predecessor), and execute a constructor branch through its generated
edge plus exactly one fetch step per field into the constructor child
`CodeStateRel`, without a caller-supplied edge-readiness premise. Exact-HPT
constructor branches additionally recover their emitted selection from the
checked attachment. Ambiguous-HPT branches recover it from the attachment's
residual-target audit and evaluator-preserved live-constructor invariant, so
constructor selection has no external semantic input. The later isomorphic
credit refinement remains active proof work.

### 2. Credit implementation refinement

Every well-formed logical IxIR₂ step is matched by the physical semantics with
the same control decision and a related state. Terminal results are related by
heap isomorphism and satisfy the terminal counter equations above.

### 3. Pipeline composition

Compose the current validated Ixon→IxIR₁ theorem, structured-control
simulation, and physical-credit refinement. The public endpoint must retain:

- successful-run forward simulation;
- target progress for each successful validated source main;
- unreachability of memory errors;
- full-result reclamation with no outstanding credit;
- the named cost relation, without claiming that reuse preserves raw
  allocation/free counters.

The current selected shared-main endpoint is
`Recursion.Compilation.sourceRefinesSelectedWithCostLaws` in
`Recursion/Costs.lean`. It projects to R3's unchanged
`sourceRefinesSelectedWithAllocationLaws` and R2's
`sourceRefinesSelectedWithResources` endpoint and retains the source sharing/oracle
premises and physical value relation. Actual physical steps establish
`live + frees + presentCredits = allocs`, including continuation credits;
halt gives `live + frees = allocs`. The common checked attachment derives a
successful release of the selected shared result, leaving `live = 0` and
`allocs = frees`, for both optimized and checked baseline selection. Literal
fallback retains the original owned IxIR₁ result and its complete release.
For recovered shared mains, R3 additionally compares the actual checked
physical baseline and selected execution. It proves
`baseline.allocs = selected.allocs + selected.reuses` and
`baseline.frees = selected.frees + selected.reuses` at halt, and the free law
after both complete releases. Both selection branches and independent
sufficient fuel are covered. The compiler derives zero baseline reuse and
equal allocation-event totals internally; its counter invariant remains
separate from the semantic heap/value relations. R4 adds
`selected.rcops ≤ baseline.rcops` and
`selected.peakLiveNodes ≤ baseline.peakLiveNodes` under the same source premises
and shared-main domain. Every actual selected prefix is bounded by the actual
baseline's terminal counters, including live nodes and recorded peaks inside
reset macros. The same complete releases carry both inequalities and R3's free
law. `CostDelta` tracks these observations separately from semantic relations;
exact per-step peak updates include internal application heap work. No new
heap or rewrite-shape premise is required. General logical/physical credit
refinement remains separate; R5 extends the selected compiler proof to
non-tail direct calls under the explicit policy below.

Later CFG, recursion, borrow, reset-insertion, or RC-coalescing passes must
either prove a local refinement that composes with these interfaces or return
an independently checked certificate. Failure remains fail-soft to the last
validated program.

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
IxIR₂ JSON is not a persistent identity.

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

## Mandatory fixtures for the first implementation

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

The structured case fixture and its differential execution witness are
producer-generated. The full baseline block-compositional induction and the
bounded source unique-list reversal now supply the theorem-backed exits.
The latter has separate consuming emission, checked translation, source
composition, and exact resource proofs, as specified below.

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
budgets, fallbacks, and artifact gate. General unique lowering and native heap
selection remain separate extensions.

## Implementation order fixed by this specification

1. Land syntax, schemas, limits, the executable validator, and positive/
   negative validation fixtures.
2. Land logical and physical evaluators plus credit-local heap-isomorphism and
   counter lemmas.
3. Land syntax-directed structured IxIR₁ lowering and its block-compositional
   simulation.
4. Generalize the fail-closed validated-pipeline attachment with exact source
   projection and shallow-free provenance; the executable checked-HPT
   attachment and recursor-case block provenance are now retained exactly,
   with semantic environment transport completed alongside item 3.
5. Add direct-recursion recognition, liveness-driven take/reset insertion,
   borrow inference, and RC normalization as separately switchable checked
   passes.

Items 1 and 2 are implemented. Item 3 has its executable lowering core,
validation witness, dead-slot-aware trace, theorem interface, partial
operand/environment foundations, exact store relation, initial
pure/allocation/retain/fetch cases, fully recursive unique/shared destruction,
public CFG-transfer/dispatch reductions, and the terminal return base case.
Canonical predecessor/edge/successor environment transfer now derives actual
operand-vector resolution from certified map/edge cardinalities; trace
certificates check register counts, exact binder-map growth and forgetting,
retained operands, terminators, and complete source/emitted/function-trace
declaration order. Recursive-state transitions
cover the non-call baseline operations, all call-entry forms, callee roots,
and return-to-caller continuation restoration. Direct/self ordinary and tail
entries also retain their exact source call/body equations. The recursive
compiler worker plus its one-pass run equation are theorem-facing. Switch-child/edge order,
Nat-prefix transfer, source child bodies, entry states, and constructor-fetch
prologues are now checked recursively and reflected into proof-facing branch
records. Those records now drive exact semantic child-state transitions for
literal-zero, literal-successor, and constructor dispatch; the constructor
transition includes the complete finite-step field-fetch prologue, and all
three derive generated-edge readiness internally. The dynamic-application
instruction/`applyMore` control seam, the exact under-saturated PAP branch,
the exact/over-saturated source branch decompositions and matched callee
entries, and return-time `applyMore` redispatch are also closed. HPT
environment initialization at function roots and successful linear-operation
transport now consume the attachment's exact checked declaration environment.
The same combined trace state initializes at the attached main and transports
the exact source suffix, HPT environment, and target recursive state through
constructor, Nat-zero, and Nat-successor dispatch and through every attached
non-call baseline operation. It now also initializes at every retained callee
root (including fail-closed main), enters direct/self ordinary and tail calls,
restores a suspended caller after an ordinary return, and closes an outermost
successful return. Exact source-fetch and scalar-leaf-free evidence is
recovered from attachment membership rather than supplied by the caller.
Dynamic `apply` and recursive `applyMore` dispatch now have attachment-facing
erased, under-, exact-, and over-saturated transitions; callee-entering paths
establish the next combined root and immediate paths align the resumed caller
for its retained continuation builder. The exhaustive strong-fuel induction
now dispatches every operation and trace terminator, and its whole-main wrapper
realizes the public forward successful-run contract with independently chosen
target budgets. Constructor selection, including the HPT-ambiguous case, is now
derived entirely from the validated producer artifacts. This completes the
IxIR₂ CFG/join-point tranche. The bounded scalar native path and source-level
shared/static-unique reuse endpoints are also delivered; native heap selection
is the next compiler milestone.

The v0 syntax and semantics support both static unique and dynamic shared
reuse with the same ownership and layout contracts.
