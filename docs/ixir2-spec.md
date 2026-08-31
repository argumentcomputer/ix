# IxIR₂ v0 specification

Last reviewed 2026-08-31.

This document freezes the first IxIR₂ semantic data model. It is normative for
the v0 syntax, ownership-flow checker,
reuse-credit behavior, and IxIR₁→IxIR₂ simulation boundary. Forward-looking
pass ideas remain in the local plans; an implementation that disagrees with
this document must change the specification deliberately rather than silently
choosing a different contract.

The in-memory syntax, bounded executable validator, and logical/physical
small-step machine are implemented in
[`IxIR2/Basic.lean`](../Compilatrix/IxIR2/Basic.lean),
[`IxIR2/Validate.lean`](../Compilatrix/IxIR2/Validate.lean), and
[`IxIR2/Eval.lean`](../Compilatrix/IxIR2/Eval.lean). Executable acceptance,
rejection, hot/cold reset, reuse/discard, PAP, and budget witnesses live in
[`IxIR2/ValidateExamples.lean`](../Compilatrix/IxIR2/ValidateExamples.lean) and
[`IxIR2/EvalExamples.lean`](../Compilatrix/IxIR2/EvalExamples.lean).
[`IxIR2/EvalCounter.lean`](../Compilatrix/IxIR2/EvalCounter.lean) supplies the
credit-local heap relation and proved local counter algebra. The codec,
IxIR₁ lowering, whole-step simulations, and their pipeline composition remain
later tranches below.

The freeze covers the in-memory Lean model and proof interfaces. Numeric wire
tags and a persistent codec are not frozen yet. No artifact may advertise a
stable `IxIR2/v0` wire version until the strict decoder, canonical encoder, and
content-address preimages are documented alongside their executable guards.

## Scope and non-goals

IxIR₂ consumes the current fully addressed IxIR₁ graph plus checked sidecars
for source provenance, function-parameter worlds, constructor field worlds and
layout, exact HPT facts used by accepted scalar-leaf frees, and—when
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
lowerer emits no reuse, and IxIR₂'s credit path is the sole authority that may
introduce physical reuse. Encountering a pre-existing raw `reuse` fails closed
until a certified translation rule is added.

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
the terminal free equation. Executable non-degenerate runs pin the resulting
intermediate and terminal laws. The whole-machine logical/physical step
refinement remains to be composed with structured lowering; this tranche does
not claim that theorem from the local algebra alone.

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

The lowering trace maps each IxIR₁ code position to an IxIR₂ block and
instruction interval. It also records the environment-to-parameter relation
at every edge. These witnesses are proof data; they are not trusted claims
from the optimizer.

## Required simulation interface

The implementation must expose three compositional results rather than one
monolithic optimizer theorem.

### 1. Structured-control simulation

For every validated baseline lowering, each IxIR₁ code execution is simulated
by the corresponding logical IxIR₂ block execution. The whole-main wrapper has
the shape:

```text
IxIR1.runMain sourceCtx sourceMain sourceFuel = ok sourceOut
  → ∃ controlFuel heapFuel logicalOut,
      IxIR2.runMain logicalCtx targetMain controlFuel heapFuel = ok logicalOut
      ∧ OutcomeRel sourceOut logicalOut
```

`OutcomeRel` includes the semantic result relation, exact root ownership, and
a live-heap relation. It does not require equal location numbers or equal
fuel.

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

Later CFG, recursion, borrow, reset-insertion, or RC-coalescing passes must
either prove a local refinement that composes with these interfaces or return
an independently checked certificate. Failure remains fail-soft to the last
validated program.

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

The theorem-backed exit additionally requires an axiom-fence entry and a
compiler-produced unique list-reversal witness. The hand-written credit
fixtures establish the primitive; they do not satisfy the optimization
milestone by themselves.

## Implementation order fixed by this specification

1. Land syntax, schemas, limits, the executable validator, and positive/
   negative validation fixtures.
2. Land logical and physical evaluators plus credit-local heap-isomorphism and
   counter lemmas.
3. Land syntax-directed structured IxIR₁ lowering and its block-compositional
   simulation.
4. Attach validated artifacts to the existing pipeline endpoint.
5. Add direct-recursion recognition, liveness-driven take/reset insertion,
   borrow inference, and RC normalization as separately switchable checked
   passes.

Items 1 and 2 are implemented. Item 3 is the active compiler milestone.

Static unique reuse precedes dynamic reset quality work, but the v0 syntax and
semantics include both lanes now so the ownership and layout contracts cannot
diverge later.
