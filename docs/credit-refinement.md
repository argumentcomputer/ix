# General credit refinement (R6)

The same IxIR₂ program now has a logical-to-physical execution proof for both
`call-local/0` and `suspended-direct-calls/1`. It covers the full instruction
language, arbitrary finite control-flow paths, and nested calls. Programs do
not need to come from a particular optimizer or carry a rewrite trace.

The public interface is
[`CreditRefinement.lean`](../Compilatrix/IxIR2/CreditRefinement.lean).
The original v0 runner and both validators retain their existing behavior.

## Domain and public results

`checked_runMain_refines` takes `Validate.CheckedWithPolicy` for the exact
program, validation context, and policy, together with a successful logical
`Policy.runMain`. Evaluation uses that program's declarations and the checked
context's schemas. Main starts with no arguments, an empty heap, and empty
value/credit files. The runner enforces scalar arguments and scalar results
at every extern call; the validator's extern policy is unchanged.

The conclusion constructs a successful physical run with the same control
and traversal budgets. `ResultRel` gives related heaps and returned values,
equal remaining budgets, and the terminal counter law. The underlying
`runMain_refines` is stronger: successful logical execution suffices without
checker acceptance. The checked wrapper retains the intended artifact
boundary without pretending that validation supplies additional semantic
ownership facts.

| Interface | Guarantee |
| --- | --- |
| `runMain_v0_refines` | The same full-credit guarantee for the original `Eval.runMain`. |
| `runMain_refines_independent` | Logical and physical runs with independently chosen successful budgets have related values, heaps, and costs through `OutcomeRel`. |
| `prefix_resources` | Every finite logical prefix has a physical prefix of the same length with related machines, uniquely owned reservations, and the intermediate counter law. |
| `runMain_prefix_resources` | Every actual physical prefix of a successful logical main has its corresponding logical prefix and those same resource facts. |
| `OutcomeRel.ownership` / `valueGraph` | Logical root ownership and the existing source-value graph transport to the physical result through a finite live-heap isomorphism. |
| `OutcomeRel.reclamation` | An owned logical result supplies a finite release budget; both actual heaps reclaim completely with the same budget and retain the comparative counter law. |
| `checked_runMain_owned` | Combines actual checked-program execution, matching results, physical root ownership, and complete reclamation. |

Complete reclamation explicitly assumes
`RootOwnership logical.store.heap [⟨program.main.signature.result, logical.value⟩]`.
This means the result owns the remaining heap under the existing world and
reference-count discipline. Execution derives positive RC and allocation
order internally; callers do not supply release progress or a physical heap
invariant. `Validate.CheckedWithPolicy` alone does not prove this semantic
ownership premise. Both shared and unique result worlds are supported.

This is successful-run forward preservation. Error reflection, divergence,
observable effect traces, finite physical capacity, and new borrow/RC
optimizations remain separate contracts.

## State relation and costs

[`CreditRelation.lean`](../Compilatrix/IxIR2/CreditRelation.lean) relates every
value register, credit entry, frame, and continuation. The heap relation uses
the existing allocation-history map: it retains old logical names while
requiring distinct physical locations only for currently live logical nodes.
This lets saved registers survive a physical slot's reuse without renaming
past values. Present/absent credits agree in layout and presence; each
present physical credit owns a distinct, empty, in-bounds slot across the
active frame and all suspended callers.

Primitive heap, instruction, application, terminator, and policy-step proofs
compose through the actual evaluator. `takeUnique`, hot `resetShared`, reuse,
and discard change the allocation map or reservation ownership as required.
Cold reset preserves the shared alias and agrees on field retains. Edges
transfer the complete remaining credit file, including reordering. Calls
preserve saved registers and reservations; no caller-supplied per-step
simulation or progress callback is needed.

For corresponding prefixes, with `k` present physical credits in all frames:

```text
logical.allocs = physical.allocs + physical.reuses
logical.frees  = physical.frees  + physical.reuses + k
physical.live + physical.frees + k = physical.allocs
```

Live nodes, RC operations, reset attempts, hot/cold decisions, and peak live
nodes agree. At return, `k = 0`. After complete reclamation both heaps have
zero live nodes and their own allocations equal frees. These are node and
event observations; reserved storage and allocator bytes need a separate
capacity model.

## Regression and trust boundary

[`CreditExamples.lean`](../Compilatrix/IxIR2/CreditExamples.lean) runs 25 accepted
program/policy combinations through the real runners and checks every paired
execution prefix, result shapes, costs, and reclamation:

- Two reservations cross reversed back edges for 0, 1, 2, 3, 16, and 64
  iterations, under both policies; v1 also suspends them across nested calls
  whose allocations must use other slots.
- Required unique, present optional shared, and absent optional shared
  credits coexist through hot/cold resets and rebuilding.
- Both optional-credit branches join before reuse, then exercise present and
  absent discard and shared reclamation.
- A borrowed callee reads a caller-owned value while a separate caller
  reservation remains suspended, then returns so the caller can reuse it.

Additional guards pin intermediate reservations, existing v0 call rejection,
layout mismatch, duplicate transfer, repeated consumption, unconsumed return,
forbidden v1 tail/PAP/apply/extern credit escape, invalidated borrow lenders,
and separate control/traversal exhaustion. These guards are imported by
`Compilatrix.lean` and run during ordinary library and Nix builds.

Ten public entries are pinned in
[`Fence.lean`](../Compilatrix/Fence.lean). They depend only on `propext`,
`Classical.choice`, and `Quot.sound`; this refinement adds no native reflection,
hashing, extern, or specification axiom. Existing source and native endpoint
assumptions retain their own scope.

Validated on 2026-09-08: the complete 592-job local build, all compiled
regression tools, and all 12 Nix checks on x86_64 Linux passed. The Nix run
used a complete source snapshot including the new modules. Existing source
and native gates passed, including all eight linked native reversal cases.
