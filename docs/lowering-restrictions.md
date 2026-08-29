# IxIR₀ → IxIR₁ lowering restriction ledger

Last reviewed 2026-08-28.

This is the decision ledger for the current mode-directed lowerer. It records
the accepted restriction today and the concrete condition that opens each
future lift. A row marked **restricted** is fail-closed behavior, not a claim
that the corresponding feature has been implemented or permanently rejected.

The executable inventory is `IxIR1.Lower.RestrictionKind.all`. It contains six
distinct entries, each with a representative exact diagnostic and rejection
witness; one aggregate `#guard` fails if any listed witness stops holding.
Diagnostics shared with the generated corpus are public constants in
`Lower.lean`, so the compiler and tests cannot silently spell the same policy
differently. `WellModedGen` additionally exercises unique capture and the
all-shared recursor boundary across seeded payloads. Under-applied `recSelf` is
checked by a focused synthetic recursor rule because it cannot occur in a
closed main outside a rule environment.

| Restriction | Current enforcement and evidence | Planned lift | Wake condition |
| --- | --- | --- | --- |
| No implicit freeze | **Restricted by adopted decision.** `UsageCheck` rejects unique values at non-unique argument, let, and result sinks; `requireResultWorld` and the variable path retain `freezeNeededMsg` as lowering backstops. `RestrictionKind.freeze` and the generated `freezeNeeded` schema pin the exact error. | Add a deep `Op.freeze` with store, ownership, progress, and cost rules. Let-bound mode loss is instead repaired by carrying the mode through erasure; it does not require `freeze`. | Any condition in `plans/freeze-contract-2026-08-19.md`: choose the runtime representation, encounter a corpus need for unique→shared contact, or schedule mode-polymorphic recursors. |
| No unique destructuring | **Restricted.** A projection demanded in the unique world is rejected before lowering; borrowing a unique source is rejected by `lowerBorrow`. `RestrictionKind.uniqueDestructuring` and the generated `uniqueProjection` schema pin the consuming-source diagnostic. | Add a genuinely consuming destructor (or typed case lowering) that shallow-frees the unique parent, moves selected fields, and deep-frees discarded fields. A non-consuming `fetch` plus `dropU` is unsound because it aliases or frees the selected child. Extend ownership/value/progress/cost proofs for that primitive. | Start the first computational unique fixture (the planned unique list reversal), or introduce IxIR₀ˢ case/layout specialization. |
| Shared, all-`many` function values | **Restricted.** Runtime PAP nodes are shared and `apply` duplicates their stored prefix. `papSafe` therefore admits only all-`many` telescopes as function values or partial applications; non-`many` definitions remain valid as saturated known calls. `RestrictionKind.sharedFunctionValues` plus generated `nonManyLambda` and `partialNonMany` cases pin the boundary. Partial applications with unique results are also rejected. | Give callable values an ownership-aware representation: either one-shot unique closures/PAPs or a richer typed callable contract that distinguishes captured and argument worlds and result ownership. | A higher-order affine/linear program is scheduled, or IxIR₀ˢ introduces the callable ownership information needed to compile one. |
| No unique captures | **Restricted as a consequence of shared PAPs.** `lowerCapture` rejects a unique entry before emitting a shared PAP; `RestrictionKind.uniqueCapture` and the generated `uniqueCapture` schema pin `uniqueCaptureMsg`. | Move a unique capture into a one-shot unique closure and make its apply/drop behavior consume exactly once. This is a subcase of the function-value lift, not an independent shared-PAP tweak. | The one-shot closure representation is chosen and its apply/drop ownership contracts exist. |
| Mode-monomorphic recursors | **Restricted.** IxIR₀ recursor declarations carry no per-argument or result `Uses`; `lowerRecursor` assigns a shared result and shared parameters/fields. A unique major consequently crosses the no-freeze backstop. `RestrictionKind.modeMonomorphicRecursors` and generated `uniqueRecursor` cases pin that composition explicitly. | Add usage-polymorphic recursor signatures in IxIR₀ˢ, then lower unique majors through the consuming-destructor path. Mixed unique→shared results additionally depend on the freeze lift. | Usage polymorphism/IxIR₀ˢ is scheduled after unique destructuring; mixed-mode publication also wakes `Op.freeze`. |
| Saturated-only `recSelf` | **Restricted.** `VEntry.recSelf` stores an arity, not a first-class value. `lowerSpine` emits `callSelf` only at saturation; under-application is rejected, while escape, borrowing, and capture have separate fail-closed diagnostics. `RestrictionKind.saturatedRecSelf` uses a synthetic one-parameter recursor whose rule supplies one of the required two arguments. | Introduce a first-class self-callable/PAP representation with exact self provenance, under-fill/over-fill semantics, ownership-aware captures, and corresponding recursive contracts. | A certified source program needs an escaping or partial recursive self application, after the function-value representation is selected. |

## Composed capability boundary

Together these policies still form the restriction wall identified in the
2026-08-18 review: unique constructor trees can be allocated, moved through
known unique demands, returned, and deep-freed, but cannot yet be inspected.
The current demonstrated payoff is therefore zero-RC alloc/move/free, not a
computational unique-data algorithm. Closing this ledger makes that boundary
precise; breaching it requires the unique-destructuring slice above and a
contentful differential fixture.

This inventory is not a completeness theorem for all lowering failures. The
seeded corpus is bounded, and internal consistency errors, ordinary usage
errors, unknown references, and declared-result mismatches are deliberately
outside these six feature-policy categories.
