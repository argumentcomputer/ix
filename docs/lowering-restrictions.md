# IxIR₀ → IxIR₁ lowering restriction ledger

Last reviewed 2026-09-07.

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
| No implicit freeze | **Restricted by adopted decision.** `UsageCheck` rejects unique values at non-unique argument, let, and result sinks; `requireResultWorld` and the variable path retain `freezeNeededMsg` as lowering backstops. `RestrictionKind.freeze` and the generated `freezeNeeded` schema pin the exact error. | Add a deep `Op.freeze` with store, ownership, progress, and cost rules. Let-bound mode loss is instead repaired by carrying the mode through erasure; it does not require `freeze`. | Choose the runtime representation, encounter a real corpus need for unique→shared publication, or schedule mode-polymorphic recursors; the live design constraints are in `plans/substructural-types.md`. |
| No unique destructuring | **Restricted in the ordinary lowerer.** A projection demanded in the unique world is rejected before lowering; borrowing a unique source is rejected by `lowerBorrow`. `RestrictionKind.uniqueDestructuring` and the generated `uniqueProjection` schema retain the diagnostic. The separate [unique-list endpoint](source-unique-reuse.md) checks its complete source schema and emits consuming extraction/shallow free followed by validated `takeUnique`/credit translation. | Generalize the checked consuming path beyond the current schema: move every field and produce one affine exact-layout credit consumed by `allocWith` or `discardCredit`. A non-consuming `fetch` plus `dropU` remains unsound because it aliases or frees the selected child. | An accepted source program needs broader consuming case/layout specialization. |
| Shared, all-`many` function values | **Restricted.** Runtime PAP nodes are shared and `apply` duplicates their stored prefix. Lowering records an owner-sensitive `FnDef.papSafe` bit, set only for shared results and all-`many` telescopes. Saturated direct `call` bypasses that gate, so affine/linear arguments and unique results remain legal for known calls; saturated or over-saturated dynamic `apply` resolves the owner declaration and rejects it unless the bit is set. Declaration rewriting and content-address rebuilding preserve the bit. `RestrictionKind.sharedFunctionValues`, the generated `nonManyLambda`/`partialNonMany` cases, and focused direct-call-versus-PAP regressions pin the boundary. | Give callable values an ownership-aware representation: either one-shot unique closures/PAPs or a richer typed callable contract that distinguishes captured and argument worlds and result ownership. | A higher-order affine/linear program is scheduled, or IxIR₀ˢ introduces the callable ownership information needed to compile one. |
| No unique captures | **Restricted as a consequence of shared PAPs.** `lowerCapture` rejects a unique entry before emitting a shared PAP; `RestrictionKind.uniqueCapture` and the generated `uniqueCapture` schema pin `uniqueCaptureMsg`. | Move a unique capture into a one-shot unique closure and make its apply/drop behavior consume exactly once. This is a subcase of the function-value lift, not an independent shared-PAP tweak. | The one-shot closure representation is chosen and its apply/drop ownership contracts exist. |
| Mode-monomorphic recursors | **Restricted in the ordinary lowerer.** IxIR₀ recursor declarations carry no per-argument or result `Uses`; `lowerRecursor` assigns shared results, parameters, and fields. `RestrictionKind.modeMonomorphicRecursors` and generated `uniqueRecursor` cases retain the no-freeze boundary. The separate unique-list endpoint checks saturated Ixon usage and source mode evidence, then records argument/field/result worlds in canonical `RecursorInstance` identities. | Generalize checked recursor instances and consuming lowering to additional source schemas. Mixed unique→shared results additionally depend on the freeze lift. | Broader usage-polymorphic recursors/IxIR₀ˢ are needed by an accepted source program; mixed-mode publication also wakes `Op.freeze`. |
| Saturated-only `recSelf` | **Restricted.** `VEntry.recSelf` stores an arity, not a first-class value. `lowerSpine` emits `callSelf` only at saturation; under-application is rejected, while escape, borrowing, and capture have separate fail-closed diagnostics. `RestrictionKind.saturatedRecSelf` uses a synthetic one-parameter recursor whose rule supplies one of the required two arguments. | Introduce a first-class self-callable/PAP representation with exact self provenance, under-fill/over-fill semantics, ownership-aware captures, and corresponding recursive contracts. | A certified source program needs an escaping or partial recursive self application, after the function-value representation is selected. |

## Composed capability boundary

These policies remain the ordinary lowerer's boundary: unique constructor
trees can be allocated, moved through known unique demands, returned, and
deep-freed, while consuming inspection needs a separate checked translation.
`UniqueReuse.compile` now supplies that translation for a closed finite Nat-list
reversal schema. Its source theorem derives consuming ownership, exact no-RC
static reuse, and complete release from actual compilation. The
[source unique record](source-unique-reuse.md) describes its seven differential
cases and excluded source forms. It does not change the six ordinary-lowering
rejections above or establish a general unique-destructuring pass.

This inventory is not a completeness theorem for all lowering failures. The
seeded corpus is bounded, and internal consistency errors, ordinary usage
errors, unknown references, and declared-result mismatches are deliberately
outside these six feature-policy categories.
