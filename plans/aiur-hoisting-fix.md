# Aiur hoisting: assertion capture and evaluation-order repair

Date: 2026-09-10. Status: implemented and regression-tested.

## Observed bug

`Ix/Aiur/Stages/Source.lean` runs `Term.hoistLets` after inline expansion,
including on functions with no inline calls. The old `assertEq` case peeled leading
lets from **both operands and the continuation**, then put all of them before
the assertion. The continuation is not an operand: its bindings and effects
must run only after the assertion succeeds.

For example, this source must reject when `x != 0`:

```text
fn check(x: G) -> G {
  assert_eq!(x, 0);
  let x = 0;
  x
}
```

The old transformation effectively produces:

```text
let x = 0;
assert_eq!(x, 0);
x
```

The later binding captures the assertion's earlier reference. This is a
compiler correctness bug that can weaken the statement enforced by a compiled
Aiur circuit; it is not evidence of a cryptographic proof-system break.

### Concrete IxBy discovery

The original object-interpreter entry decoded program and input streams into
locals both named `rest`. Source execution rejected a trailing program byte,
but compiled execution accepted trailing bytes 0, 1, and 255: both end-of-stream
checks used the input-tail pointer. The initial workaround used distinct
`programEnd` and `inputEnd` names. After the shared repair, the object entry
again uses `rest` for both tails, and the source/native rejection checks pass
with matching program/input/output commitments.

The discovery and subsequent repair are documented in
[IxBy objects](../docs/IxbyObjects.md).

## Related hazards covered

- `ioWrite` and `ioSetInfo` also treated their continuation as a strict operand.
  A read or metadata lookup in a continuation can consequently run before the
  preceding write or metadata update.
- Hoisting from one strict argument widens the scope of its locals over other
  arguments. Callee-only freshening does not protect caller-written nested
  lets, let right-hand sides, or match bindings.
- Collecting all argument let prefixes before evaluating the remaining cores
  can reorder effects between arguments. Left-to-right *prefix* order alone
  does not establish left-to-right *expression* evaluation.
- Fresh names must avoid existing inputs, bound and free locals, and names
  introduced by other inline splices. Programmatically constructed Source IR
  must not rely on an undocumented reserved spelling.
- Alpha-renaming must preserve shared bindings in alternative (`or`) patterns
  and must not convert a previously unbound reference into a bound one.

## Repair plan (implemented)

1. Add small independent regressions for assertion shadowing, IO continuation
   order, nested-let capture, argument effect order, and inline/name interactions.
   Compare original source evaluation with normalized source and compiled
   execution; use explicit expected results/errors, not agreement alone.
2. Keep continuation lets below assertions, writes, and metadata updates.
   Preserve match-arm laziness and return/function boundaries.
3. Make scope-widening transformations hygienic, using collision-free local
   names and correctly scoped substitution before inlining/hoisting.
4. Preserve complete left-to-right strict-argument evaluation when hoisting
   introduces prefixes; inspect the resulting bytecode and avoid unnecessary
   circuit/layout changes where possible.
5. Prove/verify representative successful regressions and require failing
   assertions to be rejected by native execution before entering the prover. Keep the real IxBy
   trailing-byte regression, and exercise the original shadowed entry too.
6. Run existing Aiur cross-engine/proving/cost coverage and IxBy scalar,
   control, and object suites. Investigate cost changes rather than blindly
   replacing pinned expectations. Update this plan with outcomes and limits.

## Scope and acceptance criteria

Change the shared Aiur source normalization and its regression coverage, plus
documentation needed to retire the local-workaround-only status. Preserve
unrelated workspace changes; no Rust/protocol or production-format changes
are needed for the repair.

Completion means the concrete bypass is reproduced before the fix and rejected
after it, targeted scope/order regressions pass with explicit expectations,
existing relevant suites pass (or any unrelated blocker is documented), and
the repair's limitations are recorded. This is not a full compiler refinement
proof or an end-to-end IxBy constraint-to-reference theorem.

## Implementation

- `Function.freshen` renames caller inputs and local binders before inline
  expansion; the inliner threads a collision-free name supply across splices.
  The supply starts above existing `inl#N` spellings, including free variables
  and unqualified call heads. `Term.hoistLets` also protects standalone callers.
- Pattern renaming uses one name per distinct binder in a pattern: `or`
  alternatives retain shared bindings, while illegal duplicate binders and
  mismatched alternative bindings remain detectable. Local function-call heads
  are renamed along with variable references.
- Assertion, IO, and debug statements become unit-valued wildcard lets, in
  their original sequence. Hoisting carries each statement before its
  continuation's bindings. When a later argument has a hoisted prefix, an
  earlier non-atomic core is evaluated into a fresh temporary first.
- The first repair, which merely left continuations nested, exposed a lowering
  regression in `join_verify_child`: a branching inline helper after an
  assertion was buried in a value position. Ordered statement lets expose the
  branch to the existing block-lowering path while preserving the check's
  position. Minimal guarded-operand/RHS, write/metadata/debug-before-branch,
  and explicit-return regressions now cover this case.
- The object entry's temporary naming workaround is retired. No Rust,
  protocol, production wire-format, or Compilatrix changes were made.

## Validation

The original minimal assertion bypass and argument/IO ordering failures were
reproduced before the repair. The following checks passed in the original
development workspace, before separating IxBy from the Flock branch:

| Coverage | Checks |
| --- | ---: |
| New hoisting regressions, including 37 proof/serialization/verification cases | 619 |
| Existing Aiur cross-engine, proof/grouping, cost, hash, RB-tree, and recursive-verifier tests | 1,447 |
| IxBy scalar (209), control (232), and objects (530), including full proving | 971 |
| IxBy reference (100), crypto (74), and codec (89) | 263 |
| IxVM kernel, arena/exploit rejection, native parity, and cost pins | 819 |
| Total targeted runtime checks, excluding repeated runs and theorems | 4,119 |

The recursive-verifier checks include honest acceptance, tampered proof/claim
rejection, and generated-verifier/interpreter output and query-count parity.
The kernel suite also passes its existing per-constant and shard FFT-cost
pins, and the newly compiled bytecode agrees with the checked-in generated
kernel on the parity fixtures. No cost expectations were changed.
The three object workloads retain their recorded row counts, widths, and
FFT-work estimates. Historical timing/proof-size measurements are labeled as
pre-repair observations; no new isolated performance claim is made.

```sh
lake build --wfail AiurHoistingTests IxbyAiurTests IxbyControlTests IxbyObjectsTests \
  Ix.Ixby.Aiur.ObjectsRefinement Tests.Main
RAYON_NUM_THREADS=8 .lake/build/bin/AiurHoistingTests --prove --regression
RAYON_NUM_THREADS=8 .lake/build/bin/IxbyAiurTests
RAYON_NUM_THREADS=8 .lake/build/bin/IxbyControlTests
RAYON_NUM_THREADS=8 .lake/build/bin/IxbyObjectsTests --stats
# Existing primary runners for the reference/crypto/codec checks:
lake build --wfail IxTests
RAYON_NUM_THREADS=8 .lake/build/bin/IxTests ixby ixby-crypto ixby-codec
RAYON_NUM_THREADS=8 .lake/build/bin/IxTests --ignored ixvm
```

`AiurHoistingTests` without flags runs execution-level checks; `--prove` adds
the new proof cases, and `--regression` runs the existing Aiur suites, including
the recursive verifier. `Tests.Main` registers `aiur-hoisting` as a primary
runner and `aiur-hoisting-prove` as opt-in. Proof parameters are test-only
(64 FRI queries, no proof-of-work), not a production security recommendation.

## Isolated IxBy branch validation

The publication branch is based directly on `origin/main` at `5430a5d9`, not
on the mixed Flock development history. The hoisting repair is a separate
commit. IxBy uses existing main-branch Aiur interfaces, so no Flock CLI,
fixtures, dependencies, protocol bindings, or Rust changes are included.

The isolated build passes with `--wfail`, including `IxTests` and the
representation theorem modules. Revalidation passed 2,064 hoisting/Aiur checks
(including the same 619 focused checks and 37 new proof roundtrips), all 971
IxBy scalar/control/object checks with proving enabled, and all 263
reference/crypto/codec checks. The existing main-branch recursive-verifier
suite has two fewer checks than the Flock development variant because the
experimental lookup-packing profile was not imported. Object row counts,
widths, and all three FFT-work estimates are unchanged.

The current-main kernel suite also passes all 831 checks, including native
parity, negative fixtures, and its existing per-constant/shard cost pins.
The isolated branch therefore passes 4,129 targeted runtime checks, excluding
repeated runs and theorems; no cost expectations were changed.

## Remaining boundaries and rollout

- Rebuild compiled circuits and proving/verifying keys. The source repair
  does not retroactively change old bytecode or the constraints in old keys;
  unchanged wire revisions do not imply artifact/key compatibility.
- This is differential and proof-pipeline regression coverage, not a formal
  compiler-refinement or malicious-witness soundness proof. Direct low-level
  hoisting/simplification helpers still require their documented hygiene
  preconditions; the public compilation pipeline supplies them.
- The low-level Rust prover panics on an execution error. Negative fixtures
  therefore stop at native execution, as IxBy's prover preflight does; this
  repair does not claim a new error-return contract for that low-level API.
- Native indirect calls remain unsupported. Local function-call renaming is
  checked against source evaluation and typechecking, with native compilation
  still failing closed at its existing unsupported-lowering boundary.
