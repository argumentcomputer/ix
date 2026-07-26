# Ix.Tc K0 recursion and back-edge audit

Snapshot: 2026-07-27. This is the named K0 tick/measure artifact required by
the formal-verification plan. Its production scope is the kernel call graph
rooted at `TcM.checkConst`: `Whnf`, `Infer`, `DefEq`, `Inductive`, and
`Check`, together with the shared monad, expression, local-context,
union-find, and canonical-checking helpers they call. Ingress, egress,
parallel scheduling, and the meta-level trust-audit visitor are not on that
call graph.

The audit result is now:

- zero `partial def` declarations in the production kernel call graph;
- zero `while` or `repeat` terms in the five recursive kernel modules;
- a total six-field recursive-method table, indexed by an explicit `Nat`;
- explicit finite bounds for every loop or recursive strongly connected
  component that Lean could not accept structurally;
- exact equations and fuel-boundary regressions for the totalization seams.

A finite bound is operational evidence, not a soundness proof. K1 and K2
must still prove the semantic WF properties of the transparent algorithms.

## Shared runtime fuel

There is one shared runtime counter, `TcState.recFuel`. Exactly two
production sites consume it:

| Entry | Charge point | Fast paths before the charge | Exhaustion |
|---|---|---|---|
| `RecM.whnf` | `whnfWithNatSuccMode`, after quick exits and cache hits | non-reducing forms and a warm `whnfCache` hit | `.maxRecFuel`; `TcM.tick` leaves the error state unchanged |
| `RecM.isDefEq` | `isDefEq`, after address, equivalence-manager, and cache exits | reflexive/equivalent/cached results | `.maxRecFuel`; `TcM.tick` leaves the error state unchanged |

`RecM.infer`, `RecM.whnfCore`, and `RecM.whnfNoDelta` have no entry tick.
Consequently, “every recursive hop ticks” is false and must never be used as
a termination or soundness argument.

`TcM.runRec` selects `methodsN s.recFuel.toNat` from the current state once,
not from `fuelBudget`. The method-table index is a logical call-depth bound;
crossing a back-edge uses the predecessor table without itself mutating
runtime state. Runtime ticks and method depth are therefore separate
resources even though the initial value of the latter is selected from
`recFuel`.

## Total recursive-method knot

`Methods` has six fields. The two policy-sensitive WHNF fields are necessary:
re-entering plain `whnf` would incorrectly restore successor collapse, and
re-entering plain `whnfCore` would incorrectly discard cheap projection/
recursor flags.

| Field | Successor-table implementation | Main production back-edges |
|---|---|---|
| `whnf` | `RecM.whnf` under `methodsN n` | `whnfRec` |
| `whnfCore` | `RecM.whnfCore` under `methodsN n` | retained public/legacy interface; no raw algorithmic read |
| `whnfMode` | `RecM.whnfWithNatSuccMode` under `methodsN n` | stuck-successor normalization through `whnfModeRec` |
| `whnfCoreFlags` | `RecM.whnfCoreWithFlags` under `methodsN n` | cheap/full structural recursion through `whnfCoreFlagsRec` |
| `infer` | `RecM.infer` under `methodsN n` | `inferCall`, `inferOnlyCall`, and five WHNF inference probes |
| `isDefEq` | `RecM.isDefEq` under `methodsN n` | `isDefEqCall` plus WHNF's instrumented `callIsDefEq` probe |

`methodsOut` implements all six fields as `.maxRecFuel` with the input state
unchanged. `methodsN 0 = methodsOut`; every field of `methodsN (n + 1)` runs
its corresponding algorithm under `methodsN n`. Thus every logical
back-edge decreases the table index even on tick-free paths and on arguments
that are not syntactic subterms.

The direct-read audit is:

```text
rg -n '\(← read\)\.(whnf|whnfCore|whnfMode|whnfCoreFlags|infer|isDefEq)' \
  Ix/Tc --glob '*.lean'
```

The live edges have the following roles:

- WHNF recursion uses `whnfRec`, `whnfModeRec`, and `whnfCoreFlagsRec`.
- WHNF has five direct `infer` probes in struct-eta, K-recursion, and
  decidable reduction. They still read the predecessor table; the direct
  syntax avoids an `Infer` import cycle.
- Infer's structural recursion uses `inferCall`; infer-only recursion wraps
  the same predecessor field with `TcM.withInferOnly`.
- Every recursive DefEq edge uses `isDefEqCall`. Its inference probes use
  `inferOnlyCall`.
- `Inductive.computeKTarget` uses `inferOnlyCall`.
- `Whnf.synthCtorWhenK` uses `callIsDefEq`, which adds balanced diagnostic
  dispatch instrumentation around the same predecessor field.

The four older `call*` wrappers maintain `dispatchDepth`. That counter is
not the termination argument. `maxDispatchDepth = 200000` is only a
Lean-side native-stack hardening guard, and its `.other` error is deliberately
distinct from parity-visible `.maxRecDepth`.

## Explicit local bounds and measures

| Cluster | Bound / measure | Exhaustion behavior |
|---|---|---|
| WHNF delta, core, no-delta, stuck-successor, and telescope scans | `maxWhnfFuel = 10000` through `RecM.runBounded` | `.maxRecDepth` before invoking the next step |
| DefEq lazy-delta and projection loops | `maxWhnfFuel` through `runBounded` | `.maxRecDepth` before the next step |
| Inductive positivity, universe/field, nested-type, flat-block, recursor, and telescope scans | structural worklists or `maxWhnfFuel` | structural completion or `.maxRecDepth` |
| `Check.countForalls` | `maxWhnfFuel` | `.maxRecDepth`; completed iterations retain their state, matching `EStateM` |
| Nat-offset walkers | `256 - depth` | successful `none` at zero |
| predicate Nat evaluator | `64 - depth` | successful `none` at zero |
| beta-lambda peeling | original application-argument count | returns the consumed prefix |
| positivity/nested-constructor mutual SCC | decreasing `Nat`, initialized from `maxWhnfFuel` | `.maxRecDepth` at zero |
| open Nat-reducer argument | temporary `min recFuel 4096` | restores the outer counter minus fuel actually consumed |
| DefEq semantic recursion guard | `maxDefEqDepth = 2000` | `.maxRecDepth`, after balancing `defEqDepth` |

Expression occurrence, safety-reference, universe-validation, and
well-scopedness traversals use explicit worklists with structural measures.
Canonical sorting/refinement uses input-size fuel; context truncation,
context-suffix closure, and union-find path halving use finite container-size
bounds. These replacements preserve the old traversal order where errors are
observable; unit regressions pin the LIFO universe-validation order.

The operational behavior change is intentionally narrow: malformed or
adversarial inputs that could previously diverge in an unbounded loop now
return `.maxRecDepth` at the documented cap. Valid-corpus verdict and
headroom parity is the A5 closure gate. Rust and Aiur are deliberately
unchanged in K0; any corresponding hardening is a later transport obligation
after the Ix.Tc theorem interface is stable.

## Proof and regression surface

`Ix.Tc.Verify.Totalization` exposes, and the completed trust manifest audits:

- zero/successor equations for all six `methodsN` fields;
- unchanged-error-state equations for all six `methodsOut` fields;
- `TcM.runRec` current-fuel and public-entry equations;
- exact run equations for `inferCall`, `inferOnlyCall`, `isDefEqCall`,
  `whnfRec`, `whnfModeRec`, and `whnfCoreFlagsRec`;
- wrapper equations for full/stuck WHNF, full/cheap WHNF core, Infer, Nat
  evaluators, worklists, and every introduced zero-fuel boundary;
- production `checkInductive`, recursor, `RecM.checkConst`, and
  `TcM.checkConst` roots now that the complete kernel is transparent.

Regressions cover zero table depth before mutation, one-level non-recursive
dispatch for all relevant method families, Infer structural depth, zero
local-loop fuel before the next mutation, exact LIFO diagnostics, deep
worklist stack safety, local-context restoration, and normal-corpus checker
behavior.

The reproducible source audits are:

```text
rg -n '^\s*partial def' \
  Ix/Tc/{Whnf,Infer,DefEq,Inductive,Check}.lean
rg -n '^\s*(while|repeat)\b' \
  Ix/Tc/{Whnf,Infer,DefEq,Inductive,Check}.lean
rg -n 'TcM\.tick' \
  Ix/Tc/{Whnf,Infer,DefEq,Inductive,Check}.lean
```

The first two must return no matches; the last must return exactly the WHNF
and DefEq charge sites described above.

## Boundary to K1/K2

K0 establishes total, equation-visible production functions and preserves
their tested operational behavior. It does **not** establish checker
soundness. `Methods.WF`, the conditional WHNF/Infer/DefEq WF theorems, and
the knot-closing induction `(methodsN n).WF` belong to K1/K2. In particular,
the method index closes Lean termination for tick-free cycles, but K1/K2
must still prove that each field preserves `VerifyWorld`, run support, cache
coherence, and the declared native/inductive oracle boundaries.

## Closure validation

The 2026-07-27 K0 closure run passed all of the following:

- exact four-statement sorry-frontier check;
- completed (295 roots) and statement (4 roots) trust audits;
- `lake build IxTcVerify` and the default `lake build`;
- strict `tc-unit` with warnings treated as failures;
- pinned Init/Std stress constants and accelerated-versus-pure differential;
- Init-scale anon verdict parity;
- focused anon differential, full anon/meta roundtrip, and `tc-init` suites;
- Lean4Lean replay and tutorial suites.

No production source in the Rust kernel or Aiur IxVM was changed. Their
acceptance simulation/refinement work remains downstream of the Ix.Tc
soundness theorem.
