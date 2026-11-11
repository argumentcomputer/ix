# Roots whose compiled arity is not their declared count

Regression roots for the root-arity check of the [closures
design](../../../docs/closures-design.md) ("Proof obligation"), as a family of
the [fixture corpora](../../../docs/corpus.md). Lean does not η-expand a
definition's value to its type, so a root's compiled arity (the leading λs of
the body the unfolding table gives it) can differ from the number of
parameters its declared type shows. [`src/Arity.lean`](src/Arity.lean) holds
the roots, two table entries (an η-long equation for `Arity.main4` and a
`csimp` entry for `Arity.slowDouble`) and the oracle driver for `lean
--run`; [`corpus.json`](corpus.json) records the closure, the sidecar, the
census, the cases and the interpreter's values, each at the declared type's
number of arguments.

| Roots | Shape | Compiled / declared |
| --- | --- | --- |
| `main1`, `main2`, `pm`, `main8`, `main8t`, `main10c`, `slowDouble` | as many leading λs as the type shows | equal |
| `main3`, `main4`, `main9`, `main9r`, `main10`, `main11`, `main12`, `mainB3`, `mainB4`, `main8p` | point-free or partially applied in their last parameters | 0 or 1 against 1, 2 or 3 |
| `addTo`, `halve` | recursive, point-free in the last parameter (`halve`'s kernel value has no λ, its equation one) | 1 against 2 |
| `main7`, `main7b` | the result type is a definition of a function type | 2 against 1; 1 against 1 |
| `spin` | `partial_fixpoint`, diverges after one argument; no cases | 1 against 2 |

**Not a registered family.** It is not in `Corpus.families`, so `corpus check`
and `tests-corpus` do not read it. The only required gate that reads it is
`tests-pipeline` (its `defun` part, `tests-pipeline --only defun`, in the
`suites` check), which compiles every root with P8 between the middle end and
Fir, outside the production pipeline, and with the root-arity check
(`Recheck.checkRootArities`): every root whose two counts differ must be
refused with `rt.arity` and both counts; `main7b` compiles with no readback
type; the others compile and agree with the interpreter natively. With the
η-long equation `main4` compiles at 2 and agrees; with the `csimp` entry
`slowDouble` has arity 0 and is refused. The production compiler declines
most of these roots today at `fir: fir.closures`; `spin` and `main7` compile
today, and the check, once `Recheck.run` calls it, refuses them.

**How it was produced** (2026-11-10). With the ix of
[`phase2-closures`](../phase2-closures/README.md) (the same binary: the
revision and its SHA-256 are in `corpus.json`) and Lean 4.34.1 on `PATH`,
from `IxCC/`:

```sh
lake exe corpus rebuild fixtures/corpus/phase2-arity/corpus.json --ix ../.lake/build/bin/ix
```

which runs, in `src/`, the commands the manifest records (`ix compile
--no-build --consts … --equations [--anon] --unbound`, `ix addr-of` for every
name, and `lean -Dlinter.all=false --run Arity.lean` on one line `ROOT ARGS…`
per case). The closure is larger than the roots suggest because the
`partial_fixpoint`, `omega` and `decide` proofs come with it; erasure never
visits them.
