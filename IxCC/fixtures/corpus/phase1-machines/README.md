# Numeric state machines

The `phase1-machines` family of the [fixture corpora](../../../docs/corpus.md):
programs that run as standalone executables of the generic request shell
(`ixcc compile --exe FILE --machine`; [standalone
executables](../../../docs/standalone-executables-design.md#x2-as-implemented)).
Each root is a step `Nat → Nat → Nat` of a state and an event whose result
packs the next state and a request (`IxCC/Exe/Machine.lean`).

[`src/Machines.lean`](src/Machines.lean) begins with the text of
[`IxCC/lib/IxccExe.lean`](../../../lib/IxccExe.lean), the library that parses
and renders in Lean, byte for byte (`tests-exe` checks it), then:

| Root | Machine |
| --- | --- |
| `Machines.fibMain` | K1's `fib` as an executable: one decimal argument, the result in decimal (`IxccExe.Main1`, first order) |
| `Machines.fibMainHO` | the same through `IxccExe.Main1.run fib`: `fib` passed as a closure |
| `Machines.idMain` | the identity, for the range's edges (arguments and results below `2^48`) |
| `Machines.badRequest` | always the request field 5, a kind outside the interface (the shell exits 72) |
| `Machines.echo` | the session machine: every argument byte echoed (changed by a running hash), a newline on standard error after each argument, the hash in decimal at the end and an exit with the hash modulo 256 |

The cases are states and events chosen to cover every phase and transition;
each runs at every level and natively (`tests-corpus`), and `tests-exe` runs
the roots as machine executables, `fib` beside `--exe`'s `fib`, and `echo`'s
sessions against the transcripts Lean's interpreter prints (two of them over more
than 1,400 calls, also against the session model on the byte evaluator). The oracle driver
(`main`) answers a line `ROOT S E` with the step's value, and a line
`session ROOT ARG…` with the transcript of a session under a model of the
platform written in the source in plain Lean (standard output and error in
hex, the status, the number of calls).

## The natural style (`natural`)

[`src/Natural.lean`](src/Natural.lean) holds the same machines written
without the library's workarounds: `if`, `==` and `&&` instead of the named
primitives and `bif`, `if` chains for the message table and the powers of ten
instead of balanced trees, and `Main1.step` a nested `if` on the phase instead
of one step that computes each phase's result and then selects one. It exists
so that the suites hold the middle end's result on ordinary source: the
library's workarounds were written because the middle end left such code with
closures, and these roots show that it no longer does.

| Root | Machine |
| --- | --- |
| `Natural.fibMain` | `fib` as an executable, as `Machines.fibMain`, on the same states and events |
| `Natural.onMessage` | the message phase's step alone (payload `pos * 4 + id`): its `if` and `==` chains |

Besides running every case at every level, natively and as `--exe`
executables (`tests-corpus`), `tests-corpus` asserts for each root that under
`--rc auto` it compiles zero RC with a verified compile claim, that the
closures step finds it first order (no closure keys), and that with the shrink
walk's pending join entry forced off (a test-only switch of the producer) it
still compiles and gives the same values (`Natural.fibMain` through the
fallback without the inline-round retry, since the checker refuses the run with
it, below): the gain is an optimisation, not something correctness depends
on. The choice is not in the certificate, so the checker makes its own: a
producer forced off is refused on `Natural.fibMain`, where the checker's walk
derives another program from its certificate (at allocation), and accepted on
`Natural.onMessage`, where it only counts fewer rounds (plain RC, 6 closure
keys, and the same values).
`tests-exe` does not run these roots as machine executables.

These roots sit close to the middle end's budgets: `Natural.fibMain` is the
committed program nearest three of them (its deepest Anf global against
`Anf.maxDepth`, its largest shrink step's walk work against
`Anf.maxStepWork`, its deepest walk against `Walk.maxWalkDepth`, each more
than half its budget; [Middle-end budgets](../../../docs/compiler-design.md#middle-end-budgets)).
The middle end does not take a round that would pass one of them, so a later
change that makes these roots compile with closures again, failing
`tests-corpus`'s natural-style section, may have pushed this fixture over a
budget rather than broken an optimisation: the budget survey in that suite's
log prints each maximum beside the program that reaches it.

Licence: Apache-2.0 OR MIT (original programs).

## Regenerating

[`tools/regenerate.sh`](../../../tools/regenerate.sh) regenerates it with the
rest of the committed fixtures ([Refreezing](../../../docs/corpus.md#refreezing)).
For this family alone: with the ix of this repository built at the repository
root (`lake build ix`, in its dev shell; its version is in
[`corpus.json`](corpus.json)), Lean 4.34.1 on `PATH`, and the `lake` stand-in
`regenerate.sh` writes in `FAKE`, from `IxCC/`:

```sh
lake exe corpus rebuild fixtures/corpus/phase1-machines/corpus.json --ix ../.lake/build/bin/ix --ix-path FAKE
```

which runs, in `src/`, the commands the manifest records (`ix compile --no-build
--consts … --equations --anon`, which writes the role-bound envelope, its named
twin, `ix addr-of`, and
`lean -Dlinter.all=false --run` on `Machines.lean` and `Natural.lean` for the
cases). When
`lib/IxccExe.lean` changes, copy its text over the head of `src/Machines.lean`
first.
