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
sessions against the transcripts Lean's interpreter prints. The oracle driver
(`main`) answers a line `ROOT S E` with the step's value, and a line
`session ROOT ARG…` with the transcript of a session under a model of the
platform written in the source in plain Lean (standard output and error in
hex, the status, the number of calls).

Licence: Apache-2.0 OR MIT (original programs).

## Regenerating

With the ix of this repository built at the repository root (`lake build ix`;
the revision and the binary's SHA-256 are in [`corpus.json`](corpus.json)),
Lean 4.34.1 on `PATH`, and the `lake` stand-in of [Refreezing](../../../docs/corpus.md#refreezing)
in `FAKE`, from `IxCC/`:

```sh
lake exe corpus rebuild fixtures/corpus/phase1-machines/corpus.json --ix ../.lake/build/bin/ix --ix-path FAKE
```

which runs, in `src/`, the commands the manifest records (`ix compile --no-build
--consts … --equations --anon --unbound`, its named twin, `ix addr-of`, and
`lean -Dlinter.all=false --run Machines.lean` on the cases). When
`lib/IxccExe.lean` changes, copy its text over the head of `src/Machines.lean`
first.
