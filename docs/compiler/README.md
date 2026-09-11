# Compiler

`Ix.Compiler` contains the Ixon compiler, intermediate languages, semantic
proofs, optimizers, and experimental x86-64 backend imported from Compilatrix.
Its input syntax and APIs currently live under `Ix.Compiler.Ixon`.

Build the library with `lake build IxCompiler`. Run its complete validation
suite with `lake run check-compiler`. The latter builds every `compiler-*`
executable, checks the proof and native trust boundaries, exercises byte and
object corruption cases, compares independent artifact runs, and checks the
benchmark analyzer. GNU `objdump`, `readelf`, and `sha256sum` are required.
On x86-64 Linux it also uses `cc` to link and execute the native fixtures.

The executable names have a `compiler-` prefix, for example:

```text
lake exe compiler-tests
lake exe compiler-source-native-runtime -- /tmp/ix-runtime-artifacts
lake exe compiler-benchmark -- analysis-self-check
```

Fixture inputs and reviewed expected outputs are in `Tests/Fixtures/Compiler`.
The imported JSON fixture/report formats and lowercase `compilatrix/...` hash
domains retain their existing compatibility meaning. Three expected rejection
messages and two diagnostic-report hashes change with the Lean namespace.
Canonical source/IR addresses, native object bytes, and embedded native
provenance retain their existing identities.

The benchmark runner in `Benchmarks/Compiler` retains the existing measurement
protocol and accepts explicit comparison toolchains. Running the full comparison
requires those external tools; the normal compiler check runs its analyzer's
regressions. Historical measurements and generated benchmark archives are not
part of this source import.

See [the design](compiler-design.md), [current lowering restrictions](lowering-restrictions.md),
and [trust assumptions](trusted-extern-ledger.md). These targets are independent
of the current `ix compile` command, which exports Lean declarations to Ixon.

## Provenance

The import starts from Compilatrix commit
`1c3b6fba316a210ac1f0f7541de3a1a769880374`. All 410 original library modules were
ported from `Compilatrix` to `Ix.Compiler`, together with the tests, fixture
producers, native durability shim, and benchmark sources. The port adapts paths,
Lake targets, and the component trust audit to this monorepo.

The monorepo uses Lean 4.33.1 and its existing Blake3.lean revision; the source
project used Lean 4.33.0 and an older Blake3.lean revision. The complete compiler
axiom fence is checked on the new pins. One exact expectation changes:
`IxIR2.Lower.CheckedRun.valid` no longer depends on `Classical.choice`.
The two imported license texts are retained in `Ix/Compiler/LICENSE-MIT` and
`Ix/Compiler/LICENSE-APACHE`.
