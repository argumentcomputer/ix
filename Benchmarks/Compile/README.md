# Compile

Test libraries for the Ix compiler

- [Init, Std, and Lean libraries](https://github.com/leanprover/lean4)
- [Mathlib](https://github.com/leanprover-community/mathlib4)
- [FLT project](https://github.com/ImperialCollegeLondon/FLT)
- Every native TruthMines member, independently, through the generated
  `TruthMines/Members/<Qualifier>.lean` fidelity drivers
- [Palomar.ix](https://github.com/argumentcomputer/Palomar.ix) as one aggregate
  library (its colliding constituent projects remain in isolated workspaces)

## Usage

First ensure the Lean version used to build Ix matches the `Benchmarks/Compile/lean-toolchain` version (check against `ix --version`). Then run

`ix compile /path/to/Compile<Lib>.lean` # replace `<Lib>` with `Init`, `InitStd`, `Lean`, `Mathlib`, or `FLT`

For a TruthMines constituent, use the nested fidelity workspace, for example:

`ix validate Benchmarks/Compile/TruthMines/Members/Cli.lean`

The native member wrappers import the canonical generated TruthMines drivers,
so the catalog records remain the only source of dependency pins. Run the
complete sweep with `lake exe truthmines validate`; use `--only Cli,Palomar`
to select libraries.

> [!NOTE]
> Compiling Mathlib and FLT currently requires a multi-core CPU and >64 GB RAM.
