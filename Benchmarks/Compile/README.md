# Compile

Test libraries for the Ix compiler

- [Init, Std, and Lean libraries](https://github.com/leanprover/lean4)
- [Mathlib](https://github.com/leanprover-community/mathlib4)
- [Imperial College London FLT project](https://github.com/ImperialCollegeLondon/FLT)
- [Anthropic FLT proof artifact](https://github.com/anthropics/fermats-last-theorem)
- Every native TruthMines member, independently, through the generated
  `TruthMines/Members/<Qualifier>.lean` fidelity drivers
- [Palomar.ix](https://github.com/argumentcomputer/Palomar.ix) as one aggregate
  library (its colliding constituent projects remain in isolated workspaces)

## Usage

First ensure the Lean version used to build Ix matches the `Benchmarks/Compile/lean-toolchain` version (check against `ix --version`). Then run

`ix compile /path/to/Compile<Lib>.lean` # replace `<Lib>` with `Init`, `InitStd`, `Lean`, `Mathlib`, `FLT`, or `AnthropicFLT`

The Anthropic artifact is also registered as the on-demand `AnthropicFLT`
benchmark environment. After building its oleans, benchmark the Ix compiler
and Rust kernel from the repository root with:

```sh
cd Benchmarks/Compile
lake build +CompileAnthropicFLT:olean
cd ../..
ix bench run --backend compile --env AnthropicFLT
ix bench run --backend ooc --env AnthropicFLT --ixe AnthropicFLT.ixe
```

For a TruthMines constituent, use the nested fidelity workspace, for example:

`ix validate Benchmarks/Compile/TruthMines/Members/Cli.lean`

The native member wrappers import the canonical generated TruthMines drivers,
so the catalog records remain the only source of dependency pins. Run the
complete sweep with `lake exe truthmines validate`; use `--only Cli,Palomar`
to select libraries.

> [!NOTE]
> Compiling Mathlib and the Imperial FLT project currently requires a
> multi-core CPU and >64 GB RAM. Anthropic reports that building its FLT
> artifact from scratch peaked at 153 GB RAM and used about 67 GB under
> `.lake/`, plus roughly 220 GB of generated C files. The `olean` facet above
> skips native object compilation, but Lean still emits those C files.
