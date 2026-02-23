# Compile

Test libraries for the Ix compiler

- [Init, Std, and Lean libraries](https://github.com/leanprover/lean4)
- [Mathlib](https://github.com/leanprover-community/mathlib4)
- [FLT project](https://github.com/ImperialCollegeLondon/FLT)

## Usage

First ensure the Lean version used to build Ix matches the `Benchmarks/Compile/lean-toolchain` version (check against `ix --version`). Then run

`ix compile --path /path/to/Compile<Lib>.lean` # replace `<Lib>` with `InitStd`, `Lean`, `Mathlib`, or `FLT`

> [!NOTE]
> Compiling Mathlib and FLT currently requires a multi-core CPU and >64 GB RAM.
