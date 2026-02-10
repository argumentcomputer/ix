# Compile

Runs the Ix compiler over the following libraries when imported:

- [Lean4](https://github.com/leanprover/lean4)
- [Mathlib](https://github.com/leanprover-community/mathlib4)
- [FLT project](https://github.com/ImperialCollegeLondon/FLT)

## Usage

`lake exe compile-<lib>`, e.g. `compile-mathlib`

> [!NOTE]
> Compiling Mathlib and FLT, which depends on the former, requires a multi-core CPU and 128+ GB RAM.
