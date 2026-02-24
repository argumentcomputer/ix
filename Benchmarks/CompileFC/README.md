# CompileFC

Runs the Ix compiler over the Lean environment of all defs from https://github.com/google-deepmind/formal-conjectures.

The defs in CompileFC.lean were generated automatically with the following:
```
lake update
cd .lake/packages/formal_conjectures
lake exe mk_all --lib FormalConjectures
mv FormalConjectures.lean ../../../CompileFC.lean
```

This project shadows the `formal-conjectures` project's Lean version, which is not always up to date.

## Usage

First ensure the Lean version used to build Ix matches the `Benchmarks/CompileFC/lean-toolchain` version (check against `ix --version`). Then run

`ix compile --path /path/to/CompileFC.lean`
