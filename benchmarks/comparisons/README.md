# Optional compiler comparisons

This Lake package owns the six-compiler comparison runner, counter-fold
measurements, and compiler-scaling measurements. It depends on the compiler
checkout through `../..` and uses the same reviewed Lean toolchain. Its
executables and dependency cache live in this directory's `.lake`, separately
from the compiler build.

The root `nix flake check` does not build this package, CakeML, or CompCert.
Compiler correctness gates still run in CI, including native execution,
sharing, graph, modular assembly, and source-evidence regression checks. Their
shared fixture modules remain in `../Benchmark`.

## Build and run

Run these commands from the repository root. The optional shell reads the
root flake's locked toolchains and supplies the pinned CakeML bootstrap,
CompCert, GCC, Clang, and measurement tools. It is supported on x86-64 Linux.

```sh
nix-shell benchmarks/comparisons/shell.nix
lake build source-native-runtime check-source-native-runtime \
  source-native-upstream check-source-native-upstream
lake -d benchmarks/comparisons build
benchmark=benchmarks/comparisons/.lake/build/bin/benchmark
"$benchmark" analysis-self-check
"$benchmark" build /tmp/comparison-build
"$benchmark" verify /tmp/comparison-build /tmp/comparison-verify
"$benchmark" smoke /tmp/comparison-build /tmp/comparison-smoke
"$benchmark" gc-smoke /tmp/comparison-build /tmp/comparison-gc-smoke
"$benchmark" compiler-scaling-smoke /tmp/compiler-scaling-smoke
```

Each output directory must be new. With matching tools already available,
`lake -d benchmarks/comparisons build` can be used directly. Execute the runner
from the repository root so it can find source fixtures and compiler seeds.
It locates its compiler-scaling worker beside its own executable and retains
that executable for replay.

The [comparison protocol](../protocol.md), [counter-fold protocol](../counter-fold.md),
and [compiler-scaling protocol](../compiler-scaling.md) describe measurement
and reproduction commands. Run their correctness, smoke, and replay steps
explicitly when changing the comparison package. Historical report bundles
retain their original sources and binaries.
