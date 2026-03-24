# Kernel Comparison Benchmarks

Compares wall-clock typechecking time across five Lean 4 kernel implementations on a common declaration or module.

## Checkers

| Name | Implementation | Language |
|------|---------------|-----------|
| `lean4` | Lean 4 C++ kernel (`addDeclCore`) | C++ |
| `lean4lean` | lean4lean reimplementation (`Lean4Lean.addDecl`) | Lean |
| `nanoda` | nanoda external checker | Rust |
| `ix-lean` | Ix NbE kernel (`Ix.Kernel.typecheckAll`) | Lean |
| `ix-rust` | Ix NbE kernel via FFI (`rsCheckEnvFFI`) | Rust |

## Quick Start

```bash
cd Benchmarks/Kernel

# Build everything (Lean deps + nanoda + lean4export)
lake build

# Run all checkers on Nat.add_comm (default)
lake exe bench-kernel
```

## Usage

```
lake exe bench-kernel [FLAGS]
```

### Flags

| Flag | Description |
|------|-------------|
| `-t, --target <name>` | Declaration or module to check. Default: `Nat.add_comm` |
| `-c, --checkers <list>` | Comma-separated list of checkers to run. Default: all five |
| `-j, --threads <n>` | Thread count for parallel checkers (nanoda, ix-rust). Default: all cores (`nproc`). Use `-j 1` for single-threaded. Measurements are distinguished by thread count. |
| `--from <mod>` | Module to load when target is a declaration outside Init (default: Init) |
| `-v, --verbose` | Per-constant output (lean4lean prints each `addDecl`, ix-lean/ix-rust print per-constant timing) |

### Examples

```bash
# Default: all checkers on Nat.add_comm
lake exe bench-kernel

# Check a specific declaration
lake exe bench-kernel -t Nat.succ_add

# Check all of Init (slower, doesn't work with ix yet)
lake exe bench-kernel -t Init -c lean4,lean4lean,nanoda

# Run only specific checkers
lake exe bench-kernel -c lean4,ix-rust

# Verbose mode with per-constant output (only prints fine-grained timing for ix-lean/ix-rust)
lake exe bench-kernel -v

# Single-threaded comparison (apples-to-apples)
lake exe bench-kernel -j 1

# Combine flags
lake exe bench-kernel -t Nat.add_comm -c lean4,lean4lean -v -j 1

# Typecheck def from Std
lake exe bench-kernel -t Std.HashMap.insert --from Std -c nanoda

# Check all of `Batteries` since it's in .lake/packages
❯ lake exe bench-kernel -t Batteries -c nanoda
```

## Output

Results are displayed as a markdown table with timing, and saved to `benchmark-report-compare-checkers.md`. On subsequent runs, base benchmark and percent change columns are populated automatically via the Ix benchmark infrastructure (stored in `.lake/benches/`).

```
## compare-checkers/Nat.add_comm

|   Function    | New Benchmark | Base Benchmark |   % change    |
|---------------|---------------|----------------|---------------|
|     lean4     |    1.99ms     |     1.98ms     | 0.43% slower  |
|   lean4lean   |    3.44ms     |     3.25ms     | 5.87% slower  |
| nanoda(j=24)  |    5.23ms     |     5.54ms     | 5.64% faster  |
|    ix-lean    |    6.45ms     |     4.56ms     | 41.59% slower |
| ix-rust(j=24) |    8.84ms     |     8.24ms     | 7.29% slower  |
```
