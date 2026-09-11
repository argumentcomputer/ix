# Runtime scalar source functions

The first N3 slice compiles a bounded, nonrecursive scalar language with
runtime arguments, exact Nat arithmetic, branches, joins, and direct helpers.
[`Scalar.Source.compile`](../Compilatrix/X86/ScalarSourceObject.lean) consumes
an existing `Pipeline.ValidatedCompilation` and emits a certified instruction
stream and ELF object once per source function.

Native lowering attaches at the **checked erased-source boundary**. The five
fixtures also pass the complete ordinary source compiler through checked
physical IxIR₂. The native proof uses the retained erasure certificate and
runtime application simulation; it does not select arbitrary physical IxIR₂ CFGs.
The subsequent [physical scalar CFG slice](source-native-physical-scalar.md)
provides that separate selection boundary for its declared fragment.
These are synthetic Ixon fixtures, not
additional unchanged upstream programs.

## Admitted source fragment

The export has two runtime Nat parameters. Helpers have zero, one, or two
parameters and target earlier functions in a checked topological order.
Expressions include variables, exact Word literals, addition, truncated
subtraction, immutable lets, zero/nonzero branches, and direct calls. Branch
arms return through their enclosing continuation; let bodies consume the
joined result.

Primitive recognition checks complete canonical Nat recursor, addition,
predecessor, subtraction, and lazy case-recursion bodies. Their evaluator
proofs include literals and constructed successor spines. Compilation uses no
arithmetic extern, replacement source oracle, or per-input native execution
certificate. Every accepted raw function is reconstructed and checked for
exact declaration equality before the selector issues its proof.

Limits are 32 functions, 32 local slots including parameters, 4,096 scalar
nodes per function, and selection traversal fuel 128, including expression
traversal. Dynamic or unknown calls, recursive call graphs, captured functions,
unsupported parameter uses, invalid scope, excessive arity, and mismatched
primitive bodies reject. Constants use a shared producer
`(fun (_ : Sort) => n) Sort`, erased to
`app (lam many (lit n)) erased`, to satisfy the existing ownership checker.
The reconstructed source retains this wrapper.

## Arithmetic and ABI

`ExactNat.encode` accepts precisely `0 ≤ n < 2^64`.
`Scalar.encodeArguments` rejects an oversized input before entry. Source
literals outside that range reject during selection. Neither conversion wraps.

```c
struct scalar_result { uint64_t value, status; };
struct scalar_result compilatrix_scalar(uint64_t left, uint64_t right);
```

System V AMD64 places arguments in RDI/RSI and results in RAX/RDX. Status 0
means RAX is the exact source Nat. Status 1 means an addition overflowed;
RAX is zero. The flag propagates through calls and joins. Subtraction returns
`max(left - right, 0)` without an underflow error.

An overflowing intermediate requests fallback even if later source arithmetic
could yield a representable result: `(MAX + 1) - 1` returns status 1. The caller
decides whether to evaluate the original source with unbounded Nats; the
native function does not retry internally. Untaken branch arms are not run.

The caller supplies a readable and writable stack reservation of `272 * D`
bytes, including its eight-byte return slot, where `D > entry_index`. Its base
is 16-byte aligned and addresses must not wrap. Entry RSP points to the final
word, is 8 modulo 16, and has `272 * D - 8` reserved bytes below it.
`D = entry_index + 1` is sufficient; this is a conservative bound, not the
smallest dynamic call depth. Each activation saves RBP and reserves 256 bytes
for locals; internal calls are aligned.

The proof covers arbitrary initial local bytes and saved registers. It
preserves RBX, RBP, R12–R15, the external return address, and all memory outside
the reservation. Physical RET returns to that address and increments entry
RSP by eight. There is no native heap allocation. General owned-heap capacity
and allocating calls remain F1/A1 follow-ups. Stack mapping/alignment are caller
preconditions, not native capacity guards. Invalid mappings are machine-model
negative tests, not graceful native fallback behavior.

## Proof endpoints

`Scalar.Evaluates.native` composes instruction, block, frame, and call contracts
for every accepted evaluation. `Checked.function_total` supplies an evaluation
for every correctly sized argument array, including overflow. `Evaluates.exact`
relates each successful Word result to unbounded Nat semantics, implemented in
the existing IxIR₀ evaluator by `Source.raw_evaluates`.

`ObjectEval.run_safeSteps` retains the exact return-address mask through byte
execution. `RootRun.objectResult` proves the parsed object's value, status,
return RIP, register/RSP restoration, and preservation of outside memory.
`Source.Compiled.nativeReturns` supplies execution for every pair of Words
with sufficient stack. `Source.Compiled.sourceReturns` additionally relates
each successful native result to the original source call. Its `Invocation`
retains existing source evaluation/application, sharing, oracle, and input
relation premises; it assumes no scalar or native execution.

Fifteen public axiom fences cover arithmetic, source recognition/simulation,
totality, capacity, and object execution. Pure scalar/native contracts use the
existing logical axioms. Source-indexed endpoints retain the existing
addressed-BLAKE3 exception. No new axiom, extern, or admitted proof is added.
ISA/reference agreement and actual linker/loader behavior remain existing
trust boundaries.

## Artifacts and regression gate

Policy `source-scalar-runtime/1` uses the actual IxIR₁ graph root in ELF
provenance, lowering version 5, and policy version 1. Snapshots retain source
identity, complete source compilation artifacts, function/block counts, exact
text and digest, entry offset, provenance, stack reservation, and observations.
Runtime arguments do not enter source, graph, or object identity.

| Fixture | Computation | Functions | Blocks | Text bytes | Stack bytes |
|---|---|---:|---:|---:|---:|
| add | `a + b` | 1 | 4 | 112 | 272 |
| sub | `a - b` | 1 | 6 | 129 | 272 |
| diamond | join `a = 0 ? b : a + b`, then subtract 1 | 1 | 10 | 215 | 272 |
| helpers | addition helper, then predecessor helper | 3 | 16 | 404 | 816 |
| nested | constant helper, subtraction helper, and nested branches | 3 | 20 | 474 | 816 |

```sh
lake build source-native-scalar check-source-native-scalar
.lake/build/bin/check-source-native-scalar \
  --fixture .lake/build/bin/source-native-scalar \
  --readelf readelf --objdump objdump --cc gcc \
  --harness fixtures/source-native-scalar/native_harness.c
```

Two fresh compiler processes must produce equal complete artifact sets matching
the reviewed report. The producer checks 45 feasible input pairs in both Ixon
and raw IxIR₀, plus 95 typed and actual object executions spanning zero, MAX,
addition overflow, subtraction underflow, joins, and error propagation. Huge
recursive source executions are not claimed: universal proofs supply their
agreement, while boundary tests use exact mathematical expectations.

Thirty-five malformed source variants, five scalar admission negatives, three
oversized conversions, and seven invalid stack mappings reject. The independent
checker rejects 25 artifact/observation corruptions. Binutils parses and
disassembles every object. On x86_64 Linux each object is linked once and called
166 times, including 64 further deterministic input pairs, on both ordinary
and separate guarded stacks. A lower guard page and canaries above the exact
proved reservation check bounds. The 830 linked calls check results, status,
saved registers, RSP, and caller memory. Nix check `source-native-scalar` uses
pinned tools; other platforms run artifact checks without the Linux harness.
