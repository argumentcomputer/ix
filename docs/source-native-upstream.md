# Unchanged upstream native computations

C3 carries the pinned `applyClosed` and `letClosed` exports through validated
source erasure, owned lowering, checked physical IxIR₂, structural native
selection, certified ELF emission, and linked execution. Original Lean source,
writer revision, six-constant closures, packed bytes, and roots remain unchanged.
The [source coverage matrix](source-coverage.md) retains all five upstream entries
and the addition, recursion, and captured-closure boundaries.

| Entry | Source result | Native `.text` | ELF bytes | Native calls | Stack bytes written |
| --- | ---: | ---: | ---: | ---: | ---: |
| `applyClosed` | 3 | 84 | 936 | 4 | 48 |
| `letClosed` | 4 | 91 | 944 | 4 | 48 |

Both previously stopped at the scalar selector's missing-constructor-schema
error. The new policy is `closed-unary-nat-calls/1`, with ELF lowering version 4
and pass policy version 1. The entry is closed: it takes no runtime arguments
and exports `uint64_t compilatrix_main(void)`.
Its residual native functions still execute successors and direct calls. Neither
the selector nor the emitted entry replaces the computation with its final
constant. These call measurements are separate from PERF1's runtime-input reversal.

## Accepted fragment and fallback

`Compilatrix.X86.NatCalls` traverses one-block shared functions. It accepts
literal/aliased Nat values, the actual addressed zero/successor constructors,
shared retain/release instructions, known capture-free PAPs, direct calls,
known applications, returns, and direct tail calls. A known closure parameter
specializes a residual call interface; at most one Nat argument remains. The
cache includes both the source declaration identity and parameter kinds.
Source identifiers are not hard-coded into this selector.

The finite policy allows depth 32, 64 residual functions, and 1,024 source
instructions per visited block. Recursive expansion, open main functions,
captured or unknown closures, multiple Nat arguments, branches/joins,
unsupported constructors, ownership modes, and exhausted budgets reject.
Mathematical evaluation checks every intermediate result before conversion to
an exact 64-bit word, including successor overflow. Source validation runs
before this representation pass, so ignored release instructions cannot hide
invalid register or ownership uses.

`captureClosed` retains its checked physical baseline and reports `capturedPap`.
Zero depth/function/instruction budgets also retain that baseline. Misaligned
or insufficient supplied stack memory produces no native execution certificate.
`addClosed` and the 17-constant Std slice now pass exact erased-block reuse and
stop at their recorded missing `Covered` certificates. Their addressed artifacts
are explicitly marked as preceding source erasure certification.

## Proof and observation scope

The selector's `Output` contains validation, structural lowering equality,
bounded mathematical evaluation, exact-word conversion, the actual physical
execution, its constructor-valued Nat observation, and complete shared-result
release. `Output.refinesSuccessfulRun` uses successful-run uniqueness to connect
any successful physical fuel budgets to that same value and complete store.

`IxIR2.Pipeline.Attached.sourcePhysical` supplies the general constructor-valued
source-to-physical bridge. `NatCalls.sourceObjectRefines` composes it with the
closed representation certificate and E2's execution of the actual serialized
ELF object. The theorem retains the source oracle/sharing hypotheses and an
explicit `Execution` certificate for the supplied machine state. That certificate
checks termination, RAX, saved registers, restored stack, safe call/return slots,
and a readable caller return address. `Execution.objectReturns` states the actual
object-byte return value.

The producer certifies four finite stack/register configurations, including
nonzero memory and high addresses, with 64 writable bytes below the return slot.
Native tests additionally protect the caller frame and all System V saved
registers. These are closed translation-validation and supplied-state execution
claims. N3's runtime scalar arguments, branches, joins, and general compositional
contracts, and F1's sufficient-stack theorem, remain separate work. The local
x86 model and system linker/loader obligations remain explicit. Six new axiom
fences retain the ordinary logical basis and the existing indexed-source hash
axiom; they introduce no new axiom or production FFI symbol.

The physical baseline for `applyClosed` allocates five nodes, frees one before
return, and has three RC operations; complete result release reaches five frees,
seven RC operations, and zero live nodes. `letClosed` has six allocations, one
early free, and three RC operations; release reaches six frees, eight RC
operations, and zero live nodes. Native results use an unboxed eight-byte word
and no heap allocation, RC operation, or heap release.

## Artifacts and checks

```sh
lake build source-native-upstream check-source-native-upstream
.lake/build/bin/source-native-upstream /tmp/new-upstream-native
.lake/build/bin/check-source-native-upstream \
  --fixture .lake/build/bin/source-native-upstream \
  --cc gcc --harness fixtures/source-native-upstream/native_harness.c
```

The independent checker imports the tool oracles, without importing the
compiler. It reconstructs the complete native text from residual expressions,
resolves direct-call displacements, independently reads ELF entry/symbol/text
and provenance bytes, and checks physical/reclaimed heaps and all execution
observations. It compares two fresh complete eight-file artifact sets with the
reviewed five-case matrix. Corruption, budget/stack fallback, structural selector,
overflow, full ABI, and the affected coverage neighbors are checked in Lake/Nix.

For named compiler costs, the producer accepts an optional original entry name:
`source-native-upstream NEW_DIRECTORY applyClosed`. The independent command
`check-source-native-upstream inspect DIRECTORY` checks that named artifact.
The benchmark build records wall/CPU time and peak RSS for each operation,
serialized IR/HPT evidence and snapshot sizes, native code growth, and runtime
counters. The [PERF1/C3 reference](performance/native-reverse-2026-09-09/README.md#c3-unchanged-upstream-computations)
retains 30 blocks of native call measurements: medians of 5.2040 ns for
`applyClosed` and 5.2028 ns for `letClosed` on the recorded host. It includes
uncertainty, named compile/check costs, IR/HPT and snapshot sizes, physical
and native memory counts, and independent artifact/correctness/analysis replay.
The object sizes above refer to that retained build. The [benchmark protocol](../benchmarks/protocol.md)
defines measurement and replay; the [follow-up decision](performance/native-reverse-2026-09-09/README.md#follow-up-decision)
keeps runtime arguments, broader recursion and general stack sufficiency at
their N3/F1 gates.
