# Unchanged upstream native computations

C3 carries the pinned `applyClosed`, `captureClosed`, and `letClosed` exports through validated
source erasure, owned lowering, checked physical IxIR₂, structural native
selection, certified ELF emission, and linked execution. Original Lean source,
writer revision, six-constant closures, packed bytes, and roots remain unchanged.
The [source coverage matrix](source-coverage.md) retains all five upstream entries
and the addition and recursion boundaries.

| Entry | Source result | Native `.text` | ELF bytes | Native calls | Stack bytes written |
| --- | ---: | ---: | ---: | ---: | ---: |
| `applyClosed` | 3 | 84 | 936 | 4 | 48 |
| `captureClosed` | 2 | 91 | 944 | 4 | 48 |
| `letClosed` | 4 | 91 | 944 | 4 | 48 |

The capture-free entries use `closed-unary-nat-calls/1`, with ELF lowering
version 4. `captureClosed` uses `closed-static-capture-nat-calls/1`, with
lowering version 8. Both use pass policy version 1; the report's inventory
policy is `upstream-closed-nat/2`. The original two object files remain
byte-identical. Every entry takes no runtime arguments and exports
`uint64_t compilatrix_main(void)`.
The residual native functions execute successors and direct calls; the selector
retains their expressions through emission. These computations are separate
from PERF1's runtime-input reversal.

## Accepted fragment and fallback

`Compilatrix.X86.NatCalls` traverses one-block shared functions. It accepts
literal/aliased Nat values, the actual addressed zero/successor constructors,
shared retain/release instructions, known capture-free PAPs, direct calls,
known applications, returns, and direct tail calls. A known closure parameter
specializes a residual call interface; at most one dynamic Nat argument remains.
The static-capture mode additionally admits one Nat capture whose expression
is closed with respect to the caller's argument and evaluates within exact
Word bounds. A call in that initializer may use its callee's formal argument
when the call input is itself closed.

The captured expression travels with the known PAP through closure parameters.
Application prepends it to the physical callee's parameters, and the cache key
includes the declaration, parameter kinds, closure target, and complete capture
expression. The expression remains in the specialized body. In `captureClosed`,
the two successors that construct `seed` execute on each of the two applications;
the native run takes 30 instructions, including four calls and the final return.
Source identifiers are not hard-coded into this selector.

The finite policy allows depth 32, 64 residual functions, and 1,024 source
instructions per visited block, with 1,024 recursive evaluation levels for each
capture check. Recursive expansion, open main functions, runtime-dependent or
multiple captures, unknown closures, multiple dynamic Nat arguments, branches/joins,
unsupported constructors, ownership modes, and exhausted budgets reject.
Mathematical evaluation checks every intermediate result before conversion to
an exact 64-bit word, including successor overflow. Source validation runs
before this representation pass, so ignored release instructions cannot hide
invalid register or ownership uses.

The original capture-free policy still reports `capturedPap` for `captureClosed`.
The upstream producer then tries the separate static policy. Zero depth,
function, instruction, or capture-evaluation budgets retain the checked baseline.
Erased and non-Nat captures reject, as do missing or unsafe PAP targets and
wrong arities. Misaligned
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
`Output.reclaimsSuccessfulRun` proves that the result of any such run has the
same successful release, zero live nodes, and balanced allocation/free counts.

`Expr.closed_evaluate` proves caller-argument independence of a closed initializer.
The checked `StaticCapture` retains its exact Word evaluation, and
`StaticCapture.evaluates` transports that evaluation to every caller argument.

`IxIR2.Pipeline.Attached.sourcePhysical` supplies the general constructor-valued
source-to-physical bridge. `NatCalls.sourceObjectRefines` composes it with the
closed representation certificate and E2's execution of the actual serialized
ELF object. The theorem retains the source oracle/sharing hypotheses and an
explicit `Execution` certificate for the supplied machine state. That certificate
checks termination, RAX, saved registers, restored stack, safe call/return slots,
and a readable caller return address. `Execution.objectReturns` states the actual
object-byte return value. `sourceObjectReclaims` exposes that return value and
complete physical reclamation in the same source-to-object theorem.

The producer certifies four finite stack/register configurations, including
nonzero memory and high addresses, with 64 writable bytes below the return slot.
Native tests additionally protect the caller frame and all System V saved
registers. These are closed translation-validation and supplied-state execution
claims. Runtime scalar arguments, branches/joins, reusable call contracts, and
finite stack sufficiency have a separate [scalar source contract](source-native-scalar.md);
this C3 endpoint retains its supplied-state certificate. The local x86 model
and system linker/loader obligations remain explicit. The five capture axiom
fences extend the original six C3 fences and retain the ordinary logical basis
and existing indexed-source hash axiom. They introduce no new axiom or
production FFI symbol. Runtime or heap-valued captures and allocating native
bodies remain outside this closed policy.

The physical baseline for `applyClosed` allocates five nodes, frees one before
return, and has three RC operations; complete result release reaches five frees,
seven RC operations, and zero live nodes. `letClosed` has six allocations, one
early free, and three RC operations; release reaches six frees, eight RC
operations, and zero live nodes. `captureClosed` has five allocations, two early
frees, and eight RC operations; release reaches five frees, eleven RC operations,
and zero live nodes. Native results use an unboxed eight-byte word and no heap
allocation, RC operation, or heap release.

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
observations. For the captured fixture it also independently checks the physical
initializer, PAP target and capture register, callee parameter order, two
applications, and exact residual capture expression. Instruction counts and
stack depth are reconstructed from executed expressions.

It compares two fresh complete nine-file artifact sets with the reviewed
five-case matrix and rejects 42 artifact corruptions. These include a changed
capture key, swapped parameters, a wrong closure target or PAP capture register,
and replacing the capture expression with an equal-valued constant. Selector
tests cover distinct captures of the same declaration, the maximum Word,
overflow, open initializers, capture shape, arity, safety, and budgets. The full
ABI and affected coverage neighbors are checked in Lake/Nix.

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
Those retained measurements cover `applyClosed` and `letClosed`; `captureClosed`
has correctness and resource observations here, without new timing claims.
The [benchmark protocol](../benchmarks/protocol.md)
defines measurement and replay; the [follow-up decision](performance/native-reverse-2026-09-09/README.md#follow-up-decision)
keeps runtime arguments, broader recursion and general stack sufficiency at
their N3/F1 gates.
