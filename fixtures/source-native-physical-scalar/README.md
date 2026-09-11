These six synthetic Ixon sources compile through validated erasure, addressed
IxIR₁, checked physical IxIR₂, and the general physical scalar CFG selector.
The sources are in `Compilatrix/X86/PhysicalScalarSources.lean`. Runtime
operands are literal Nats; the compiler supplies all intermediate graphs.

`expected.json` pins the complete artifact inventory and roots, selected
function/block counts, text hashes and sizes, finite stack reservations, and
test inventories. The producer creates fresh ELF objects and full compiler
snapshots; the checker compares two complete generations byte for byte.

The families return `a`, a zero/successor tag, `a - 1`, a branch choosing `b`
or `a - 1`, composed predecessor/tag helpers, and composed predecessor/choice
helpers. Subtraction here is truncated Nat subtraction. All 19 boundary pairs
per family run in Ixon, IxIR₀, IxIR₁, logical/physical IxIR₂, typed x86, and the
actual ELF byte interpreter, including maximum Word inputs. Four separate
physical CFG cases exercise joins, parallel swaps, reordered blocks, and a
nullary constant helper across 76 additional inputs.

The C harness independently checks the six mathematical functions on 19
boundary and 64 deterministic random pairs, both on the normal stack and on
a finite stack above a protected page: 996 native calls in total. It checks
saved registers, stack restoration, caller frames, and reservation canaries.
The selector and object proofs are documented in
[`docs/source-native-physical-scalar.md`](../../docs/source-native-physical-scalar.md).
