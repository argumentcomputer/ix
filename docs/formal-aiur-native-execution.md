# Native execution for formal Aiur

Formal Aiur executes programs with a bytecode interpreter
(`crates/aiur/src/execute.rs`). A generator (`aiur-codegen`) also emits a
native Rust executor from a checked program. The generated executor produces the
same execution record as the interpreter, so either can feed proving. This
document describes the design, the conditions it meets, how it is built and
selected, and how it was validated and measured.

## Why a generator for formal bytecode

A generated executor is specific to one program and one instruction set.
Formal programs have no built-in u8/u32 operations: byte arithmetic is a call
into fixed byte tables (`UInt8::pair_xors`, …) and word hints. Population
plans read formal's `Execution`: a `QueryMap` per callable, typed `Memory`
and bound hints. The generator therefore takes formal's checked program as
input and emits code that writes that record through `aiur`'s own runtime.

## Properties of formal bytecode that make generation tractable

Measured on an IxVM export (`ixvm-711f6dd9…`, before role binding): 828
functions and 52,515 instructions, using 13 of the 14 opcodes. None of its
11,454 branches and jumps goes backwards. That is an invariant, not an
observation: the checker rejects backward control flow. Recursion happens
only through calls, so every function body is a forward DAG.

Forward-only does not mean SSA. 541 of those 828 functions write some
register more than once: match compilation (`Aiur/Aiur/Execution/Compile.lean`)
copies each arm's result into shared registers, and checked bytecode allows
overwrites and simultaneous copies in general. Generated code therefore keeps
mutable registers with explicit branch-merge assignments, preserving
simultaneous-copy semantics, and reconstructs regions with joins rather than
duplicating successor blocks.

## Design

### Generate from the normalized execution representation

`Program::check_with` (`crates/aiur/src/bytecode.rs`) produces the
representation the interpreter runs:

- dead arithmetic removed (`dead_code::eliminate`);
- immutable registers aliased and literals hoisted into per-function initial
  registers (`link_registers`);
- skippable instructions (hoisted literals, empty guards and branches, no-op
  copies and assertions, jumps) collapsed into dispatch entries
  (`execution_steps`, `crates/aiur/src/execute/dispatch.rs`);
- copy/jump suffixes collapsed into return plans (`return_plans`).

The generator consumes that representation. In `Blake3::compress`, for
example, all 2,162 guards are empty and its 32 assertions have
`runtime_check: false`, so the raw 3,853 instructions overstate its work.
Original PCs are kept, because hint sites and error locations are keyed by
them, and the dispatch entries' logical instruction counts are kept, because
`Execution::instructions` must match the interpreter.

Memory-type indices are not stable: `memory_types` is built from a
`HashMap`, so its order can differ between processes. Generated code refers
to memory operations by function and PC; the runtime resolves the type when
the kernel is bound.

### A shared runtime interface

Query tables, memory interning, hint sites and the register handlers are
private to `aiur`. Generated code does not reimplement them: `aiur` exposes a
narrow runtime (`aiur::native::Runtime`, feature `native`), and generated
code supplies only function bodies. The runtime owns:

- **Calls:** cache lookup, rejection of a pending (in-progress) query, row
  insertion before the body runs, output validation and completion
  (`Runtime::begin`, `Runtime::finish`). A cache hit increments that query's
  multiplicity only; it never replays the body's table, memory or hint
  effects.
- **Callables:** fixed-table (map) calls and hint evaluation, with the same
  providers and validation as the interpreter.
- **Memory:** typed store (interning, multiplicity) and load.
- **Accounting:** the record's storage charges and budget cancellation.

This is a function-dispatch contract, separate from the `Map` overrides
(which replace one table call with a closure).

### Packaging

The generator is the library `aiur-codegen`: `native_executor` turns a
checked program into Rust source for a type implementing
`aiur::native::Kernel`, from the program's bytecode and its normalized plan
(derived by `aiur`'s own checker). `lake build ix` writes the executors of
IxVM's claim verifier (`Ixvm`), the recursive verifier (`Verifier`) and
aggregation (`Aggregation`) to `.lake/build/formal-generated/native`, and
`crates/formal-generated` compiles them with `include!` under its
`executors` feature; without it the crate is empty, so `--workspace` builds
need no generated sources ([code generation](formal-aiur-codegen.md)).
`crates/ixvm-native` and `crates/stark-verifier-native` compare the linked
executors with the interpreter on real invocations. The generator itself is
tested by the coverage fixture of `crates/aiur-codegen-tests`.

Each expansion carries a fingerprint covering the program, its normalized
plan, the field and the runtime ABI version (`aiur::native::ABI_VERSION`).
Binding a kernel to a checked program (`PreparedHints::bind_native`)
compares fingerprints and rejects a mismatch before execution, so a kernel
only ever runs the program it was generated from.

## Correctness conditions

### Trust

Generated execution stays outside proof verification: the trusted artifact,
constraints and verification path are unchanged, and a wrong record makes
proving fail rather than producing an accepted proof. That is weaker than
unconditional source-level soundness. The memo soundness theorem
(`Aiur/Aiur/MemoSoundness.lean`) assumes the memo graph is acyclic, and
native execution keeps the existing Rust/backend trust boundary.

Execution is also used without proving: the `ixvm` host's check mode
(`crates/ixvm/src/proof.rs`) accepts a claim after execution alone. A
generator bug could therefore produce a wrong check result. Pending-query
rejection and every failure path (guards, assertions with runtime checks,
`Fail`, division by zero, dangling pointers, hint and output validation)
behave as in the interpreter. Proof parity on successful fixtures is
necessary but not sufficient, which is why the validation below also
compares failures.

### Record parity

The native executor produces the same logical record as the interpreter:

- query rows in the same order per table, with the same inputs, outputs and
  multiplicities (`QueryMap::eq` deliberately ignores row order, so it does
  not establish identical record layout or proof bytes);
- the same memory entries, addresses and multiplicities, in order;
- the same fixed-table counts, output and instruction count;
- the same failure, at the same function and PC, with the same message.

`aiur::native::record_diff` checks all of these.

### Map overrides

Generated code computes a fixed-table call's outputs from the table itself
when the table has a closed form, while the interpreter takes them from a
bound override. Binding an override checks only its row indices, because the
tables certify its answers in the proof. Binding a native kernel therefore
also requires every bound override to return each table row's own index and
output; otherwise binding fails and the interpreter runs the job.

Binding costs about 3 ms for IxVM's byte-table overrides, paid per prepared
invocation, plus about 17 ms the first time for the program's fingerprint,
which is then kept with the checked program. Small IxVM claims save only
8–15 ms of execution, so binding cost matters at that size.

### Allocation accounting

Record storage charges (query rows, memory entries, table counts) reuse the
interpreter's accounting. Native stack frames and locals cost differently
from the interpreter's heap frames and reusable register vectors, so they
are not charged as fictitious interpreter allocations. The record reports
the native stack touched (`Execution::native_stack_bytes`), but that figure
is not charged to the record reservation. Budget cancellation is retained.

## Build and executor selection

The formal prover (`crates/ix-prover`) runs inside `ix` as part of the Rust
static library. Its feature `native` enables all three executors together;
`ix-ffi`'s `native-executors` feature turns it on, which `lake build ix`
selects for `ix` after generating the executors.

`lake build ix` generates the executors (`formal_generated` in
`lakefile.lean`) from the certified IxVM, recursive verifier and aggregation
packages in the checkout's artifact cache, compiling missing ones in process
first; the `IX_*_ARTIFACT` variables supply trusted packages instead.
`ix prepare` (`Ix/Cli/PrepareCmd.lean`) fills the cache ahead of time.
When a selected program differs from the one its linked executor was
generated from, `ix` reports it and runs the interpreter, or fails under
`IX_FORMAL_NATIVE=1`.

Executor selection (`crates/ix-prover/src/executor.rs`) happens once per
loaded artifact. With `native`, a program runs on the kernel whose
fingerprint matches its own (`native-ixvm`, `native-verifier` or
`native-aggregation`), or on the interpreter if none matches. For a
program whose trace has depth circuits (`CheckedProgram::track_depth`), the
runtime records each query's call height as the interpreter does: it keeps
a stack of the pending queries' SCCs and heights, raised by finished and
cached callees in the same SCC, so generated code is the same with or
without depth circuits.
`IX_PROVER_EXECUTOR=interpreter` forces the interpreter. A job whose map
overrides disagree with their tables fails to bind its kernel and runs on
the interpreter. Single-claim reports (`crates/ix-prover/src/tools.rs`) name
the executor that ran (`executor`), and `Ix.FormalProver.executors` lists the
executors linked into the build; `ix prepare` prints them.

Generated code keeps the interpreter's register numbering in a local array
and emits each function as a dispatch loop over basic blocks. Runtime
operations return a one-word `Failed` and keep the error in the runtime, and
everything except the instruction counter is out of line. Native executions
run on one thread with a 4 GiB reserved stack; `stacker` grows it only
beyond that (`aiur::native::grow`).

Known gaps:

- Function profiling stays on the interpreter.
- Native stack use is reported but not charged to the record reservation.
  Under a tight `RecordReservation` the interpreter can therefore fail with a
  storage error, from charging its frame stack and register vectors, where
  native execution succeeds, and a successful native run leaves less charged
  on a shared pool.
- Failures native execution has that the interpreter does not: starting its
  large-stack thread can fail, and recursion beyond that stack grows it with
  `stacker`, which aborts rather than returning an error if it cannot
  allocate. An instruction-counter overflow (2^64 instructions) is reported
  as `<native>` at instruction 0 rather than at the current function.

## Validation

These results were recorded on `formal-aiur-perf` between `9da877bce` and
`1e8cc6bd7` (2026-11-03), before role binding changed IxVM. Every comparison
requires identical records, as defined above, or identical failures.

- **Coverage fixture** (`crates/aiur-codegen-tests/tests/coverage.rs`): memoized and
  mutual recursion, a branch join with a simultaneous swap, typed ROM, a
  fixed table with and without a fixed-arity override, data hints, constant
  and dynamic division, and every failure path (guard, checked assertion,
  `Fail`, division by zero, pending query, dangling pointer, out-of-domain
  table argument). Runs over a prime field and Goldilocks, and checks that a
  kernel does not bind to a different program. A deliberately wrong copy
  emission (sequential instead of simultaneous) makes it fail.
- **Recursive verifier** (224 functions): `stark-verifier fixture`'s proof
  and two larger synthetic proofs (`stark-verifier-native fixture`), 32,635
  to 582,772 queries.
- **Proofs**: `stark-verifier-native prove`, with the verifier exported with
  its circuits (`stark-export export-trace`), proves the interpreter's and
  the native record of each verifier input above under one plan; the proofs
  are byte-identical and verify. `ixvm-native prove` does the same for IxVM
  with the exported IxVM package: the six accepted claims below give
  byte-identical, verified proofs (6.2–6.5 MB).
- **IxVM** (828 functions, 14,521 dispatch entries): seven claims over the
  `Init` environment, run with `ixvm-native compare` on the host inputs.
  `Nat.add_comm`, `List.reverse_append`, `Nat.add_assoc`,
  `List.length_append`, `Nat.lt_irrefl` and `Option.map_id` are accepted
  with identical records. `Nat.gcd_comm` is rejected by both executors at
  `KernelSubst::ctx_next_cut`, instruction 1 ("let pattern mismatch"), with
  the same error.

## Measurements

One RTX PRO 6000 host (32 threads), 2026-11-02/03, release builds with
`-Ctarget-cpu=native`, median of nine runs, measured on `formal-aiur-perf`
at `1e8cc6bd7`. Each verifier comparison started only after 15 seconds with the CPU at least
90% idle; the IxVM comparisons ran on an otherwise idle machine. Times are
execution only, from a fresh record.

| Workload | Queries | Table calls | Interpreter | Native | Speedup |
|---|---:|---:|---:|---:|---:|
| Verifier, 2^12 rows × 17 columns, 64 queries | 381,832 | 5.1M | 0.149 s | 0.077 s | 1.94× |
| Verifier, 2^16 rows × 65 columns, 100 queries | 582,772 | 14.8M | 0.428–0.437 s | 0.230 s | 1.86–1.90× |
| IxVM `Nat.add_comm` | 216,867 | — | 0.029 s | 0.020 s | 1.44× |
| IxVM `List.reverse_append` | 310,503 | — | 0.048 s | 0.029 s | 1.63× |
| IxVM `Nat.gcd_comm` (rejected) | — | — | 0.604 s | 0.420 s | 1.44× |
| IxVM `Nat.add_assoc` | 160,393 | — | 0.021 s | 0.015 s | 1.44× |
| IxVM `List.length_append` | 327,107 | — | 0.050 s | 0.032 s | 1.59× |
| IxVM `Nat.lt_irrefl` | 389,673 | — | 0.061 s | 0.045 s | 1.35× |
| IxVM `Option.map_id` | 120,328 | — | 0.015 s | 0.012 s | 1.32× |

Before table calls were computed in closed form (below), the same builds
measured 1.24–1.25× on the verifier and 1.28–1.40× on IxVM.

### Where the time goes

A callgrind run of the 2^12-row verifier input, on an intermediate build
(x86-64-v3) that read table outputs directly, shows native execution
retiring 599M instructions against the interpreter's 1,383M, 2.3× fewer,
with fewer L1 data misses (14.0M against 25.6M) and the same last-level
write misses (0.83M against 0.85M, mostly fresh record storage). Wall time
improved far less than instruction count because:

- **Table calls dominate.** The larger verifier input makes 14.8M
  fixed-table calls against 384K function calls. Through the bound map, each
  call costs an indirect call into the registered handler plus a random
  counter increment in a 64K-row table, which generated code alone does not
  remove.
- **Generated code misses the instruction cache.** 99.4% of the run's 36M
  L1 instruction-cache misses were in generated code, a third of them in
  `Blake3::compress`. Its 3,853 instructions compiled to 96 KB of
  straight-line code, three times the L1 instruction cache, while the
  interpreter's whole dispatch loop is 20 KB. Compact error paths and
  out-of-line runtime calls brought `compress` to 40 KB (64 KB with
  closed-form table calls inline).

Every map in the recursive verifier and in IxVM is a byte table whose input
table is a dense enumeration and whose outputs are simple expressions of the
arguments (`xor`, `add` with carry, `sub` with borrow, `mul` low and high,
bit decomposition, two xor splits). The generator verifies such forms against
every table row and emits the call as arithmetic plus one counter increment
(`Runtime::count_map`, inline). That took the verifier from 1.25× to
1.86–1.94× and IxVM from 1.28–1.40× to 1.44–1.63×; `compress` grew to 87 KB,
but the removed calls outweigh its instruction-cache cost.

IxVM gains less. In a callgrind run of `List.reverse_append`, native
execution retires 195M instructions against the interpreter's 397M, and 73M
of the 195M are in `Runtime::begin`: memoized call lookup and row insertion,
the same work as the interpreter's `request`. IxVM makes far more function
calls per unit of work than the verifier, and generated code does not change
their cost.

The same profile shows where host time went for one IxVM claim: decoding the
14.6 MB JSON invocation cost 932M instructions and preparing its hints and
streams another 325M, three times the interpreter's whole execution. For
small claims, the input transport, not the executor, set the host's time.

Approaches that measured worse and were removed:

- Running fixed-arity handlers on the generated register array: it escapes,
  so registers can no longer stay in machine registers (1.07× instead of
  1.17× at that point).
- Computing table rows from dense input tables but reading outputs from the
  table: it adds a random table read per call, and an out-of-line version
  ran at 0.36× with `-Ctarget-cpu=native` but 0.88× with x86-64-v3, a
  CPU-feature-specific effect that was not explained.
- A scratch frame per table call for the fixed-arity handlers: 1.05–1.08×,
  within what code layout alone appears to move these numbers.
- `Runtime::begin` and `finish` generic over a constant arity, so hashing,
  key comparison and row copies unroll instead of looping and calling
  `memcpy`. `begin` retires about 254 instructions per call on IxVM
  (287K calls of 3.2 argument words for `List.reverse_append`, most of them
  new rows) with only about 4 data-cache misses per call, so fewer
  instructions looked promising; native times moved between −8% and +10%
  across seven IxVM claims and two verifier inputs, inside layout noise.

Results moved by up to about 15% between builds that changed only code
layout, so differences smaller than that are not meaningful here.

### Next steps for speed

- Profile with hardware counters on a host that allows `perf`, to separate
  instruction-cache, branch and memory stalls.
- Shrink straight-line bodies further, for example by emitting repeated
  table-call sequences as loops over operand tables.
- Give closed-form calls a direct pointer to each map's counters; the
  inline increment still walks from the runtime through the query table and
  map record on every call.
- Cheaper memoized calls for IxVM: `Runtime::begin` hashes and probes the
  query table on every call, as the interpreter does. Unrolling it for a
  constant arity did not help (see above), so the remaining cost is likely
  stalls that callgrind does not model; hardware counters should come first.

## Generated CUDA trace population

`crates/aiur-tracegen` applies the same approach to trace population: it
emits a straight-line CUDA row writer for each eligible function circuit of
a checked program's trace, and `crates/formal-generated` compiles the IxVM
writers that `lake build ix` generates in a CUDA build. Like the native executor generator, it replaces a fixed-table
call with arithmetic only when a closed form is verified against every table
row, and a bundle binds only to the program whose population fingerprint it
was generated from. The two take different inputs: execution creates
records, while population reads records and writes circuit columns from the
compiled population plans (`crates/aiur/src/trace/plan.rs`).
[formal-aiur-streaming-traces.md](formal-aiur-streaming-traces.md) describes
where generated population fits in incremental trace generation.
