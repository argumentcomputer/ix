# Checked borrowed calls from source

B1 adds an optional checked borrowed ABI for closed programs with scalar
results. Eighteen accepted Ixon inputs read the same shared constructor twice
through a direct call chain. Every case reduces actual RC operations from 5
to 3, returns the same source result, frees all three allocations, and keeps
the peak at two live heap nodes.

This delivery uses bounded translation validation of the exact closed
execution. It does not establish a reusable simulation of open functions on
arbitrary runtime arguments. The separate [B2 extension](source-borrow-runtime.md)
adds that proof for an open shared tag-reading family, with selection
independent of runtime input or closed replay.

## Source and entry point

[`Borrow.compileValidated`](../Compilatrix/Borrow/Pipeline.lean) first runs
`IxIR2.Pipeline.compileValidated` and retains its complete attachment.
`Borrow.select` applies the same optional pass to an existing attachment.
Invalid source remains a compiler error; failed inference, rewriting, source
execution, target execution, or resource comparison retains the exact checked
baseline program.

[`Borrow.Examples.source`](../Compilatrix/Borrow/Sources.lean) constructs
canonical synthetic Ixon constants, not intermediate IR. One declaration
group contains Nat, a tag recursor, zero to eight forwarding functions, and a
function that calls the reader twice on the same argument. References within
the group become known direct calls. Its dependency graph is acyclic; placing
definitions in a source group does not require recursive SCC inference.

Both constructor branches execute. The reader returns 11 for zero and 22 for
successor; the latter also fetches its unused scalar field. Shared PAP entry
and application remain part of the compiled source path. This is a synthetic
source witness, with no claim of new upstream or Std acceptance.

## Checked inference and rewriting

[`IxIR2.Borrow`](../Compilatrix/IxIR2/Borrow/Rewrite.lean) proposes a borrowed
variant for a function with one owned shared parameter and a shared result.
Dependency iteration tries additions to the current summary set. Every
attempt reconstructs the variants from the exact baseline and checks the
whole program, including affected bodies, edges, direct calls, and wrappers.
Unknown or incompatible uses reject that attempt without discarding earlier
checked summaries.

The rewrite changes parameter capabilities to caller-rooted borrows, replaces
retains of the borrowed root with non-consuming moves, and removes its
baseline releases. Moves preserve result-register numbering. Field views are
tracked separately: a retain that creates an owned result from a projected
field is preserved. The ordinary capability validator checks every proposed
block annotation and lender transfer.

Original entries keep their signatures and PAP eligibility. Each owned
wrapper calls its borrowed variant, keeps the argument alive until that call
returns, releases the argument, and returns the owned result. Known calls
inside borrowed variants target the corresponding variants. A tail borrow
must be rooted in the caller; a local owner cannot survive its ending frame.
Root return, storage, and PAP capture cannot consume a borrowed capability.

The pass rejects take/reset and credit operations in candidate bodies, plus
extern and self-call forms. It therefore respects later ownership
requirements instead of treating every conservative baseline release as
evidence that a parameter must own. General recursive SCCs and mixed or
multi-parameter borrowing remain outside this version.

Defaults admit at most 32 candidates, 16 rounds, and 256 attempts. Each
attempt uses the existing bounded whole-program validator. Source replay and
each target replay have explicit fuel limits; the fixtures use 1,000 source,
control, and heap-work units. All fixture candidates succeed in the first
round, followed by one no-change round: `depth + 3` attempts and summaries.

Borrowed entries receive deterministic labels under
`compilatrix/borrowed-entry/1\0`. A collision with any declaration is rejected.
These remain logical internal labels. The separate
[canonical IxIR₂ snapshot](ixir2-wire.md) root commits to all actual selected
bodies while retaining those labels. `Wire.ofBorrow` exports the actual
selection or fallback with exact program/context and validation proofs.

## Semantic and resource certificates

[`Replay.lean`](../Compilatrix/IxIR2/Borrow/Replay.lean) derives successful
physical executions of the exact baseline and reconstructed program. It
accepts only equal Nat results, strictly fewer executed RC operations,
complete reclamation in both runs, and nonincreasing peak live heap nodes.
Reclamation checks every heap slot is empty as well as zero live nodes and
equal allocation/free counters. These conditions are proved fields of the
returned certificate, not caller-supplied simulation callbacks.

The source attachment additionally executes the original Ixon root and checks
its result against the baseline. Public interfaces are:

- `IxIR2.Borrow.Checked.valid` and `exactRewrite`: whole-program validation
  and the exact reconstruction equation.
- `IxIR2.Borrow.Execution.steps`: the runner equation yields the actual
  finite small-step execution and remaining budget.
- `IxIR2.Borrow.Improved.preservation` and `resources`: equal results,
  complete reclamation, strict RC decrease, and the peak bound.
- `Borrow.Improved.sourcePreservation` and `resources`: original-source
  agreement and those resource laws for the selected compiled program.
- `Borrow.Selection.valid` and `fallbackExact`: every selected artifact is
  checked, and rejection preserves the baseline exactly.

Ten [axiom fences](../Compilatrix/Fence.lean) cover these interfaces. The core
results use `propext` and `Quot.sound`; indexed source statements retain the
existing logical and addressed-source BLAKE3 basis. No new axiom, Lean FFI,
native reflection proof, target runtime, or modeled oracle is introduced.

## Measured tradeoffs and scope

Let `d` be the forwarding depth and `s` be 0 for zero or 1 for successor.
The checked executions and complete artifacts give:

| Observation | Baseline | Borrowed |
| --- | ---: | ---: |
| Result | `11 + 11s` | `11 + 11s` |
| RC operations | 5 | 3 |
| Allocations / frees | 3 / 3 | 3 / 3 |
| Final live nodes | 0 | 0 |
| Peak live heap nodes | 2 | 2 |
| Control transitions | `21 + 2d + 2s` | `24 + 2d + 2s` |
| Heap-work units | `6 + s` | `5 + s` |
| Stored declarations | `d + 6` | `2d + 9` |
| Stored instructions | 13 | `2d + 16` |

The wrappers cost three additional control transitions and increase code
size. Reduced RC is not a native latency claim. Peak policy counts live heap
nodes; it does not bound occupied bytes or stack capacity. A regression where
delaying the final release saves two RC operations but raises peak from one
node to two is explicitly rejected.

The existing scalar x86 selector rejects both artifacts at
`missingConstructorSchema`. Shared native RC and this borrowed ABI are not
implemented by the separate unique-list native endpoint, so this package has
no native measurement. The producer prints source-compilation and borrow-check
wall time separately from deterministic snapshots; representative local runs
over all 18 cases took 25–30 ms and 7–10 ms respectively.

## Reproducibility and rejection gate

```sh
lake build source-borrow check-source-borrow
./.lake/build/bin/check-source-borrow --fixture .lake/build/bin/source-borrow
```

The producer emits the original constant bytes, all retained compiler graphs,
renamings and HPT artifacts, full baseline and selected programs, summaries,
validation work, stage results, and every physical execution prefix. The
independent checker compares all 19 files from two fresh processes, checks
the pinned source roots and constant-byte hashes, reconstructs caller/callee
rewrites, and uses a separate small interpreter to check every frame value,
continuation transition, heap slot, RC operation, and release work item.
Its imports exclude the compiler, optimizer, validator, and evaluator.

Twelve boundary guards cover return/store/capture escape, local tail-lender
death, later reset, peak regression, absent RC benefit, replay fuel,
label collision, duplicate or missing summaries, and candidate limits. A
separate positive guard preserves a projected-field retain. Three source
fallbacks exercise exhausted inference, target replay, and source replay.
Thirteen deliberate artifact corruptions must fail the independent checker,
including altered wrappers, borrowed interfaces, prefix registers/refcounts,
reported resources, fallback programs, and source bytes. The checker, its
helpers, and [reviewed source matrix](../fixtures/source-borrow/expected.json)
are integrity-pinned. The `source-borrow` Nix check runs this gate.

The 2026-09-08 delivery passed the 654-job local build, all twelve compiled
regression gates, and all fourteen Nix checks on x86_64 Linux.
