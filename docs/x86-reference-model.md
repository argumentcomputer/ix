# x86 reference-model readiness

The 2026-09-09 decision is to proceed with local E1 proofs while preparing
the Sail x86 reference route. The candidate model is pinned and its emitted
subset is mapped. Reference execution has not been run, so S0's dynamic
comparison is pending; S1 and S2 are also pending. This decision does not
retire the local ISA specification assumption.

The inspected snapshot is
[`sail-x86-from-acl2` at `0c6c023dccc7c20d8d9dbfc481f01d9bb49d62bf`](https://github.com/rems-project/sail-x86-from-acl2/tree/0c6c023dccc7c20d8d9bb49d62bf).
The downloaded archive's SHA-256 is
`3b4df2a26433915a8b8789cd7f4240dda82835a6bad7b8d118535e2557d0c6f6`.
[`x86-reference-model.json`](x86-reference-model.json) records the exact
archive, inspected entry points and unfinished adapter pins. The metadata
is integrity-pinned by the trust ledger. The archive is not a build input.

## Inspected coverage

| Emitted forms | Snapshot implementation |
| --- | --- |
| MOV registers/immediates, stores, MOV loads at 32/64 bits, MOVZX loads at 8/16 bits, LEA | [`move.sail`](https://github.com/rems-project/sail-x86-from-acl2/blob/0c6c023dccc7c20d8d9dbfc481f01d9bb49d62bf/model/move.sail) |
| Register ALU/CMP and immediate groups 80/81 | [`arith_and_logic.sail`](https://github.com/rems-project/sail-x86-from-acl2/blob/0c6c023dccc7c20d8d9dbfc481f01d9bb49d62bf/model/arith_and_logic.sail) |
| Two-operand IMUL | [`multiply.sail`](https://github.com/rems-project/sail-x86-from-acl2/blob/0c6c023dccc7c20d8d9dbfc481f01d9bb49d62bf/model/multiply.sail) |
| Register PUSH/POP | [`push_and_pop.sail`](https://github.com/rems-project/sail-x86-from-acl2/blob/0c6c023dccc7c20d8d9dbfc481f01d9bb49d62bf/model/push_and_pop.sail) |
| rel32 JMP/tail JMP and near Jcc | [`jump_and_loop.sail`](https://github.com/rems-project/sail-x86-from-acl2/blob/0c6c023dccc7c20d8d9dbfc481f01d9bb49d62bf/model/jump_and_loop.sail), [`conditional.sail`](https://github.com/rems-project/sail-x86-from-acl2/blob/0c6c023dccc7c20d8d9dbfc481f01d9bb49d62bf/model/conditional.sail) |
| Direct and runtime CALL, RET | [`subroutine.sail`](https://github.com/rems-project/sail-x86-from-acl2/blob/0c6c023dccc7c20d8d9dbfc481f01d9bb49d62bf/model/subroutine.sail) |

Frame allocation/free use ordinary SUB/ADD; spills/reloads use ordinary
memory operands. There are no reference pseudo-opcodes to assume. The model
sets IMUL CF/OF from signed-product overflow and leaves SF/ZF undefined,
matching the local model's explicit unknown flags. Mapping an entry point is
source inspection, not a decode or execution equivalence theorem.

## Build readiness and route

The snapshot's [Makefile](https://github.com/rems-project/sail-x86-from-acl2/blob/0c6c023dccc7c20d8d9dbfc481f01d9bb49d62bf/model/Makefile)
provides C-emulator and Isla generation targets, with no Lean generation
recipe. Its [validation instructions](https://github.com/rems-project/sail-x86-from-acl2/blob/0c6c023dccc7c20d8d9dbfc481f01d9bb49d62bf/translator/validation/Readme.md)
were last tested with Sail revision `4f8532ae` and describe a 64-bit
application view (`set64bit=1`, `app_view=1`). The current project environment
has no Sail/OCaml/opam/dune/Z3 installation; no reference generator or emulator
was built or executed during this review.

Sail introduced an experimental Lean backend in 0.19, and a
[`lean-sail` support library](https://github.com/rems-project/lean-sail)
exists. Thus an absent Lean target in this older x86 snapshot does not imply
that Sail lacks Lean support. Compatibility of this snapshot, the current
backend and this project's Lean 4.33.0 has not been established.
[Sail changelog](https://github.com/rems-project/sail/blob/sail2/CHANGELOG.md).

The next reference steps are concrete:

1. Finish S0 by establishing a pinned generator build for this exact snapshot
   and running emitted load/store/branch cases in the 64-bit application
   view, then extending the comparison to every form in the metadata.
   Compare registers, RIP, defined flags, memory effects and faults. Existing
   GNU and native gates are useful independent evidence but do not execute
   this reference model.
2. For S1, pin the Sail compiler and Lean support-library revisions; record
   all generation options and source inputs from `model/Makefile`; generate
   the Lean model and kernel-check it with Lean 4.33.0. Make generation
   reproducible in Nix and audit the generated definitions and axioms.
   Keep any syntax compatibility changes as reviewed patches against the
   pinned source. A hand-written replacement for the reference step is not
   a reference adapter.
3. For S2, define explicit local/reference relations for registers, byte RIP,
   relevant flags, mapped memory and faults. Start with load/store/branch,
   then prove every emitted form and compose the native observation. Account
   for canonical addresses, alignment behavior, undefined flags, stack
   return addresses and external procedure contracts. Only that theorem
   can discharge the ISA ledger entry.

These compatibility and proof obligations remain open. [E2 stream/ELF proofs](x86-stream-objects.md)
use the [local E1 interface](x86-encoded-instructions.md) while
the reference route is established.
