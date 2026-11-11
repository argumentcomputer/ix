# Standalone executables without a C driver

Written 2026-11-14. **Status: planned.** Milestones X0 to X6 are in the
[roadmap](roadmap.md#standalone-executables). Only the lines that say
*implemented* or *measured* describe code or runs that exist.

## Motivation

The owner decided (2026-11-14): "standalone executables should be a target on
the roadmap, and I think we cannot have a C driver. That feels like a
cop-out. We should be able to self-host that logic."

Today a compiled program runs only inside `runtime_driver.c`
([`fixtures/x86/runtime_driver.c`](../fixtures/x86/runtime_driver.c), 364
lines, about 40 of them inline assembly), linked by the system linker. It:
- parses `--region`, `--stack`, `--type`/`--sig`, `--dump` and `--time`;
- maps the region and a stack with a guard page (`mmap`, `mprotect`);
- for each input line, parses up to five words with `strtoull` (the wrappers,
  not the driver, tag them), stores the stack budget at `region + 16`, calls
  `cx_init` and then the root through an assembly trampoline that switches to
  the mapped stack and checks callee-saved registers with sentinels;
- prints `status value ok` and, with `--type`, a C mirror of `Rt.readback`.

It re-initialises the region for every line and never calls `cx_drop` (the
session protocol with `cx_drop` is `rc-reuse-driver.c`'s, modelled by
[`X86/DriverSession.lean`](../IxCC/X86/DriverSession.lean)). Its parsing is
looser than the model it stands for: `strtoull` accepts `0x10`, `12x` and
`-1`, and a missing argument becomes 0, whereas `X86.Linked` applies a root to
exactly its parameter count.

What it puts in the trusted base: the C compiler that builds it, the C
library and dynamic loader it runs on, the system linker that places the
object and resolves its symbols, and the driver itself, all summarised as the
ledger assumption `x86-phase1-runtime-driver-model`
([trust ledger](trusted-extern-ledger.md)): that the driver and linker realise
the model `X86.Driver`/`X86.Linked`, including that a run the model shows
non-faulting touches only modelled memory. None of that is about the
program; all of it sits between the proved object and a user.

## The core tension

IxCC's theorems are about pure terms. The grounded statement
([end-to-end certification](end-to-end.md)) says that a constant applied to
literals denotes a value in every strong model of the accepted environment.
Lean's `IO` primitives are opaque constants with no value law in IxCK's model,
so a program's `IO` behaviour has no meaning there. Three ways through:

1. **A pure certified program and a self-hosted shell.** The certified unit
   stays a pure function (`Nat`s to a `Nat` today; argument and input bytes to
   output bytes and an exit code with Phase 3; a `step` from state and event to
   state and request for interaction). Everything the C driver does is done by
   code IxCC generates. Grounding is untouched: the shell only feeds literals
   in and renders the result out.
2. **Effects in the semantics.** An event-trace semantics for Src, refined at
   every level against an environment oracle, as CompCert, CakeML and PureCake
   do. IxCC prepared for it: per-level theorems are stated in the traced shape
   of `IxCC.Sem` (D-1), so adding events changes the unfolding lemmas, not the
   per-construct proofs. The program denotes a pure description of its
   interaction, and the theorem says the process's trace is one the
   description allows for the answers the environment gave.
3. **Lean's own `IO`.** Recorded interpretations for a chosen set of `IO`
   opaques (the world as an oracle and a trace; the standard streams as fixed
   records over a few primitives; write, read, exit and the monotonic clock as
   transitions), relative to which `main` denotes a world transformer. It needs
   the machinery of (2), strings and byte arrays, fixed-width integers, P8 (the
   standard streams are records of closures) and the interpretation table of
   [DR5](data-and-roots-design.md#dr5-library-structures-and-opaque-constants).

**Recommendation.** (1) for the first executables, in stages; then (2), with
(3)'s interpretations on top, for ordinary Lean `main`. Both use one platform
interface, so the shell of (1) becomes an interpreter that performs requests
by calling the platform procedures of (2).

## Design

### The executable

IxCC writes the executable itself: no C compiler, no C library, no linker, no
assembler. A static ELF executable holds:
- an ELF header (`ET_EXEC`, or `ET_DYN` for a position-independent load) with
  `e_entry` at the shell's first instruction;
- a read-and-execute `PT_LOAD` segment: the headers, the shell, and the
  certified object's text byte for byte;
- a read-and-write `PT_LOAD` segment with no file bytes, zero-filled by the
  loader, holding the program's stack and its region;
- `PT_GNU_STACK` (not executable) and a `PT_NOTE` carrying today's provenance
  note.

Section headers are optional. What IxCC must add beyond today's object writer
([`X86/ELF.lean`](../IxCC/X86/ELF.lean), which writes a relocatable object with
exactly eight sections and no program headers, checked by
[`X86/ELFValidate.lean`](../IxCC/X86/ELFValidate.lean)) is a sibling writer and
an independent reader and validator in the same style: the exact segment
inventory, page-congruent offsets, the executable segment not writable and the
writable one not executable, disjoint segments, the entry at the shell, and
the bytes at the text offset equal to the certified text and at the shell
offset equal to the certified shell.

**The object needs nothing resolved** (measured): four K1 objects (`fib`,
`ackermann`, `tak`, `gcd`) and the plain-RC `List.reverse` object have no
relocations, no undefined symbols, no RIP-relative or absolute operands and no
indirect branches; their only symbols are the exports. What makes it so: since
the runtime became Lir code (D10), the back end emits no runtime-call
instruction, so the writer's named PC32 relocations to runtime symbols
(`runtimeSymbols`, `relocationBytes` in `X86/ELF.lean`) are never used; and the
object proofs hold for any text base, which is position independence at the
level of the model. The format and its checker still *admit* runtime
relocations, so "no relocations" is a property of today's output, not a
checked invariant; the executable writer requires an empty relocation
inventory.

**Memory: a static layout.** Stack and region live in the zero-filled
segment, with sizes fixed when the executable is written (as CakeML's heap
size and Solo5's manifest are). This needs no system call, keeps the process
compatible with the strictest confinement (below), and makes the driver
contract decidable on constants. The alternative is mapping them at start-up
(three more system calls and their model).

### The shell

At start-up the shell:
1. optionally confines the process (strict seccomp: only `read`, `write`,
   `exit` and `sigreturn` remain allowed);
2. reads `argc` and `argv` from the initial stack, checks the arity and parses
   each argument as a decimal numeral (2^64 or more is `natOverflow`, as
   `X86.Linked.call` says);
3. stores the budget at `region + 16`, sets the stack pointer to the static
   stack's top, and calls `cx_init(region, size, budget)` by a direct call;
4. calls the root by a direct call with the parsed arguments;
5. renders the result in decimal and writes it to standard output, then exits
   0; or writes a fixed message for a resource failure to standard error and
   exits with a fixed code per failure; a usage error exits 2.

**The driver contract becomes a theorem.** `X86.Driver`
([`X86/Driver.lean`](../IxCC/X86/Driver.lean)) records the base, region,
size, budget, stack pointer, return address, initial bytes, flags and other
registers of the object's calls; `Driver.Ok` and `Driver.CanonicalOk` are
arithmetic on them. Under a static layout every one of these is a constant
fixed when the executable is written, so `CanonicalOk` holds by evaluation, as
`Driver.exists_canonicalOk` already shows for other constants. What remains to
prove: a *shell lemma* (the shell, started in the loader's post-state, reaches
each call in exactly the model's state and does not touch the region in
between), and a *permission-monotonicity* lemma for the byte machine (a run
that does not fault under the model's mapping runs the same under any larger
mapping with the same bytes), which replaces the ledger's "touches only
modelled memory". What stays assumed is the initial process state: the
loader maps the two segments as declared and zero-fills the writable one,
`rip` is the entry, and the stack holds `argc` and `argv` as the System V
x86-64 ABI's process initialisation says. One model change is needed: the
model calls `cx_init` and the root with one register file and one return
address (`X86.Linked.call` uses one `Driver` for both); a shell calls from two
sites, so those become per call. The object theorems hold for every register
file and return address, so the change should be mechanical.

**Where the shell's code comes from.**
- *First*: typed x86 written in Lean (an `X86.Program` value), encoded by
  IxCC's own encoder with its certificate, checked by its stream checker and
  proved on the byte machine with the existing stream-trace infrastructure. A
  feasibility experiment outside this tree laid out such an executable by hand
  for K1's `fib`: 2,080 bytes (a 143-instruction shell, the object's text
  unchanged); after `execve` it made only `write` and `exit`, ran under strict
  seccomp and at a second load base, and agreed with the C driver on every
  well-formed input, including heap, stack and `natOverflow` failures.
- *Then*: more of the logic moves into Lean source compiled by IxCC as the
  fragment grows: with a numeric request protocol, parsing and rendering become
  Lean functions in a small library compiled with the program, and the shell
  becomes a generic interpreter; with byte arrays, arguments and output are
  bytes the program handles; with traced events, the start-up logic itself
  (build the argument list, run `main`, report an uncaught error, return the
  exit code) is a Lean function compiled by IxCC.
- *Always at the machine level*: the process entry (a few instructions: pass
  the initial stack pointer, align the stack, call the start-up function) and
  one small procedure per system call. They cannot be Lean source compiled by
  IxCC, because compiled program text never contains the system-call
  instruction (below). They are typed x86 in Lean, proved against a stated
  model of each call. They are machine code, never C.

### The platform interface

One effect signature, in the manner of Solo5's and MirageOS's: version 0 is
the argument block, `write(stream, bytes)` for standard output and error, and
`exit(code)`; then `read(input, max)`, a monotonic clock and a wall clock;
later devices named in a manifest and acquired before confinement. In Lean it
is a request and response type for state machines and an event type with a
trace semantics for the theorems; each operation is a finite, non-looping
state transition, so each can be specified and checked mechanically.

| | Linux process | IxOS |
| --- | --- | --- |
| Entry | the shell at `e_entry`, System V initial stack | the tender or monitor calls the program's entries |
| write, read, exit | system calls | the tender's console, input and termination |
| clock | a system call (not the vDSO, so the confinement filter is exact) | the processor's or hypervisor's clock |
| memory | the static zero-filled segment | a region the monitor assigns, `CanonicalOk` checked at admission |
| confinement | strict seccomp, then a filter listing exactly the signature's calls | Ring-0 admission: no privileged rows, no indirect branches |

*Certified once:* the program text, which contains no platform code and is
identical on every platform, and the Lean-written loop and start-up logic.
*Per platform:* the entry, the platform procedures and their proofs, the
loader or boot assumption, and the platform's model (the system calls or the
tender's interface), each a ledgered specification.

**Two stages of effects.** First, *requests returned as data*: a
state-machine root returns a request (write these bytes, read up to this many,
exit with this code) and its next state, and the shell performs the request and
calls `step` again; this is option (a) of
[DR9](data-and-roots-design.md#dr9-effects-and-io). Later, *calls to platform
procedures* treated as traced events, which is what ordinary Lean `IO` needs:
option (b) of DR9.

**The system-call instruction lives only in platform code.** The Ring-0
admission check ([`Ring0.lean`](../IxCC/Ring0.lean)) refuses every program
whose instruction table contains a privileged or system opcode, `0F 05`
included. The row for it therefore lives in a separate platform table (or
carries a platform-only flag the program checker refuses), so the program's
text stays admissible under the IxOS tender. The no-indirect-calls decision
(D20) holds: the shell reaches `cx_init` and the root by direct calls fixed
when the executable is written; the program never calls the shell while
effects are requests; when effects become platform calls, the program reaches
the platform procedures by direct calls whose displacements are fixed by the
layout.

### Output, and what remains of readback

An executable produces its own output: today the shell renders a `Nat` in
decimal, which is the whole of readback at that type; with byte arrays the
program returns its output bytes; with requests it writes them. General
`Rt.readback` leaves the end-user path. It remains for *function claims*
(a compile claim about a root, read back at its type by a verifier or a host)
and for the test harness, on the host side in Lean.

### The theorems, by stage

- **`Nat` executables.** Assume the byte machine with the system-call row is
  the processor; the loader's post-state for the executable; and the
  behaviour of `write` and `exit`. Then a run on `k` arguments either has `k`
  equal to the root's arity and every argument a decimal numeral, writes the
  decimal of `v` and exits 0 where the linked object returns `v`; or writes a
  failure message and exits with the failure's code, where the object reports
  that resource failure; or exits 2. It makes no other system call and does
  not fault unless the source goes wrong. With today's object theorem, `v` is
  the view of SrcEval's result; with the [spine](end-to-end.md), it is what the
  constant applied to the arguments denotes in every strong model.
- **Batch byte programs.** Under the model of `read` as well: if the process
  exits with code `c` after writing bytes `o`, then `main` applied to the
  argument bytes and the bytes the reads returned evaluates to `(o, c)`, or the
  source goes wrong, or a resource failure is reported.
- **State machines.** Every finite trace of platform events the process
  performs, with the environment's answers, is one obtained by iterating the
  source `step` on those answers, unless `step` goes wrong on the way, and no
  event outside the signature occurs. Per call this is today's theorem; across
  calls it is the session induction DR9 plans.
- **Lean `IO`, relative to an interpretation.** For every trace and exit code
  of the process, in every strong model in which the interpreted `IO` opaques
  take their recorded values, `main` applied to the arguments denotes a world
  transformer that produces that trace and code from the environment's
  answers. Relative to the interpretation, as recorded interpretations are
  ([DR5](data-and-roots-design.md#dr5-library-structures-and-opaque-constants)).

**Composition with the end-to-end statement.** The x86 statement's "the
linked object returns `w`" becomes "the executable exits after writing `w`",
and the trusted base changes from the instruction-set, loader and driver
models to the instruction-set model with the system-call row, the loader's
post-state for a static executable, and the platform's system-call model.

**What an executable claim binds.** The object's compile claim, plus the
executable's hash, the platform, the shell's version (the hash of its
certified bytes), the entry convention (for numerals: decimal arguments and a
decimal result; later the root's ABI descriptor,
[DR7](data-and-roots-design.md#dr7-what-the-compile-claim-binds)) and the
layout (the region and stack sizes, which affect only resource failures). A
verifier rechecks the object's claim, rebuilds the executable
deterministically from the object and the certified shell, and compares
hashes.

## Trust

| Component | Today | After X0 (shell ledgered) | After X0-P (shell proved) | Later (requests, platform calls) |
| --- | --- | --- | --- | --- |
| C compiler | trusted: builds the driver and links | gone | gone | gone |
| C library and dynamic loader | trusted: the driver runs on them | gone | gone | gone |
| System linker | trusted: places the object, resolves symbols | gone: IxCC writes the file | gone | gone |
| `runtime_driver.c` | modelled by `x86-phase1-runtime-driver-model` | replaced by a typed-x86 shell, ledgered | proved: the driver contract is a lemma from the loader's post-state | a generic request interpreter; then only the entry and the platform procedures |
| Readback in C | what a user sees | gone: the shell renders the `Nat` | proved | gone: the program writes its own bytes |
| System calls after start | many kinds (the C driver's dynamic loading and set-up) | `write`, `exit`, enforced by strict seccomp | same | the signature's calls, enforced by a filter |
| ISA model | as today | plus the system-call row | same | plus calls to platform procedures |
| Loading | a dynamic executable with an interpreter | a static executable, two loadable segments, no relocations | same | same |

## Prior art

- **Unikernels and minimal platform interfaces.** MirageOS (an application
  written against device signatures, with the platform chosen at build time)
  and Solo5 (about a dozen host calls, a start-of-day memory record, and a
  Linux-process tender that sets up its devices and then confines itself with a
  seccomp filter). IxCC takes the platform as a *signature*, the small
  start-of-day record, and "set up, then confine". Williams, Koller, Lucina and
  Prakash, "Unikernels as Processes" (SoCC 2018): a seccomp-confined process
  is an isolation boundary as narrow as a virtual machine's, which supports
  running the same program as a confined Linux process. Unikraft and Nanos show
  one program over several platform layers is ordinary; Nanos's direction (a
  wide Linux system-call interface) is the one to avoid.
- **A functional language on bare metal.** House (a Haskell system with a
  small hardware monad and a pure model of it) and HaLVM (Haskell on Xen):
  the effect interface should be that small and have a pure model; IxCC has
  no runtime in C, so its platform layer can be smaller still.
- **Software-isolated processes.** Hunt and Larus, "Singularity: Rethinking
  the Software Stack" (2007): isolation from a checked compiler rather than
  address spaces, the model for IxCC's Ring-0 admission and the IxOS tender.
  Yang and Hawblitzel, "Safe to the Last Instruction" (Verve, PLDI 2010): a
  small verified machine-level layer under checked compiled code, with the
  assembler, linker and boot loader still trusted; IxCC emits that layer's
  bytes itself, so they leave the trusted base.
- **Verified compilers and the operating system.** CakeML: the compiler
  theorem holds for every machine state in which the code is *installed*,
  with I/O through an oracle, and the start-up code and I/O stubs in C; IxCC
  takes the theorem's shape and the oracle, and does the installation in
  proved IxCC-generated code instead of C. CompCert (Monniaux and Boldo, "The
  Trusted Computing Base of the CompCert Verified Compiler"): traces of
  external calls, with the assembler, linker, C library and start-up code
  outside the proof; CompCertELF (Wang et al., OOPSLA 2020) closes part of that
  gap. IxCC already writes and checks its own objects, and an executable
  writer closes the linker and loader gap. Mullen et al., "Œuf" (CPP 2018): a
  verified pure core called by an unverified C shim, which is IxCC's present
  position; IxCC generates and proves the shim. CertiCoq: a C runtime proved
  with VST; IxCC keeps the platform layer free of C as its runtime is.
  Kanabar et al., "PureCake" (PLDI 2023): interaction trees for effects in a
  pure language, reconciled with an oracle at the machine level, the domain
  for Lean `IO` in option (2).
- **End to end without an operating system.** Erbsen et al.,
  "Integration Verification across Software and Hardware for a Simple Embedded
  System" (PLDI 2021): application, drivers, compiler and processor as one
  proof, with I/O as a trace predicate over events; IxCC states an
  executable's behaviour as a trace over platform events, with no operating
  system in the statement. Hyperkernel, seL4 with CakeML or Pancake
  components, and CertiKOS: design the platform interface so that each
  operation is a finite transition that can be checked automatically.
  Hawblitzel et al., "IronFleet" (SOSP 2015): a host loop whose steps perform
  I/O against a stated specification, the shape of the state-machine stage.
- **Start-up code in the language.** Zig defines the process entry as a
  few-instruction naked function and does the rest in Zig; Rust without the
  standard library does the same with raw system calls. That is the end state
  here: a few instructions of entry, and everything else in Lean.

## Milestones

Sizes are estimates, with their basis.

| Id | Content | Depends on | Exit test | Size [estimate] |
| --- | --- | --- | --- | --- |
| X0 | `ixcc compile --exe` for roots of `Nat` parameters and a `Nat` result: the executable writer and its independent checker; the shell as typed x86 with a platform-only system-call row; static layout with `CanonicalOk` by evaluation; per-call return address and registers in `X86.Driver`; a ledger entry for the loader's post-state, `write`, `exit` and the shell | — | every K1 fixture and `phase1-scalar` root as an executable matches its expected output, Lean's interpreter and the C driver; strict seccomp on; only `write` and `exit` after start; byte-identical executables on two machines; the checker rejects mutated headers and truncations | 2–3.5k lines, 3–6 weeks (today's object path is about 2.2k lines across `ELF*.lean`; the shell is about 150 instructions of Lean data) |
| X0-P | The shell proved: the shell lemma, parsing and rendering, the system-call row's model, permission monotonicity; the `Nat` executable theorem fenced | X0 | the theorem fenced on the standard axioms; the driver-model assumption retired for executables | 3–6k lines, 2–4 months (the `cx_init` proof is 0.5k lines and the stream-trace infrastructure exists) |
| X1 | XB-1 and IxOS-0, redefined: IxCC-written test executables speak today's line protocol (and the session protocol with `cx_drop` for the RC gates); readback on the host side in Lean | X0 | the native suites (`tests-rt`, `tests-pipeline`, `tests-corpus`, `tests-own`, the back end's runtime cases, the RC native modes) pass with `runtime_driver.c` off the execution path and no C compiler in their inputs | 1–2k lines, 2–4 weeks after X0 |
| X2 | Numeric state machines: the generic request shell, parsing and rendering in a small Lean library compiled with the program, the session theorem on `Nat` states | X0 (X0-P for the proof) | `fib` as an executable whose parsing and rendering are Lean; a 1,000-call session against Lean's interpreter; the session theorem fenced | 2–4k lines (DR9 (a) is 3–6k with heap states) |
| X3 | Batch byte executables: arguments and input bytes in, output bytes and an exit code out; an exported byte-array allocation entry; the model of `read` | Phase 3 (DR2, DR3, DR6) | programs in the manner of `wc` and `sha256sum` byte-identical to Lean-compiled executables over a corpus of inputs | 2–4k lines beyond the DR items |
| X4 | Interactive executables: state-machine roots with heap states; platform interface version 1 (read, write, exit, clock); a seccomp filter of exactly the interface | DR1, DR6, DR9 (a) | an echo or counter-map program; a 1,000-call session; the state-machine theorem fenced | DR9 (a)'s 3–6k plus 1–2k |
| X5 | Lean `main : IO` over a recorded subset: traced events through the pipeline, platform calls as direct calls to platform procedures, the interpretation table for `IO`, the start-up logic in Lean | X4, DR2–DR5, P8, the reading of interpreted opaques (DC-2) | the benchmark fixtures' `main` functions compile unchanged and print what Lean's executables print | 10–25k lines, a weak basis (8–20k for traced events through about ten levels, plus the table) |
| X6 | The platform interface implemented by the IxOS tender (part of IxOS-2): the same program text as a Linux process and as a SIP | X4, IxOS-1 | one program, two platforms, the same outputs | with IxOS-2 |

## The C driver until it is deleted

It stays as it is, pinned in the ledger, until X1. During X1 one gate runs both
and compares them line by line for one cycle. Then `runtime_driver.c`, its pin
and the C link paths of the native suites and of the Nix checks are removed.
`rc-runtime-driver.c` and `rc-reuse-driver.c`, which reuse its trampoline and
decoder, move to the test shell with it. The other C files in
[`fixtures/x86`](../fixtures/x86) are test harnesses (`backend_driver.c`,
`exports_harness.c`, `native_harness.c`, `unwind_harness.c`), ported as
convenient; `hw_diff_harness.c` tests the processor against the instruction
table, not compiled programs, and can stay.

## Decided questions

These were put to the owner as DO-28 to DO-36 in the
[roadmap](roadmap.md#open-decisions) and decided on 2026-11-14, each as its
default:
1. Whether "self-host that logic" is met by a pure certified program plus a
   small proved machine-level layer that IxCC generates from Lean, never C,
   with the system-call residue never compiled from Lean source.
2. A static layout, or mapping memory at start-up.
3. Requests as data first, platform calls later, over one interface.
4. The system-call instruction only in platform code.
5. Self-confinement with seccomp by default.
6. What an executable claim binds.
7. The redefinition of XB-1 and IxOS-0.
8. Whether numeric state machines (X2) come before Phase 3.
9. Lean `IO` through platform calls rather than a transformation of `main`
   into a state machine.

Also open, for the design: whether the executable writer, its reader and its
validator share code with today's object writer or stay siblings; and how
much of the stream-trace infrastructure applies to a shell that is not
compiler output.
