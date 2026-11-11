# Standalone executables without a C driver

Written 2026-11-14. **Status:** X0 implemented (`ixcc compile --exe`, see
[X0 as implemented](#x0-as-implemented)); X1 implemented (the native suites run
their objects as test executables IxCC writes, with no C, see [X1 as
implemented](#x1-as-implemented)); X0-P and X2 to X6 planned. Milestones X0 to
X6 are in the [roadmap](roadmap.md#standalone-executables). Only the lines that
say *implemented* or *measured* describe code or runs that exist.

## Motivation

The owner decided (2026-11-14): "standalone executables should be a target on
the roadmap, and I think we cannot have a C driver. That feels like a
cop-out. We should be able to self-host that logic."

Until X1 a compiled program ran only inside a C runtime driver (364 lines,
about 40 of them inline assembly), linked by the system linker; X1 removed it
([below](#the-c-drivers-removed)). It:
- parsed `--region`, `--stack`, `--type`/`--sig`, `--dump` and `--time`;
- mapped the region and a stack with a guard page (`mmap`, `mprotect`);
- for each input line, parsed up to five words with `strtoull` (the wrappers,
  not the driver, tag them), stored the stack budget at `region + 16`, called
  `cx_init` and then the root through an assembly trampoline that switched to
  the mapped stack and checked callee-saved registers with sentinels;
- printed `status value ok` and, with `--type`, a C mirror of `Rt.readback`.

It re-initialised the region for every line and never called `cx_drop` (the
session protocol with `cx_drop` was a second C harness's, modelled by
[`X86/DriverSession.lean`](../IxCC/X86/DriverSession.lean)). Its parsing was
looser than the model it stood for: `strtoull` accepts `0x10`, `12x` and
`-1`, and a missing argument became 0, whereas `X86.Linked` applies a root to
exactly its parameter count.

What it put in the trusted base: the C compiler that built it, the C
library and dynamic loader it ran on, the system linker that placed the
object and resolved its symbols, and the driver itself, all summarised as the
ledger assumption `x86-phase1-runtime-driver-model`
([trust ledger](trusted-extern-ledger.md)): that the driver and linker
realised the model `X86.Driver`/`X86.Linked`, including that a run the model
shows non-faulting touches only modelled memory. None of that is about the
program; all of it sat between the proved object and a user.

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
1. confines the process: no new privileges, then a seccomp filter that
   allows only `write` to standard output and error and `exit` (implemented as
   a filter, not strict mode: strict mode cannot be entered under an existing
   filter, such as a build sandbox's, and it would also allow `read`);
2. reads `argc` and `argv` from the initial stack, checks the arity and parses
   each argument as a decimal numeral (2^64 or more is `natOverflow`, as
   `X86.Linked.call` says);
3. stores the budget at `region + 16`, sets the stack pointer to the static
   stack's top, and calls `cx_init(region, size, budget)` by a direct call;
4. calls the root by a direct call with the parsed arguments;
5. renders the result in decimal and writes it to standard output, then exits
   0; or writes a fixed message for a resource failure to standard error and
   exits with a fixed code per failure (`64 + status`); a wrong argument count
   exits 2 and an argument that is not a decimal numeral 3.

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
- *First*: typed x86 written in Lean, encoded by IxCC's own encoder and,
  later, proved on the byte machine. As implemented it is not an `X86.Program`
  (which cannot hold a system call) but a program of the shell's own
  instruction type, whose operations are the typed instructions plus the
  system call and direct calls of the object's exports; each typed
  instruction is checked with the table's validity test and encoded by the
  compiler's encoder, but the stream checker does not run on it. A
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
included. As implemented, the system call is not a row of any table: it is a
constructor of the shell's own instruction type with its own two-byte
encoding ([`X86/Exe/Shell.lean`](../IxCC/X86/Exe/Shell.lean)), so the
program table, its laws and its hardware-differential gate are unchanged and
the program's text stays admissible under the IxOS tender. The no-indirect-calls decision
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

- **`Nat` executables.** Assume the byte machine with the system call is the
  processor; the loader's post-state for the executable; and the behaviour of
  `prctl`, `seccomp`, `write` and `exit`. Then a run on `k` arguments either
  has `k` equal to the root's arity and every argument a decimal numeral,
  writes the decimal of `v` and exits 0 where the linked object returns `v`;
  or writes a failure message and exits with the failure's code, where the
  object reports that resource failure; or exits 2 or 3 (a wrong count, a
  non-numeral), or 75 if the confinement is refused. It makes no system call
  but those four and does not fault unless the source goes wrong. With today's object theorem, `v` is
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

| Component | Before X0 | After X0 (shell ledgered) | After X0-P (shell proved) | Later (requests, platform calls) |
| --- | --- | --- | --- | --- |
| C compiler | trusted: builds the driver and links | gone | gone | gone |
| C library and dynamic loader | trusted: the driver runs on them | gone | gone | gone |
| System linker | trusted: places the object, resolves symbols | gone: IxCC writes the file | gone | gone |
| The C runtime driver | modelled by `x86-phase1-runtime-driver-model` | replaced by a typed-x86 shell, ledgered | proved: the driver contract is a lemma from the loader's post-state | a generic request interpreter; then only the entry and the platform procedures |
| Readback in C | what a user sees | gone: the shell renders the `Nat` | proved | gone: the program writes its own bytes |
| System calls after start | many kinds (the C driver's dynamic loading and set-up) | `prctl` and `seccomp` (the confinement), then `write` and `exit`, enforced by a seccomp filter (implemented) | same | the signature's calls, enforced by a filter |
| ISA model | as before | plus the system call, outside the program table | same | plus calls to platform procedures |
| Loading | a dynamic executable with an interpreter | a static executable, two loadable segments, no relocations | same | same |

The test gates followed in X1: the native suites run their objects as test
executables IxCC writes (the same writer, with a test shell; [X1 as
implemented](#x1-as-implemented)), so the C compiler, the C library, the
system linker and the C driver are off their execution path too.

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
| X0 | `ixcc compile --exe` for roots of `Nat` parameters and a `Nat` result: the executable writer and its independent checker; the shell as typed x86 with the system call outside the program table; static layout with `CanonicalOk` proved; a ledger entry for the loader's post-state, the system calls and the shell. **Implemented** ([below](#x0-as-implemented)), also for `Bool` and other results without fields, rendered `#k`; the per-call return address and registers in `X86.Driver` moved to X0-P | — | every corpus root of the fragment (K1's and the `phase1-*` families') on every case agrees with the manifest, SrcEval, ByteEval and the C driver; a seccomp filter on; only `prctl`, `seccomp`, `write` and `exit`; the checker rejects mutated headers and truncations | 2–3.5k lines, 3–6 weeks (today's object path is about 2.2k lines across `ELF*.lean`; the shell is about 150 instructions of Lean data). Measured: 1.1k lines of production code and 0.4k of tests |
| X0-P | The shell proved: the shell lemma, parsing and rendering, the system call's model, permission monotonicity, a return address and register file per call in `X86.Driver`; the `Nat` executable theorem fenced | X0 | the theorem fenced on the standard axioms; the driver-model assumption retired for executables | 3–6k lines, 2–4 months (the `cx_init` proof is 0.5k lines and the stream-trace infrastructure exists) |
| X1 | XB-1 and IxOS-0, redefined: IxCC-written test executables speak today's line protocol (and the session protocol with `cx_drop` for the RC gates); readback on the host side in Lean. **Implemented** ([below](#x1-as-implemented)): the test shell serves binary requests, and the host in Lean speaks the line and session protocols over them; the C drivers are deleted | X0 | the native suites (`tests-rt`, `tests-pipeline`, `tests-corpus`, `tests-own`, the back end's runtime cases, the RC native modes) pass with the C runtime driver off the execution path and no C compiler in their inputs | 1–2k lines, 2–4 weeks after X0 |
| X2 | Numeric state machines: the generic request shell, parsing and rendering in a small Lean library compiled with the program, the session theorem on `Nat` states | X0 (X0-P for the proof) | `fib` as an executable whose parsing and rendering are Lean; a 1,000-call session against Lean's interpreter; the session theorem fenced | 2–4k lines (DR9 (a) is 3–6k with heap states) |
| X3 | Batch byte executables: arguments and input bytes in, output bytes and an exit code out; an exported byte-array allocation entry; the model of `read` | Phase 3 (DR2, DR3, DR6) | programs in the manner of `wc` and `sha256sum` byte-identical to Lean-compiled executables over a corpus of inputs | 2–4k lines beyond the DR items |
| X4 | Interactive executables: state-machine roots with heap states; platform interface version 1 (read, write, exit, clock); a seccomp filter of exactly the interface | DR1, DR6, DR9 (a) | an echo or counter-map program; a 1,000-call session; the state-machine theorem fenced | DR9 (a)'s 3–6k plus 1–2k |
| X5 | Lean `main : IO` over a recorded subset: traced events through the pipeline, platform calls as direct calls to platform procedures, the interpretation table for `IO`, the start-up logic in Lean | X4, DR2–DR5, P8, the reading of interpreted opaques (DC-2) | the benchmark fixtures' `main` functions compile unchanged and print what Lean's executables print | 10–25k lines, a weak basis (8–20k for traced events through about ten levels, plus the table) |
| X6 | The platform interface implemented by the IxOS tender (part of IxOS-2): the same program text as a Linux process and as a SIP | X4, IxOS-1 | one program, two platforms, the same outputs | with IxOS-2 |

## X0 as implemented

**Implemented.** `ixcc compile CLOSURE.ixe --equations EQ.json --exe FILE
[--stack BYTES] [--region BYTES]` writes a static executable of the first
root ([`IxCC/Exe.lean`](../IxCC/Exe.lean),
[`IxCC/X86/Exe/`](../IxCC/X86/Exe)); `FILE N1 … Nk` prints the result.
- **The file** (`X86/Exe/Write.lean`): an `ET_EXEC` image with no section
  headers: the ELF header, four program headers (the file read and execute at
  `0x400000`; the stack and then the region, zero-filled, read and write at
  `0x10000000`; the object's provenance note; `PT_GNU_STACK`), the note, the
  object's text byte for byte at the next 64-byte boundary, the read-only data
  (the seccomp filter and the messages) and the shell last. An object with a
  relocation is refused. `fib`'s executable is 3,004 bytes: text 1,168, data
  482, shell 956.
- **The check** (`X86/Exe/Validate.lean`, `X86/Exe/Read.lean`): read back
  independently; header, segments, size, zero gaps and every part as planned;
  each of the shell's two calls, decoded from the file, lands on its export's
  offset in the object's symbol table. `check_sound` states these facts;
  `writeChecked` refuses a file the check refuses.
- **The shell** (`X86/Exe/Shell.lean`, `X86/Exe/Code.lean`): 38 blocks of
  code and 9 message blocks, 956 to 977 bytes encoded. It makes `prctl`,
  `seccomp`, `write` (once unless the kernel writes part of the line) and
  `exit`, in that order. Exit statuses: 0 with the value on standard output
  (`n` for a `Nat`, `#k` for a constructor without fields); 2 for a wrong
  argument count, 3 for an argument that is not one or more ASCII digits;
  65 to 68 for the wrapper's heap, stack, `natOverflow` and trap (67 also for
  a numeral of `2^64` or more); 70 for a broken calling convention or an
  unknown status; 71 for a result word of neither shape; 74 for a failed
  write; 75 if the confinement is refused. Every failure writes a message to
  standard error.
- **The contract** (`X86/Exe/Layout.lean`): `Layout.driver` is the instance
  of `X86.Driver` each call is meant to see, and `Layout.driver_canonicalOk`
  proves `Driver.CanonicalOk` for every accepted layout (a stack that is a
  multiple of 16 and at least 8 KiB, a region of at least 4 KiB, together at
  most `2^40` bytes) and every return address after the object's text and
  below the zero-filled segment. That the shell realises this driver is not
  proved. The model's one return address and register file for both calls is
  recorded in that module and left unchanged.
- **The fragment** (`Exe.fragment`): at most five parameters, all `Nat`; a
  `Nat` result or a constructor without fields of an inductive whose
  constructors have none (`Bool` among them); immortal, zero-RC or plain-RC
  policy. Refused: `exe.params` (a parameter that is not a `Nat`, such as the
  resource corpus's trap roots), `exe.result` (constructor trees),
  `exe.layout`. What the native suites' test executables handle and a
  production executable does not:
  constructor-tree results, parameters that are not `Nat`, fewer arguments
  than parameters, several roots and several input lines in one process,
  regions under 4 KiB, timing and a dump of the object area.
- **Tests** (*measured*, x86-64 Linux): `tests-corpus --exe` runs 135 roots
  on 1,402 cases as executables, each agreeing with the manifest, SrcEval,
  ByteEval where the case fixes the layout both use, and the native run (under
  the C driver at X0, as a test executable since X1); one
  case is skipped (a 4,095-byte region) and the three trap roots are refused.
  `tests-exe` (4,532 assertions) covers the layout, the shell for every arity
  and result kind, the writer and its check under about 4,300 mutations, the
  refusals, malformed and oversized arguments, a trap, the confinement read
  from `/proc` and, under `strace`, the system calls.

## X1 as implemented

**Implemented.** The native suites run every compiled object as a *test
executable* IxCC writes, with no C compiler, C library or linker on the
execution path, and the C drivers are deleted. Built in two steps: first every
native suite ran each case both ways and required the two to agree line by line
(no disagreement on any of 2,955 lines, the RC controls' 4,393 checks or the
reuse sessions' 114,820); then the C drivers went.

- **The writer takes any frame** ([`X86/Exe/Write.lean`](../IxCC/X86/Exe/Write.lean),
  [`X86/Exe/Validate.lean`](../IxCC/X86/Exe/Validate.lean)). A frame is the
  platform code an executable embeds (its read-only data and its shell
  program), the exports that code calls (one call site each, in order) and
  the zero-filled segments the loader maps for it (one program header each).
  `writeFor` writes and checks a file of any frame: `checkFor` reads it back
  as the production check does, with the header counting the frame's program
  headers, and `checkFor_sound` (fenced on the standard axioms) gives the
  production check's facts plus the data bytes. The production executable is
  the frame `Input.frame`; `plan`, `checkWith`, `check`, `check_sound`,
  `Fields`, `Certified` and `writeChecked` keep their statements, and
  `Layout.driver_canonicalOk` is untouched. The writer also refuses segments
  that are unaligned, empty, out of order, overlapping the file or past
  `2^47`, which the production frame never is.
- **The test shell** ([`IxCCTests/Exe/TestShell.lean`](../IxCCTests/Exe/TestShell.lean)):
  test code, outside the production API, written as a `Shell.Program` like
  the production shell and encoded by the same encoder. After `prctl` and a
  seccomp filter that allows only `read` from descriptor 0, `write` to 1 or
  2, and `exit`, it serves requests of eight 64-bit words from standard
  input: *call* export `k` with six argument registers (sentinels in `rbx`,
  `rbp`, `r12` to `r15`, `rsp` at a fixed top; it answers `rax`, `rdx` and
  whether the sentinels and `rsp` came back); *read* bytes of the region;
  *write* bytes into the region; *end*. A range outside the region, an
  unknown request, an export index out of range or input that ends inside a
  request ends the run with its own status. Its memory: the program stack and
  the shell's own 256 bytes in one zero-filled segment at `0x10000000`, and
  the region in a segment of its own, one unmapped page above it or at a fixed
  address (the back end's generated programs compute with the Lean test
  region's address, `0x10000`). Nothing is mapped below the stack, right
  below the region or past the region's last page, so a stray write there
  faults (`tests-exe` shows it for a store just below and just past the
  region).
- **Binary requests, not the line protocol.** The milestone was planned with
  the test executables speaking the C driver's line protocol. What was built
  instead: the shell parses and renders nothing, and the line protocol, the
  `cx_drop` session and the back end's context set-up are host code in Lean
  ([`IxCCTests/Exe/Session.lean`](../IxCCTests/Exe/Session.lean),
  [`IxCCTests/Rt/Native.lean`](../IxCCTests/Rt/Native.lean)). The reason: the
  machine code the native gates trust shrinks to a request loop, a bounds
  check and the calls, and the parsing that was looser than the model
  (`strtoull`) and the decoding become Lean, tested like the rest of the suites.
  Per input line the host stores the budget at `region + 16`, calls `cx_init`
  (an `init` line if it fails) and the root with the line's words (at most
  five, zero beyond, saturated at `2^64 - 1` as `strtoull` saturated them), and
  reads the context and the object area back. The time of a root call is
  measured around its request, so it includes the pipe's round trip.
- **Two decoders.** Every result decoded natively is decoded by `Rt.readback`
  and by an independent decoder
  ([`IxCCTests/Rt/Decoder.lean`](../IxCCTests/Rt/Decoder.lean)), the C driver's
  decoder transcribed to Lean from its own logic (its own parser of the type
  and signature texts, its own word reads and bounds, its own rendering), and
  the two must agree; the observation the suites check is the independent
  decoder's, and `Rt.readback` of the dump is checked beside it, as the C
  decoder and `Rt.readback` were. Its independence is separate code with a
  separate derivation in the same language, not a second language.
- **The other harnesses.** The RC procedures' controls
  ([`IxCCTests/Rt/Rc/NativeControls.lean`](../IxCCTests/Rt/Rc/NativeControls.lean)):
  the C program's checks transcribed one for one, 4,393, with its output lines.
  The session with `cx_drop` (`IxCCTests/Rt/Rc/ReuseSupport.lean`): one
  initialization, then per call the complete value (two decoders), the
  result's unique count, `cx_drop`, the stable bump pointer and the exact free
  chain; the same 114,820 checks. The back end's harness
  (`IxCCTests/Backend/Native.lean`): the context block set up as its
  `init_context` did, the pattern of the Lean test region, the fixed region.
- **The suites' flag** is `--native` (it was `--cc CC`).
- **The system linker still checks the compiler's objects.** `ixcc compile`
  still writes relocatable objects, and no native gate links them any more, so
  `check-x86-object --ixcc` (the `x86-elf-object` check) compiles eleven objects
  in the check: the five K1 programs, `k1.ixe`'s five roots in one object, the
  real-source RC fixture on the plain-RC route, `gcd` on the zero-RC route
  (`--rc auto`), and in one object each the ABI family's eighteen roots of
  arities 0 to 5, the scalar family's twenty-three and the boundary family's,
  all read without their erased typing; it links each with the system linker
  into a static executable with no C library, entered at `cx_init` and never
  run: every global function of the object is required to be defined, and
  `readelf` finds each in the linked file at the linked text's address plus its
  object offset (126 exports). *Measured:* the whole check takes about 4 s on
  the build box with these eleven objects (2.8 s with the first seven, 0.6 s
  without any).
- **Measured** (x86-64 Linux): every native suite passes on test executables alone,
  with the native lines it ran in the comparison: `tests-rt` 180, `tests-pipeline` 450,
  `tests-corpus` 1,596 (1,412 before a further corpus family was registered), `tests-own`
  412, `check-backend` 119, `tests-pipeline-rc` 9 (`native`) and 12 (`negative`),
  `tests-rc-certificate fresh` 9 (codec) and 16 (replay) plus the reuse sessions' 168 calls
  and drops; every result with a type decoded alike by both decoders; the RC controls'
  4,393 checks and the reuse sessions' 114,820.

## The C drivers, removed

X1 deleted the C runtime driver, the RC controls' and the reuse session's C
harnesses (which reused its trampoline and decoder) and the back end's C
driver, with their ledger pins, the C link paths of the native suites and the
C compiler of the `suites` and `rc-native` checks. C remains in the tree only as
test harnesses: `native_harness.c`, `exports_harness.c` and `unwind_harness.c`
in [`fixtures/x86`](../fixtures/x86), with which `x86-elf-object` checks that
the system linker accepts the object writer's relocatable objects (one with a
runtime relocation the harness defines) and runs them, and
`hw_diff_harness.c`, with which `x86-hardware` tests the processor against the
instruction table. No gate runs a compiled program through C.

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

Settled by X0: the executable writer, its reader and its validator are
siblings of the object's, sharing only the object reader's field reader
(`ELFRead`) and its symbol lookup. Still open: how much of the stream-trace
infrastructure applies to a shell that is not compiler output ([open
questions](#open-questions)).

## Open questions

- How much of the stream-trace infrastructure applies to a shell that is not
  compiler output (above).
- **A guard between the production executable's stack and region.**
  `ixcc compile --exe` puts the program stack and the region in one
  zero-filled segment (`X86/Exe/Layout.lean`), so a write just below the
  region lands in the top of the stack, where the shell's call leaves its
  return address, rather than faulting. The native suites' test executables
  have the region in a segment of its own, an unmapped page above the stack
  segment, and `tests-exe` shows a store just outside it crashing the process.
  Should the production layout do the same? The cost in the proofs: the frame
  gains a second zero-filled segment, so the four program headers that
  `check_sound` states (`Fields`, `expectedPrograms`) become five, and
  `Layout.driver_canonicalOk`'s arithmetic moves the region by the gap (its
  clauses, the region apart from the stack among them, already hold without
  one). The proved pipeline does not rely on a guard: `Recheck.sound` covers
  runs the model shows non-faulting, in which the object touches only the
  region and its call stack, so a guard changes only what a program outside
  the theorem (a wrong model, or an object the checker did not accept) does
  when it writes there: fault, instead of corrupting the stack.
