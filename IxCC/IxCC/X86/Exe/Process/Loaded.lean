import IxCC.X86.Exe.Validate

/-!
# The loader's post-state (a specification)

One of the three hypotheses of the shell theorem (with `Process.Syscall` and
`Process.Step`): the state in which the kernel starts an executable
`X86.Exe.writeFor` wrote, with arguments `args`. It transcribes:

- **the ELF loader** (System V gABI, chapter 5, "Program Loading"; Linux
  `fs/binfmt_elf.c`, `load_elf_binary`): each `PT_LOAD` mapped at its virtual
  address with the file's bytes at its offset, so the file's first segment
  (offset 0, address `fileBase`) holds the whole file; control enters at
  `e_entry`, which the checked header gives as the shell's first byte;
- **the initial stack** (System V x86-64 psABI, §3.4.1 "Initial Stack and
  Register State", Figure 3.9; Linux `create_elf_tables`): `argc` at `rsp`,
  then `argv[0]` to `argv[argc − 1]` and a null pointer, `argv[i]` for
  `i ≥ 1` pointing at the bytes of the `i`-th argument and a NUL. The block
  lies outside the frame's zero-filled segments, since the kernel's mappings
  do not overlap.

**Not assumed**: any permission (a fault only ends a trace), the zero fill of
the zero-filled segments, the other registers, the flags, `argv[0]`'s bytes,
`envp` and the auxiliary vector. The shell reads nothing but the argument
block that it has not written itself.
-/

set_option autoImplicit false

namespace IxCC.X86.Exe.Process

/-- Argument bytes a C string can carry: each byte of each argument is
nonzero. -/
def ArgsOk (args : List (List Nat)) : Prop := ∀ a ∈ args, ∀ b ∈ a, 0 < b ∧ b < 256

/-- **The initial stack** at `sp` (System V x86-64 psABI §3.4.1, Figure 3.9):
`argc`, then `argv[0]` … `argv[argc − 1]` and a null pointer; for `i ≥ 1`,
`argv[i]` points at the bytes of `args[i − 1]` and a NUL (`argc = 0` is the
empty block). Every word of it and every byte of the arguments lies where
`apart` says. -/
def ArgBlock (m : Memory) (sp : Word) (args : List (List Nat)) (apart : Word → Prop) : Prop :=
  ∃ argc : Nat, argc < 2 ^ 61 ∧
    m.read64 sp = UInt64.ofNat argc ∧
    ((argc = 0 ∧ args = []) ∨ argc = args.length + 1) ∧
    m.read64 (sp + UInt64.ofNat (8 * (argc + 1))) = 0 ∧
    (∀ i a, args[i]? = some a →
      m.read64 (sp + UInt64.ofNat (8 * (i + 2))) ≠ 0 ∧
      (∀ j < a.length, m.bytes (m.read64 (sp + UInt64.ofNat (8 * (i + 2))) + UInt64.ofNat j) = UInt8.ofNat a[j]!) ∧
      m.bytes (m.read64 (sp + UInt64.ofNat (8 * (i + 2))) + UInt64.ofNat a.length) = 0) ∧
    (∀ i ≤ argc + 1, ∀ b < 8, apart (sp + UInt64.ofNat (8 * i + b))) ∧
    (∀ i a, args[i]? = some a → ∀ j ≤ a.length,
      apart (m.read64 (sp + UInt64.ofNat (8 * (i + 2))) + UInt64.ofNat j))

/-- Outside the zero-filled segments `segments` (each `(address, size)`). -/
def OutsideSegments (segments : List (Nat × Nat)) (a : Word) : Prop :=
  ∀ seg ∈ segments, a.toNat < seg.1 ∨ seg.1 + seg.2 ≤ a.toNat

/-- **The loader's post-state** for an executable `c` of frame `f`, run with
arguments `args` (see the module note): `rip` the entry (the shell's first
byte, `e_entry`), the file's bytes at `fileBase`, and the argument block at
`rsp`, outside the frame's zero-filled segments. Nothing is assumed of
permissions, other registers, the flags or the zero fill. -/
def Loaded {f : Frame} {object : ByteArray} (c : Checked f object) (args : List (List Nat))
    (s : ByteEval.State) : Prop :=
  s.rip = UInt64.ofNat (fileBase + c.plan.placement.shellOffset) ∧
  (∀ i < c.bytes.size, s.core.memory.bytes (UInt64.ofNat (fileBase + i)) = c.bytes[i]!) ∧
  ArgBlock s.core.memory (s.core.readReg .rsp) args (OutsideSegments f.segments)

end IxCC.X86.Exe.Process
