import IxCC.X86.ELFRead

/-!
# An independent reader for the standalone executable

Reads the ELF header and the program headers of an ELF64 file, with the
field reader of the object reader (`ELFRead`). It imports neither the
executable writer nor the shell. Field layouts: System V gABI, "ELF Header"
and "Program Header"; x86-64 psABI.
-/

namespace IxCC.X86.Exe.Read

open IxCC.X86.ELFRead (natural slice header Header require)

structure ProgramHeader where
  kind : Nat
  flags : Nat
  offset : Nat
  address : Nat
  physical : Nat
  fileSize : Nat
  memorySize : Nat
  alignment : Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def programHeader (bytes : ByteArray) (offset : Nat) : Option ProgramHeader := do
  return ⟨← natural bytes offset 4, ← natural bytes (offset + 4) 4, ← natural bytes (offset + 8) 8,
    ← natural bytes (offset + 16) 8, ← natural bytes (offset + 24) 8, ← natural bytes (offset + 32) 8,
    ← natural bytes (offset + 40) 8, ← natural bytes (offset + 48) 8⟩

structure View where
  header : Header
  programs : List ProgramHeader
  deriving BEq, Repr, Inhabited

/-- The header and at most 16 program headers of 56 bytes, all inside the file. -/
def parse (bytes : ByteArray) : Option View := do
  let h ← header bytes
  require (h.programEntrySize == 56 && decide (h.programCount ≤ 16) &&
    decide (h.programOffset + 56 * h.programCount ≤ bytes.size))
  let programs ← (List.range h.programCount).mapM fun i => programHeader bytes (h.programOffset + 56 * i)
  return { header := h, programs }

/-- The target of a `call rel32` whose displacement is at file offset `field`,
in a file mapped at `base`: the address after the field plus the signed
displacement, if the byte before the field is the `E8` opcode. -/
def callTarget (bytes : ByteArray) (base field : Nat) : Option Int := do
  require (field ≥ 1 && bytes[field - 1]? == some 0xe8)
  let raw ← natural bytes field 4
  let displacement : Int := if raw < 2 ^ 31 then raw else (raw : Int) - 2 ^ 32
  return (base + field + 4 : Nat) + displacement

end IxCC.X86.Exe.Read
