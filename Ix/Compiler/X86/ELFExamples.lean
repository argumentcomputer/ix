import Ix.Compiler.X86.ELF
import Ix.Compiler.X86.EncodeExamples

/-!
Executable checks for the minimal ELF64 relocatable-object writer.  These
checks cover the writer's internal layout; the native fixture and external
binutils check independently parse, disassemble, link, and execute its output.
-/

namespace Ix.Compiler.X86.ELF.Examples

open Ix.Compiler.X86
open Ix.Compiler.X86.Encode
open Ix.Compiler.X86.ELF
open Ix.Compiler.Ixon

def fixtureProvenance : Provenance :=
  .ixir1Policy (Address.replicate 0x42) 1 1

#guard (Provenance.bytes fixtureProvenance).size ==
  provenanceDomain.size + 1 + 32 + 8

#guard (Provenance.bytes (.ixir2 (Address.replicate 0x42))).size ==
  provenanceDomain.size + 1 + 32

def encodeObject (program : Program) : Except String (Encode.Output × ByteArray) := do
  let encoded ← Encode.Program.encode program |>.mapError reprStr
  let object ← ELF.write
    { encoded
      entryBlock := program.entry
      provenance := fixtureProvenance } |>.mapError reprStr
  return (encoded, object)

def readNatural (input : ByteArray) (offset count : Nat) : Nat :=
  (List.range count).foldl (fun value index =>
    value + (input.get! (offset + index)).toNat * 2 ^ (8 * index)) 0

def containsBytes (input needle : ByteArray) : Bool :=
  (List.range (input.size + 1)).any fun offset =>
    input.extract offset (offset + needle.size) == needle

def arithmeticObjectAccepted : Bool :=
  match encodeObject Ix.Compiler.X86.Examples.arithmeticProgram with
  | .error _ => false
  | .ok (encoded, object) =>
      let sectionHeadersOffset := readNatural object 40 8
      let textHeader := sectionHeadersOffset + 64
      let textOffset := readNatural object (textHeader + 24) 8
      let textSize := readNatural object (textHeader + 32) 8
      object.extract 0 4 == ByteArray.mk #[0x7f, 0x45, 0x4c, 0x46] &&
        readNatural object 16 2 == 1 &&
        readNatural object 18 2 == 62 &&
        readNatural object 52 2 == 64 &&
        readNatural object 58 2 == 64 &&
        readNatural object 60 2 == 8 &&
        readNatural object 62 2 == 7 &&
        object.size == sectionHeadersOffset + 8 * 64 &&
        textSize == encoded.text.size &&
        object.extract textOffset (textOffset + textSize) == encoded.text &&
        containsBytes object ".note.compilatrix".toUTF8 &&
        containsBytes object ".note.GNU-stack".toUTF8 &&
        containsBytes object "compilatrix_main".toUTF8 &&
        containsBytes object (Provenance.bytes fixtureProvenance)

#guard arithmeticObjectAccepted

def runtimeRelocationAccepted : Bool :=
  match encodeObject Ix.Compiler.X86.Examples.runtimeProgram with
  | .error _ => false
  | .ok (_, object) =>
      let sectionHeadersOffset := readNatural object 40 8
      let relocationHeader := sectionHeadersOffset + 2 * 64
      let relocationOffset := readNatural object (relocationHeader + 24) 8
      let relocationSize := readNatural object (relocationHeader + 32) 8
      relocationSize == 24 &&
        object.extract relocationOffset (relocationOffset + 24) ==
          (u64 22 ++ word64 (relocationInfo 3 2) ++
            word64 (Int64.ofInt (-4)).toUInt64) &&
        containsBytes object "compilatrix_rt_allocate".toUTF8

#guard runtimeRelocationAccepted

def invalidEntryRejected : Bool :=
  match Encode.Program.encode Ix.Compiler.X86.Examples.arithmeticProgram with
  | .error _ => false
  | .ok encoded =>
      match ELF.write
          { encoded
            entryBlock := 99
            provenance := fixtureProvenance } with
      | .error (.missingEntryBlock 99) => true
      | _ => false

#guard invalidEntryRejected

def invalidEntryOffsetRejected : Bool :=
  match Encode.Program.encode Ix.Compiler.X86.Examples.arithmeticProgram with
  | .error _ => false
  | .ok encoded =>
      let invalid :=
        { encoded with blockOffsets := #[encoded.text.size] }
      match ELF.write
          { encoded := invalid
            entryBlock := 0
            provenance := fixtureProvenance } with
      | .error (.invalidEntryOffset offset size) =>
          offset == encoded.text.size && size == encoded.text.size
      | _ => false

#guard invalidEntryOffsetRejected

def invalidExportRejected : Bool :=
  match Encode.Program.encode Ix.Compiler.X86.Examples.arithmeticProgram with
  | .error _ => false
  | .ok encoded =>
      match ELF.write
          { encoded
            entryBlock := 0
            exportName := ""
            provenance := fixtureProvenance } with
      | .error .invalidExportName => true
      | _ => false

#guard invalidExportRejected

def invalidRelocationAddendRejected : Bool :=
  match Encode.Program.encode Ix.Compiler.X86.Examples.runtimeProgram with
  | .error _ => false
  | .ok encoded =>
      let invalid :=
        { encoded with relocations := encoded.relocations.map fun relocation =>
            { relocation with addend := 0 } }
      match ELF.write
          { encoded := invalid
            entryBlock := 0
            provenance := fixtureProvenance } with
      | .error (.invalidRelocationAddend 22 0) => true
      | _ => false

#guard invalidRelocationAddendRejected

def duplicateSymbolRejected : Bool :=
  match Encode.Program.encode Ix.Compiler.X86.Examples.runtimeProgram with
  | .error _ => false
  | .ok encoded =>
      match ELF.write
          { encoded
            entryBlock := 0
            exportName := "compilatrix_rt_allocate"
            provenance := fixtureProvenance } with
      | .error (.duplicateSymbol "compilatrix_rt_allocate") => true
      | _ => false

#guard duplicateSymbolRejected

end Ix.Compiler.X86.ELF.Examples
