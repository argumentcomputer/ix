import IxCC.Aiur.AIR.Memory

namespace IxCCTests.Aiur.MemoryAIR

open _root_.Aiur (G)
open IxCC.Aiur.AIR.Memory

def realRow (pointer value : G) (multiplicity : G := 1) : Row :=
  ⟨multiplicity, 1, pointer, [value]⟩

def padding (pointer value : G) : Row := ⟨0, 0, pointer, [value]⟩

def arbitraryStart : Table :=
  ⟨1, #[realRow 7 70, realRow 8 80, padding 900 42]⟩

def wrapped : Table :=
  ⟨1, #[realRow (0 - 1) 51, realRow 0 52, realRow 1 53, padding 77 99]⟩

def signed : Table := ⟨1, #[realRow 7 70 (0 - 2), realRow 8 80 0]⟩

def repeatedContents : Table := ⟨1, #[realRow 7 42, realRow 8 42]⟩

def selfPointer : Table := ⟨1, #[realRow 7 7]⟩

def allPadding : Table := ⟨1, #[padding 12 99, padding 3 42]⟩

def emptyTable : Table := ⟨1, #[]⟩

def zeroWidth : Table := ⟨0, #[⟨1, 1, 7, []⟩, ⟨0, 0, 50, []⟩]⟩

def distinctBuckets : List Table :=
  [⟨1, #[realRow 7 11]⟩, ⟨2, #[⟨1, 1, 7, [22, 33]⟩]⟩]

def skippedPointer : Table := ⟨1, #[realRow 7 70, realRow 9 80]⟩

def repeatedPointer : Table := ⟨1, #[realRow 7 70, realRow 7 80]⟩

def paddingThenReal : Table := ⟨1, #[padding 6 60, realRow 7 70]⟩

def inactiveProvider : Table := ⟨1, #[⟨1, 0, 7, [70]⟩]⟩

def nonBoolean : Table := ⟨1, #[⟨0, 2, 7, [70]⟩]⟩

end IxCCTests.Aiur.MemoryAIR
