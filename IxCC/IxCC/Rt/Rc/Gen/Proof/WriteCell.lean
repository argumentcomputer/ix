import IxCC.Rt.Rc.Gen.Proof.LiveMemory

/-! # The in-place rewrite of a cell, as memory

`writeCell mem addresses a b cls`: the memory after the cell at `a` is rewritten with body `b`, a
fresh header (scan count, class `cls`, tag, one reference) and then field `j`'s word at
`a + 8 + 8j` (a value word at a scanned position, a raw word at a scalar one; `0` for a field
without a word), in field order. Definitions only: its memory facts are in `Gen.Proof.Rewrite`,
the in-place reuse it carries out in `Gen.Proof.InPlace` (`inPlace_ready`); the controls
(`IxCCTests.Rt.Rc.GenReuseControls`) run this same definition. Nothing emits this rewrite yet. -/

set_option autoImplicit false
namespace IxCC.Rt.Rc.Gen
open Lir
open IxCC.Rt.Rc.Procs (AddressMap)

/-- The stores of a body's fields into the cell at `a`: field `j`'s word at `a + 8 + 8j`
(`0` for a field without a word). -/
def writeFields (mem : X86.Memory) (addresses : AddressMap) (a : Word) (c : Fir.CtorInfo)
    (entries : List (Own.RVal × Nat)) : X86.Memory :=
  entries.foldl (fun mem (value, j) =>
    mem.write .w64 (a + UInt64.ofNat (8 + 8 * j)) ((fieldWord addresses c j value).getD 0)) mem

/-- The memory after an in-place rewrite of the cell at `a`: a fresh header (one reference) and
the new body's words, scanned then scalar. -/
def writeCell (mem : X86.Memory) (addresses : AddressMap) (a : Word) (b : Own.Body) (cls : Nat) :
    X86.Memory :=
  writeFields (mem.write .w64 a (dynamicHeader b.ctor.nobj cls b.ctor.tag 1)) addresses a b.ctor
    b.fields.zipIdx

end IxCC.Rt.Rc.Gen
