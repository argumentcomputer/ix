import IxCC.Rt.Rc.Procs
import IxCC.Rt.Rc.Gen.Procs
import IxCCTests.Rt.Rc.GenControls
import IxCC.Rt.Procs.Entry
import IxCC.Lir.SplitEdges
import IxCC.Lir.WellFormed
import IxCC.Backend

/-! Compile the exact RC procedures through the existing validated
backend. Export wrappers adapt the procedures' zero-result arity only; they
perform no allocation or reclamation themselves. -/

namespace IxCCTests.Rt.Rc.Emit
open IxCC
open IxCC.Rt.Rc.Procs

def effectWrapper (name : String) (f : Nat) : Lir.Func :=
  { name, params := [0], results := 1, conv := .sysvExport name
    blocks := #[{ body := #[.call [] f [.v 0]], term := .ret [.imm 1] }] }

def program : Lir.Program :=
  { funcs := #[inc, dec,
      { alloc 2 1 with conv := .sysvExport "cx_rc_alloc2" },
      { alloc 31 1 with conv := .sysvExport "cx_rc_alloc31" },
      { alloc 0 1 with conv := .sysvExport "cx_rc_alloc0" },
      { alloc 32 1 with conv := .sysvExport "cx_rc_alloc32" },
      Rt.Procs.cxInit, effectWrapper "cx_rc_inc" 0, effectWrapper "cx_rc_dec" 1]
    main := 2 }

def emit (path : System.FilePath) : IO Unit := do
  let p := program.splitCriticalEdges
  IO.ofExcept p.check
  let cfg : Backend.Config :=
    { provenance := .ixir1Policy (Ixon.Address.replicate 0x52) 1 1
      reps := fun f => (p.funcs[f]?).map fun fd => fd.params.map fun _ => .word }
  let result ← IO.ofExcept ((Backend.compile p cfg).mapError toString)
  IO.FS.writeBinFile path result.object
  IO.println s!"H2 native object: {result.object.size} bytes, {result.exports.length} exports"


/-- The general-layout procedures (`Rt.Rc.Gen`), exported for `GenNativeControls`: `cx_init`,
allocation by layout for five layouts (classes 34, 2, 44 and 3, and a refused field-less layout),
the release behind an effect wrapper, the uniqueness test, and for the negative controls today's
release and a mutant of the general one (`GenControls.mutant`), each behind an effect wrapper. -/
def genProgram : Lir.Program :=
  let allocExport (n s t : Nat) : Lir.Func :=
    { Rt.Rc.Gen.alloc ⟨n, s, t⟩ with conv := .sysvExport s!"cx_rc_alloc_{n}_{s}_{t}" }
  { funcs := #[Rt.Rc.Gen.dec, Rt.Procs.cxInit, allocExport 40 0 3, allocExport 0 1 5,
      allocExport 254 1 7, allocExport 2 0 1, allocExport 0 0 1, effectWrapper "cx_rc_dec" 0,
      { Rt.Rc.Gen.isUnique with conv := .sysvExport "cx_rc_is_unique" },
      Rt.Rc.Procs.dec, GenControls.mutant, effectWrapper "cx_rc_dec_today" 9,
      effectWrapper "cx_rc_dec_mutant" 10]
    main := 2 }

def emitGen (path : System.FilePath) : IO Unit := do
  let p := genProgram.splitCriticalEdges
  IO.ofExcept p.check
  let cfg : Backend.Config :=
    { provenance := .ixir1Policy (Ixon.Address.replicate 0x52) 1 1
      reps := fun f => (p.funcs[f]?).map fun fd => fd.params.map fun _ => .word }
  let result ← IO.ofExcept ((Backend.compile p cfg).mapError toString)
  IO.FS.writeBinFile path result.object
  IO.println s!"general-layout native object: {result.object.size} bytes, {result.exports.length} exports"

end IxCCTests.Rt.Rc.Emit
