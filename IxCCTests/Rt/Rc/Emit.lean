import IxCC.Rt.Rc.Procs
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

end IxCCTests.Rt.Rc.Emit
