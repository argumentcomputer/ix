import IxCC.Own.Plain.Syntax

namespace IxCC.Own.Plain

/-- Per-function parameter borrow masks (`true` = `@borrowed`, `false` = owned). -/
abbrev BorrowSigs := Src.NatMap (List Bool)

/-- Bind parameter/constructor metadata to the actual source program; proposal
bodies and optional borrow masks remain explicit untrusted data for the separate checker. -/
structure Program where
  source : Fir.Program
  bodies : Src.NatMap Code
  borrows : BorrowSigs := .leaf

def Program.canonical (P : Fir.Program) : Program :=
  { source := P
    bodies := P.funs.map fun fd => lowerCode (fd.params.map (·.1)) [] fd.body }

end IxCC.Own.Plain
