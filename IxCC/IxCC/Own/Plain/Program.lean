import IxCC.Own.Plain.Syntax

namespace IxCC.Own.Plain

/-- Bind parameter/constructor metadata to the actual source program; proposal
bodies remain explicit untrusted data for the separate checker. -/
structure Program where
  source : Fir.Program
  bodies : Src.NatMap Code

def Program.canonical (P : Fir.Program) : Program :=
  { source := P
    bodies := P.funs.map fun fd => lowerCode (fd.params.map (·.1)) [] fd.body }

end IxCC.Own.Plain
