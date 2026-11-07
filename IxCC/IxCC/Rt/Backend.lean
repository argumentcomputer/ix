import IxCC.Rt.Lower
import IxCC.Backend

/-! # `Rt.lower`'s output through the backend

The glue M1.I1 uses between the runtime and the backend (05 §6.1): every
root and `cx_init` is a SysV export, `cx_init` taking its region size and
stack budget as words and every root its arguments as tagged `Nat`s (the
wrapper checks them below 2^63). The object's entry symbol is the first
root's; `cx_init` and the other roots follow it in the symbol table. -/

namespace IxCC.Rt

/-- How each export passes its arguments. -/
def Lowered.reps (l : Lowered) (fn : Lir.FunId) : Option (List Xv.Stacking.ArgRep) :=
  if fn == l.init then some [.word, .word] else none

def Lowered.config (l : Lowered) (provenance : X86.ELF.Provenance) : Backend.Config :=
  { provenance, reps := l.reps }

/-- An ELF object exporting `cx_init` and every root (`Backend.compile`). -/
def Lowered.compile (l : Lowered) (provenance : X86.ELF.Provenance) : Except Backend.Error Backend.Artifact :=
  Backend.compile l.program (l.config provenance)

end IxCC.Rt
