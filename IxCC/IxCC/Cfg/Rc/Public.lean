import IxCC.Cfg.Rc.Native
import IxCC.Rt.Backend

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Public


def dropWrapper (callee : Nat) : Lir.Func :=
  { Native.decrementWrapper callee with name := "cx_drop", conv := .sysvExport "cx_drop" }

structure Lowered where
  runtime : Rt.Lowered
  drop : Lir.FunId

def Lowered.reps (l : Lowered) (f : Lir.FunId) : Option (List Xv.Stacking.ArgRep) :=
  if f == l.drop then some [.word] else l.runtime.reps f

def lower (config : Rt.Config) (F : Fir.Program) (bodies : Src.NatMap Own.Plain.Code)
    (P : Program) : Except String Lowered := do
  let original ← Native.lower config F bodies P
  let layout : Native.Layout := ⟨P.base.size, P.base.ctors.filter (fun c => c.arity > 0)⟩
  let drop := original.program.funcs.size
  let program : Lir.Program :=
    { original.program with funcs := original.program.funcs.push (dropWrapper layout.decProc) }
  program.check
  return { runtime := { original with program }, drop }

end IxCC.Cfg.Rc.Public
