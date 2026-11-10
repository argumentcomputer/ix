import IxCC.Cfg.Rc.Native
import IxCC.Rt.Backend

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native

/-- Exact caller-saved clobber sets for the generated RC runtime procedures
and markers. -/
def Layout.clobbers (l : Layout) (base : Xv.Xl.Env) (fn : Lir.FunId) : List X86.GPR :=
  if fn == l.incWrapper then [.rax, .r11]
  else if fn == l.decWrapper then [.rax, .rcx, .rdx, .rsi, .rdi, .r11]
  else if fn == l.incProc then [.rax]
  else if fn == l.decProc then [.rax, .rcx, .rdx, .rsi, .rdi]
  else if l.allocProc 0 ≤ fn && fn < l.allocProc l.ctors.length then
    [.rax, .rcx, .rdx]
  else if l.allocWrapper 0 ≤ fn && fn < l.allocWrapper l.ctors.length then
    match l.ctors[fn - l.allocWrapper 0]? with
    | some c =>
      if c.arity ≤ 2 then [.rax, .rcx, .rdx, .r11]
      else if c.arity == 3 then [.rax, .rcx, .rdx, .r8, .r11]
      else if c.arity == 4 then [.rax, .rcx, .rdx, .r8, .r9, .r11]
      else if c.arity == 5 then [.rax, .rcx, .rdx, .r8, .r9, .r10, .r11]
      else base.clobbers fn
    | none => base.clobbers fn
  else base.clobbers fn

def Layout.env (l : Layout) (base : Xv.Xl.Env) : Xv.Xl.Env :=
  { clobbers := l.clobbers base }

end IxCC.Cfg.Rc.Native

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
