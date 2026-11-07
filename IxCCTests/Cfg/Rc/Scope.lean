import IxCC.Cfg.Rc.Scoped
import IxCC.Own.Plain.Program

namespace IxCCTests.Cfg.Rc.Scope
open IxCC IxCC.Cfg.Rc
open IxCC.Cfg (Instr)

private def identity : Fir.Fun :=
  { key := .const 950 [], params := [(0, .tobj)], vars := 1, body := .ret (.var 0) }

private def source : Fir.Program :=
  { funs := Src.NatMap.ofDense [identity], size := 1, exports := [0], ctors := [], known := {} }

private def proposed (F : Fir.Program) : Program :=
  (generate F (Own.Plain.Program.canonical F).bodies).getD {base := default, actions := .leaf}

private def hiddenFunction : Fir.Program :=
  {source with funs := source.funs.insert 9 identity}

/-- The ordinary exact-map gate and the scope gate intentionally differ on an
extra source function. The candidate still has the exact numbered lowering;
only the stronger gate used by the simulation rejects the hidden callee. -/
example : checkProgram hiddenFunction (Own.Plain.Program.canonical hiddenFunction).bodies
    (proposed hiddenFunction) = true := by decide

example : checkScopedProgram hiddenFunction (Own.Plain.Program.canonical hiddenFunction).bodies
    (proposed hiddenFunction) = false := by decide

example : checkScopedProgram source (Own.Plain.Program.canonical source).bodies
    (proposed source) = true := by decide

end IxCCTests.Cfg.Rc.Scope
