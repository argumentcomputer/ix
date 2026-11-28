import IxCC.Cfg.Rc.Check
import IxCC.Cfg.Rc.Names

set_option autoImplicit false
namespace IxCC.Cfg.Rc


def programNames (F : Fir.Program) (bodies : Src.NatMap Own.Plain.Code) : Bool :=
  (List.range F.size).all fun f =>
    match F.fun? f, bodies.get? f with
    | some fd, some body =>
      names (paramBound 0 (fd.params.map (·.1))) body &&
      fd.params.all (fun p => decide (p.1 < fd.vars)) &&
      varsBelow fd.vars body &&
      reuseCtorsOk F.ctors body
    | _, _ => false

/-- Conservative source-map restriction used by the first call simulation:
every successful source lookup is a numbered function. -/
def sourceDense (F : Fir.Program) : Bool :=
  F.funs.toList.all fun p => decide (p.1 < F.size)

def checkScopedProgram (F : Fir.Program) (bodies : Src.NatMap Own.Plain.Code) (P : Program)
    (borrows : Own.Plain.BorrowSigs := .leaf) (uniqs : Own.Plain.UniqSigs := .leaf) : Bool :=
  checkProgram F bodies P borrows uniqs && programNames F bodies && sourceDense F

end IxCC.Cfg.Rc
