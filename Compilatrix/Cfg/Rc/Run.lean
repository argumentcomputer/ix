import Compilatrix.Cfg.Rc.Semantics

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc


/-- Existing structural Cfg fuel, now justified for explicit atomic RC actions.
Physical release-loop charges belong to the separate native simulation. -/
def run (P : Program) (clock f : Nat) (args : List Own.RVal) (H : Own.Heap := {}) :
    Sem.Result (Own.RVal × Own.Heap) :=
  Sem.runClocked (step P) (Cfg.fuelFor P.base clock) clock (.call f args [] H)

end Compilatrix.Cfg.Rc
