import IxCC.Rt.Rc.View

set_option autoImplicit false
namespace IxCC.Recheck.RcReplay
open IxCC.Rt.Rc.Procs.Readback

/-- The complete view uses the existing viewResult convention: a rejected
root result is stuck, and hence covered by GoesWrong. -/
def treeViewOf (table : List Lam.CtorInfo) (types : Nat → Option (Rt.Sig × Rt.FoTy))
    (root : Nat) (observation : Option Sem.Obs) : Option (Option Sem.Obs) :=
  match types root with
  | none => some none
  | some (sig, ty) => (observation.bind (treeView table sig ty)).map some

end IxCC.Recheck.RcReplay
