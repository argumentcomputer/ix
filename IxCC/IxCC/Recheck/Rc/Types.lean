import IxCC.Recheck.Rc.Replay
import IxCC.Recheck.Rc.View
import IxCC.Recheck.Readback

set_option autoImplicit false
namespace IxCC.Recheck.RcReplay
open IxCC.Sem (Obs)

def Front.tys (f : Front) (root : Nat) : Option (Rt.Sig × Rt.FoTy) :=
  (f.src.roots[root]?).bind fun entry => Recheck.rootTy f.src f.cfg.base entry.2

def Front.view (f : Front) : Nat → Option Obs → Option (Option Obs) :=
  treeViewOf f.anf.ctors f.tys

end IxCC.Recheck.RcReplay
