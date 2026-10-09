import Compilatrix.Recheck.Rc.Replay
import Compilatrix.Recheck.Rc.View
import Compilatrix.Recheck.Readback

set_option autoImplicit false
namespace Compilatrix.Recheck.RcReplay
open Compilatrix.Sem (Obs)

def Front.tys (f : Front) (root : Nat) : Option (Rt.Sig × Rt.FoTy) :=
  (f.src.roots[root]?).bind fun entry => Recheck.rootTy f.src f.cfg.base entry.2

def Front.view (f : Front) : Nat → Option Obs → Option (Option Obs) :=
  treeViewOf f.anf.ctors f.tys

end Compilatrix.Recheck.RcReplay
