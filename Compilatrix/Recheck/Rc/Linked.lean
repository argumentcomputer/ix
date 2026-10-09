import Compilatrix.Recheck.Rc.Replay
import Compilatrix.Recheck.Rc.Types
import Compilatrix.X86.Linked

set_option autoImplicit false
namespace Compilatrix.Recheck.RcReplay


/-- The actual emitted object's roots, using the same parameter counts and
readback types as the physical loaded language. -/
def Artifact.linkedRoots (a : Artifact) : List X86.Linked.Root :=
  a.front.lowered.roots.zipIdx.map fun (p, r) =>
    {symbol := p.2, params := Recheck.cfgParams a.front.cfg.base p.1, ty := a.front.tys r}

def Artifact.linked (a : Artifact) (driver : X86.Driver) : X86.Linked :=
  {object := a.backend.object, init := Rt.Procs.initSymbol, roots := a.linkedRoots, driver}

end Compilatrix.Recheck.RcReplay
