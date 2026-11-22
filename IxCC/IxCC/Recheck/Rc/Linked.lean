import IxCC.Recheck.Rc.Replay
import IxCC.Recheck.Rc.Types
import IxCC.X86.Linked

set_option autoImplicit false
namespace IxCC.Recheck.RcReplay


/-- The actual emitted object's roots, using the same parameter counts and
readback types as the physical loaded language. -/
def Artifact.linkedRoots (a : Artifact) : List X86.Linked.Root :=
  a.front.lowered.roots.zipIdx.map fun (p, r) =>
    {symbol := p.2, params := Recheck.cfgParams a.front.cfg.base p.1, ty := a.front.tys r}

def Artifact.linked (a : Artifact) (driver : X86.Driver) : X86.Linked :=
  {object := a.backend.object, init := Rt.Procs.initSymbol, roots := a.linkedRoots, driver}

/-- The object with `cx_init` called under `driver` and the roots from site
`s` (a caller with two call sites). -/
def Artifact.linkedAt (a : Artifact) (driver : X86.Driver) (s : X86.Driver.Site) : X86.LinkedAt :=
  ⟨a.linked driver, s⟩

end IxCC.Recheck.RcReplay
