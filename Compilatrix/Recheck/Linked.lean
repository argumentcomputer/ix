import Compilatrix.Recheck.Run
import Compilatrix.X86.Linked

/-!
# What `Recheck.run`'s artifact runs as

`Artifact.linked a D` is the object `Recheck.run` made, run by the driver
`D` (`X86.Linked`, the object's `Lang`): its bytes, `cx_init`'s symbol, and
one root per lowered root, in order, with the root's symbol, the parameter
count of its Cfg function and its readback type (`rootTy`: the scalar types
and supported ground first-order constructor signatures, or none). These are the entries of the loaded
Lir program (`Rt.Loaded.ofLowered`), so the two languages take the same
inputs; where the artifact lists a root (`Artifact.roots`) it is the same
symbol, parameter count and type.

`Artifact.front` is the artifact's front half: the levels `Recheck.runLir`
returns.
-/

namespace Compilatrix.Recheck

/-- The artifact's levels from the checked source to Lir. -/
def Artifact.front (a : Artifact) : Front :=
  { src := a.src, checked := a.checked, lam := a.lam, anf := a.anf, fir := a.fir, own := a.own, cfg := a.cfg
    lowered := a.lowered }

/-- The roots the object exports, as the driver calls them. -/
def Artifact.linkedRoots (a : Artifact) : List X86.Linked.Root :=
  a.lowered.roots.zipIdx.map fun (p, r) =>
    { symbol := p.2, params := cfgParams a.cfg p.1, ty := (a.src.roots[r]?).bind (rootTy a.src a.cfg ·.2) }

/-- **The artifact's object, run by the driver `D`.** -/
def Artifact.linked (a : Artifact) (D : X86.Driver) : X86.Linked :=
  { object := a.object, init := Rt.Procs.initSymbol, roots := a.linkedRoots, driver := D }

end Compilatrix.Recheck
