import Compilatrix.Fir.Syntax
import Compilatrix.Rt.Readback

set_option autoImplicit false
namespace Compilatrix.Rt.Rc.Procs.Readback
open Compilatrix.Sem (Obs)

mutual
/-- Complete source-ID to runtime-tag view. A mismatch declines, exactly as
the existing scalar view does; every accepted constructor field is retained. -/
def treeView (table : List Lam.CtorInfo) (sig : Sig) (ty : FoTy) (source : Obs) : Option Obs :=
  match ty, source with
  | .nat, .nat n => some (.nat n)
  | .ind i, .ctor cid fields => do
    let c ← Fir.CtorInfo.ofKey table (.src cid)
    let types ← sig.ctor? i c.tag
    let values ← fieldsView table sig types fields
    return .ctor c.tag values
  | _, _ => none
termination_by sizeOf source

def fieldsView (table : List Lam.CtorInfo) (sig : Sig)
    (types : List FoTy) (source : List Obs) : Option (List Obs) :=
  match types, source with
  | [], [] => some []
  | ty :: types, value :: source => do
    let value' ← treeView table sig ty value
    let source' ← fieldsView table sig types source
    return value' :: source'
  | _, _ => none
termination_by sizeOf source
end

end Compilatrix.Rt.Rc.Procs.Readback
