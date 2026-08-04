import Ix.Tc.Verify.Check.CheckConstTransaction
import Ix.Tc.Verify.Check.BlockDefinition
import Ix.Tc.Verify.Check.BlockOracle
import Ix.Tc.Verify.Check.QuotientBoundary

/-!
# Public coordinated-block checker theorem

This is E0's stable public import frontier.  It instantiates the recursive
driver with the exact finite method table chosen by `TcM.runRec` and crosses
the public error-isolation wrapper.  Successful isolation is transparent, so
the semantic disposition is indexed by the public checker's exact final
state.
-/

namespace Ix.Tc

namespace TcM.checkConst

/-- A successful public checker call either atomically accepts the exact
routed block or executes the separately verified standalone branch.  The
coordinated body certifier is explicitly relative to K3 singleton-definition
evidence or E2's inductive/recursor oracle resources. -/
theorem blockDisposition
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {id : KId .anon} {before after : TcState .anon}
    (hbefore : CoordinatedKernelStateWF semantics trProj world support before)
    (hexactCatalog : ExactCoordinatedCatalog world)
    (hfault : TcM.LazyFaultPreserves
      (CoordinatedKernelStateWF semantics trProj world support))
    (hfaultBlock : TcM.LazyFaultPreserves
      (fun state => BlockStateWF trProj state world))
    (certify : ∀ {block : KId .anon}
      {members : Array (KId .anon)} {kind : CheckBlockKind}
      {routed bodyAfter : TcState .anon},
      ExactCheckBlock world block members kind →
      id ∈ members →
      RecM.ExactBlockBodySuccessTrace
        (Ix.Tc.methodsN (m := .anon) before.recFuel.toNat)
        block id members kind routed bodyAfter →
      CertifiedBlockBodySuccess semantics trProj world support
        (Ix.Tc.methodsN (m := .anon) before.recFuel.toNat)
        block id members kind routed bodyAfter)
    (hrun : TcM.checkConst id before = .ok () after) :
    CheckConstSuccessDisposition semantics trProj world support
      (Ix.Tc.methodsN (m := .anon) before.recFuel.toNat)
      id before after := by
  let methods := Ix.Tc.methodsN (m := .anon) before.recFuel.toNat
  have hbody : (RecM.checkConst id).run methods before = .ok () after := by
    unfold TcM.checkConst TcM.isolateCheckErrors TcM.runRec at hrun
    cases hinner :
        (RecM.checkConst id).run
          (Ix.Tc.methodsN (m := .anon) before.recFuel.toNat) before with
    | ok value middle =>
        simp only [hinner] at hrun
        cases hrun
        rfl
    | error err failed =>
        simp only [hinner] at hrun
        contradiction
  apply RecM.checkConst_success_disposition hbefore hexactCatalog hfault
    hfaultBlock ?_ hbody
  intro block members kind routed bodyAfter hexact hmember trace
  simpa [methods] using certify hexact hmember trace

end TcM.checkConst

end Ix.Tc
