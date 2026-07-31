import Ix.Tc.Verify.Whnf.StructEta.Classifier

/-!
# Struct-eta universe and rebuild tail

Classifier reduces the post-selection state obligation to
`finishStructEtaAfterSort`.  This slice discharges that tail from the finite
run certificate: the verified universe walker preserves the complete WHNF
invariant on success and partial-state error, and a successful RHS is rebuilt
only through request-certified projection/application interning.
-/

namespace Ix.Tc

namespace TcM

/-- Universe instantiation preserves the complete K1 invariant on both
outcomes.  On success it additionally returns the pure-spec equation and a
result in finite run support.  The error proof is important here: production
uses non-backtracking `EStateM`, so a failed walk may retain intern-table
updates made before the error. -/
theorem instantiateUnivParams_whnf_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx}
    {us : Array (KUniv .anon)} {e : KExpr .anon}
    {s : TcState .anon}
    (hcollision : support.CollisionFree)
    (hreach : ∀ x, KExpr.InstUnivReach us e x → support x) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      (TcM.instantiateUnivParams e us)
      (fun result _ =>
        KExpr.instantiateUnivParamsSpec e us = .ok result ∧
          support result) := by
  intro hI
  cases hrun : TcM.instantiateUnivParams e us s with
  | ok result after =>
      obtain ⟨hspec, hIafter, _, hresultSupport⟩ :=
        TcM.instantiateUnivParams_whnf_of_run hcollision hreach hI hrun
      exact ⟨hIafter, hspec, hresultSupport⟩
  | error err after =>
      have hwalk := TcM.instantiateUnivParams_wf hcollision.expr hreach
        ⟨hI.1.core.intern, hI.1.internSupport.expr⟩
      rw [hrun] at hwalk
      have hframe : InternUpdateFrame s after := hwalk.2.1
      have hunivs := hwalk.2.2
      have hconsts : after.env.consts = s.env.consts := by
        simpa [InternUpdateFrame] using
          congrArg (fun state : TcState .anon => state.env.consts) hframe
      have henv : after.env =
          {s.env with intern := after.env.intern} := by
        simpa [InternUpdateFrame] using
          congrArg (fun state : TcState .anon => state.env) hframe
      have hcover : support.CoversIntern after.env.intern := {
        expr := hwalk.1.2
        univ := by
          intro u hu
          exact hI.1.internSupport.univ u (by
            simpa only [InternTable.UnivSupport, hunivs] using hu)
      }
      have hcaches :
          CacheInvariant semantics (.stable world) support after.env := by
        rw [henv]
        exact hI.1.caches.of_intern_update
      have hkernel : KernelStateWF semantics trProj world support after := {
        core := hI.1.core.of_consts_eq hconsts hwalk.1.1
        internSupport := hcover
        caches := hcaches
      }
      exact ⟨hframe.whnfStateInv hkernel hI, trivial⟩

end TcM

namespace RecM

namespace StructEtaBuildRequests

/-- Hoare form of the existing finite rebuild evaluator.  A request
certificate makes the intern-only helper operationally total, so its error
arm is vacuous; success returns the certificate's exact final syntax. -/
theorem wf {α : Type} {initial : TcState .anon}
    {program : TcM .anon α} {requests : List WalkerRequest}
    {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {methods : Methods .anon} {s : TcState .anon}
    {indId : KId .anon} {major rhs : KExpr .anon} {fields : UInt64}
    {prefixArgs trailingArgs : Array (KExpr .anon)}
    {final : KExpr .anon}
    (h : StructEtaBuildRequests requests indId major rhs fields prefixArgs
      trailingArgs final)
    (hrhs : support rhs) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((finishStructEtaResult indId major rhs fields prefixArgs
        trailingArgs).run methods)
      (fun result _ => result = final ∧ support result) := by
  intro hI
  obtain ⟨sf, hrunBuild, hIf, _, hfinalSupport⟩ := h.eval hrun hI hrhs
  rw [hrunBuild]
  exact ⟨hIf, rfl, hfinalSupport⟩

end StructEtaBuildRequests

/-- The actual H3 tail preserves state from an execution-indexed finite
request census.  No totality assumption is made for universe instantiation:
if the verified walker errors, its partial intern state is retained; if it
succeeds, `hbuild` must certify exactly that pure-spec RHS and all subsequent
generated intern requests. -/
theorem finishStructEtaAfterSort_wf_of_requests
    {α : Type} {initial : TcState .anon}
    {program : TcM .anon α} {requests : List WalkerRequest}
    {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {methods : Methods .anon}
    {recUs : Array (KUniv .anon)} {spine : Array (KExpr .anon)}
    {recr : IotaInfo .anon} {rule : RecRule .anon} {indId : KId .anon}
    {major majorSortW : KExpr .anon} {s : TcState .anon}
    (hreach : ∀ x,
      KExpr.InstUnivReach recUs rule.rhs x → support x)
    (hbuild : ∀ {rhs},
      KExpr.instantiateUnivParamsSpec rule.rhs recUs = .ok rhs →
      Σ final, StructEtaBuildRequests requests indId major rhs rule.fields
        (spine.extract 0
          (min (recr.params + recr.motives + recr.minors) spine.size))
        (spine.extract (recr.majorIdx + 1) spine.size) final) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((finishStructEtaAfterSort recUs spine recr rule indId major
        majorSortW).run methods)
      (fun _ _ => True) := by
  unfold finishStructEtaAfterSort
  split
  · exact TcM.WF.pure fun _ => trivial
  · simp only [pure_bind]
    rw [ReaderT.run_bind, ReaderT.run_monadLift]
    apply TcM.WF.bind
      (TcM.instantiateUnivParams_whnf_wf hrun.collisionFree hreach)
    intro rhs afterInst hrhs
    obtain ⟨final, hcert⟩ := hbuild hrhs.1
    rw [ReaderT.run_bind]
    apply TcM.WF.bind (hcert.wf hrun hrhs.2)
    intro result afterBuild _
    exact TcM.WF.pure fun _ => trivial

end RecM
end Ix.Tc
