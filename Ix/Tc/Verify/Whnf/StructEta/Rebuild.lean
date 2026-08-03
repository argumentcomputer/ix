import Ix.Tc.Verify.Whnf.Iota.StructEtaControl

/-!
# Finite struct-eta rebuild closure

StructEtaControl identifies the exact successful path through `tryStructEtaIota`, but
its final acceptance theorem still accepts the post-state invariant, the
intern-only frame, and finite result support as premises.  This slice derives
those three facts from the concrete projection/application requests made by
`finishStructEtaResult`.

The remaining `WhnfMeaning` premise is intentional.  Collision-safe
execution shows that production built the requested syntax; it does not prove
that the selected recursor rule is a registered Theory equation or that raw
projections have the required interpretation.
-/

namespace Ix.Tc
namespace RecM

/-- Finite request certificate for the projection/application pairs generated
by a contiguous struct-field range.  The indices expose the exact field
number, accumulator, request order, and final expression. -/
inductive StructEtaFieldRequests (requests : List WalkerRequest)
    (indId : KId .anon) (major : KExpr .anon) :
    Nat → Nat → KExpr .anon → KExpr .anon → Prop
  | nil (field result) :
      StructEtaFieldRequests requests indId major 0 field result result
  | cons {fuel field result final}
      (proj : WalkerRequest.internExpr
        (KExpr.mkPrj indId field.toUInt64 major) ∈ requests)
      (app : WalkerRequest.internExpr
        (KExpr.mkApp result
          (KExpr.mkPrj indId field.toUInt64 major)) ∈ requests)
      (tail : StructEtaFieldRequests requests indId major fuel (field + 1)
        (KExpr.mkApp result
          (KExpr.mkPrj indId field.toUInt64 major)) final) :
      StructEtaFieldRequests requests indId major (fuel + 1) field result
        final

namespace StructEtaFieldRequests

/-- The final accumulator of a certified field segment belongs to the finite
run support. -/
theorem support {α : Type} {initial : TcState .anon}
    {program : TcM .anon α} {requests : List WalkerRequest}
    {runSupport : RunSupport}
    (hrun : RunAssumptions initial program requests runSupport)
    {indId : KId .anon} {major : KExpr .anon}
    {fuel field : Nat} {result final : KExpr .anon}
    (h : StructEtaFieldRequests requests indId major fuel field result final)
    (hresult : runSupport result) : runSupport final := by
  induction h with
  | nil => exact hresult
  | cons proj app tail ih =>
      exact ih (hrun.coverage.internExpr app)

/-- Execute the production field helper from its exact finite request
certificate.  Collision freedom makes each returned projection/application
syntactically exact, and the intern-only frames compose across the loop. -/
theorem eval {α : Type} {initial : TcState .anon}
    {program : TcM .anon α} {requests : List WalkerRequest}
    {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {methods : Methods .anon} {s : TcState .anon}
    {indId : KId .anon} {major : KExpr .anon}
    {fuel field : Nat} {result final : KExpr .anon}
    (h : StructEtaFieldRequests requests indId major fuel field result final)
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s) :
    ∃ sf,
      (finishStructEtaFields indId major fuel field result).run methods s =
          .ok final sf ∧
      WhnfStateInv layer semantics trProj world support uvars Delta sf ∧
      InternUpdateFrame s sf := by
  induction h generalizing s with
  | nil =>
      exact ⟨s, rfl, hI, InternUpdateFrame.refl s⟩
  | @cons fuel field result final proj app tail ih =>
      obtain ⟨sProj, hproj, hIProj, hframeProj⟩ :=
        hrun.internExpr_whnf_eval proj hI
      obtain ⟨sApp, happ, hIApp, hframeApp⟩ :=
        hrun.internExpr_whnf_eval app hIProj
      obtain ⟨sf, htail, hIf, hframeTail⟩ := ih hIApp
      refine ⟨sf, ?_, hIf,
        hframeProj.trans (hframeApp.trans hframeTail)⟩
      unfold finishStructEtaFields
      rw [ReaderT.run_bind, ReaderT.run_monadLift]
      change EStateM.bind
        (TcM.intern (KExpr.mkPrj indId field.toUInt64 major)) _ s = _
      unfold EStateM.bind
      rw [hproj]
      simp only
      rw [ReaderT.run_bind, ReaderT.run_monadLift]
      change EStateM.bind
        (TcM.intern
          (KExpr.mkApp result
            (KExpr.mkPrj indId field.toUInt64 major))) _ sProj = _
      unfold EStateM.bind
      rw [happ]
      exact htail

end StructEtaFieldRequests

/-- One certificate for all three rebuild segments: prefix applications,
field projections/applications, and trailing applications. -/
structure StructEtaBuildRequests (requests : List WalkerRequest)
    (indId : KId .anon) (major rhs : KExpr .anon) (fields : UInt64)
    (prefixArgs trailingArgs : Array (KExpr .anon))
    (final : KExpr .anon) : Type where
  prefixResult : KExpr .anon
  fieldsResult : KExpr .anon
  prefixCert : FinishAppRequests requests
    (prefixArgs.extract 0 prefixArgs.size).toList rhs prefixResult
  fieldCert : StructEtaFieldRequests requests indId major fields.toNat 0
    prefixResult fieldsResult
  trailingCert : FinishAppRequests requests
    (trailingArgs.extract 0 trailingArgs.size).toList fieldsResult final

namespace StructEtaBuildRequests

/-- All three certified segments preserve the invariant and compose to the
exact production rebuild.  Result support follows from the same requests. -/
theorem eval {α : Type} {initial : TcState .anon}
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
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (hrhs : support rhs) :
    ∃ sf,
      (finishStructEtaResult indId major rhs fields prefixArgs trailingArgs).run
          methods s = .ok final sf ∧
      WhnfStateInv layer semantics trProj world support uvars Delta sf ∧
      InternUpdateFrame s sf ∧
      support final := by
  obtain ⟨sPrefix, hprefix, hIPrefix, hframePrefix⟩ :=
    h.prefixCert.eval hrun hI
  obtain ⟨sFields, hfields, hIFields, hframeFields⟩ :=
    h.fieldCert.eval hrun hIPrefix
  obtain ⟨sf, htrailing, hIf, hframeTrailing⟩ :=
    h.trailingCert.eval hrun hIFields
  have hprefixSupport : support h.prefixResult :=
    h.prefixCert.support hrun hrhs
  have hfieldsSupport : support h.fieldsResult :=
    h.fieldCert.support hrun hprefixSupport
  have hfinalSupport : support final :=
    h.trailingCert.support hrun hfieldsSupport
  exact ⟨sf,
    finishStructEtaResult_of_segments hprefix hfields htrailing,
    hIf, hframePrefix.trans (hframeFields.trans hframeTrailing),
    hfinalSupport⟩

end StructEtaBuildRequests

namespace StructEtaIotaSuccessTrace

/-- Successful struct eta with state/resource facts derived from the exact
finite run.  Compared with StructEtaControl's `acceptance`, the final invariant, frame,
and support are conclusions.  The frame intentionally starts at the final
probe state: classification and recursive callbacks may update caches or
fuel and therefore do not, in general, form an `InternUpdateFrame`.  Later
exhaustive helper composition supplies the one remaining prefix invariant.
The Theory meaning remains the explicit inductive semantic boundary. -/
theorem acceptance_of_requests
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx}
    {methods : Methods .anon} {recId : KId .anon}
    {recr : IotaInfo .anon} {recUs : Array (KUniv .anon)}
    {spine : Array (KExpr .anon)} {s sf : TcState .anon}
    {result : KExpr .anon}
    (h : StructEtaIotaSuccessTrace methods recId recr recUs spine s result
      sf)
    {source : KExpr .anon}
    (hProbeI : WhnfStateInv layer semantics trProj world support uvars Delta
      h.probes.sMajorSortW)
    (hreach : ∀ x,
      KExpr.InstUnivReach recUs h.selection.rule.rhs x → support x)
    (hbuild : StructEtaBuildRequests requests h.selection.indId
      spine[recr.majorIdx]! h.rhs h.selection.rule.fields
      (spine.extract 0
        (min (recr.params + recr.motives + recr.minors) spine.size))
      (spine.extract (recr.majorIdx + 1) spine.size) result)
    (hmeaning : WhnfMeaning trProj world uvars Delta source result) :
    (tryStructEtaIota recId recr recUs spine).run methods s =
        .ok (some result) sf ∧
      WhnfStateInv layer semantics trProj world support uvars Delta sf ∧
      InternUpdateFrame h.probes.sMajorSortW sf ∧
      support result ∧
      WhnfMeaning trProj world uvars Delta source result := by
  obtain ⟨_, hInstI, hInstFrame, hRhsSupport⟩ :=
    TcM.instantiateUnivParams_whnf_of_run hrun.collisionFree hreach hProbeI
      h.instantiation
  obtain ⟨sf', hBuildRun, hFinalI, hBuildFrame, hResultSupport⟩ :=
    hbuild.eval hrun hInstI hRhsSupport
  rw [h.rebuild] at hBuildRun
  cases hBuildRun
  exact ⟨h.eval, hFinalI,
    hInstFrame.trans hBuildFrame,
    hResultSupport, hmeaning⟩

end StructEtaIotaSuccessTrace
end RecM
end Ix.Tc
