import Ix.Tc.Verify.Infer.Callbacks

/-!
# Recursive-result substitution resources

Let inference substitutes a fixed value into a type returned by a recursive
callback.  Since that body is dynamic, this module exposes the walker through
a finite support closure rather than static request-list membership.
-/

namespace Ix.Tc

/-- Finite operational and arithmetic closure for substitution over
supported inputs. -/
structure SubstitutionResources (support : RunSupport) : Prop where
  reach : ∀ {body arg : KExpr .anon} {depth : UInt64},
    support body → support arg → ∀ x,
      KExpr.SubstReach arg body depth x → support x
  bounds : ∀ {body arg : KExpr .anon} {depth : UInt64},
    support body → support arg →
      WalkerRequest.Bounds (.subst body arg depth)

namespace SubstitutionResources

/-- Request-independent execution of the production substitution walker. -/
theorem whnf_wf
    {support : RunSupport} (hresources : SubstitutionResources support)
    (hcollision : support.CollisionFree)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {body arg : KExpr .anon} {depth : UInt64}
    (hbodySupport : support body) (hargSupport : support arg)
    {s : TcState .anon} :
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) s
      (TcM.runIntern (subst body arg depth))
      (fun result after =>
        result = KExpr.substSpec body arg depth ∧
          support result ∧ InternUpdateFrame s after) := by
  have hbounds := hresources.bounds (depth := depth)
    hbodySupport hargSupport
  obtain ⟨hbody, harg, hcut, hargsz, _⟩ := hbounds
  have hreach := hresources.reach (depth := depth)
    hbodySupport hargSupport
  apply TcM.WF.mono
    (TcM.runIntern_whnf_wf (fun it hwf hcover => by
      have post := Ix.Tc.subst_spec hcollision.expr hbody harg hcut hargsz
        hreach hwf hcover.expr
      exact ⟨post.1, post.2.1,
        hcover.of_expr_univs post.2.2
          (subst_preservesUnivs body arg depth it)⟩))
  · intro result after hpost
    rcases hpost with ⟨rfl, hframe⟩
    exact ⟨rfl, hreach _ (KExpr.SubstReach.spec arg body depth), hframe⟩
  · intro _ _ herror
    exact herror

end SubstitutionResources

end Ix.Tc
