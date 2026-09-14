import Ix.Kernel.Whnf

/-! The direct beta step's operational equation is shared by the named
verification and the independent set-model refinement. -/

namespace Ix.Kernel.RecM

/-- Exact production step for a direct one-argument beta redex. The head
callback equation records the actual returned lambda, independently of any
semantic specification of the recursive method table. -/
theorem whnfCoreWithFlagsStep_betaOne
    {methods : Methods .anon} {s s' : TcState .anon}
    {nm : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {ty body arg result : KExpr .anon}
    {lamMd appMd : ExprInfo .anon} {flags : WhnfFlags}
    (hhead : methods.whnfCoreFlags (.lam nm bi ty body lamMd) flags s =
      .ok (.lam nm bi ty body lamMd) s)
    (hwalk : TcM.runIntern (simulSubst body #[arg] 0) s = .ok result s') :
    (whnfCoreWithFlagsStep
      (.app (.lam nm bi ty body lamMd) arg appMd) flags).run methods s =
      .ok (.next result) s' := by
  unfold whnfCoreWithFlagsStep
  rw [ReaderT.run_bind]
  simp only [KExpr.collectSpine, KExpr.collectSpine.go]
  change EStateM.bind
    (methods.whnfCoreFlags (.lam nm bi ty body lamMd) flags) _ s = _
  unfold EStateM.bind
  rw [hhead]
  simp [consumeBetaLams, consumeBetaLamsFuel]
  change ReaderT.run
    (BoundedStep.next <$> liftM
      (TcM.runIntern (simulSubst body #[arg] 0)) :
        RecM .anon (BoundedStep (KExpr .anon) (KExpr .anon))) methods s = _
  rw [ReaderT.run_map, ReaderT.run_monadLift]
  rw [← bind_pure_comp]
  change EStateM.bind (TcM.runIntern (simulSubst body #[arg] 0))
    (fun r => pure (BoundedStep.next r)) s = _
  unfold EStateM.bind
  rw [hwalk]
  rfl

end Ix.Kernel.RecM
