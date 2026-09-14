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

/-- A structurally recursive list view of an application spine.  The proof
below connects it to production's accumulator/reverse implementation, while
this view makes translation induction direct. -/
def appSpineView (e : KExpr m) : KExpr m × List (KExpr m) :=
  match e with
  | .app f a _ =>
      let (head, args) := appSpineView f
      (head, args ++ [a])
  | e => (e, [])
termination_by structural e

/-- Production's accumulator contains the reversed pending suffix; the
structural view contributes the already ordered prefix. -/
theorem appSpineView_go (e : KExpr m) (acc : Array (KExpr m)) :
    let (head, args) := appSpineView e
    (KExpr.collectSpine.go e acc).1 = head ∧
      (KExpr.collectSpine.go e acc).2.toList =
        args ++ acc.toList.reverse := by
  induction e generalizing acc <;>
    simp_all [appSpineView, KExpr.collectSpine.go,
      List.reverse_append, List.append_assoc]

/-- The structural view is extensionally the actual production spine. -/
theorem appSpineView_collectSpine (e : KExpr m) :
    let (head, args) := appSpineView e
    e.collectSpine.1 = head ∧ e.collectSpine.2.toList = args := by
  simpa [KExpr.collectSpine] using appSpineView_go e #[]

/-- The imperative `for` loop in `finishAppResult` is exactly a monadic
left fold over the requested suffix.  This equation fixes both argument order
and the consumed-prefix boundary without changing the production helper. -/
theorem finishAppResult_eq_foldlM (result : KExpr m)
    (args : Array (KExpr m)) (consumed : Nat) :
    finishAppResult result args consumed =
      (args.extract consumed args.size).foldlM (m := RecM m)
        (fun result arg => liftM (TcM.intern (KExpr.mkApp result arg)))
        result := by
  unfold finishAppResult
  simp [Array.forIn_yield_eq_foldlM]

/-- The WHNF suffix loop and cheap beta use the same interned application
chain, including the exact final intern-table state. -/
theorem finishAppResult_eq_internAppChain (result : KExpr m)
    (args : Array (KExpr m)) (consumed : Nat) (methods : Methods m) (before : TcState m) :
    (finishAppResult result args consumed).run methods before =
      TcM.runIntern (internAppChain result (args.extract consumed args.size).toList) before := by
  rw [finishAppResult_eq_foldlM, ← Array.foldlM_toList]
  generalize (args.extract consumed args.size).toList = remaining
  induction remaining generalizing result before with
  | nil => rfl
  | cons argument remaining ih =>
      rw [List.foldlM_cons, ReaderT.run_bind, ReaderT.run_monadLift]
      change EStateM.bind (TcM.intern (KExpr.mkApp result argument)) _ before = _
      unfold EStateM.bind TcM.intern TcM.runIntern
      exact ih _ _

/-- Exact production step for general multi-argument beta.  Unlike the
single-argument convenience theorem, this exposes the lambda-peeling result,
the simultaneous-substitution execution, and rebuilding of only the
unconsumed argument suffix. -/
theorem whnfCoreWithFlagsStep_betaMany
    {methods : Methods .anon} {s s₁ s₂ s₃ : TcState .anon}
    {f arg head : KExpr .anon} {appInfo : ExprInfo .anon}
    {args : Array (KExpr .anon)}
    {nm : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {ty body body₀ : KExpr .anon} {lamInfo : ExprInfo .anon}
    {consumed : Array (KExpr .anon)} {substituted result : KExpr .anon}
    {flags : WhnfFlags}
    (hspine : (.app f arg appInfo : KExpr .anon).collectSpine = (head, args))
    (hhead : methods.whnfCoreFlags head flags s =
      .ok (.lam nm bi ty body lamInfo) s₁)
    (hconsume : consumeBetaLams (.lam nm bi ty body lamInfo) args =
      (body₀, consumed))
    (hnonempty : (!consumed.isEmpty) = true)
    (hsubst : TcM.runIntern (simulSubst body₀ consumed.reverse 0) s₁ =
      .ok substituted s₂)
    (hfinish : (finishAppResult substituted args consumed.size).run methods s₂ =
      .ok result s₃) :
    (whnfCoreWithFlagsStep (.app f arg appInfo) flags).run methods s =
      .ok (.next result) s₃ := by
  unfold whnfCoreWithFlagsStep
  rw [ReaderT.run_bind]
  rw [hspine]
  change EStateM.bind (methods.whnfCoreFlags head flags) _ s = _
  unfold EStateM.bind
  rw [hhead]
  simp only
  rw [hconsume]
  simp only
  rw [hnonempty]
  simp only [↓reduceIte]
  change ReaderT.run
    ((liftM (TcM.runIntern (simulSubst body₀ consumed.reverse 0)) >>= fun r => do
      pure PUnit.unit
      let r ← finishAppResult r args consumed.size
      pure (BoundedStep.next r)) :
        RecM .anon (BoundedStep (KExpr .anon) (KExpr .anon))) methods s₁ = _
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind
    (TcM.runIntern (simulSubst body₀ consumed.reverse 0)) _ s₁ = _
  unfold EStateM.bind
  rw [hsubst]
  change EStateM.bind
    (ReaderT.run (finishAppResult substituted args consumed.size) methods) _
      s₂ = _
  unfold EStateM.bind
  rw [hfinish]
  rfl

end Ix.Kernel.RecM
