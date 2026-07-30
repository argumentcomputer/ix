import Ix.Tc.Verify.State
import Ix.Tc.Verify.Execution
import Ix.Tc.Verify.Frame

/-!
# G3b: execution-indexed run assumptions

An explicit request list is not, by itself, evidence that it describes a
checker run: choosing `[]` would make coverage and bounds vacuous.  This file
builds on `ExecutionRequests`, an inductive certificate indexed by the actual
`TcM` computation and initial state. Its atomic constructors are exactly
the currently audited interning operations; its composition constructors
mirror `bind` and `tryCatch`; its silent constructors require intern-table
preservation, so the request list bounds the run's interning.

`ExecutionRequests` and `RunAssumptions` live in Verify/Execution.lean so the
temporary statement skeleton can import them without importing concrete
translation relations. The adapter lemmas here project that bundle into the
existing walker masters and retain both finite intern ranges in post-states.
-/

namespace Ix.Tc

/-- State invariant used by run-level adapters and top-level statements. G4
adds stable-world provenance for every warm cache entry. -/
def SupportedState (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld)
    (support : RunSupport) (s : TcState .anon) : Prop :=
  KernelStateWF semantics trProj world support s

/-- Rebuild full run support after an expression-only operation, using its
universe-table frame. -/
theorem RunSupport.CoversIntern.of_expr_univs {support : RunSupport}
    {before after : InternTable .anon}
    (hbefore : support.CoversIntern before)
    (hexpr : ∀ e, after.ExprSupport e → support e)
    (hunivs : after.univs = before.univs) :
    support.CoversIntern after := by
  refine ⟨hexpr, ?_⟩
  intro u hu
  exact hbefore.univ u (by
    simpa only [InternTable.UnivSupport, hunivs] using hu)

namespace RunAssumptions

/-! ### Direct intern adapters -/

/-- Direct expression interning is exact and keeps both intern ranges inside
the run support. -/
theorem internExpr_spec {α : Type} {initial : TcState .anon}
    {program : TcM .anon α} {requests : List WalkerRequest}
    {support : RunSupport}
    (h : RunAssumptions initial program requests support)
    {e : KExpr .anon} (hmem : WalkerRequest.internExpr e ∈ requests)
    {it : InternTable .anon} (hwf : it.WF)
    (hsup : support.CoversIntern it) :
    (it.internExpr e).1 = e ∧
      (it.internExpr e).2.WF ∧
      support.CoversIntern (it.internExpr e).2 := by
  have hSe : support e := h.coverage.internExpr hmem
  have hkcf : KExpr.KeyCollisionFree
      (fun v => it.ExprSupport v ∨ v = e) :=
    KExpr.keyCollisionFree_anon.mpr <|
      h.collisionFree.expr.mono fun x hx =>
        hx.elim (hsup.expr x) fun hxe => hxe ▸ hSe
  have hcanon : (it.internExpr e).1 = e := by
    have heq := InternTable.internExpr_eraseMeta hwf hkcf
    rwa [KExpr.eraseMeta_anon, KExpr.eraseMeta_anon] at heq
  refine ⟨hcanon, hwf.internExpr e, ?_⟩
  constructor
  · intro x hx
    rcases InternTable.ExprSupport.of_internExpr hx with hx | rfl
    · exact hsup.expr x hx
    · exact hSe
  · intro u hu
    exact hsup.univ u (by
      simpa only [InternTable.UnivSupport,
        InternTable.internExpr_univs] using hu)

/-- Direct universe interning is exact and keeps both intern ranges inside
the run support. -/
theorem internUniv_spec {α : Type} {initial : TcState .anon}
    {program : TcM .anon α} {requests : List WalkerRequest}
    {support : RunSupport}
    (h : RunAssumptions initial program requests support)
    {u : KUniv .anon} (hmem : WalkerRequest.internUniv u ∈ requests)
    {it : InternTable .anon} (hwf : it.WF)
    (hsup : support.CoversIntern it) :
    (it.internUniv u).1 = u ∧
      (it.internUniv u).2.WF ∧
      support.CoversIntern (it.internUniv u).2 := by
  have hSu : support.univ u := h.coverage.internUniv hmem
  have hcf : KUniv.CollisionFree
      (fun v => it.UnivSupport v ∨ v = u) :=
    h.collisionFree.univ.mono fun v hv =>
      hv.elim (hsup.univ v) fun hvu => hvu ▸ hSu
  have hcanon : (it.internUniv u).1 = u := by
    have heq := InternTable.internUniv_eraseMeta hwf hcf
    rwa [KUniv.eraseMeta_anon, KUniv.eraseMeta_anon] at heq
  refine ⟨hcanon, hwf.internUniv u, ?_⟩
  constructor
  · intro x hx
    exact hsup.expr x (by
      simpa only [InternTable.ExprSupport,
        InternTable.internUniv_exprs] using hx)
  · intro v hv
    rcases InternTable.UnivSupport.of_internUniv hv with hv | rfl
    · exact hsup.univ v hv
    · exact hSu

/-! ### Existing walker-master adapters -/

theorem lift_spec {α : Type} {initial : TcState .anon}
    {program : TcM .anon α} {requests : List WalkerRequest}
    {support : RunSupport}
    (h : RunAssumptions initial program requests support)
    {e : KExpr .anon} {shift cutoff : UInt64}
    (hmem : WalkerRequest.lift e shift cutoff ∈ requests)
    {it : InternTable .anon} (hwf : it.WF)
    (hsup : support.CoversIntern it) :
    (lift e shift cutoff it).1 = KExpr.liftSpec e shift cutoff ∧
      (lift e shift cutoff it).2.WF ∧
      support.CoversIntern (lift e shift cutoff it).2 := by
  obtain ⟨hcon, hcut, _⟩ := h.requestBounds hmem
  have post := Ix.Tc.lift_spec h.collisionFree.expr hcon hcut
    (h.coverage.lift hmem) hwf hsup.expr
  exact ⟨post.1, post.2.1,
    hsup.of_expr_univs post.2.2 (lift_preservesUnivs e shift cutoff it)⟩

theorem subst_spec {α : Type} {initial : TcState .anon}
    {program : TcM .anon α} {requests : List WalkerRequest}
    {support : RunSupport}
    (h : RunAssumptions initial program requests support)
    {body arg : KExpr .anon} {depth : UInt64}
    (hmem : WalkerRequest.subst body arg depth ∈ requests)
    {it : InternTable .anon} (hwf : it.WF)
    (hsup : support.CoversIntern it) :
    (subst body arg depth it).1 = KExpr.substSpec body arg depth ∧
      (subst body arg depth it).2.WF ∧
      support.CoversIntern (subst body arg depth it).2 := by
  obtain ⟨hbody, harg, hcut, hargsz, _⟩ := h.requestBounds hmem
  have post := Ix.Tc.subst_spec h.collisionFree.expr hbody harg hcut hargsz
    (h.coverage.subst hmem) hwf hsup.expr
  exact ⟨post.1, post.2.1,
    hsup.of_expr_univs post.2.2 (subst_preservesUnivs body arg depth it)⟩

theorem simulSubst_spec {α : Type} {initial : TcState .anon}
    {program : TcM .anon α} {requests : List WalkerRequest}
    {support : RunSupport}
    (h : RunAssumptions initial program requests support)
    {body : KExpr .anon} {substs : Array (KExpr .anon)} {depth : UInt64}
    (hmem : WalkerRequest.simulSubst body substs depth ∈ requests)
    {it : InternTable .anon} (hwf : it.WF)
    (hsup : support.CoversIntern it) :
    (simulSubst body substs depth it).1 =
        KExpr.simulSubstSpec body substs depth ∧
      (simulSubst body substs depth it).2.WF ∧
      support.CoversIntern (simulSubst body substs depth it).2 := by
  obtain ⟨hbody, hsubsts, hsizes, hwalk, _⟩ := h.requestBounds hmem
  have post := Ix.Tc.simulSubst_spec h.collisionFree.expr hbody hsubsts
    hsizes hwalk (h.coverage.simulSubst hmem) hwf hsup.expr
  exact ⟨post.1, post.2.1,
    hsup.of_expr_univs post.2.2
      (simulSubst_preservesUnivs body substs depth it)⟩

theorem instRev_spec {α : Type} {initial : TcState .anon}
    {program : TcM .anon α} {requests : List WalkerRequest}
    {support : RunSupport}
    (h : RunAssumptions initial program requests support)
    {body : KExpr .anon} {fvars : Array (KExpr .anon)}
    (hmem : WalkerRequest.instRev body fvars ∈ requests)
    {it : InternTable .anon} (hwf : it.WF)
    (hsup : support.CoversIntern it) :
    (instantiateRev body fvars it).1 =
        KExpr.instantiateRevSpec body fvars 0 ∧
      (instantiateRev body fvars it).2.WF ∧
      support.CoversIntern (instantiateRev body fvars it).2 := by
  obtain ⟨hbody, _, hwalk⟩ := h.requestBounds hmem
  have post := Ix.Tc.instantiateRev_spec h.collisionFree.expr hbody hwalk
    (h.coverage.instRev hmem) hwf hsup.expr
  exact ⟨post.1, post.2.1,
    hsup.of_expr_univs post.2.2
      (instantiateRev_preservesUnivs body fvars it)⟩

/-- API-level abstraction adapter, including its two no-op fast paths. -/
theorem abstractFVars_spec {α : Type} {initial : TcState .anon}
    {program : TcM .anon α} {requests : List WalkerRequest}
    {support : RunSupport}
    (h : RunAssumptions initial program requests support)
    {body : KExpr .anon} {fvars : Array FVarId}
    (hmem : WalkerRequest.abstractFVars body fvars ∈ requests)
    {it : InternTable .anon} (hwf : it.WF)
    (hsup : support.CoversIntern it) :
    (abstractFVars body fvars it).1 =
        KExpr.abstractFVarsResult body fvars ∧
      (abstractFVars body fvars it).2.WF ∧
      support.CoversIntern (abstractFVars body fvars it).2 := by
  obtain ⟨hbody, _, hwalk, _⟩ := h.requestBounds hmem
  have post :
      (abstractFVars body fvars it).1 =
          KExpr.abstractFVarsResult body fvars ∧
        (abstractFVars body fvars it).2.WF ∧
        (∀ x, (abstractFVars body fvars it).2.ExprSupport x →
          support x) := by
    by_cases hfast : (fvars.isEmpty || !body.hasFVars) = true
    · have hrun : abstractFVars body fvars it = (body, it) := by
        rw [abstractFVars_eq, if_pos hfast]
        rfl
      rw [hrun]
      exact ⟨by simp [KExpr.abstractFVarsResult, hfast], hwf, hsup.expr⟩
    · have cached := Ix.Tc.abstractFVarsCached_spec
          h.collisionFree.expr hbody
          (depth := 0) (it := it) (sc := {}) (by simpa using hwalk)
          (h.coverage.abstractFVars hmem) hwf hsup.expr
          (WalkScratchInv.empty support _)
      have hrun : abstractFVars body fvars it =
          ((abstractFVarsCached body (abstractFVarPositions fvars)
            fvars.size.toUInt64 0 (it, {})).1,
           (abstractFVarsCached body (abstractFVarPositions fvars)
            fvars.size.toUInt64 0 (it, {})).2.1) := by
        rw [abstractFVars_eq, if_neg hfast]
        rfl
      rw [hrun]
      exact ⟨by
        rw [KExpr.abstractFVarsResult, if_neg hfast]
        exact cached.result, cached.wf, cached.sup⟩
  exact ⟨post.1, post.2.1,
    hsup.of_expr_univs post.2.2
      (abstractFVars_preservesUnivs body fvars it)⟩

/-- Adapter for the cached abstraction master.  The remaining API wrapper
lemma exposes the slow-path master separately for recursive proof clients. -/
theorem abstractFVarsCached_spec {α : Type}
    {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest} {support : RunSupport}
    (h : RunAssumptions initial program requests support)
    {body : KExpr .anon} {fvars : Array FVarId}
    (hmem : WalkerRequest.abstractFVars body fvars ∈ requests)
    {depth : UInt64} {it : InternTable .anon} {sc : Scratch .anon}
    (hdepth : depth = 0)
    (hwf : it.WF) (hsup : ∀ x, it.ExprSupport x → support x)
    (hsc : WalkScratchInv support
      (KExpr.abstractFVarsSpec · (abstractFVarPositions fvars)
        fvars.size.toUInt64 ·) sc) :
    WalkPost support
      (KExpr.abstractFVarsSpec · (abstractFVarPositions fvars)
        fvars.size.toUInt64 ·)
      depth body
      (abstractFVarsCached body (abstractFVarPositions fvars)
        fvars.size.toUInt64 depth (it, sc)) := by
  subst depth
  obtain ⟨hbody, _, hwalk, _⟩ := h.requestBounds hmem
  exact Ix.Tc.abstractFVarsCached_spec h.collisionFree.expr hbody
    (by simpa using hwalk) (h.coverage.abstractFVars hmem) hwf hsup hsc

theorem instantiateUnivParams_wf {α : Type}
    {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest} {support : RunSupport}
    (h : RunAssumptions initial program requests support)
    {e : KExpr .anon} {us : Array (KUniv .anon)}
    (hmem : WalkerRequest.instUniv e us ∈ requests)
    {s : TcState .anon} :
    TcM.WF (fun s => s.env.intern.WF ∧
        ∀ x, s.env.intern.ExprSupport x → support x) s
      (TcM.instantiateUnivParams e us)
      (fun r s' => KExpr.instantiateUnivParamsSpec e us = .ok r ∧
        s' = { s with env := { s.env with intern := s'.env.intern } } ∧
        s'.env.intern.univs = s.env.intern.univs)
      (fun _ s' =>
        s' = { s with env := { s.env with intern := s'.env.intern } } ∧
        s'.env.intern.univs = s.env.intern.univs) :=
  TcM.instantiateUnivParams_wf h.collisionFree.expr
    (h.coverage.instUniv hmem)

/-! ### Hoare adapters for checker-proof composition -/

/-- Generic bridge from an `InternM` master to the checker Hoare kernel.
`runIntern` changes only `env.intern`, so loaded/catalog agreement frames
automatically while the supplied master re-establishes key coherence and both
finite intern ranges. -/
theorem runIntern_supported_wf {semantics : CacheSemantics}
    {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {x : InternM .anon α} {expected : α} {s : TcState .anon}
    (hspec : ∀ it : InternTable .anon, it.WF →
      support.CoversIntern it →
      (x it).1 = expected ∧ (x it).2.WF ∧
        support.CoversIntern (x it).2) :
    TcM.WF (SupportedState semantics trProj world support) s
      (TcM.runIntern x)
      (fun result s' => result = expected ∧
        s' = { s with env := { s.env with intern := s'.env.intern } }) := by
  intro hI
  obtain ⟨hstate, hsupport, hcaches⟩ := hI
  rcases hrun : x s.env.intern with ⟨result, intern⟩
  have hpost := hspec s.env.intern hstate.intern hsupport
  rw [hrun] at hpost
  simp only [TcM.runIntern, hrun]
  refine ⟨⟨hstate.of_consts_eq rfl hpost.2.1, hpost.2.2,
      hcaches.of_intern_update⟩,
    hpost.1, trivial⟩

theorem lift_wf {α : Type} {initial : TcState .anon}
    {program : TcM .anon α} {requests : List WalkerRequest}
    {support : RunSupport}
    (h : RunAssumptions initial program requests support)
    {semantics : CacheSemantics} {trProj : RawProjRel} {world : VerifyWorld}
    {e : KExpr .anon} {shift cutoff : UInt64}
    (hmem : WalkerRequest.lift e shift cutoff ∈ requests)
    {s : TcState .anon} :
    TcM.WF (SupportedState semantics trProj world support) s
      (TcM.runIntern (lift e shift cutoff))
      (fun result s' => result = KExpr.liftSpec e shift cutoff ∧
        s' = { s with env := { s.env with intern := s'.env.intern } }) :=
  runIntern_supported_wf fun _ hwf hsup =>
    h.lift_spec hmem hwf hsup

theorem subst_wf {α : Type} {initial : TcState .anon}
    {program : TcM .anon α} {requests : List WalkerRequest}
    {support : RunSupport}
    (h : RunAssumptions initial program requests support)
    {semantics : CacheSemantics} {trProj : RawProjRel} {world : VerifyWorld}
    {body arg : KExpr .anon} {depth : UInt64}
    (hmem : WalkerRequest.subst body arg depth ∈ requests)
    {s : TcState .anon} :
    TcM.WF (SupportedState semantics trProj world support) s
      (TcM.runIntern (subst body arg depth))
      (fun result s' => result = KExpr.substSpec body arg depth ∧
        s' = { s with env := { s.env with intern := s'.env.intern } }) :=
  runIntern_supported_wf fun _ hwf hsup =>
    h.subst_spec hmem hwf hsup

theorem simulSubst_wf {α : Type} {initial : TcState .anon}
    {program : TcM .anon α} {requests : List WalkerRequest}
    {support : RunSupport}
    (h : RunAssumptions initial program requests support)
    {semantics : CacheSemantics} {trProj : RawProjRel} {world : VerifyWorld}
    {body : KExpr .anon} {substs : Array (KExpr .anon)} {depth : UInt64}
    (hmem : WalkerRequest.simulSubst body substs depth ∈ requests)
    {s : TcState .anon} :
    TcM.WF (SupportedState semantics trProj world support) s
      (TcM.runIntern (simulSubst body substs depth))
      (fun result s' =>
        result = KExpr.simulSubstSpec body substs depth ∧
        s' = { s with env := { s.env with intern := s'.env.intern } }) :=
  runIntern_supported_wf fun _ hwf hsup =>
    h.simulSubst_spec hmem hwf hsup

theorem instRev_wf {α : Type} {initial : TcState .anon}
    {program : TcM .anon α} {requests : List WalkerRequest}
    {support : RunSupport}
    (h : RunAssumptions initial program requests support)
    {semantics : CacheSemantics} {trProj : RawProjRel} {world : VerifyWorld}
    {body : KExpr .anon} {fvars : Array (KExpr .anon)}
    (hmem : WalkerRequest.instRev body fvars ∈ requests)
    {s : TcState .anon} :
    TcM.WF (SupportedState semantics trProj world support) s
      (TcM.runIntern (instantiateRev body fvars))
      (fun result s' =>
        result = KExpr.instantiateRevSpec body fvars 0 ∧
        s' = { s with env := { s.env with intern := s'.env.intern } }) :=
  runIntern_supported_wf fun _ hwf hsup =>
    h.instRev_spec hmem hwf hsup

theorem abstractFVars_wf {α : Type} {initial : TcState .anon}
    {program : TcM .anon α} {requests : List WalkerRequest}
    {support : RunSupport}
    (h : RunAssumptions initial program requests support)
    {semantics : CacheSemantics} {trProj : RawProjRel} {world : VerifyWorld}
    {body : KExpr .anon} {fvars : Array FVarId}
    (hmem : WalkerRequest.abstractFVars body fvars ∈ requests)
    {s : TcState .anon} :
    TcM.WF (SupportedState semantics trProj world support) s
      (TcM.runIntern (abstractFVars body fvars))
      (fun result s' =>
        result = KExpr.abstractFVarsResult body fvars ∧
        s' = { s with env := { s.env with intern := s'.env.intern } }) :=
  runIntern_supported_wf fun _ hwf hsup =>
    h.abstractFVars_spec hmem hwf hsup

/-- Universe instantiation can throw after extending the expression intern
table, so this adapter explicitly re-establishes the invariant and frame on
both outcomes. -/
theorem instUniv_wf {α : Type} {initial : TcState .anon}
    {program : TcM .anon α} {requests : List WalkerRequest}
    {support : RunSupport}
    (h : RunAssumptions initial program requests support)
    {semantics : CacheSemantics} {trProj : RawProjRel} {world : VerifyWorld}
    {e : KExpr .anon} {us : Array (KUniv .anon)}
    (hmem : WalkerRequest.instUniv e us ∈ requests)
    {s : TcState .anon} :
    TcM.WF (SupportedState semantics trProj world support) s
      (TcM.instantiateUnivParams e us)
      (fun result s' =>
        KExpr.instantiateUnivParamsSpec e us = .ok result ∧
        s' = { s with env := { s.env with intern := s'.env.intern } })
      (fun _ s' =>
        s' = { s with env := { s.env with intern := s'.env.intern } }) := by
  intro hI
  obtain ⟨hstate, hsupport, hcaches⟩ := hI
  have hrunWF := h.instantiateUnivParams_wf hmem
    (s := s) ⟨hstate.intern, hsupport.expr⟩
  match hrun : TcM.instantiateUnivParams e us s with
  | .ok result s' =>
    rw [hrun] at hrunWF
    have hintern := hrunWF.1.1
    have hsupport' := hrunWF.1.2
    have hspec := hrunWF.2.1
    have hframe := hrunWF.2.2.1
    have hunivs := hrunWF.2.2.2
    have hcovered := hsupport.of_expr_univs hsupport' hunivs
    have hconsts : s'.env.consts = s.env.consts :=
      congrArg (fun state => state.env.consts) hframe
    have hcaches' : CacheInvariant semantics
        (CacheAuthority.stable world) support s'.env := by
      rw [hframe]
      exact hcaches.of_intern_update
    exact ⟨⟨hstate.of_consts_eq hconsts hintern, hcovered, hcaches'⟩,
      hspec, hframe⟩
  | .error err s' =>
    rw [hrun] at hrunWF
    have hintern := hrunWF.1.1
    have hsupport' := hrunWF.1.2
    have hframe := hrunWF.2.1
    have hunivs := hrunWF.2.2
    have hcovered := hsupport.of_expr_univs hsupport' hunivs
    have hconsts : s'.env.consts = s.env.consts :=
      congrArg (fun state => state.env.consts) hframe
    have hcaches' : CacheInvariant semantics
        (CacheAuthority.stable world) support s'.env := by
      rw [hframe]
      exact hcaches.of_intern_update
    exact ⟨⟨hstate.of_consts_eq hconsts hintern, hcovered, hcaches'⟩,
      hframe⟩

end RunAssumptions

end Ix.Tc
