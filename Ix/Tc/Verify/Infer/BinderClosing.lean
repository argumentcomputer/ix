import Ix.Tc.Verify.Infer.BinderScopes

/-!
# Semantic binder closing for inference

Lambda and let inference open a de Bruijn binder as a fresh free variable,
infer under that tagged context, and then call `abstractFVars` before leaving
the scope.  This module proves the reverse half of that round trip: singleton
fvar abstraction retags the concrete expression back to the original
de Bruijn context without changing its Theory translation.
-/

namespace Ix.Tc

open Lean4Lean (VExpr VLocalDecl)

namespace KVLCtx.RetagFVar

/-- Reverse the distinguished-variable lookup introduced by retagging. -/
theorem find?_hit_rev
    {fvData : FVarId × List FVarId} {decl : VLocalDecl}
    {depth : Nat} {source target : KVLCtx}
    (W : KVLCtx.RetagFVar fvData decl depth source target) :
    ∀ {e A : VExpr}, target.find? (.inr fvData.1) = some (e, A) →
      source.find? (.inl depth) = some (e, A) := by
  induction W with
  | zero =>
      intro e A H
      simp [KVLCtx.find?, KVLCtx.next] at H ⊢
      exact H
  | @succ depth source target d W ih =>
      intro e A H
      simp [KVLCtx.find?, KVLCtx.next] at H ⊢
      obtain ⟨e', A', H, rfl, rfl⟩ := H
      exact ⟨_, _, ih H, rfl, rfl⟩

/-- Variables below the retagged binder keep the same de Bruijn index. -/
theorem find?_lt_rev
    {fvData : FVarId × List FVarId} {decl : VLocalDecl}
    {depth : Nat} {source target : KVLCtx}
    (W : KVLCtx.RetagFVar fvData decl depth source target) :
    ∀ {j : Nat} {e A : VExpr}, j < depth →
      target.find? (.inl j) = some (e, A) →
      source.find? (.inl j) = some (e, A) := by
  induction W with
  | zero => intro j e A hj; omega
  | @succ depth source target d W ih =>
      intro j e A hj H
      cases j with
      | zero => simpa [KVLCtx.find?, KVLCtx.next] using H
      | succ j =>
          simp [KVLCtx.find?, KVLCtx.next] at H ⊢
          obtain ⟨e', A', H, rfl, rfl⟩ := H
          exact ⟨_, _, ih (by omega) H, rfl, rfl⟩

/-- Variables at or above the retagged binder regain the one index consumed
by its de Bruijn form. -/
theorem find?_ge_rev
    {fvData : FVarId × List FVarId} {decl : VLocalDecl}
    {depth : Nat} {source target : KVLCtx}
    (W : KVLCtx.RetagFVar fvData decl depth source target) :
    ∀ {j : Nat} {e A : VExpr}, depth ≤ j →
      target.find? (.inl j) = some (e, A) →
      source.find? (.inl (j + 1)) = some (e, A) := by
  induction W with
  | zero =>
      intro j e A hj H
      simp [KVLCtx.find?, KVLCtx.next] at H ⊢
      exact H
  | @succ depth source target d W ih =>
      intro j e A hj H
      cases j with
      | zero => omega
      | succ j =>
          simp [KVLCtx.find?, KVLCtx.next] at H ⊢
          obtain ⟨e', A', H, rfl, rfl⟩ := H
          exact ⟨_, _, ih (by omega) H, rfl, rfl⟩

/-- Any other fvar lookup is unaffected by retagging. -/
theorem find?_fvar_ne_rev
    {fvData : FVarId × List FVarId} {decl : VLocalDecl}
    {depth : Nat} {source target : KVLCtx}
    (W : KVLCtx.RetagFVar fvData decl depth source target) :
    ∀ {fv : FVarId} {e A : VExpr}, fv ≠ fvData.1 →
      target.find? (.inr fv) = some (e, A) →
      source.find? (.inr fv) = some (e, A) := by
  induction W with
  | zero =>
      intro fv e A hne H
      simp [KVLCtx.find?, KVLCtx.next, Ne.symm hne] at H ⊢
      exact H
  | @succ depth source target d W ih =>
      intro fv e A hne H
      simp [KVLCtx.find?, KVLCtx.next] at H ⊢
      obtain ⟨e', A', H, rfl, rfl⟩ := H
      exact ⟨_, _, ih hne H, rfl, rfl⟩

end KVLCtx.RetagFVar

@[simp] theorem abstractFVarPositions_singleton_hit (fv : FVarId) :
    (abstractFVarPositions #[fv])[fv]? = some 0 := by
  simp [abstractFVarPositions]

theorem abstractFVarPositions_singleton_miss {fv other : FVarId}
    (hne : other ≠ fv) :
    (abstractFVarPositions #[fv])[other]? = none := by
  simp [abstractFVarPositions, Ne.symm hne]

/-- Singleton fvar abstraction reverses a context retag at any syntactic
binder depth.  `Constructed` supplies the no-wrap fact for the `i + 1`
variable arm; the size bound supplies every recursive `depth + 1`. -/
theorem TrKExprS.closeFVarSpec
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    {target : KVLCtx} {body : KExpr .anon} {bodyV : VExpr}
    (H : TrKExprS env uvars nameOf trProj target body bodyV)
    (hcon : KExpr.Constructed body) :
    ∀ {fvData : FVarId × List FVarId} {decl : VLocalDecl}
      {source : KVLCtx} {dk : Nat} {depth : UInt64},
      KVLCtx.RetagFVar fvData decl dk source target →
      depth.toNat = dk →
      depth.toNat + body.size + 1 < UInt64.size →
      TrKExprS env uvars nameOf trProj source
        (KExpr.abstractFVarsSpec body
          (abstractFVarPositions #[fvData.1]) 1 depth) bodyV := by
  intro fvData decl source dk depth W hdepth hbig
  induction hcon generalizing source target dk depth bodyV with
  | @var idx name md hidx =>
      rw [KExpr.mkVar_shape] at H
      cases H with
      | @var _ _ _ _ e A hfind =>
          rw [KExpr.mkVar_shape, KExpr.abstractFVarsSpec]
          by_cases hge : idx ≥ depth
          · rw [if_pos hge, KExpr.mkVar_shape]
            refine .var (A := A) ?_
            have hsucc : (idx + 1).toNat = idx.toNat + 1 := by
              rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl,
                Nat.mod_eq_of_lt hidx]
            rw [hsucc]
            exact W.find?_ge_rev (by
              rw [← hdepth]
              exact UInt64.le_iff_toNat_le.mp hge) hfind
          · rw [if_neg hge]
            refine .var (A := A) ?_
            exact W.find?_lt_rev (by
              rw [← hdepth]
              have hnle : ¬depth.toNat ≤ idx.toNat := fun h =>
                hge (UInt64.le_iff_toNat_le.mpr h)
              omega) hfind
  | @fvar id name md =>
      rw [KExpr.mkFVar_shape] at H
      cases H with
      | @fvar _ _ _ _ e A hfind =>
          rw [KExpr.mkFVar_shape, KExpr.abstractFVarsSpec]
          by_cases heq : id = fvData.1
          · subst id
            simp only [abstractFVarPositions_singleton_hit, UInt64.add_zero]
            rw [KExpr.mkVar_shape]
            refine .var (A := A) ?_
            simpa only [UInt64.add_zero, hdepth] using
              W.find?_hit_rev hfind
          · simp only [abstractFVarPositions_singleton_miss heq]
            exact .fvar (W.find?_fvar_ne_rev heq hfind)
  | @sort u md =>
      rw [KExpr.mkSort_shape] at H
      cases H with
      | sort hu =>
          exact .sort hu
  | @const id us md =>
      rw [KExpr.mkConst_shape] at H
      cases H with
      | const hname hconst hus hsize =>
          exact .const hname hconst hus hsize
  | @app f arg md hf harg ihf iharg =>
      rw [KExpr.mkApp_shape] at H
      cases H with
      | @app _ _ _ _ fV argV A B hfun hargTy hfTr hargTr =>
          have hbig' : depth.toNat + (f.size + arg.size + 1) + 1 <
              UInt64.size := hbig
          rw [KExpr.mkApp_shape, KExpr.abstractFVarsSpec,
            KExpr.mkApp_shape]
          exact .app (W.toCtx_eq.symm ▸ hfun) (W.toCtx_eq.symm ▸ hargTy)
            (ihf hfTr W hdepth (by omega))
            (iharg hargTr W hdepth (by omega))
  | @lam name bi ty inner md hty hinner ihty ihinner =>
      rw [KExpr.mkLam_shape] at H
      cases H with
      | @lam _ _ _ _ _ _ tyV innerV htyType htyTr hinnerTr =>
          have hbig' : depth.toNat + (ty.size + inner.size + 1) + 1 <
              UInt64.size := hbig
          have hsucc : (depth + 1).toNat = dk + 1 := by
            rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl,
              hdepth]
            exact Nat.mod_eq_of_lt
              (Nat.lt_of_le_of_lt (by omega) hbig')
          rw [KExpr.mkLam_shape, KExpr.abstractFVarsSpec,
            KExpr.mkLam_shape]
          exact .lam (W.toCtx_eq.symm ▸ htyType)
            (ihty htyTr W hdepth (by omega))
            (ihinner hinnerTr W.succ hsucc (by rw [hsucc]; omega))
  | @all name bi ty inner md hty hinner ihty ihinner =>
      rw [KExpr.mkAll_shape] at H
      cases H with
      | @all _ _ _ _ _ _ tyV innerV htyType hinnerType htyTr hinnerTr =>
          have hbig' : depth.toNat + (ty.size + inner.size + 1) + 1 <
              UInt64.size := hbig
          have hsucc : (depth + 1).toNat = dk + 1 := by
            rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl,
              hdepth]
            exact Nat.mod_eq_of_lt
              (Nat.lt_of_le_of_lt (by omega) hbig')
          rw [KExpr.mkAll_shape, KExpr.abstractFVarsSpec,
            KExpr.mkAll_shape]
          exact .all (W.toCtx_eq.symm ▸ htyType)
            (by simpa [W.toCtx_eq] using hinnerType)
            (ihty htyTr W hdepth (by omega))
            (ihinner hinnerTr W.succ hsucc (by rw [hsucc]; omega))
  | @letE name ty val inner nondep md hty hval hinner ihty ihval ihinner =>
      rw [KExpr.mkLet_shape] at H
      cases H with
      | @letE _ _ _ _ _ _ _ tyV valV innerV hvalType htyTr hvalTr
          hinnerTr =>
          have hbig' : depth.toNat +
              (ty.size + val.size + inner.size + 1) + 1 < UInt64.size :=
            hbig
          have hsucc : (depth + 1).toNat = dk + 1 := by
            rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl,
              hdepth]
            exact Nat.mod_eq_of_lt
              (Nat.lt_of_le_of_lt (by omega) hbig')
          rw [KExpr.mkLet_shape, KExpr.abstractFVarsSpec,
            KExpr.mkLet_shape]
          exact .letE (W.toCtx_eq.symm ▸ hvalType)
            (ihty htyTr W hdepth (by omega))
            (ihval hvalTr W hdepth (by omega))
            (ihinner hinnerTr W.succ hsucc (by rw [hsucc]; omega))
  | @prj id field val md hval ihval =>
      rw [KExpr.mkPrj_shape] at H
      cases H with
      | @prj _ _ _ _ _ structName valueV resultV hname hvalTr hproj =>
          rw [KExpr.mkPrj_shape, KExpr.abstractFVarsSpec,
            KExpr.mkPrj_shape]
          exact .prj hname (ihval hvalTr W hdepth (by
            rw [KExpr.mkPrj_shape] at hbig
            change depth.toNat + (val.size + 1) + 1 < UInt64.size at hbig
            omega)) (W.toCtx_eq.symm ▸ hproj)
  | @nat value blob md =>
      rw [KExpr.mkNat_shape] at H
      cases H with
      | nat hlit =>
          exact .nat hlit
  | @str value blob md =>
      rw [KExpr.mkStr_shape] at H
      cases H with
      | str hlit =>
          exact .str hlit

/-- Entry-depth form used after `openBinder`/`openLet`. -/
theorem TrKExprS.closeFVarZero
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    {Delta : KVLCtx} {decl : VLocalDecl}
    {body : KExpr .anon} {bodyV : VExpr}
    {fv : FVarId} {deps : List FVarId}
    (H : TrKExprS env uvars nameOf trProj
      ((some (fv, deps), decl) :: Delta) body bodyV)
    (hbounds : WalkerRequest.Bounds (.abstractFVars body #[fv])) :
    TrKExprS env uvars nameOf trProj ((none, decl) :: Delta)
      (KExpr.abstractFVarsSpec body (abstractFVarPositions #[fv]) 1 0)
      bodyV := by
  apply H.closeFVarSpec hbounds.1 (.zero (fvData := (fv, deps))) rfl
  have hbig := hbounds.2.2.2
  change body.lbr.toNat + body.size + 1 < UInt64.size at hbig
  have : body.size + 1 < UInt64.size := by omega
  simpa using this

/-- The API-level fast path is semantically identical to the singleton
abstraction specification under its audited bounds. -/
theorem TrKExprS.closeFVarResult
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    {Delta : KVLCtx} {decl : VLocalDecl}
    {body : KExpr .anon} {bodyV : VExpr}
    {fv : FVarId} {deps : List FVarId}
    (H : TrKExprS env uvars nameOf trProj
      ((some (fv, deps), decl) :: Delta) body bodyV)
    (hbounds : WalkerRequest.Bounds (.abstractFVars body #[fv])) :
    TrKExprS env uvars nameOf trProj ((none, decl) :: Delta)
      (KExpr.abstractFVarsResult body #[fv]) bodyV := by
  have hspec := H.closeFVarZero hbounds
  unfold KExpr.abstractFVarsResult
  change TrKExprS env uvars nameOf trProj ((none, decl) :: Delta)
    (if #[fv].isEmpty || (!body.hasFVars && body.lbr == 0) then body
      else KExpr.abstractFVarsSpec body
        (abstractFVarPositions #[fv]) 1 0) bodyV
  split
  · next hfast =>
      have hnotEmpty : (#[fv] : Array FVarId).isEmpty = false := rfl
      have hfastRaw : (!body.hasFVars) = true ∧ body.lbr = 0 := by
        simpa only [hnotEmpty, Bool.false_or, Bool.and_eq_true,
          beq_iff_eq] using hfast
      have hfast' : body.hasFVars = false ∧ body.lbr = 0 := by
        cases hbody : body.hasFVars <;> simp_all
      have hid := KExpr.abstractFVarsSpec_id
        (pos := abstractFVarPositions #[fv]) (n := 1) (depth := 0)
        hbounds.1 (by simpa using hbounds.2.2.1) hfast'.1
        (by rw [hfast'.2];
            exact UInt64.le_iff_toNat_le.mpr (Nat.le_refl 0))
      rw [hid] at hspec
      exact hspec
  · exact hspec

/-- Finite closure needed to abstract one dynamically allocated fvar from
any supported recursive result.  `FVarId` itself is finite, and the body
quantifier is restricted to the finite run support. -/
structure SingletonAbstractionResources (support : RunSupport) : Prop where
  bounds : ∀ {body : KExpr .anon}, support body → ∀ fv : FVarId,
    WalkerRequest.Bounds (.abstractFVars body #[fv])
  reach : ∀ {body : KExpr .anon}, support body → ∀ fv x,
    KExpr.AbstractReach (abstractFVarPositions #[fv])
      #[fv].size.toUInt64 body 0 x → support x

namespace RunAssumptions

/-- Request-independent operational/semantic closing rule.  This is the
form needed by recursive callbacks, whose freshly allocated id is not known
when a concrete execution request list is formed. -/
theorem abstractFVars_close_whnf_wf_of_resources
    {support : RunSupport}
    (hcollision : support.CollisionFree)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {decl : VLocalDecl}
    {body : KExpr .anon} {bodyV : VExpr}
    {fv : FVarId} {deps : List FVarId}
    (hbounds : WalkerRequest.Bounds (.abstractFVars body #[fv]))
    (hreach : ∀ x, KExpr.AbstractReach (abstractFVarPositions #[fv])
      #[fv].size.toUInt64 body 0 x → support x)
    (hbody : TrKExprS world.venv uvars world.nameOf trProj
      ((some (fv, deps), decl) :: Delta) body bodyV)
    {s : TcState .anon} :
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars
        ((some (fv, deps), decl) :: Delta)) s
      (TcM.runIntern (abstractFVars body #[fv]))
      (fun result after =>
        result = KExpr.abstractFVarsResult body #[fv] ∧
          support result ∧ InternUpdateFrame s after ∧
          TrKExprS world.venv uvars world.nameOf trProj
            ((none, decl) :: Delta) result bodyV) := by
  have hresultTr := hbody.closeFVarResult hbounds
  have hresultSupport : support (KExpr.abstractFVarsResult body #[fv]) := by
    unfold KExpr.abstractFVarsResult
    split
    · exact hreach body
        (KExpr.AbstractReach.self (abstractFVarPositions #[fv])
          #[fv].size.toUInt64 body 0)
    · exact hreach _
        (KExpr.AbstractReach.spec (abstractFVarPositions #[fv])
          #[fv].size.toUInt64 body 0)
  apply TcM.WF.mono
    (TcM.runIntern_whnf_wf (fun it hwf hsupport =>
      abstractFVars_support_spec hcollision hbounds hreach hwf hsupport))
  · intro result after hpost
    rcases hpost with ⟨rfl, hframe⟩
    exact ⟨rfl, hresultSupport, hframe, hresultTr⟩
  · intro _ _ herror
    exact herror

/-- Execution-list specialization used when the abstraction request is
known statically. -/
theorem abstractFVars_close_whnf_wf
    {alpha : Type} {initial : TcState .anon}
    {program : TcM .anon alpha} {requests : List WalkerRequest}
    {support : RunSupport}
    (h : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {decl : VLocalDecl}
    {body : KExpr .anon} {bodyV : VExpr}
    {fv : FVarId} {deps : List FVarId}
    (hmem : WalkerRequest.abstractFVars body #[fv] ∈ requests)
    (hbody : TrKExprS world.venv uvars world.nameOf trProj
      ((some (fv, deps), decl) :: Delta) body bodyV)
    {s : TcState .anon} :
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars
        ((some (fv, deps), decl) :: Delta)) s
      (TcM.runIntern (abstractFVars body #[fv]))
      (fun result after =>
        result = KExpr.abstractFVarsResult body #[fv] ∧
          support result ∧ InternUpdateFrame s after ∧
          TrKExprS world.venv uvars world.nameOf trProj
            ((none, decl) :: Delta) result bodyV) :=
  abstractFVars_close_whnf_wf_of_resources h.collisionFree
    (h.requestBounds hmem) (h.coverage.abstractFVars hmem) hbody

end RunAssumptions

namespace SingletonAbstractionResources

/-- Package the generic closing theorem through the finite recursive-result
resource used by lambda and let inference. -/
theorem close_whnf_wf
    {support : RunSupport}
    (hresources : SingletonAbstractionResources support)
    (hcollision : support.CollisionFree)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {decl : VLocalDecl}
    {body : KExpr .anon} {bodyV : VExpr}
    {fv : FVarId} {deps : List FVarId}
    (hbodySupport : support body)
    (hbody : TrKExprS world.venv uvars world.nameOf trProj
      ((some (fv, deps), decl) :: Delta) body bodyV)
    {s : TcState .anon} :
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars
        ((some (fv, deps), decl) :: Delta)) s
      (TcM.runIntern (abstractFVars body #[fv]))
      (fun result after =>
        result = KExpr.abstractFVarsResult body #[fv] ∧
          support result ∧ InternUpdateFrame s after ∧
          TrKExprS world.venv uvars world.nameOf trProj
            ((none, decl) :: Delta) result bodyV) :=
  RunAssumptions.abstractFVars_close_whnf_wf_of_resources hcollision
    (hresources.bounds hbodySupport fv)
    (hresources.reach hbodySupport fv) hbody

end SingletonAbstractionResources

end Ix.Tc
