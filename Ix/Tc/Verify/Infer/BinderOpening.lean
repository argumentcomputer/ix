import Ix.Tc.Verify.Infer.ScopedLocals

/-!
# Semantic binder opening for inference

Inference replaces one de Bruijn binder with a freshly minted free variable
before making its recursive call.  The concrete syntax loses one bvar, but
the Theory context keeps the same local declaration.  This module models
that retagging and proves that `instantiateRev` preserves the translated
Theory expression.
-/

namespace Ix.Tc

open Lean4Lean (VExpr VLocalDecl)

namespace KVLCtx

variable (fvData : FVarId × List FVarId) (decl : VLocalDecl) in
/-- Retag one de Bruijn local as a free-variable local at a given syntactic
binder depth.  The Theory context is unchanged. -/
inductive RetagFVar : Nat → KVLCtx → KVLCtx → Prop
  | zero {Delta : KVLCtx} :
      RetagFVar 0 ((none, decl) :: Delta) ((some fvData, decl) :: Delta)
  | succ {depth : Nat} {source target : KVLCtx} {d : VLocalDecl} :
      RetagFVar depth source target →
      RetagFVar (depth + 1) ((none, d) :: source) ((none, d) :: target)

theorem RetagFVar.toCtx_eq
    {fvData : FVarId × List FVarId} {decl : VLocalDecl}
    {depth : Nat} {source target : KVLCtx}
    (W : RetagFVar fvData decl depth source target) :
    source.toCtx = target.toCtx := by
  induction W with
  | zero => cases decl <;> rfl
  | @succ depth source target d W ih =>
      cases d <;> simp [KVLCtx.toCtx, ih]

theorem RetagFVar.find?_hit
    {fvData : FVarId × List FVarId} {decl : VLocalDecl}
    {depth : Nat} {source target : KVLCtx}
    (W : RetagFVar fvData decl depth source target) :
    ∀ {e A : VExpr}, source.find? (.inl depth) = some (e, A) →
      target.find? (.inr fvData.1) = some (e, A) := by
  induction W with
  | zero =>
      intro e A H
      simp [find?, next] at H ⊢
      exact H
  | @succ depth source target d _ ih =>
      intro e A H
      simp [find?, next] at H ⊢
      obtain ⟨e', A', H, rfl, rfl⟩ := H
      exact ⟨_, _, ih H, rfl, rfl⟩

theorem RetagFVar.find?_lt
    {fvData : FVarId × List FVarId} {decl : VLocalDecl}
    {depth : Nat} {source target : KVLCtx}
    (W : RetagFVar fvData decl depth source target) :
    ∀ {j : Nat} {e A : VExpr}, j < depth →
      source.find? (.inl j) = some (e, A) →
      target.find? (.inl j) = some (e, A) := by
  induction W with
  | zero => intro j e A hj; omega
  | @succ depth source target d _ ih =>
      intro j e A hj H
      cases j with
      | zero => simpa [find?, next] using H
      | succ j =>
          simp [find?, next] at H ⊢
          obtain ⟨e', A', H, rfl, rfl⟩ := H
          exact ⟨_, _, ih (by omega) H, rfl, rfl⟩

theorem RetagFVar.find?_gt
    {fvData : FVarId × List FVarId} {decl : VLocalDecl}
    {depth : Nat} {source target : KVLCtx}
    (W : RetagFVar fvData decl depth source target) :
    ∀ {j : Nat} {e A : VExpr}, depth < j →
      source.find? (.inl j) = some (e, A) →
      target.find? (.inl (j - 1)) = some (e, A) := by
  induction W with
  | zero =>
      intro j e A hj H
      cases j with
      | zero => omega
      | succ j => simpa [find?, next] using H
  | @succ depth source target d _ ih =>
      intro j e A hj H
      cases j with
      | zero => omega
      | succ j =>
          cases j with
          | zero => omega
          | succ j =>
              simp [find?, next] at H ⊢
              obtain ⟨e', A', H, rfl, rfl⟩ := H
              exact ⟨_, _, ih (by omega) H, rfl, rfl⟩

theorem RetagFVar.find?_fvar
    {fvData : FVarId × List FVarId} {decl : VLocalDecl}
    {depth : Nat} {source target : KVLCtx}
    (W : RetagFVar fvData decl depth source target)
    (hfresh : fvData.1 ∉ source.fvars) :
    ∀ {fv : FVarId} {e A : VExpr},
      source.find? (.inr fv) = some (e, A) →
      target.find? (.inr fv) = some (e, A) := by
  induction W with
  | @zero Delta =>
      intro fv e A H
      have hmem : fv ∈ Delta.fvars := by
        simpa using find?_inr_mem H
      have hne : fvData.1 ≠ fv := fun heq =>
        hfresh (by simpa [heq] using hmem)
      simp [find?, next, hne] at H ⊢
      exact H
  | @succ depth source target d _ ih =>
      intro fv e A H
      simp only [fvars_cons_none] at hfresh
      simp [find?, next] at H ⊢
      obtain ⟨e', A', H, rfl, rfl⟩ := H
      exact ⟨_, _, ih hfresh H, rfl, rfl⟩

end KVLCtx

/-- Replacing one de Bruijn binder with its freshly tagged fvar leaves the
Theory expression unchanged. -/
theorem TrKExprS.openFVar
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    {source : KVLCtx} {body : KExpr .anon} {bodyV : VExpr}
    (H : TrKExprS env uvars nameOf trProj source body bodyV) :
    ∀ {fvData : FVarId × List FVarId} {decl : VLocalDecl}
      {target : KVLCtx} {dk : Nat} {depth : UInt64}
      {name : Mode.anon.F Name},
      KVLCtx.RetagFVar fvData decl dk source target →
      depth.toNat = dk →
      fvData.1 ∉ source.fvars →
      depth.toNat + body.size + 1 < UInt64.size →
      TrKExprS env uvars nameOf trProj target
        (KExpr.instantiateRevSpec body #[.mkFVar fvData.1 name] depth)
        bodyV := by
  induction H with
  | @var source i name info e A hfind =>
      intro fvData decl target dk depth fvName W hdepth hfresh hbig
      rw [KExpr.instantiateRevSpec]
      have harrSize :
          #[KExpr.mkFVar fvData.1 fvName].size.toUInt64 = 1 := rfl
      rw [harrSize]
      have hsuccNat : (depth + 1).toNat = depth.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig)
      by_cases heq : i = depth
      · subst i
        have hlt : depth < depth + 1 :=
          UInt64.lt_iff_toNat_lt.mpr (by rw [hsuccNat]; omega)
        have hwindow : ((depth ≥ depth && depth < depth + 1) = true) := by
          simp [hlt]
        rw [if_pos hwindow]
        simp
        exact .fvar (W.find?_hit (by simpa [hdepth] using hfind))
      · by_cases hgt : depth < i
        · have hgeSucc : depth + 1 ≤ i :=
            UInt64.le_iff_toNat_le.mpr (by
              rw [hsuccNat]
              have := UInt64.lt_iff_toNat_lt.mp hgt
              omega)
          have hnltSucc : ¬i < depth + 1 := fun hlt => by
            have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
            have hge' := UInt64.le_iff_toNat_le.mp hgeSucc
            omega
          have hwindow : ¬((i ≥ depth && i < depth + 1) = true) := by
            simp [hnltSucc]
          rw [if_neg hwindow, if_pos hgeSucc, KExpr.mkVar_shape]
          refine .var (A := A) ?_
          have hOneLe : (1 : UInt64) ≤ i :=
            UInt64.le_iff_toNat_le.mpr (by
              have := UInt64.lt_iff_toNat_lt.mp hgt
              simp only [UInt64.toNat_ofNat]
              omega)
          rw [UInt64.toNat_sub_of_le i 1 hOneLe,
            show (1 : UInt64).toNat = 1 from rfl]
          exact W.find?_gt (by
            rw [← hdepth]
            exact UInt64.lt_iff_toNat_lt.mp hgt) hfind
        · have hlt : i.toNat < dk := by
            have hne : i.toNat ≠ depth.toNat := fun h =>
              heq (UInt64.toNat_inj.mp h)
            have hnlt : ¬depth.toNat < i.toNat := fun h =>
              hgt (UInt64.lt_iff_toNat_lt.mpr h)
            omega
          have hnge : ¬i ≥ depth := fun h => by
            have hle := UInt64.le_iff_toNat_le.mp h
            have hne : depth.toNat ≠ i.toNat := fun hEq =>
              heq (UInt64.toNat_inj.mp hEq.symm)
            exact hgt (UInt64.lt_iff_toNat_lt.mpr (by omega))
          have hngeSucc : ¬i ≥ depth + 1 := fun h =>
            hnge (UInt64.le_iff_toNat_le.mpr (by
              have h' := UInt64.le_iff_toNat_le.mp h
              rw [hsuccNat] at h'
              omega))
          have hwindow : ¬((i ≥ depth && i < depth + 1) = true) := by
            simp [hnge]
          rw [if_neg hwindow, if_neg hngeSucc]
          exact .var (W.find?_lt hlt hfind)
  | @fvar source fv name info e A hfind =>
      intro fvData decl target dk depth fvName W hdepth hfresh hbig
      exact .fvar (W.find?_fvar hfresh hfind)
  | @sort source u info hu =>
      intro fvData decl target dk depth fvName W hdepth hfresh hbig
      exact .sort hu
  | @const source id us info cname ci hname hconst hus hsize =>
      intro fvData decl target dk depth fvName W hdepth hfresh hbig
      exact .const hname hconst hus hsize
  | @app source f a info fV aV A B hfun harg hf ha ihf iha =>
      intro fvData decl target dk depth fvName W hdepth hfresh hbig
      have hbig' : depth.toNat + (f.size + a.size + 1) + 1 <
          UInt64.size := hbig
      rw [KExpr.instantiateRevSpec, KExpr.mkApp_shape]
      exact .app (W.toCtx_eq ▸ hfun) (W.toCtx_eq ▸ harg)
        (ihf W hdepth hfresh (by omega))
        (iha W hdepth hfresh (by omega))
  | @lam source name bi ty body info tyV bodyV htype hty hbody ihty ihbody =>
      intro fvData decl target dk depth fvName W hdepth hfresh hbig
      have hbig' : depth.toNat + (ty.size + body.size + 1) + 1 <
          UInt64.size := hbig
      have hsucc : (depth + 1).toNat = dk + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl,
          hdepth]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig')
      rw [KExpr.instantiateRevSpec, KExpr.mkLam_shape]
      exact .lam (W.toCtx_eq ▸ htype)
        (ihty W hdepth hfresh (by omega))
        (ihbody W.succ hsucc (by simpa using hfresh) (by
          rw [hsucc]
          omega))
  | @all source name bi ty body info tyV bodyV htyType hbodyType hty hbody
      ihty ihbody =>
      intro fvData decl target dk depth fvName W hdepth hfresh hbig
      have hbig' : depth.toNat + (ty.size + body.size + 1) + 1 <
          UInt64.size := hbig
      have hsucc : (depth + 1).toNat = dk + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl,
          hdepth]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig')
      rw [KExpr.instantiateRevSpec, KExpr.mkAll_shape]
      exact .all (W.toCtx_eq ▸ htyType)
        (by simpa [W.toCtx_eq] using hbodyType)
        (ihty W hdepth hfresh (by omega))
        (ihbody W.succ hsucc (by simpa using hfresh) (by
          rw [hsucc]
          omega))
  | @letE source name ty val body nondep info tyV valV bodyV hvalType hty
      hval hbody ihty ihval ihbody =>
      intro fvData decl target dk depth fvName W hdepth hfresh hbig
      have hbig' : depth.toNat +
          (ty.size + val.size + body.size + 1) + 1 < UInt64.size := hbig
      have hsucc : (depth + 1).toNat = dk + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl,
          hdepth]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig')
      rw [KExpr.instantiateRevSpec, KExpr.mkLet_shape]
      exact .letE (W.toCtx_eq ▸ hvalType)
        (ihty W hdepth hfresh (by omega))
        (ihval W hdepth hfresh (by omega))
        (ihbody W.succ hsucc (by simpa using hfresh) (by
          rw [hsucc]
          omega))
  | @prj source sid field val info sName valueV resultV hname hval hproj
      ihval =>
      intro fvData decl target dk depth fvName W hdepth hfresh hbig
      have hbig' : depth.toNat + (val.size + 1) + 1 < UInt64.size := hbig
      rw [KExpr.instantiateRevSpec, KExpr.mkPrj_shape]
      exact .prj hname (ihval W hdepth hfresh (by omega))
        (W.toCtx_eq ▸ hproj)
  | @nat source value blob info hlit =>
      intro fvData decl target dk depth fvName W hdepth hfresh hbig
      exact .nat hlit
  | @str source value blob info hlit =>
      intro fvData decl target dk depth fvName W hdepth hfresh hbig
      exact .str hlit

/-- Entry-depth specialization used by the three production binder branches. -/
theorem TrKExprS.openFVarZero
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    {Delta : KVLCtx} {decl : VLocalDecl}
    {body : KExpr .anon} {bodyV : VExpr}
    {fv : FVarId} {deps : List FVarId} {name : Mode.anon.F Name}
    (H : TrKExprS env uvars nameOf trProj
      ((none, decl) :: Delta) body bodyV)
    (hfresh : fv ∉ Delta.fvars)
    (hbound : body.size + 1 < UInt64.size) :
    TrKExprS env uvars nameOf trProj
      ((some (fv, deps), decl) :: Delta)
      (KExpr.instantiateRevSpec body #[.mkFVar fv name] 0) bodyV :=
  H.openFVar .zero rfl (by simpa using hfresh) (by simpa using hbound)

end Ix.Tc
