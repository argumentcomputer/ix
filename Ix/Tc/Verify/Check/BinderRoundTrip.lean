import Ix.Tc.Verify.Check.PreTranslationScopes
import Ix.Tc.Verify.Infer.BinderClosing

/-!
# Binder open/close round trip

The Lean4Lean checker closes a freshly opened binder with
`FVarsIn.abstract_instantiate1`.  Ix uses address-carrying `KExpr` smart
constructors and separate cached walkers, so K3 needs the corresponding pure
syntax theorem for `instantiateRevSpec` followed by singleton
`abstractFVarsSpec`.
-/

namespace Ix.Tc

namespace KExpr

/-- One selected free-variable id does not occur in an expression. -/
def FVarAbsent (target : FVarId) : KExpr .anon → Prop
  | .fvar id _ _ => id ≠ target
  | .app fn arg _ => fn.FVarAbsent target ∧ arg.FVarAbsent target
  | .lam _ _ type body _ | .all _ _ type body _ =>
      type.FVarAbsent target ∧ body.FVarAbsent target
  | .letE _ type value body _ _ =>
      type.FVarAbsent target ∧ value.FVarAbsent target ∧
        body.FVarAbsent target
  | .prj _ _ value _ => value.FVarAbsent target
  | _ => True

end KExpr

namespace PreTrKExprS

/-- A pre-translation can mention only fvars registered by its `KVLCtx`. -/
theorem fvarAbsent
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {Delta : KVLCtx} {source : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    (hsource : PreTrKExprS env uvars nameOf trProj Delta source sourceV)
    {target : FVarId} (hfresh : target ∉ Delta.fvars) :
    source.FVarAbsent target := by
  induction hsource with
  | var => trivial
  | fvar hfind =>
      intro heq
      subst target
      exact hfresh (KVLCtx.find?_inr_mem hfind)
  | sort => trivial
  | const => trivial
  | app _ _ ihfn iharg => exact ⟨ihfn hfresh, iharg hfresh⟩
  | lam _ _ ihtype ihbody =>
      exact ⟨ihtype hfresh, ihbody (by simpa using hfresh)⟩
  | all _ _ ihtype ihbody =>
      exact ⟨ihtype hfresh, ihbody (by simpa using hfresh)⟩
  | letE _ _ _ ihtype ihvalue ihbody =>
      exact ⟨ihtype hfresh, ihvalue hfresh,
        ihbody (by simpa using hfresh)⟩
  | prj _ _ _ ihvalue => exact ihvalue hfresh
  | nat => trivial
  | str => trivial

end PreTrKExprS

namespace KExpr

/-- Opening one de Bruijn binder with a fresh fvar and immediately
abstracting that exact fvar reconstructs the original constructed `KExpr`.
The bound is a deliberately simple joint no-wrap condition for both walkers.
-/
theorem abstractFVarsSpec_instantiateRevSpec_singleton
    {body : KExpr .anon} {fv : FVarId} {name : Mode.anon.F Name}
    {depth : UInt64}
    (hcon : Constructed body)
    (hfresh : body.FVarAbsent fv)
    (hbig : depth.toNat + body.size + 1 < UInt64.size) :
    abstractFVarsSpec
        (instantiateRevSpec body #[.mkFVar fv name] depth)
        (abstractFVarPositions #[fv]) 1 depth = body := by
  induction hcon generalizing depth with
  | @var idx varName info hidx =>
      have hsucc : (depth + 1).toNat = depth.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig)
      rw [mkVar_shape, instantiateRevSpec]
      have hsize : #[KExpr.mkFVar fv name].size.toUInt64 = 1 := rfl
      rw [hsize]
      by_cases heq : idx = depth
      · subst idx
        have hlt : depth < depth + 1 :=
          UInt64.lt_iff_toNat_lt.mpr (by rw [hsucc]; omega)
        have hwindow :
            ((depth ≥ depth && depth < depth + 1) = true) := by
          simp [hlt]
        rw [if_pos hwindow]
        have hindex : (1 - 1 - (depth - depth)).toNat = 0 := by simp
        rw [hindex, getElem!_pos #[KExpr.mkFVar fv name] 0 (by simp)]
        change abstractFVarsSpec (KExpr.mkFVar fv name)
          (abstractFVarPositions #[fv]) 1 depth = mkVar depth varName info
        rw [mkFVar_shape, abstractFVarsSpec,
          abstractFVarPositions_singleton_hit]
        simp only [UInt64.add_zero]
      · by_cases hgt : depth < idx
        · have hgeSucc : depth + 1 ≤ idx :=
            UInt64.le_iff_toNat_le.mpr (by
              rw [hsucc]
              have := UInt64.lt_iff_toNat_lt.mp hgt
              omega)
          have hnltSucc : ¬idx < depth + 1 := fun hlt => by
            have := UInt64.lt_iff_toNat_lt.mp hlt
            have := UInt64.le_iff_toNat_le.mp hgeSucc
            omega
          have hwindow :
              ¬((idx ≥ depth && idx < depth + 1) = true) := by
            simp [hnltSucc]
          have hone : (1 : UInt64) ≤ idx :=
            UInt64.le_iff_toNat_le.mpr (by
              have := UInt64.lt_iff_toNat_lt.mp hgt
              simp only [UInt64.toNat_ofNat]
              omega)
          have honeNat : 1 ≤ idx.toNat :=
            UInt64.le_iff_toNat_le.mp hone
          have hshift : idx - 1 ≥ depth :=
            UInt64.le_iff_toNat_le.mpr (by
              rw [UInt64.toNat_sub_of_le idx 1 hone,
                show (1 : UInt64).toNat = 1 from rfl]
              have hgeSuccNat := UInt64.le_iff_toNat_le.mp hgeSucc
              rw [hsucc] at hgeSuccNat
              exact Nat.le_sub_of_add_le
                hgeSuccNat)
          have hround : idx - 1 + 1 = idx := by
            apply UInt64.toNat_inj.mp
            rw [UInt64.toNat_add, UInt64.toNat_sub_of_le idx 1 hone,
              show (1 : UInt64).toNat = 1 from rfl]
            rw [Nat.sub_add_cancel honeNat]
            exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.lt_succ_self _) hidx)
          rw [if_neg hwindow, if_pos hgeSucc, mkVar_shape,
            abstractFVarsSpec, if_pos hshift, hround]
          exact mkVar_shape idx varName info
        · have hnge : ¬idx ≥ depth := fun hge => by
            have hle := UInt64.le_iff_toNat_le.mp hge
            have hne : idx.toNat ≠ depth.toNat := fun h =>
              heq (UInt64.toNat_inj.mp h)
            exact hgt (UInt64.lt_iff_toNat_lt.mpr (by omega))
          have hwindow :
              ¬((idx ≥ depth && idx < depth + 1) = true) := by
            simp [hnge]
          have hngeSucc : ¬idx ≥ depth + 1 := fun hge =>
            hnge (UInt64.le_iff_toNat_le.mpr (by
              have hgeNat := UInt64.le_iff_toNat_le.mp hge
              rw [hsucc] at hgeNat
              omega))
          rw [if_neg hwindow, if_neg hngeSucc, abstractFVarsSpec,
            if_neg hnge]
  | @fvar id fvarName info =>
      have hne : id ≠ fv := by
        rw [mkFVar_shape] at hfresh
        exact hfresh
      rw [mkFVar_shape]
      change (match (abstractFVarPositions #[fv])[id]? with
        | some p => mkVar (depth + p) (anonName (m := .anon))
        | none => .fvar id fvarName (mkFVar id fvarName info).info) = _
      rw [abstractFVarPositions_singleton_miss hne]
  | sort => rfl
  | const => rfl
  | @app fn arg info hfn harg ihfn iharg =>
      rcases hfresh with ⟨hfnFresh, hargFresh⟩
      rw [mkApp_shape, size] at hbig
      rw [mkApp_shape, instantiateRevSpec, mkApp_shape, abstractFVarsSpec,
        ihfn (depth := depth) hfnFresh (by omega),
        iharg (depth := depth) hargFresh (by omega)]
      exact mkApp_shape fn arg info
  | @lam binderName bi type body info htype hbody ihtype ihbody =>
      rcases hfresh with ⟨htypeFresh, hbodyFresh⟩
      rw [mkLam_shape, size] at hbig
      have hsucc : (depth + 1).toNat = depth.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig)
      rw [mkLam_shape, instantiateRevSpec, mkLam_shape, abstractFVarsSpec,
        ihtype (depth := depth) htypeFresh (by omega),
        ihbody (depth := depth + 1) hbodyFresh (by rw [hsucc]; omega)]
      exact mkLam_shape binderName bi type body info
  | @all binderName bi type body info htype hbody ihtype ihbody =>
      rcases hfresh with ⟨htypeFresh, hbodyFresh⟩
      rw [mkAll_shape, size] at hbig
      have hsucc : (depth + 1).toNat = depth.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig)
      rw [mkAll_shape, instantiateRevSpec, mkAll_shape, abstractFVarsSpec,
        ihtype (depth := depth) htypeFresh (by omega),
        ihbody (depth := depth + 1) hbodyFresh (by rw [hsucc]; omega)]
      exact mkAll_shape binderName bi type body info
  | @letE binderName type value body nondep info htype hvalue hbody
      ihtype ihvalue ihbody =>
      rcases hfresh with ⟨htypeFresh, hvalueFresh, hbodyFresh⟩
      rw [mkLet_shape, size] at hbig
      have hsucc : (depth + 1).toNat = depth.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig)
      rw [mkLet_shape, instantiateRevSpec, mkLet_shape, abstractFVarsSpec,
        ihtype (depth := depth) htypeFresh (by omega),
        ihvalue (depth := depth) hvalueFresh (by omega),
        ihbody (depth := depth + 1) hbodyFresh (by rw [hsucc]; omega)]
      exact mkLet_shape binderName type value body nondep info
  | @prj id field value info hvalue ihvalue =>
      rw [mkPrj_shape, size] at hbig
      rw [mkPrj_shape, instantiateRevSpec, mkPrj_shape, abstractFVarsSpec,
        ihvalue (depth := depth) hfresh (by omega)]
      exact mkPrj_shape id field value info
  | nat => rfl
  | str => rfl

end KExpr

/-- Close a successfully inferred opened binder back to its original Ix
syntax.  The opening bounds justify the pure round trip; the closing bounds
justify the production abstraction walker whose translation theorem supplies
the typed result. -/
theorem TrKExprS.closeOpenedFVarZero
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {Delta : KVLCtx} {decl : Lean4Lean.VLocalDecl}
    {body bodyOpen : KExpr .anon} {bodyV : Lean4Lean.VExpr}
    {fv : FVarId} {deps : List FVarId} {name : Mode.anon.F Name}
    (H : TrKExprS env uvars nameOf trProj
      ((some (fv, deps), decl) :: Delta) bodyOpen bodyV)
    (hopen : bodyOpen = KExpr.instantiateRevSpec body
      #[KExpr.mkFVar fv name] 0)
    (hfresh : body.FVarAbsent fv)
    (hopenBounds : WalkerRequest.Bounds
      (.instRev body #[KExpr.mkFVar fv name]))
    (hcloseBounds : WalkerRequest.Bounds
      (.abstractFVars bodyOpen #[fv])) :
    TrKExprS env uvars nameOf trProj ((none, decl) :: Delta) body bodyV := by
  subst bodyOpen
  have hclosed := H.closeFVarZero hcloseBounds
  have hround := KExpr.abstractFVarsSpec_instantiateRevSpec_singleton
    (name := name) (depth := 0) hopenBounds.1 hfresh
      (by simpa using hopenBounds.2.2)
  rw [hround] at hclosed
  exact hclosed

end Ix.Tc
