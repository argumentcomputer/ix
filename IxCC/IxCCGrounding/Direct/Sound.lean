import IxCCGrounding.Direct.Rules

/-!
# The direct route is sound (`IxCCGrounding.Direct.Sound`)

**Part F.** `direct_sound`: in every model with the laws, at every assignment one of the
profiles stands for, every function of the checker establishes its judgement, by one induction
on the fuel. Laws used: `defn_value` (δ), `cval_params` (through `den_inst` and `den_inst_exact`: a
constant at its levels, δ and ι at levels), `proj_ctor` (the projection of a constructor, at a
structure that is never a proposition), `iota_rule` (ι at a recursor of an inductive
without indices) and `nat_accel` (a `Nat` primitive on literals). Not used: `ctor_canon`.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel

universe w

section Sem

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv} {M : Model V env}
  {φ : LevelParam → Nat}

/-- **The checker's soundness, at one fuel.** -/
structure DirectSound (M : Model V env) (φ : LevelParam → Nat) (x : DCtx) (n : Nat) : Prop where
  infer : ∀ Γ e T, dInfer x n Γ e = some T → HasTy M φ Γ e T
  sort : ∀ Γ T u, dSort x n Γ T = some u → HasTy M φ Γ T (.sort u)
  check : ∀ Γ a A, dCheck x n Γ a A = true → ChecksAt M φ Γ a A
  fits : ∀ Γ T as, dFits x n Γ T as = true → FitsAt M φ Γ T as
  whnf : ∀ δ Γ e e', whnfD x n δ Γ e = some e' → Reduces M φ Γ e e'
  conv : ∀ Γ T A, convD x n Γ T A = true → DenEq M φ Γ T A
  struct : ∀ Γ T A, convStruct x n Γ T A = true → DenEq M φ Γ T A
  args : ∀ Γ ps qs, convArgs x n Γ ps qs = true → ∀ ρ, CtxSat M φ Γ ρ → ∀ Ys Ys',
    DenotesList M.cval env φ ρ ps Ys → DenotesList M.cval env φ ρ qs Ys' → Ys = Ys'

theorem headPi_reduces {Γ : List KExpr} {w : KExpr → Option KExpr} {T T' : KExpr}
    (hw : ∀ T'', w T = some T'' → Reduces M φ Γ T T'') (h : headPi w T = some T') :
    Reduces M φ Γ T T' := by
  unfold headPi at h
  split at h
  · cases h; exact reduces_refl
  · exact hw T' h

/-! ## Walks along a spine -/

theorem walkArgs_hasTy {Γ : List KExpr} {step : KExpr → KExpr → Option KExpr}
    (hstep : ∀ T a T', step T a = some T' → ∀ F, HasTy M φ Γ F T → HasTy M φ Γ (.app F a) T') :
    ∀ (args : List KExpr) (h T T' : KExpr), walkArgs step T args = some T' → HasTy M φ Γ h T →
      HasTy M φ Γ (Expr.mkAppN h args) T'
  | [], _, _, _, hw, hT => by simp only [walkArgs, Option.some.injEq] at hw; subst hw; exact hT
  | a :: as, h, T, T', hw, hT => by
    simp only [walkArgs] at hw
    split at hw
    · rename_i T1 h1
      exact walkArgs_hasTy hstep as (.app h a) T1 T' hw (hstep T a T1 h1 h hT)
    · cases hw

theorem walkCount_sites {Γ : List KExpr} {step : KExpr → KExpr → Option KExpr}
    (hstep : ∀ T a T', step T a = some T' → ∀ F, HasTy M φ Γ F T →
      HasTy M φ Γ (.app F a) T' ∧ (DenotesIn M φ Γ (.app F a) → SiteOk M φ Γ F a)) :
    ∀ (args : List KExpr) (h T : KExpr), HasTy M φ Γ h T → DenotesIn M φ Γ (Expr.mkAppN h args) →
      ∀ s ∈ (spineSites Γ h args).take (walkCount step T args), SiteOk M φ s.1 s.2.1 s.2.2
  | [], _, _, _, _, s, hs => by simp [spineSites] at hs
  | a :: as, h, T, hT, hD, s, hs => by
    simp only [walkCount, spineSites] at hs
    split at hs
    · rename_i T1 h1
      obtain ⟨hT1, hsite⟩ := hstep T a T1 h1 h hT
      simp only [List.take_succ_cons, List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact hsite (denotesIn_mkAppN_head as hD)
      · exact walkCount_sites hstep as (.app h a) T1 hT1 hD s hs
    · simp at hs

/-! ## Fuel zero -/

theorem directSound_zero {x : DCtx} : DirectSound M φ x 0 where
  infer := by intro _ _ _ h; simp [dInfer] at h
  sort := by intro _ _ _ h; simp [dSort] at h
  check := by intro _ _ _ h; simp [dCheck] at h
  fits := by intro _ _ _ h; simp [dFits] at h
  whnf := by intro _ _ _ _ h; simp [whnfD] at h
  conv := by intro _ _ _ h; simp [convD] at h
  struct := by intro _ _ _ h; simp [convStruct] at h
  args := by intro _ _ _ h; simp [convArgs] at h

/-! ## One fuel more -/

section Succ

variable (hL : Laws M) (hN : NatBasis env) {x : DCtx} (hx : x.Reads env) (hφ : AtProf φ x)
  {n : Nat} (IH : DirectSound M φ x n)
include IH

include hφ in
/-- **One application along a spine, at this fuel** (`dStep x n` reduces and checks at `n`). -/
theorem step_of : ∀ site Γ T a T', dStep x n site Γ T a = some T' → ∀ F,
    HasTy M φ Γ F T →
    HasTy M φ Γ (.app F a) T' ∧ (site = true → DenotesIn M φ Γ (.app F a) → SiteOk M φ Γ F a) := by
  intro site Γ T a T' h F hF
  unfold dStep stepWith at h
  split at h
  · rename_i A B m hpi
    have hr := headPi_reduces (fun T'' hw => IH.whnf true Γ T T'' hw) hpi
    have hF' := hasTy_of_reduces hF hr
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hc
      have ha := IH.check Γ a A hc.2
      refine ⟨hasTy_app hF' ha, fun hs hD => ?_⟩
      subst hs
      rcases hc.1 with h0 | h1
      · cases h0
      · exact siteOk_of_pi hF' ha (regime_of_pwFalse hφ h1) hD
    · cases h
  · cases h

include hL hN hx hφ in
theorem infer_succ : ∀ Γ e T, dInfer x (n + 1) Γ e = some T → HasTy M φ Γ e T := by
  intro Γ e T h
  cases e with
  | bvar i =>
    simp only [dInfer, Option.map_eq_some_iff] at h
    obtain ⟨A, hA, rfl⟩ := h
    exact hasTy_bvar hA
  | const k us =>
    simp only [dInfer] at h
    split at h
    · rename_i ci hf
      split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true] at hc
        exact hasTy_const hL ((hx k).symm.trans hf) hc.2
      · cases h
    · cases h
  | app f a =>
    have he := mkAppN_getApp (Expr.app f a)
    unfold dInfer at h
    split at h
    · rename_i D b m a1 rest hfn hargs
      split at h
      · rename_i hc
        rw [hfn, hargs] at he
        rw [← he]
        exact hasTy_of_reduct (IH.infer Γ _ T h) (reduces_beta rest (IH.check Γ a1 D hc))
      · cases h
    · split at h
      · rename_i T0 hT0
        rw [← he]
        exact walkArgs_hasTy (fun T a T' hs F hF => (step_of hφ IH false Γ T a T' hs F hF).1)
          _ _ T0 T h (IH.infer Γ _ T0 hT0)
      · cases h
  | lit l =>
    cases l with
    | natVal k => simp only [dInfer, Option.some.injEq] at h; subst h; exact hasTy_lit hN
    | strVal s =>
      simp only [dInfer] at h
      exact hasTy_of_reduct (IH.infer Γ _ T h) reduces_strLit
  | sort u => simp only [dInfer, Option.some.injEq] at h; subst h; exact hasTy_sort
  | forallE A B m =>
    simp only [dInfer] at h
    split at h
    · rename_i u v hu hv
      split at h
      · rename_i hz
        cases h
        exact hasTy_pi (IH.sort Γ A u hu) (IH.sort _ B v hv) (zeroAt_holds hφ hz)
      · cases h
    · cases h
  | lam D b m =>
    simp only [dInfer] at h
    split at h
    · rename_i hf
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨Tb, hTb, rfl⟩ := h
      exact hasTy_lam (regime_of_pwFalse hφ hf) (IH.infer _ b Tb hTb)
    · cases h
  | _ => simp [dInfer] at h

include hL hx in
theorem whnf_succ : ∀ δ Γ e e', whnfD x (n + 1) δ Γ e = some e' → Reduces M φ Γ e e' := by
  intro δ Γ e e' h
  have he := mkAppN_getApp e
  unfold whnfD at h
  split at h
  · rename_i D b m a1 rest hfn hargs
    split at h
    · cases h; exact reduces_refl
    · rename_i k e2 hb
      rw [hfn, hargs] at he
      rw [← he]
      have hr := betaStar_reduces (fun a A hc => IH.check Γ a A hc) (a1 :: rest) (.lam D b m)
      rw [hb] at hr
      exact reduces_trans hr (IH.whnf δ Γ _ _ h)
  · rename_i k us hfn
    split at h
    · -- a `Nat` primitive on literals
      rename_i e2 hp
      rw [hfn] at he
      rw [← he]
      exact reduces_trans (primStep_sound hL (fun a a' hw => IH.whnf true Γ a a' hw) hp)
        (IH.whnf δ Γ _ _ h)
    · split at h
      · -- ι
        rename_i _ e2 hi
        rw [hfn] at he
        rw [← he]
        exact reduces_trans (iotaStep_sound hL hx (fun a a' hw => IH.whnf true Γ a a' hw)
          (fun T as hf => IH.fits Γ T as hf) (fun ps qs hc => IH.args Γ ps qs hc) hi)
          (IH.whnf δ Γ _ _ h)
      · split at h
        · rename_i _ _ cv val hint hf
          split at h
          · rename_i hc
            simp only [Bool.and_eq_true, beq_iff_eq] at hc
            rw [hfn] at he
            rw [← he]
            exact reduces_trans (reduces_delta hL ((hx k).symm.trans hf) hc.2 _) (IH.whnf δ Γ _ _ h)
          · cases h; exact reduces_refl
        · cases h; exact reduces_refl
  · rename_i s i p hfn
    split at h
    · rename_i p' hp
      split at h
      · rename_i ck cus np nf cargs entry hca hfp
        obtain ⟨hpfn, ⟨cv0, hck0⟩, hpargs⟩ := ctorApp?_spec hca
        split at h
        · rename_i cvC np1 nf1 fi hfc hfi
          rw [hck0] at hfc
          cases hfc
          split at h
          · rename_i hc
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
            obtain ⟨⟨⟨⟨⟨⟨hct, hns⟩, _⟩, hlen⟩, _⟩, hdef⟩, hfits⟩ := hc
            rw [hfn] at he
            rw [← he]
            exact reduces_trans
              (reduces_proj hL _ (IH.whnf δ Γ p p' hp) hpfn hpargs ((hx _).symm.trans hck0)
                ((DCtx.findProj?_eq hx s i).symm.trans hfp) hct
                (DCtx.neverProp_sound hx hns) hlen hdef (IH.fits Γ _ cargs hfits) hfi)
              (IH.whnf δ Γ _ _ h)
          · cases h; exact reduces_refl
        · cases h; exact reduces_refl
      · cases h; exact reduces_refl
    · cases h
  · cases h; exact reduces_refl

theorem sort_succ : ∀ Γ T u, dSort x (n + 1) Γ T = some u → HasTy M φ Γ T (.sort u) := by
  intro Γ T u h
  unfold dSort at h
  split at h
  · rename_i u' hT
    cases h
    exact IH.infer Γ T _ hT
  · rename_i S _ hT
    split at h
    · rename_i u' hw
      cases h
      exact hasTy_of_reduces (IH.infer Γ T S hT) (IH.whnf true Γ S _ hw)
    · cases h
  · cases h

include hφ in
theorem check_succ : ∀ Γ a A, dCheck x (n + 1) Γ a A = true → ChecksAt M φ Γ a A := by
  intro Γ a A h
  cases a with
  | lam A1 b m1 =>
    unfold dCheck at h
    split at h
    · rename_i A2 B2 m2 hpi
      simp only [Bool.and_eq_true] at h
      exact checks_lam (headPi_reduces (fun T'' hw => IH.whnf true Γ A T'' hw) hpi)
        (IH.conv Γ A1 A2 h.1.1) (regime_of_pwEq hφ h.1.2) (IH.check _ b B2 h.2)
    · cases h
  | _ =>
    unfold dCheck at h
    split at h
    · rename_i T hT
      exact checks_of_hasTy (IH.infer Γ _ T hT) (IH.conv Γ T A h)
    · cases h

theorem fits_succ : ∀ Γ T as, dFits x (n + 1) Γ T as = true → FitsAt M φ Γ T as := by
  intro Γ T as h
  unfold dFits at h
  exact fitsWith_sound (fun a A hc => IH.check Γ a A hc) as T h

theorem args_succ : ∀ Γ ps qs, convArgs x (n + 1) Γ ps qs = true → ∀ ρ, CtxSat M φ Γ ρ →
    ∀ Ys Ys', DenotesList M.cval env φ ρ ps Ys → DenotesList M.cval env φ ρ qs Ys' → Ys = Ys' := by
  intro Γ ps qs h ρ hρ Ys Ys' hY hY'
  cases ps with
  | nil =>
    cases qs with
    | nil => cases hY; cases hY'; rfl
    | cons _ _ => simp [convArgs] at h
  | cons p ps =>
    cases qs with
    | nil => simp [convArgs] at h
    | cons q qs =>
      simp only [convArgs, Bool.and_eq_true] at h
      cases hY with
      | cons hp hps =>
        cases hY' with
        | cons hq hqs =>
          rw [IH.conv Γ p q h.1 ρ hρ _ _ hp hq, IH.args Γ ps qs h.2 ρ hρ _ _ hps hqs]

include hφ in
theorem struct_succ : ∀ Γ T A, convStruct x (n + 1) Γ T A = true → DenEq M φ Γ T A := by
  intro Γ T A h
  rcases T with _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _⟩ | _ <;>
    rcases A with _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _⟩ | _ <;>
    simp only [convStruct] at h <;>
    first
    | (simp only [Bool.and_eq_true] at h
       exact denEq_pi (regime_of_pwEq hφ h.1.1) (IH.conv _ _ _ h.1.2) (IH.conv _ _ _ h.2))
    | (simp only [Bool.and_eq_true] at h
       exact denEq_lam (regime_of_pwEq hφ h.1.1) (IH.conv _ _ _ h.1.2) (IH.conv _ _ _ h.2))
    | (simp only [Bool.and_eq_true] at h
       exact denEq_natLit_left (IH.conv _ _ _ h.2))
    | (simp only [Bool.and_eq_true] at h
       exact denEq_natLit_right (IH.conv _ _ _ h.2))
    | (simp only [Bool.and_eq_true, beq_iff_eq] at h
       exact denEq_spine (fun ρ _ Y Y' hY hY' => eqUpTo_sound hφ _ _ h.1.2 ρ Y Y' hY hY')
         (IH.args _ _ _ h.2))
    | (simp at h)

include hφ in
theorem conv_succ : ∀ Γ T A, convD x (n + 1) Γ T A = true → DenEq M φ Γ T A := by
  intro Γ T A h
  unfold convD at h
  simp only [Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · rw [beq_iff_eq.mp h]; exact denEq_refl_syn
  · exact fun ρ _ Y Y' hY hY' => eqUpTo_sound hφ _ _ h ρ Y Y' hY hY'
  · split at h
    · rename_i T' A' hT hA
      have hrT := IH.whnf false Γ T T' hT
      have hrA := IH.whnf false Γ A A' hA
      simp only [Bool.or_eq_true] at h
      rcases h with (h | h) | h
      · exact denEq_of_reduces hrT hrA fun ρ _ Y Y' hY hY' => eqUpTo_sound hφ _ _ h ρ Y Y' hY hY'
      · exact denEq_of_reduces hrT hrA (IH.struct Γ T' A' h)
      · split at h
        · rename_i T'' A'' hT' hA'
          simp only [Bool.and_eq_true] at h
          exact denEq_of_reduces (reduces_trans hrT (IH.whnf true Γ T' T'' hT'))
            (reduces_trans hrA (IH.whnf true Γ A' A'' hA')) (IH.conv Γ T'' A'' h.2)
        · cases h
    · cases h

end Succ

/-- **The direct route is sound**, in every model with the laws, at every assignment one of the
profiles stands for. -/
theorem direct_sound (hL : Laws M) (hN : NatBasis env) {x : DCtx} (hx : x.Reads env)
    (hφ : AtProf φ x) : ∀ n, DirectSound M φ x n
  | 0 => directSound_zero
  | n + 1 =>
    have IH := direct_sound hL hN hx hφ n
    { infer := infer_succ hL hN hx hφ IH
      sort := sort_succ IH
      check := check_succ hφ IH
      fits := fits_succ IH
      whnf := whnf_succ hL hx IH
      conv := conv_succ hφ IH
      struct := struct_succ hφ IH
      args := args_succ IH }

end Sem

end IxCC.Grounding
