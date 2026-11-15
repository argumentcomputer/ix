import IxVMRefinement.Core.Loaded
import IxC.Kernel.Verify.InstLevels
import IxVMRefinement.Nat.Levels
import IxVMRefinement.Obs.KernelCheck0
import Ix.IxVM.Consistency.Statement

/-! # Parameter coverage of validated annotations

The heap representation retains exact binder levels while allowing semantic equality at
sorts and constant universe arguments. The scope validator bounds the parameters used by
binder metadata. Combined with the reader's parameter coverage and `Annotates`, this bounds
all parameters of the represented output without requiring annotation to preserve metadata.
-/

namespace IxVM.Refinement.Core.Scope

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel)
open Ix.Kernel (Expr Level LevelParam)

local macro "scope_lt_calls" : tactic =>
  `(tactic| (simp only [List.length_cons, List.length_append]; omega))

private def propWhenDefined (lps : List LevelParam) : KExpr → Bool
  | .bvar _ | .sort _ | .const _ _ | .lit _ => true
  | .fvar _ ty => propWhenDefined lps ty
  | .app f a => propWhenDefined lps f && propWhenDefined lps a
  | .lam ty b m | .forallE ty b m =>
    (propWhenDefined lps ty && propWhenDefined lps b) && m.pw.paramsDefined lps
  | .letE ty v b _ =>
    (propWhenDefined lps ty && propWhenDefined lps v) && propWhenDefined lps b
  | .proj _ _ e => propWhenDefined lps e

private theorem propWhenDefined_liftLooseBVars {lps : List LevelParam} (n : Nat) :
    ∀ (e : KExpr) (c : Nat),
      propWhenDefined lps e = true →
      propWhenDefined lps (e.liftLooseBVars n c) = true
  | .bvar _, _, _ => by
    simp only [Expr.liftLooseBVars]
    split <;> rfl
  | .fvar _ _, _, h => h
  | .sort _, _, _ => rfl
  | .const _ _, _, _ => rfl
  | .lit _, _, _ => rfl
  | .app f a, c, h => by
    simp only [propWhenDefined, Bool.and_eq_true] at h
    simp only [Expr.liftLooseBVars, propWhenDefined, Bool.and_eq_true]
    exact ⟨propWhenDefined_liftLooseBVars n f c h.1,
      propWhenDefined_liftLooseBVars n a c h.2⟩
  | .lam ty b _, c, h | .forallE ty b _, c, h => by
    simp only [propWhenDefined, Bool.and_eq_true] at h
    simp only [Expr.liftLooseBVars, propWhenDefined, Bool.and_eq_true]
    exact ⟨⟨propWhenDefined_liftLooseBVars n ty c h.1.1,
      propWhenDefined_liftLooseBVars n b (c + 1) h.1.2⟩, h.2⟩
  | .letE ty v b _, c, h => by
    simp only [propWhenDefined, Bool.and_eq_true] at h
    simp only [Expr.liftLooseBVars, propWhenDefined, Bool.and_eq_true]
    exact ⟨⟨propWhenDefined_liftLooseBVars n ty c h.1.1,
      propWhenDefined_liftLooseBVars n v c h.1.2⟩,
      propWhenDefined_liftLooseBVars n b (c + 1) h.2⟩
  | .proj _ _ e, c, h => by
    simp only [propWhenDefined] at h
    simp only [Expr.liftLooseBVars, propWhenDefined]
    exact propWhenDefined_liftLooseBVars n e c h

private theorem propWhenDefined_instantiate1Lift {lps : List LevelParam} {v : KExpr}
    (hv : propWhenDefined lps v = true) :
    ∀ (b : KExpr) (j : Nat),
      propWhenDefined lps b = true →
      propWhenDefined lps (b.instantiate1Lift v j) = true
  | .bvar _, j, _ => by
    simp only [Expr.instantiate1Lift]
    split
    · exact propWhenDefined_liftLooseBVars j v 0 hv
    · split <;> rfl
  | .fvar _ _, _, hb => hb
  | .sort _, _, _ => rfl
  | .const _ _, _, _ => rfl
  | .lit _, _, _ => rfl
  | .app f a, j, hb => by
    simp only [propWhenDefined, Bool.and_eq_true] at hb
    simp only [Expr.instantiate1Lift, propWhenDefined, Bool.and_eq_true]
    exact ⟨propWhenDefined_instantiate1Lift hv f j hb.1,
      propWhenDefined_instantiate1Lift hv a j hb.2⟩
  | .lam ty b _, j, hb | .forallE ty b _, j, hb => by
    simp only [propWhenDefined, Bool.and_eq_true] at hb
    simp only [Expr.instantiate1Lift, propWhenDefined, Bool.and_eq_true]
    exact ⟨⟨propWhenDefined_instantiate1Lift hv ty j hb.1.1,
      propWhenDefined_instantiate1Lift hv b (j + 1) hb.1.2⟩, hb.2⟩
  | .letE ty val b _, j, hb => by
    simp only [propWhenDefined, Bool.and_eq_true] at hb
    simp only [Expr.instantiate1Lift, propWhenDefined, Bool.and_eq_true]
    exact ⟨⟨propWhenDefined_instantiate1Lift hv ty j hb.1.1,
      propWhenDefined_instantiate1Lift hv val j hb.1.2⟩,
      propWhenDefined_instantiate1Lift hv b (j + 1) hb.2⟩
  | .proj _ _ e, j, hb => by
    simp only [propWhenDefined] at hb
    simp only [Expr.instantiate1Lift, propWhenDefined]
    exact propWhenDefined_instantiate1Lift hv e j hb

private theorem allLevelParamsDefined_liftLooseBVars {lps : List LevelParam} (n : Nat) :
    ∀ (e : KExpr) (c : Nat),
      e.allLevelParamsDefined lps = true →
      (e.liftLooseBVars n c).allLevelParamsDefined lps = true
  | .bvar _, _, _ => by
    simp only [Expr.liftLooseBVars]
    split <;> rfl
  | .fvar _ _, _, h => h
  | .sort _, _, h => h
  | .const _ _, _, h => h
  | .lit _, _, _ => rfl
  | .app f a, c, h => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.liftLooseBVars, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨allLevelParamsDefined_liftLooseBVars n f c h.1,
      allLevelParamsDefined_liftLooseBVars n a c h.2⟩
  | .lam ty b _, c, h | .forallE ty b _, c, h => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.liftLooseBVars, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨allLevelParamsDefined_liftLooseBVars n ty c h.1.1,
      allLevelParamsDefined_liftLooseBVars n b (c + 1) h.1.2⟩, h.2⟩
  | .letE ty v b _, c, h => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.liftLooseBVars, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨allLevelParamsDefined_liftLooseBVars n ty c h.1.1,
      allLevelParamsDefined_liftLooseBVars n v c h.1.2⟩,
      allLevelParamsDefined_liftLooseBVars n b (c + 1) h.2⟩
  | .proj _ _ e, c, h => by
    simp only [Expr.allLevelParamsDefined] at h
    simp only [Expr.liftLooseBVars, Expr.allLevelParamsDefined]
    exact allLevelParamsDefined_liftLooseBVars n e c h

private theorem allLevelParamsDefined_instantiate1Lift {lps : List LevelParam} {v : KExpr}
    (hv : v.allLevelParamsDefined lps = true) :
    ∀ (b : KExpr) (j : Nat),
      b.allLevelParamsDefined lps = true →
      (b.instantiate1Lift v j).allLevelParamsDefined lps = true
  | .bvar _, j, _ => by
    simp only [Expr.instantiate1Lift]
    split
    · exact allLevelParamsDefined_liftLooseBVars j v 0 hv
    · split <;> rfl
  | .fvar _ _, _, hb => hb
  | .sort _, _, hb => hb
  | .const _ _, _, hb => hb
  | .lit _, _, _ => rfl
  | .app f a, j, hb => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hb
    simp only [Expr.instantiate1Lift, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨allLevelParamsDefined_instantiate1Lift hv f j hb.1,
      allLevelParamsDefined_instantiate1Lift hv a j hb.2⟩
  | .lam ty b _, j, hb | .forallE ty b _, j, hb => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hb
    simp only [Expr.instantiate1Lift, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨allLevelParamsDefined_instantiate1Lift hv ty j hb.1.1,
      allLevelParamsDefined_instantiate1Lift hv b (j + 1) hb.1.2⟩, hb.2⟩
  | .letE ty val b _, j, hb => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hb
    simp only [Expr.instantiate1Lift, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨allLevelParamsDefined_instantiate1Lift hv ty j hb.1.1,
      allLevelParamsDefined_instantiate1Lift hv val j hb.1.2⟩,
      allLevelParamsDefined_instantiate1Lift hv b (j + 1) hb.2⟩
  | .proj _ _ e, j, hb => by
    simp only [Expr.allLevelParamsDefined] at hb
    simp only [Expr.instantiate1Lift, Expr.allLevelParamsDefined]
    exact allLevelParamsDefined_instantiate1Lift hv e j hb

private theorem annotates_allLevelParamsDefined_of_pw {lps : List LevelParam} {e' e₀ : KExpr}
    (hann : IxVM.Consistency.Annotates e' e₀)
    (hpw : propWhenDefined lps e' = true)
    (hdef : e₀.allLevelParamsDefined lps = true) :
    e'.allLevelParamsDefined lps = true := by
  induction hann with
  | bvar | sort | const | lit => exact hdef
  | fvar _ ih =>
    simp only [propWhenDefined] at hpw
    simp only [Expr.allLevelParamsDefined] at hdef ⊢
    exact ih hpw hdef
  | app _ _ ihf iha =>
    simp only [propWhenDefined, Bool.and_eq_true] at hpw
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hdef ⊢
    exact ⟨ihf hpw.1 hdef.1, iha hpw.2 hdef.2⟩
  | lam _ _ ihty ihb | forallE _ _ ihty ihb =>
    simp only [propWhenDefined, Bool.and_eq_true] at hpw
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hdef ⊢
    exact ⟨⟨ihty hpw.1.1 hdef.1.1, ihb hpw.1.2 hdef.1.2⟩, hpw.2⟩
  | proj _ ihe =>
    simp only [propWhenDefined] at hpw
    simp only [Expr.allLevelParamsDefined] at hdef ⊢
    exact ihe hpw hdef
  | letE _ ih =>
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hdef
    exact ih hpw (allLevelParamsDefined_instantiate1Lift hdef.1.2 _ 0 hdef.2)

private theorem validate_univ_params_seen_aux :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → fname = "KernelCheck::validate_univ_params_seen" →
      ∀ (u : KLevel) (nl : Nat) (pu : SourceValue F),
        args = [pu, .field (nl : F)] → nl < 4294967296 → RepKLevel h u pu →
        u.allParamsDefined (List.range nl) = true :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' cs => fname = "KernelCheck::validate_univ_params_seen" →
      ∀ (u : KLevel) (nl : Nat) (pu : SourceValue F),
        args = [pu, .field (nl : F)] → nl < 4294967296 → RepKLevel h u pu →
        u.allParamsDefined (List.range nl) = true)
    (fun fname args h r h' cs ev ih hfn u nl pu hargs hnl hu => by
      subst hfn hargs
      rcases Obs.«KernelCheck::validate_univ_params_seen».obs ev with
        ⟨ld12, _, _, _⟩ |
        ⟨x_inner, cs40, ld12, ev42, hc59⟩ |
        ⟨x_a, x_b, v77, m78, cs88, cs110, ld12, ev90, ev112, hc129⟩ |
        ⟨x_a, x_b, v147, m148, cs158, cs180, ld12, ev160, ev182, hc199⟩ |
        ⟨x_i, v223, m226, cs234, ld12, ev236, heq259, _, _, _⟩
      · obtain rfl := LevelsAux.zero_of_load hu ld12; rfl
      · obtain ⟨inner, rfl, hinner⟩ := LevelsAux.succ_of_load hu ld12
        subst hc59
        exact ih _ _ _ _ _ _ (by scope_lt_calls) ev42 rfl inner nl x_inner rfl hnl hinner
      · obtain ⟨a, b, rfl, ha, hb⟩ := LevelsAux.max_of_load hu ld12
        subst hc129
        simp only [Level.allParamsDefined, Bool.and_eq_true]
        exact ⟨ih _ _ _ _ _ _ (by scope_lt_calls) ev90 rfl a nl x_a rfl hnl ha,
          ih _ _ _ _ _ _ (by scope_lt_calls) ev112 rfl b nl x_b rfl hnl
            (hb.mono (ObsFn.heap_extends ev90))⟩
      · obtain ⟨a, b, rfl, ha, hb⟩ := LevelsAux.imax_of_load hu ld12
        subst hc199
        simp only [Level.allParamsDefined, Bool.and_eq_true]
        exact ⟨ih _ _ _ _ _ _ (by scope_lt_calls) ev160 rfl a nl x_a rfl hnl ha,
          ih _ _ _ _ _ _ (by scope_lt_calls) ev182 rfl b nl x_b rfl hnl
            (hb.mono (ObsFn.heap_extends ev160))⟩
      · obtain ⟨p, rfl, hp, rfl⟩ := LevelsAux.param_of_load hu ld12
        subst heq259
        obtain ⟨_, _, hlt, _, _⟩ := Lib.less_than_fields_field ev236
        have hplt : p < nl := by
          have hp' : (p : Nat) < 4294967296 := hp
          have h1 : ((p : F)).val = p :=
            ZMod.val_natCast_of_lt (Nat.lt_trans hp' (by decide))
          have h2 : ((nl : F)).val = nl :=
            ZMod.val_natCast_of_lt (Nat.lt_trans hnl (by decide))
          simpa [h1, h2] using hlt.mp rfl
        simp [Level.allParamsDefined, hplt])

private theorem validate_univ_params_seen_spec {u : KLevel} {nl : Nat} {pu r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} (hnl : nl < 4294967296) (hu : RepKLevel h u pu)
    (ev : ObsFn W "KernelCheck::validate_univ_params_seen" [pu, .field (nl : F)] h r h' cs) :
    u.allParamsDefined (List.range nl) = true :=
  validate_univ_params_seen_aux _ _ _ _ _ _ ev rfl u nl pu rfl hnl hu

private theorem validate_binder_params_aux {κ : _root_.Address → KKey} {Γ : Nat → KExpr} :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → fname = "KernelCheck::validate_expr_well_scoped" →
      ∀ (k nl : Nat) (E : KExpr) (pe pdepth : SourceValue F),
        args = [pe, pdepth, .field (nl : F)] → nl < 4294967296 →
        Tm κ 0 Γ h k E pe →
        propWhenDefined (List.range nl) E = true :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' cs => fname = "KernelCheck::validate_expr_well_scoped" →
      ∀ (k nl : Nat) (E : KExpr) (pe pdepth : SourceValue F),
        args = [pe, pdepth, .field (nl : F)] → nl < 4294967296 →
        Tm κ 0 Γ h k E pe →
        propWhenDefined (List.range nl) E = true)
    (fun fname args h r h' cs ev ih hfn k nl E pe pdepth hargs hnl hE => by
      subst hfn hargs
      rcases Obs.«KernelCheck::validate_expr_well_scoped».obs ev with
        ⟨x_i, _, _, _, ld12, _, _, _, _, _⟩ |
        ⟨x_l, cs93, ld12, ev95, _⟩ |
        ⟨x_addr, x_lvls, v130, m131, p138, cs144, v155, m156, cs166, v188, m191, cs199, cs221,
          ld12, ev146, _, ev168, ev201, _, ev223, _⟩ |
        ⟨x_f, x_a, v258, m259, cs269, cs299, ld12, ev271, ev301, hc326⟩ |
        ⟨x_t, x_b, x_l, v349, m350, cs360, v379, m380, cs390, cs420, v424,
          ld12, ev362, ev392, _, ev422, hc455⟩ |
        ⟨x_t, x_b, x_l, v478, m479, cs489, v508, m509, cs519, cs549, v553,
          ld12, ev491, ev521, _, ev551, hc584⟩ |
        ⟨x_t, x_v, x_b, v607, m608, cs618, v645, m646, cs656, cs686, v690,
          ld12, ev620, ev658, _, ev688, hc721⟩ |
        ⟨_, ld12, _, _, _⟩ |
        ⟨_, _, x_e1, cs767, ld12, ev769, hc794⟩
      · obtain ⟨_, _, _, ⟨_, rfl⟩ | ⟨_, hd, _⟩⟩ := hE.bvar_of_load ld12
        · rfl
        · omega
      · obtain ⟨_, rfl, _⟩ := hE.sort_of_load ld12
        rfl
      · obtain ⟨_, _, rfl, _⟩ := hE.const_of_load ld12
        rfl
      · obtain ⟨Ef, Ea, rfl, hf, ha⟩ := hE.app_of_load ld12
        subst hc326
        simp only [propWhenDefined, Bool.and_eq_true]
        exact ⟨ih _ _ _ _ _ _ (by scope_lt_calls) ev271 rfl k nl Ef x_f pdepth rfl hnl hf,
          ih _ _ _ _ _ _ (by scope_lt_calls) ev301 rfl k nl Ea x_a pdepth rfl hnl
            (ha.mono (ObsFn.heap_extends ev271))⟩
      · obtain ⟨T, B, ℓ, rfl, ht, hb, hℓ⟩ := hE.lam_of_load ld12
        subst hc455
        have e1 := ObsFn.heap_extends ev362
        have e2 := ObsFn.heap_extends ev392
        have hℓ_def := validate_univ_params_seen_spec hnl hℓ ev362
        simp only [propWhenDefined, Bool.and_eq_true]
        exact ⟨⟨ih _ _ _ _ _ _ (by scope_lt_calls) ev392 rfl k nl T x_t pdepth rfl hnl (ht.mono e1),
          ih _ _ _ _ _ _ (by scope_lt_calls) ev422 rfl (k + 1) nl B x_b v424 rfl hnl
            (hb.mono (e1.trans e2))⟩,
          Level.zeronessOf_paramsDefined hℓ_def⟩
      · obtain ⟨T, B, ℓ, rfl, ht, hb, hℓ⟩ := hE.forallE_of_load ld12
        subst hc584
        have e1 := ObsFn.heap_extends ev491
        have e2 := ObsFn.heap_extends ev521
        have hℓ_def := validate_univ_params_seen_spec hnl hℓ ev491
        simp only [propWhenDefined, Bool.and_eq_true]
        exact ⟨⟨ih _ _ _ _ _ _ (by scope_lt_calls) ev521 rfl k nl T x_t pdepth rfl hnl (ht.mono e1),
          ih _ _ _ _ _ _ (by scope_lt_calls) ev551 rfl (k + 1) nl B x_b v553 rfl hnl
            (hb.mono (e1.trans e2))⟩,
          Level.zeronessOf_paramsDefined hℓ_def⟩
      · obtain ⟨T, V, B, rfl, _, hv, hb⟩ := hE.letE_of_load ld12
        subst hc721
        have e1 := ObsFn.heap_extends ev620
        have e2 := ObsFn.heap_extends ev658
        have hv_def := ih _ _ _ _ _ _ (by scope_lt_calls) ev658 rfl k nl V x_v pdepth rfl hnl
          (hv.mono e1)
        have hb_def := ih _ _ _ _ _ _ (by scope_lt_calls) ev688 rfl (k + 1) nl B x_b v690 rfl hnl
          (hb.mono (e1.trans e2))
        exact propWhenDefined_instantiate1Lift hv_def B 0 hb_def
      · rcases hE.lit_of_load ld12 with ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩ <;> rfl
      · obtain ⟨a, i, E₁, _, rfl, _, he₁⟩ := hE.proj_of_load ld12
        subst hc794
        exact ih _ _ _ _ _ _ (by scope_lt_calls) ev769 rfl k nl E₁ x_e1 pdepth rfl hnl he₁)

/-- A scope-validated heap term that annotates a parameter-covered reader term also has
parameter-covered binder metadata, even when annotation synthesized that metadata. -/
theorem validatedAnnotation_allLevelParamsDefined
    {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {k nl : Nat} {e' e₀ : KExpr} {p depth r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hnl : nl < 4294967296)
    (rep : Tm κ 0 Γ h k e' p)
    (hann : IxVM.Consistency.Annotates e' e₀)
    (hdef : e₀.allLevelParamsDefined (List.range nl) = true)
    (ev : ObsFn W "KernelCheck::validate_expr_well_scoped"
      [p, depth, .field (nl : F)] h r h' cs) :
    e'.allLevelParamsDefined (List.range nl) = true :=
  annotates_allLevelParamsDefined_of_pw hann
    (validate_binder_params_aux _ _ _ _ _ _ ev rfl k nl e' p depth rfl hnl rep) hdef

/-- Positional closed form of scope preservation, matching the reader conversion bridge. -/
theorem validatedAnnotation_positional
    {κ : _root_.Address → KKey} {nl : Nat} {e' e₀ : KExpr}
    {p depth r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hnl : nl < 4294967296)
    (rep : TmC κ h (posOf (List.range nl) e') p)
    (hann : IxVM.Consistency.Annotates e' e₀)
    (hdef : e₀.allLevelParamsDefined (List.range nl) = true)
    (ev : ObsFn W "KernelCheck::validate_expr_well_scoped"
      [p, depth, .field (nl : F)] h r h' cs) :
    e'.allLevelParamsDefined (List.range nl) = true := by
  have rep' : Tm κ 0 (fun _ => .sort .zero) h 0 e' p := by
    simpa only [posOf, posLevels, List.length_range, Expr.instantiateLevelParams_self]
      using rep 0 (fun _ => .sort .zero)
  exact validatedAnnotation_allLevelParamsDefined hnl rep' hann hdef ev

end IxVM.Refinement.Core.Scope
