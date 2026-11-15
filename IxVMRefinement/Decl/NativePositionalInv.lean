import IxVMRefinement.Decl.NativePositional

/-! # Structural inversions for positional native typing -/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model
open Ix.Kernel.Rules (Infer Red)
open Core (KExpr posOf posLevels)

private theorem inverseBinderPW {ps : List LevelParam}
    (hp : ps.Perm (List.range ps.length)) (mb : BinderMeta) :
    Level.substPW (List.range ps.length) (ps.map .param)
      (Level.substPW ps (posLevels ps) mb.pw) = mb.pw := by
  have h := invPosOf_posOf hp (.forallE (.sort .zero) (.sort .zero) mb)
  simp only [invPosOf, posOf, Expr.instantiateLevelParams, Level.subst] at h
  exact congrArg BinderMeta.pw (Expr.forallE.inj h).2.2

private theorem full_spine_head {env : Env .anon} {d : Nat} :
    ∀ (args : List KExpr) {f t : KExpr},
      Infer env .full d (Expr.mkAppN f args) t → ∃ tf, Infer env .full d f tf
  | [], _, _, h => ⟨_, h⟩
  | _ :: args, _, _, h => by
    obtain ⟨_, hh⟩ := full_spine_head args h
    obtain ⟨_, _, _, _, _, hf, _⟩ := Rules.Infer.app_inv hh
    exact ⟨_, hf⟩

private theorem projSlots_inst (env : Env .anon) (ks : List LevelParam) (us : List Level)
    (e : KExpr) :
    Expr.ProjSlotsOk env (e.instantiateLevelParams ks us) ↔ Expr.ProjSlotsOk env e := by
  induction e <;> simp_all [Expr.ProjSlotsOk, Expr.instantiateLevelParams]

/-- The native package has all structural inversions required by the existing native model.
Stored universe scope is used exactly when commuting a stored telescope with a permutation. -/
theorem judgeInv_nativePosRulesJ : JudgeInv nativePosRulesJ where
  infer_sort := by
    intro env d level t h
    rcases h with h | ⟨_, ps, hp, h⟩
    · exact Rules.Infer.sort_inv h
    · apply posOf_inj hp
      exact Rules.Infer.sort_inv h
  sort_sort := by
    intro env d level other h
    obtain ⟨ps, hp, h⟩ := h
    apply Expr.sort.inj
    apply posOf_inj hp
    exact congrArg Expr.sort (Rules.Red.sort_eq h)
  infer_forallE := by
    intro env d ty body t mb h
    rcases h with h | ⟨scope, ps, hp, h⟩
    · obtain ⟨s, level, bs, other, hi, hr, hbi, hbr, hpw, ht⟩ :=
        Rules.Infer.forallE_inv h
      exact ⟨s, level, bs, other, Or.inl hi, rulesToNativePos.sort hr,
        Or.inl hbi, rulesToNativePos.sort hbr, hpw, ht⟩
    · obtain ⟨s, level, bs, other, hi, hr, hbi, hbr, hpw, ht⟩ :=
        Rules.Infer.forallE_inv h
      have hbi' : Infer env .full (d + 1)
          (posOf ps (body.instantiate1 (.fvar d ty))) bs := by
        simpa only [posOf, Expr.instantiateLevelParams_instantiate1,
          Expr.instantiateLevelParams] using hbi
      refine ⟨invPosOf ps s, invPosLevel ps level, invPosOf ps bs, invPosLevel ps other,
        Or.inr ⟨scope, posRulesJ_infer_of_pos hp hi⟩, posRulesJ_sort_of_pos hp hr,
        Or.inr ⟨scope, posRulesJ_infer_of_pos hp hbi'⟩,
        posRulesJ_sort_of_pos hp hbr, ?_, ?_⟩
      · rw [invPosLevel, Level.zeronessOf_subst, hpw, inverseBinderPW hp]
      · have pulled := congrArg (invPosOf ps) ht
        rw [invPosOf_posOf hp] at pulled
        exact pulled
  infer_spine_sort := by
    intro env d name levels args t ci binders level h hf hs
    rcases h with h | ⟨scope, ps, hp, h⟩
    · exact judgeInv_rulesJ.infer_spine_sort h hf hs
    · have hinfer : Infer env .full d
          (Expr.mkAppN (.const name (levels.map (Level.subst ps (posLevels ps))))
            (args.map (posOf ps))) (posOf ps t) := by
        simpa only [posOf, Expr.instantiateLevelParams_mkAppN,
          Expr.instantiateLevelParams] using h
      obtain ⟨_, hhead⟩ := full_spine_head _ hinfer
      obtain ⟨ci', hfind, _, hlength, _⟩ := Rules.Infer.const_inv hhead
      rw [hf] at hfind
      cases Option.some.inj hfind
      have hlength' : levels.length = ci.toConstantVal.levelParams.length := by
        simpa only [List.length_map] using hlength
      have has := Expr.stripPis_instantiateLevelParams_isSome ps (posLevels ps)
        args.length (by rw [hs]; rfl)
      obtain ⟨⟨pbs, residual⟩, hstrip⟩ := Option.isSome_iff_exists.mp has
      have hres := (Expr.stripPis_instantiateLevelParams_eq ps (posLevels ps)
        args.length hs hstrip).1
      rw [hres] at hstrip
      rw [Core.InferAux.instantiateLevelParams_comp hlength' (scope name ci hf)] at hstrip
      have hsort : posOf ps t = .sort (Level.subst ps (posLevels ps) level) := by
        apply infer_spine_sortR (args.map (posOf ps)) (f := .const name
          (levels.map (Level.subst ps (posLevels ps)))) (ty :=
          ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams
            (levels.map (Level.subst ps (posLevels ps))))
        · intro t' hi
          obtain ⟨ci'', hf', _, _, ht⟩ := Rules.Infer.const_inv hi
          rw [hf] at hf'
          cases Option.some.inj hf'
          exact ht
        · simpa only [List.length_map, Expr.instantiateLevelParams] using hstrip
        · exact hinfer
      apply posOf_inj hp
      exact hsort
  annot_noProjAt := by
    intro env e e' name i hann hinfer hnf hslot
    obtain ⟨t, hi⟩ := hinfer
    rcases hi with hi | ⟨_, ps, hp, hi⟩
    · exact judgeInv_rulesJ.annot_noProjAt hann ⟨t, hi⟩ hnf hslot
    · have hnf' : e'.hasFvar = false :=
        Expr.not_hasFvar_of_fvarsBelow_zero
          ((annot_wscoped hann (Expr.WScoped.of_not_hasFvar hnf)).fvarsBelow)
      have hnfPos : (posOf ps e').hasFvar = false := by
        rw [posOf, Expr.hasFvar_instantiateLevelParams]; exact hnf'
      have slots := infer_projSlots hi rfl (Expr.FvarTysOk.of_not_hasFvar _ hnfPos)
      exact Expr.ProjSlotsOk.noProjAt hslot e'
        ((projSlots_inst env ps (posLevels ps) e').mp slots)

end IxVM.Refinement.Decl
