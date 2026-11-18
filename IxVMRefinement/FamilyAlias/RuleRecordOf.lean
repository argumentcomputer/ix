import IxVMRefinement.FamilyAlias.RuleRecord

/-! # A rule's renamed record from its facts and its alias

`iotaRuleRenRunJ_of_aliased`: IxC's renamed rule record `IotaRuleRenRunJ` over the family package
`famJ h`, at the environment `envM` after the family's types and constructors and the
environment `envSelf` after its recursors without rules, from a rule's facts with its alias found
(`RuleAliased`). The route is `FamilyAlias/RuleRecord.lean`'s module docstring.

What the record needs beyond the rule's facts is listed in the hypotheses, each a fact about the
family or about the environments, not about the rule:

* the prefix is well formed and stores well-formed constants (`StoreInv`), the recursor's level
  parameters are positions in some order;
* `g` moves members only, and moves each (a member's model is stored in the prefix, the member
  is not); `h` sends a member's model key to the member's model and fixes what the prefix
  stores; the recursor and every member of `blk` are members;
* the recursor's annotated type is closed, bounded, in its level parameters, and resolves in the
  prefix renamed by `g`;
* `envM` finds the rule's constructor as `RuleCtor` names it, and that constructor's type
  resolves in the prefix renamed by `g`; `envM` finds the rule's alias where `E` does;
* `envSelf` extends the prefix, stores the aliases `h` moves, and stores every key whose image
  under `g` the prefix stores. -/

namespace IxVM.Refinement.Decl.FamilyAlias

open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel (Env Expr Key Level ConstantInfo ConstantVal RecRule LevelParam BinderMeta EnvWF
  EnvExt Derived auxKey openPisAtFvars isEqHead nestedRuleShape recRuleBits eqName)
open Ix.Kernel.Rules (Annot Red DefEq Infer)

set_option linter.unusedVariables false

/-- **A rule's renamed record from its facts and its alias** (module docstring). -/
theorem iotaRuleRenRunJ_of_aliased
    {env E envM envSelf : Env .anon} {g h : KKey → KKey} {blk : List (ConstantInfo .anon)}
    {tys : List KExpr} {bn : List KKey} {recKey : KKey} {lps : List LevelParam} {tyA : KExpr}
    {mI rP j : Nat} {r : RecRule .anon} {rhsA : KExpr} {thm : KKey}
    (hra : RuleAliased env E g blk tys bn recKey lps tyA mI rP j r rhsA thm)
    (hwf : EnvWF env) (hsi : Ix.Kernel.Open.StoreInv env)
    (hperm : lps.Perm (List.range lps.length))
    (hout : ∀ k, bn.contains k = false → g k = k)
    (hgne : ∀ k, bn.contains k = true → g k ≠ k)
    (htarget : ∀ k, bn.contains k = true → h (auxKey k .model) = g k)
    (hfix : ∀ k, (env.find? k).isSome = true → h k = k)
    (hrecbn : bn.contains recKey = true)
    (hblk : ∀ ci ∈ blk, bn.contains ci.name = true)
    (htyF : tyA.hasFvar = false) (htyB : tyA.looseBVarsBounded 0 = true)
    (htyL : tyA.allLevelParamsDefined lps = true)
    (htyR : (tyA.renameConsts g).constsResolve env = true)
    (hctor : ∀ cvj cnP cnF, RuleCtor env blk tys r.ctor cvj cnP cnF →
      envM.find? r.ctor = some (.ctorInfo cvj cnP cnF) ∧
        (cvj.type.renameConsts g).constsResolve env = true)
    (hiota : envM.find? (iotaKey recKey j) = E.find? (iotaKey recKey j))
    (hext : EnvExt env envSelf) (hA : AliasEnv envSelf h)
    (hstored : ∀ k, (env.find? (g k)).isSome = true → (envSelf.find? k).isSome = true) :
    ∃ r', IotaRuleRenRunJ (famJ h) envM envSelf (blockRen bn) recKey lps tyA mI rP j r r' ∧
      IxVM.Consistency.RuleStored r' r ∧ r'.rhs = rhsA := by
  obtain ⟨cvj, cnP, cnF, lvls, pins, cvt, vt, hw, hfindA⟩ := hra
  obtain ⟨hctorM, hctyR⟩ := hctor cvj cnP cnF hw.ctor
  have hmono : ∀ k, (env.find? k).isSome = true → (envSelf.find? k).isSome = true := by
    intro k hk
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hk
    exact Option.isSome_iff_exists.mpr ⟨c, hext.find hc⟩
  /- the renamings -/
  have hfg : ∀ k, g k = k → blockRen bn k = k := by
    intro k hk
    cases hb : bn.contains k with
    | true => exact absurd hk (hgne k hb)
    | false => exact ite_eq_right (by rw [hb]; exact Bool.false_ne_true)
  have hcomp : ∀ e : KExpr, (e.renameConsts g).constsResolve env = true →
      e.renameConsts (fun k => h (blockRen bn k)) = e.renameConsts g := fun e he =>
    (renameConsts_comp (blockRen bn) h e).symm.trans
      (comp_of_renamed_resolves hout htarget hfix he)
  have hctorK : h (blockRen bn r.ctor) = g r.ctor := by
    cases hb : bn.contains r.ctor with
    | true =>
      have hk : blockRen bn r.ctor = auxKey r.ctor .model := ite_eq_left hb
      rw [hk]
      exact htarget r.ctor hb
    | false =>
      have hk : blockRen bn r.ctor = r.ctor :=
        ite_eq_right (by rw [hb]; exact Bool.false_ne_true)
      rw [hk, hout r.ctor hb]
      rcases hw.ctor with hc | ⟨i, cv, tyC, hbi, -, hname, -⟩
      · exact hfix r.ctor (by rw [hc]; rfl)
      · exfalso
        have hmem : (ConstantInfo.ctorInfo cv cnP cnF : ConstantInfo .anon) ∈ blk :=
          List.mem_of_getElem? hbi
        have hin : bn.contains cv.name = true := hblk _ hmem
        rw [hname, hb] at hin
        exact Bool.false_ne_true hin
  /- the right-hand side -/
  have hann : Annot 0 r.rhs rhsA := annot_of_annotates hw.annotated hw.closed hw.bounded 0
  obtain ⟨hrhsF, -⟩ := (judgeFrames_posRulesJ env).annot_syntax hann hw.closed hw.bounded
  obtain ⟨t', ps, hps, hinf⟩ := hw.typed
  have hrhsG : (rhsA.renameConsts g).constsResolve env = true := by
    have hfv : (posOf ps (rhsA.renameConsts g)).hasFvar = false := by
      unfold posOf
      rw [hasFvar_instantiateLevelParams, Ix.Kernel.hasFvar_renameConsts]
      exact hrhsF
    have h1 := infer_constsResolve hinf hsi hfv
    unfold posOf at h1
    rw [Ix.Kernel.Expr.constsResolve_instantiateLevelParams] at h1
    exact h1
  have hrhsA : rhsA.renameConsts (fun k => h (blockRen bn k)) = rhsA.renameConsts g :=
    hcomp _ hrhsG
  have hrhsRes : rhsA.constsResolve envSelf = true :=
    constsResolve_of_renamed hstored hmono rhsA hrhsG
  have htyRes : tyA.constsResolve envSelf = true :=
    constsResolve_of_renamed hstored hmono tyA htyR
  have htyped : ∃ t', (renameJ (blockRen bn) (famJ h)).infer envSelf 0 rhsA t' :=
    ⟨t', Or.inr ⟨hrhsF, hA,
      LeavesFixed.of_closed ((Ix.Kernel.hasFvar_renameConsts _ rhsA).trans hrhsF),
      by rw [renameConsts_comp, hrhsA]; exact posRulesJ_infer_weaken hext ⟨ps, hps, hinf⟩⟩⟩
  /- the statement, opened -/
  obtain ⟨hsF, hsB, hsR, hsL⟩ := statement_scope hwf hw.thm hperm hw.thmLevels
  have hst := hw.statement
  obtain ⟨fvs, tbody, hop, heqh, h3, hrest⟩ := hst
  dsimp only at hrest
  obtain ⟨hfn, hlen, htake, hmajor, cdoms, cres, rdoms, lrest, fvsP, crest2, cdomsP, crestP,
    xFvsP, ldoms, hcd, hcresl, hrd, hopP, hcdP, hopX, hldl, hleaves, ldomsL, lrest2, hlam, htl,
    hruns⟩ := hrest
  have htargs := eq_three_of_length (Expr.bvar 0) tbody.getAppArgs h3
  obtain ⟨α, lhsS, rhsS, htargs', hα, hL, hR⟩ : ∃ α lhsS rhsS : KExpr,
      tbody.getAppArgs = [α, lhsS, rhsS] ∧ tbody.getAppArgs.getD 0 (.bvar 0) = α ∧
      tbody.getAppArgs.getD 1 (.bvar 0) = lhsS ∧ tbody.getAppArgs.getD 2 (.bvar 0) = rhsS :=
    ⟨_, _, _, htargs, rfl, rfl, rfl⟩
  rw [hL] at hfn hlen htake hmajor
  rw [hα, hL, hR] at hruns
  obtain ⟨ℓ, hhd⟩ := isEqHead_const heqh
  have htbform : tbody = .app (.app (.app (.const eqName [ℓ]) α) lhsS) rhsS := by
    have h0 := Ix.Kernel.Expr.mkAppN_getApp tbody
    rw [hhd, htargs'] at h0
    exact h0.symm
  obtain ⟨-, -, -, hflen, -, -⟩ := Ix.Kernel.Verify.openPisAtFvars_stripPis (rP + cnF) hop
  obtain ⟨-, hfvscl, -⟩ := openPisAtFvars_fvars_closed (rP + cnF) hsB hop
  /- the statement's side is fixed by `h` -/
  have hstmtfix : (invPosOf lps cvt.type).renameConsts h = invPosOf lps cvt.type :=
    renameConsts_eq_self_of_constsResolve hfix _ hsR
  obtain ⟨hfvsfix, htbfix⟩ := openPisAtFvars_fixed hop hstmtfix
  have hfvsfixe : ∀ x ∈ fvs, x.renameConsts h = x := map_eq_self_mem hfvsfix
  have hαfix : α.renameConsts h = α := by
    have h1 := congrArg (fun e : KExpr => e.renameConsts h) htbform
    simp only [htbfix] at h1
    rw [htbform] at h1
    simp only [Expr.renameConsts] at h1
    injection h1 with h2 _
    injection h2 with h4 _
    injection h4 with _ h6
    exact h6.symm
  have hLfix : lhsS.renameConsts h = lhsS := by
    have h1 := congrArg (fun e : KExpr => e.renameConsts h) htbform
    simp only [htbfix] at h1
    rw [htbform] at h1
    simp only [Expr.renameConsts] at h1
    injection h1 with h2 _
    injection h2 with _ h5
    exact h5.symm
  have hRfix : rhsS.renameConsts h = rhsS := by
    have h1 := congrArg (fun e : KExpr => e.renameConsts h) htbform
    simp only [htbfix] at h1
    rw [htbform] at h1
    simp only [Expr.renameConsts] at h1
    injection h1 with _ h3
    exact h3.symm
  have hlargsfix : lhsS.getAppArgs.map (·.renameConsts h) = lhsS.getAppArgs := by
    rw [← IxVM.Refinement.Decl.getAppArgs_renameConsts, hLfix]
  /- the copy -/
  have hpinsres := pins_renamed_resolve hw.major htyR
  have hpcomp : ∀ p ∈ pins, (p.renameConsts (blockRen bn)).renameConsts h = p.renameConsts g :=
    fun p hp => comp_of_renamed_resolves hout htarget hfix (hpinsres p hp)
  obtain ⟨hren, hopc⟩ := ruleCopy_spec (f := blockRen bn) hsF hsB hsR hop heqh htargs' hfn hlen
    hmajor hw.pins_scope hfix (htarget recKey hrecbn) hctorK hpcomp
  obtain ⟨lhs', hlhs'⟩ : ∃ lhs' : KExpr, lhs' =
      Expr.mkAppN (.const (auxKey recKey .model) (lps.map .param))
        (lhsS.getAppArgs.dropLast ++
          [Expr.mkAppN (.const (blockRen bn r.ctor) lvls)
            ((pins.map fun p => Expr.instSpine (fvs.take rP) (rP - 1)
              (p.renameConsts (blockRen bn))) ++ fvs.drop rP)]) := ⟨_, rfl⟩
  rw [← hlhs', hhd] at hopc
  have hlhsren : lhs'.renameConsts h = lhsS := by
    have h1 := IxVM.Refinement.Decl.openPisAtFvars_renameConsts h (rP + cnF)
      (copyStatement (auxKey recKey .model) lps
        (fun _ => copyMajor (blockRen bn) r.ctor lvls cnF pins) (invPosOf lps cvt.type)) 0
    rw [hren, hop, hopc] at h1
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    have h2 := h1.2
    rw [htbform] at h2
    simp only [Expr.renameConsts] at h2
    injection h2 with h4 _
    injection h4 with _ h6
    exact h6.symm
  have hlargs' : lhs'.getAppArgs = lhsS.getAppArgs.dropLast ++
      [Expr.mkAppN (.const (blockRen bn r.ctor) lvls)
        ((pins.map fun p => Expr.instSpine (fvs.take rP) (rP - 1)
          (p.renameConsts (blockRen bn))) ++ fvs.drop rP)] := by
    rw [hlhs']
    exact IxVM.Refinement.Decl.getAppArgs_mkAppN_const _ _ _
  have hlast' : lhs'.getAppArgs.getLastD (.bvar 0) =
      Expr.mkAppN (.const (blockRen bn r.ctor) lvls)
        ((pins.map fun p => Expr.instSpine (fvs.take rP) (rP - 1)
          (p.renameConsts (blockRen bn))) ++ fvs.drop rP) := by
    rw [hlargs', getLastD_append_single]
  have hfn' : (lhs'.getAppFn == Expr.const (blockRen bn recKey) (lps.map .param)) = true := by
    have hk : blockRen bn recKey = auxKey recKey .model := ite_eq_left hrecbn
    rw [hk, hlhs', IxVM.Refinement.Decl.getAppFn_mkAppN]
    exact beq_self_eq_true _
  have hlen' : lhs'.getAppArgs.length = mI + 1 := by
    rw [hlargs', List.length_append, List.length_dropLast, hlen]
    simp
  have htake' : (lhs'.getAppArgs.take rP == fvs.take rP) = true := by
    obtain ⟨hle, -⟩ := majorShape_inv hw.major
    rw [hlargs', List.take_append_of_le_length (by rw [List.length_dropLast, hlen]; omega),
      take_dropLast_of_lt (by rw [hlen]; omega), htake]
    exact beq_self_eq_true _
  have hidx : ((lhs'.getAppArgs).drop rP).take (mI - rP) =
      (lhsS.getAppArgs.drop rP).take (mI - rP) := by
    obtain ⟨hle, -⟩ := majorShape_inv hw.major
    rw [hlargs']
    exact take_drop_dropLast_append _ _ _ _ (by rw [hlen]; omega)
  /- the copy's left side has its leaves fixed by `h` -/
  have hLF : LeavesFixed h lhs' := by
    rw [hlhs']
    refine LeavesFixed.mkAppN' (LeavesFixed.of_closed rfl) (fun x hx => ?_)
    rcases List.mem_append.mp hx with hx | hx
    · exact LeavesFixed.of_renameConsts_eq
        (map_eq_self_mem hlargsfix x (List.mem_of_mem_dropLast hx))
    · rw [List.mem_singleton] at hx
      subst hx
      refine LeavesFixed.mkAppN' (LeavesFixed.of_closed rfl) (fun y hy => ?_)
      rcases List.mem_append.mp hy with hy | hy
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
        exact LeavesFixed.instSpine'
          (LeavesFixed.of_closed
            ((Ix.Kernel.hasFvar_renameConsts _ p).trans (hw.pins_scope p hp).1))
          (fun a ha => LeavesFixed.of_renameConsts_eq (hfvsfixe a (List.mem_of_mem_take ha)))
      · exact LeavesFixed.of_renameConsts_eq (hfvsfixe y (List.mem_of_mem_drop hy))
  /- the record's terms under `f`, pulled back from the facts' along `h` -/
  have hctyC : cvj.type.renameConsts (fun k => h (blockRen bn k)) = cvj.type.renameConsts g :=
    hcomp _ hctyR
  have htyC : tyA.renameConsts (fun k => h (blockRen bn k)) = tyA.renameConsts g :=
    hcomp _ htyR
  have hpinsFmap : (pins.map fun p => Expr.instSpine (fvs.take rP) (rP - 1)
      (p.renameConsts (blockRen bn))).map (·.renameConsts h) =
      pins.map fun p => Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts g) := by
    rw [List.map_map]
    refine List.map_congr_left (fun p hp => ?_)
    show (Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts (blockRen bn))).renameConsts h =
      Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts g)
    rw [← IxVM.Refinement.Decl.instSpine_renameConsts, hpcomp p hp, List.map_take, hfvsfix]
  have hxfix : (fvs.drop rP).map (·.renameConsts h) = fvs.drop rP := by
    rw [List.map_drop, hfvsfix]
  have hpre : (fvs.take rP).map (·.renameConsts h) = fvs.take rP := by
    rw [List.map_take, hfvsfix]
  obtain ⟨cdomsF, cresF, hcdF, hcdFmap, hcresFmap⟩ := instPisAt_pullback (h := h)
    (xs := (pins.map fun p => Expr.instSpine (fvs.take rP) (rP - 1)
      (p.renameConsts (blockRen bn))) ++ fvs.drop rP)
    (e := (cvj.type.instantiateLevelParams cvj.levelParams lvls).renameConsts (blockRen bn))
    (by rw [List.map_append, hpinsFmap, hxfix])
    (by rw [renameConsts_comp]; exact instantiateLevelParams_agree _ _ hctyC) hcd
  obtain ⟨rdomsF, lrestF, hrdF, hrdFmap, -⟩ := instPisAt_pullback (h := h) hpre
    (by rw [renameConsts_comp]; exact htyC) hrd
  have hcresFl : cresF.getAppArgs.length = cnP + (mI - rP) := by
    rw [← hcresl, ← hcresFmap, IxVM.Refinement.Decl.getAppArgs_renameConsts, List.length_map]
  /- the record's raw terms: `f` then `h` is `g` on them -/
  have hfvsPa := (openPisAtFvars_agree hopP htyC).1
  have hpinsA : ∀ p ∈ pins,
      p.renameConsts (fun k => h (blockRen bn k)) = p.renameConsts g :=
    fun p hp => (renameConsts_comp _ _ p).symm.trans (hpcomp p hp)
  have hpinsPa : (pins.map fun p => Expr.instSpine (fvsP.take rP) (rP - 1) p).map
      (·.renameConsts (fun k => h (blockRen bn k))) =
      (pins.map fun p => Expr.instSpine (fvsP.take rP) (rP - 1) p).map (·.renameConsts g) := by
    rw [List.map_map, List.map_map]
    exact List.map_congr_left (fun p hp => instSpine_agree (map_take_agree rP hfvsPa) (hpinsA p hp))
  obtain ⟨hcdomsPa, hcrestPa⟩ := instPisAt_agree hcdP hpinsPa
    (instantiateLevelParams_agree _ _ hctyC)
  obtain ⟨hxFvsPa, -⟩ := openPisAtFvars_agree hopX hcrestPa
  have hlamxs : (fvsP ++ xFvsP).map (·.renameConsts (fun k => h (blockRen bn k))) =
      (fvsP ++ xFvsP).map (·.renameConsts g) := by
    rw [List.map_append, List.map_append, hfvsPa, hxFvsPa]
  obtain ⟨hldomsLa, -⟩ := instLamsAt_agree hlam hlamxs hrhsA
  /- the walks and the two sides' typings -/
  obtain ⟨r1, r2, r3, r4, r5, ⟨tl, hil, hdl⟩, ⟨tr, hir, hdr⟩⟩ := hruns
  have hruns' : IotaRunsJ (renameJ (blockRen bn) (famJ h)) envSelf (rP + cnF)
      ((lhs'.getAppArgs.drop rP).take (mI - rP)) (cresF.getAppArgs.drop cnP)
      ((fvs.drop rP).map Expr.fvarTypeD) (cdomsF.drop cnP)
      ((fvs.take rP).map Expr.fvarTypeD) rdomsF
      ((fvsP ++ xFvsP).map Expr.fvarTypeD) ldomsL
      rhsS (Expr.mkAppN (rhsA.renameConsts (blockRen bn)) fvs) α lhs' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hidx]
      refine defEqListJ_renameJ_of_pos hext hA ?_
      rw [List.map_take, List.map_drop, hlargsfix, List.map_drop,
        ← IxVM.Refinement.Decl.getAppArgs_renameConsts, hcresFmap]
      exact r1
    · refine defEqListJ_renameJ_of_pos hext hA ?_
      have hd : (cdomsF.drop cnP).map (·.renameConsts h) = cdoms.drop cnP := by
        rw [List.map_drop, hcdFmap]
      rw [map_fvarTypeD_renameConsts', hxfix, hd]
      exact r2
    · refine defEqListJ_renameJ_of_pos hext hA ?_
      rw [map_fvarTypeD_renameConsts', hpre, hrdFmap]
      exact r3
    · exact defEqListJ_renameJ_of_renamed hext hA r4 (map_fvarTypeD_agree hlamxs) hldomsLa
    · refine Or.inl ⟨hA, Or.inl ?_⟩
      rw [hRfix, IxVM.Refinement.Decl.mkAppN_renameConsts, renameConsts_comp, hrhsA, hfvsfix]
      exact posRulesJ_defeq_weaken hext r5
    · exact ⟨tl, Or.inl ⟨hA, hLF, by rw [hlhsren]; exact posRulesJ_infer_weaken hext hil⟩,
        Or.inl ⟨hA, Or.inr (by rw [hαfix]; exact posRulesJ_defeq_weaken hext hdl)⟩⟩
    · exact ⟨tr, Or.inl ⟨hA, LeavesFixed.of_renameConsts_eq hRfix,
          by rw [hRfix]; exact posRulesJ_infer_weaken hext hir⟩,
        Or.inl ⟨hA, Or.inr (by rw [hαfix]; exact posRulesJ_defeq_weaken hext hdr)⟩⟩
  /- the alias, as `envM` finds it -/
  have hcvt : envM.findCV? (iotaKey recKey j) =
      some (ruleAlias bn recKey lps j r.ctor lvls cnF pins thm cvt.type).toConstantVal := by
    show (envM.find? _).map _ = _
    rw [hiota, hfindA]
    rfl
  have heq' : isEqHead (Expr.app (.app (.app (.const eqName [ℓ]) α) lhs') rhsS).getAppFn =
      true := by
    show isEqHead (Expr.const eqName [ℓ]) = true
    rw [← hhd]
    exact heqh
  obtain ⟨hle, bsT, dom, body, mb, D, hstrip, hdfn, hdlen, hpinsEq, hdtake, hddrop⟩ :=
    majorShape_inv hw.major
  obtain ⟨cbs, cbody, cc, cus, hcs, hcb⟩ := Ix.Kernel.Expr.ctorTeleOk_head hw.ctorTele
  by_cases hplain : Expr.recRulePlain tyA mI rP cnP cvj.levelParams = true
  · /- a canonical rule -/
    obtain ⟨hcnp, hlvls, hpinsB⟩ := recRulePlain_pins_lvls hstrip hdfn hplain
    have hpinsR : pins = (List.range cnP).map (fun k => Expr.bvar (rP - 1 - k)) := by
      rw [hpinsEq]
      exact hpinsB
    obtain ⟨-, -, -, hfPlen, -, -⟩ := Ix.Kernel.Verify.openPisAtFvars_stripPis rP hopP
    obtain ⟨-, hfvsPcl, hfvsPsh⟩ := openPisAtFvars_fvars_closed rP htyB hopP
    have hpinsFt : (pins.map fun p => Expr.instSpine (fvs.take rP) (rP - 1)
        (p.renameConsts (blockRen bn))) = fvs.take cnP := by
      have h1 := map_instSpine_bvar_range_eq_take (xs := fvs.take rP) (cnP := cnP) (rP := rP)
        (by rw [List.length_take, hflen]; omega) hcnp
        (fun x hx => hfvscl x (List.mem_of_mem_take hx))
      rw [List.take_take, Nat.min_eq_left hcnp] at h1
      rw [← h1, hpinsR, List.map_map, List.map_map]
      rfl
    have hpinsPt : (pins.map fun p => Expr.instSpine (fvsP.take rP) (rP - 1) p) =
        fvsP.take cnP := by
      have h1 := map_instSpine_bvar_range_eq_take (xs := fvsP.take rP) (cnP := cnP) (rP := rP)
        (by rw [List.length_take, hfPlen]; omega) hcnp
        (fun x hx => hfvsPcl x (List.mem_of_mem_take hx))
      rw [List.take_take, Nat.min_eq_left hcnp] at h1
      rw [← h1, hpinsR]
    subst hlvls
    rw [instantiateLevelParams_self_eq] at hcdF hcdP
    rw [hpinsFt] at hcdF hlast'
    rw [hpinsPt] at hcdP htl
    -- the parameter domains, from the typed pins
    have hfvarsP : ∀ x ∈ (fvsP.take cnP).map (·.renameConsts g), ∃ idx ty, x = .fvar idx ty := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp (List.mem_of_mem_take hy)
      obtain ⟨ty, hty⟩ := hfvsPsh k hk
      rw [hty]
      exact ⟨_, _, rfl⟩
    have hdP := typedListJ_fvars_to_defEqListJ hfvarsP htl
    rw [← map_fvarTypeD_renameConsts'] at hdP
    have hdP' := defEqListJ_renameJ_of_renamed hext hA hdP
      (map_fvarTypeD_agree (map_take_agree cnP hfvsPa)) hcdomsPa
    refine ⟨_, ⟨cvj, cnP, cnF, rhsA, hctorM, hw.nfields, hw.bounded, hw.closed, hann, hw.levels,
      hrhsRes, hw.lams, htyped, .plain, rfl, Or.inl ⟨hplain, rfl, ?_⟩⟩, ⟨rfl, rfl, hw.annotated⟩, rfl⟩
    refine ⟨_, fvs, Expr.app (.app (.app (.const eqName [ℓ]) α) lhs') rhsS, hcvt, rfl, hopc,
      heq', rfl, ?_⟩
    exact ⟨hfn', hlen', htake',
      by show (lhs'.getAppArgs.getLastD (.bvar 0) == _) = true
         rw [hlast']
         exact beq_self_eq_true _, hw.ctorTele,
      cdomsF, cresF, rdomsF, fvsP, cdomsP, crestP, xFvsP, crest2, ldoms, lrestF, hcdF, hcresFl,
      hrdF, hopP, hcdP, hopX, ldomsL, lrest2, hlam, hdP', hruns'⟩
  · /- a nested rule -/
    have hno : ∀ p ∈ dom.getAppArgs.take cnP, noLooseIn 0 (mI - rP) p = true := by
      intro p hp
      rw [hdtake] at hp
      obtain ⟨q, -, rfl⟩ := List.mem_map.mp hp
      exact noLooseIn_liftLooseBVars_self (mI - rP) q 0
    have hnrs := nestedRuleShape_of_major_pins (env' := envM) (envSelf := envSelf)
      (cvName := recKey) (j := j) hcvt hle hstrip hdfn hdlen hno hddrop htyF htyB htyRes htyL
    rw [← hpinsEq] at hnrs
    -- the pins' leaves are parameter domains, which name no member
    have hpinLF : ∀ a ∈ pins.map (fun p => Expr.instSpine (fvsP.take rP) (rP - 1) p),
        LeavesFixed h (a.renameConsts (blockRen bn)) := by
      intro a ha l hl
      rw [Ix.Kernel.Verify.fvarLeaves_renameConstsE] at hl
      obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.mp hl
      have hg0 : l₀.2.renameConsts g = l₀.2 := hleaves a ha l₀ hl₀
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      have hagree : l₀.2.renameConsts (fun k => h (blockRen bn k)) = l₀.2.renameConsts g := by
        rcases Ix.Kernel.fvarLeaves_instSpine (rP - 1) hl₀ with hl₁ | ⟨x, hx, hl₁⟩
        · rw [Ix.Kernel.Expr.fvarLeaves_eq_nil_of_not_hasFvar (hw.pins_scope p hp).1] at hl₁
          exact nomatch hl₁
        · have hxa : x.renameConsts (fun k => h (blockRen bn k)) = x.renameConsts g :=
            List.map_inj_left.mp hfvsPa x (List.mem_of_mem_take hx)
          exact leaves_agree hxa l₀ hl₁
      have hf0 : l₀.2.renameConsts (blockRen bn) = l₀.2 :=
        renameConsts_eq_self_of_fixed hfg l₀.2 hg0
      show (l₀.2.renameConsts (blockRen bn)).renameConsts h = l₀.2.renameConsts (blockRen bn)
      rw [renameConsts_comp, hagree, hg0, hf0]
    have htl' := typedListJ_famJ_of_renamed hext hA htl hpinsPa hcdomsPa hpinLF
    refine ⟨_, ⟨cvj, cnP, cnF, rhsA, hctorM, hw.nfields, hw.bounded, hw.closed, hann, hw.levels,
      hrhsRes, hw.lams, htyped, .nested lvls pins, rfl,
      Or.inr ⟨Bool.eq_false_iff.mpr hplain, lvls, pins, rfl, hnrs, ?_⟩⟩, ⟨rfl, rfl, hw.annotated⟩, rfl⟩
    refine ⟨_, fvs, Expr.app (.app (.app (.const eqName [ℓ]) α) lhs') rhsS, hcvt, rfl, hopc,
      heq', rfl, ?_⟩
    exact ⟨hfn', hlen', htake',
      by show Expr.ErasedEq (lhs'.getAppArgs.getLastD (.bvar 0)) _
         rw [hlast']
         exact Ix.Kernel.Expr.ErasedEq.rfl _,
      ⟨cbs, cbody, hcs, by rw [hcb]⟩, cdomsF, cresF, rdomsF, lrestF, fvsP, crest2, cdomsP,
      crestP, xFvsP, ldoms, hcdF, hcresFl, hrdF, hopP, ⟨hcdP, hopX, beq_iff_eq.mpr hldl⟩,
      ldomsL, lrest2, hlam, htl', hruns'⟩

end IxVM.Refinement.Decl.FamilyAlias
