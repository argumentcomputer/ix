import IxCCGrounding.CaseLevels
import IxCCGrounding.RecRun
import IxCCGrounding.RecLevels
import IxCCGrounding.RecOrdFacts

/-!
# F2 at an `ordinary` recursor (`IxCCGrounding.RecOrdinary`), W-c step 2

`fire_ordinaryK`: `fire_noParamsK` (`IxCCGrounding.Fundamental`) at a recursor with parameters
(`List.rec`, `Option.rec`). What changes:

* the prefix is `np + nmot + nmin`, and the major's constructor value carries its own parameters
  `Ps` (`RelV.con`), which ι takes as they are: every stored rule does not compare parameters
  (`RecOrdRules`), so `paramsBlindIotaG` (ι at the constructor's own parameters, then β along the
  law's own spine, `spineOk_lamTeleG`) replaces `noParamsIota`, and the rule body's context comes
  from the spine's fit, with no field-domain fact (`RecFields`);
* the rule λs' regimes: each carries the major binder's datum (`RecOrdRules`), whose regime is not
  zero at an F2 site (`LastSiteOk`, `last_regime`);
* the constructor's image at the major domain's levels `ls0` (`MajorAt`): with no level parameter,
  `majorAt_of_agree` at vacuous agreement; with some, from `OrdLevels`: level agreement at the F2
  site (`RecLevelAgree`, at the recursor head's `Ok` and the value's), or canonicity
  (`ctorFields_canonP`, the legacy laws), `RecNoLevels` excluding the case.

`spineOk_lamTeleG` and `paramsBlindIotaG` are `IxCCCorrect.SpineIota`'s theorems, moved here so the
fundamental lemma can read them (`IxCC.Correct.spineOk_lamTele` and `.paramsBlindIota` are now these).
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Src (Value Slot Term CId Program Levels)
open IxCC.Sem (Result later later_succ later_zero)

universe w

section Sem

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

/-! ## ι with parameters, from the law's own spine -/

/-- **The law's spine puts each argument in its λ's domain.** A λ-telescope denoting `H`, every
λ of it in graph regime, applied along a `SpineOk` spine of its length: the arguments fit the
telescope's domains (as a `∀`-telescope over any codomain), and the application is the body's
denotation with them bound. No typing and no canonicity: `lamR_dom_eq` and `lamR_ne_pt`. -/
theorem spineOk_lamTeleG {cval : KKey → (LevelParam → Nat) → V} {φ : LevelParam → Nat} :
    ∀ (bs : List (KExpr × BinderMeta)) (b : KExpr) {ρ : BVarIdx → V} {H : V} {xs : List V},
      Denotes cval env φ ρ (lamTele bs b) H → SpineOk H xs → xs.length = bs.length →
      (∀ p ∈ bs, regime φ p.2.pw ≠ 0) →
      (∀ C : KExpr, Fits cval env φ ρ (piTele bs C) xs (pushAll xs ρ) C) ∧
        ∃ Y, Denotes cval env φ (pushAll xs ρ) b Y ∧ xs.foldl app H = Y
  | [], b, ρ, H, [], hH, _, _, _ =>
    ⟨fun C => by rw [pushAll_nil]; exact .nil, H, by rwa [pushAll_nil], rfl⟩
  | [], _, _, _, _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, _, _, _, [], _, _, hl, _ => by simp at hl
  | (A, m) :: bs, b, ρ, H, x :: xs, hH, hsp, hl, hreg => by
    have hH' : Denotes cval env φ ρ (.lam A (lamTele bs b) m) H := hH
    obtain ⟨Ad, F, hA, hF, -, rfl⟩ := den_lam.mp hH'
    have hr : regime φ m.pw ≠ 0 := hreg (A, m) (List.mem_cons_self ..)
    obtain ⟨⟨v, A', B, hmem, hx⟩, hsp'⟩ := hsp
    have hv : v ≠ 0 := by
      intro hv0
      subst hv0
      exact lamR_ne_pt hr (eq_pt_of_mem_piR_zero hmem)
    have hAA : A' = Ad := lamR_dom_eq hr hv hmem
    rw [hAA] at hx
    have happ : app (lamR (regime φ m.pw) Ad F) x = F x := app_lamR_pos hr hx
    rw [happ] at hsp'
    obtain ⟨hfit, Y, hY, hfold⟩ := spineOk_lamTeleG bs b (ρ := push x ρ) (hF x hx) hsp'
      (by simpa using hl) (fun p hp => hreg p (List.mem_cons_of_mem _ hp))
    refine ⟨fun C => ?_, Y, by rwa [pushAll_cons], ?_⟩
    · have h := hfit C
      rw [← pushAll_cons] at h
      exact .cons hA hx h
    · rw [List.foldl_cons, happ]
      exact hfold

/-- **ι at a recursor with parameters, at a rule that does not compare them** (no canonicity):
the recursor applied to its prefix `As.take mI` and to a major that is rule `krl`'s constructor
image `K` at the major domain's levels applied to `ys` (the constructor's **own** parameters and
its fields, fitting the constructor's type there) is the rule body's denotation with the prefix
and the fields `ys.drop nP` bound, which fit the rule's λ-domains. Laws: ι alone. -/
theorem paramsBlindIotaG (M : Model V env) (hι : IotaLaw M.cval env) {kr : KKey}
    {cvr : ConstantVal .anon} {mI : Nat} {krules : List (RecRule .anon)}
    (hf : env.find? kr = some (.recInfo cvr mI mI krules)) {krl : RecRule .anon}
    (hkrl : krl ∈ krules) (hcmp : krl.compareParams = false) {cvC : ConstantVal .anon}
    {nP nF : Nat} (hcC : env.find? krl.ctor = some (.ctorInfo cvC nP nF))
    {bs : List (KExpr × BinderMeta)} {b : KExpr} (hrhs : krl.rhs = lamTele bs b)
    (hbsl : bs.length = mI + nF) {φ : LevelParam → Nat} (hreg : ∀ p ∈ bs, regime φ p.2.pw ≠ 0)
    {ρ σ : BVarIdx → V} {R : KExpr} {As : List V}
    (hfit : Fits M.cval env φ ρ cvr.type As σ R) (hlen : As.length = mI + 1)
    {dom body : KExpr} {m : BinderMeta} {D : KKey} {ls : List Level}
    (hpb : piBody mI cvr.type = .forallE dom body m) (hdom : dom.getAppFn = .const D ls)
    {K : V} {ys : List V} {σC : BVarIdx → V} {RC : KExpr}
    (hK : Denotes M.cval env φ ρ (.const krl.ctor ls) K)
    (hys : Fits M.cval env φ ρ (cvC.type.instantiateLevelParams cvC.levelParams ls) ys σC RC)
    (hyl : ys.length = nP + nF) (hmaj : As[mI]? = some (ys.foldl app K)) :
    ∃ H Y, Denotes M.cval env φ ρ krl.rhs H ∧
      Denotes M.cval env φ (pushAll (As.take mI ++ ys.drop nP) ρ) b Y ∧
      As.foldl app (M.cval kr φ) = Y ∧
      ∀ C : KExpr, Fits M.cval env φ ρ (piTele bs C) (As.take mI ++ ys.drop nP)
        (pushAll (As.take mI ++ ys.drop nP) ρ) C := by
  have hdrop : As.drop mI = [ys.foldl app K] := by
    rw [List.getElem?_eq_getElem (by omega)] at hmaj
    rw [List.drop_eq_getElem_cons (by omega), Option.some.inj hmaj,
      List.drop_eq_nil_of_le (by omega)]
  have hsplit : As = As.take mI ++ [ys.foldl app K] := by rw [← hdrop, List.take_append_drop]
  have hxl : (As.take mI).length = mI := by simp; omega
  have hfit' := hfit
  rw [hsplit] at hfit'
  obtain ⟨σ1, R1, hf1, hf2⟩ := fits_append hfit'
  have hR1 : R1 = .forallE dom body m := by rw [fits_piBody hf1, hxl, hpb]
  subst hR1
  obtain ⟨X, hX, hKX⟩ : ∃ X, Denotes M.cval env φ σ1 dom X ∧ ys.foldl app K ∈ˢ X := by
    cases hf2 with
    | cons hA hx _ => exact ⟨_, hA, hx⟩
  have hRden : Denotes M.cval env φ ρ (.const kr (cvr.levelParams.map .param)) (M.cval kr φ) := by
    have h1 : Denotes M.cval env φ ρ (.const kr (cvr.levelParams.map .param))
        (M.cval kr (Level.substFn φ cvr.levelParams (cvr.levelParams.map .param))) :=
      Denotes.const (ci := .recInfo cvr mI mI krules) hf (by simp [ConstantInfo.toConstantVal])
    rwa [substFn_self] at h1
  obtain ⟨H, hH, -, hspine, heq⟩ := hι kr cvr mI mI krules krl hf hkrl cvC nP nF hcC
    (cvr.levelParams.map .param) φ ρ σ1 σC (As.take mI) ys dom body RC m D ls (M.cval kr φ) K X
    (by simp) hxl hyl hRden (by rw [inst_self]; exact hf1) hdom hX hK hys hKX
    (fun h => absurd h (by rw [hcmp]; decide)) (fun h => absurd rfl h)
  rw [inst_self] at hH
  have e2 : (As.take mI).take mI = As.take mI := by rw [List.take_take, Nat.min_self]
  rw [e2] at hspine heq
  rw [hrhs] at hH
  obtain ⟨hfits, Y, hY, hYe⟩ := spineOk_lamTeleG bs b hH hspine
    (by simp [hxl, hyl]; omega) hreg
  refine ⟨H, Y, by rw [hrhs]; exact hH, hY, ?_, hfits⟩
  have e3 : As.foldl app (M.cval kr φ) =
      (As.take mI ++ [ys.foldl app K]).foldl app (M.cval kr φ) := by rw [← hsplit]
  rw [e3, heq, hYe]

/-! ## The constructor image at the recursor's levels, by canonicity, with parameters -/

/-- **`ctorFields_canon` with parameters** (the legacy laws' route): a constructor image built at
`ψ` on its own parameters `Ps'` and fields `Fs`, lying in the major domain's set, is the image at
the levels the major domain names applied to the domain's parameters `Ps` and the same fields, which
fit there. Laws: `CtorCanon` (restricted to an inductive never a proposition), `cval_params`. -/
theorem ctorFields_canonP (M : Model V env) (hL : LawsCore M) (hcc : CtorCanon M) {c D : KKey}
    {cvC : ConstantVal .anon} {nP nF : Nat} (hcC : env.find? c = some (.ctorInfo cvC nP nF))
    (hnd : cvC.levelParams.Nodup) (hcl : bvarsLt 0 cvC.type = true)
    (hdef : cvC.type.allLevelParamsDefined cvC.levelParams = true)
    (hhead : (piBody (nP + nF) cvC.type).getAppFn = .const D (cvC.levelParams.map .param))
    (hN : NeverProp env D) {ls : List Level} (hls : cvC.levelParams.length = ls.length)
    {φ ψ : LevelParam → Nat} {ρ ρc σc τ : BVarIdx → V} {Rc dom : KExpr} {Ps' Fs Ps : List V}
    {X : V} (hfit : Fits M.cval env ψ ρc cvC.type (Ps' ++ Fs) σc Rc) (hPl' : Ps'.length = nP)
    (hFl : Fs.length = nF) (hdom : dom.getAppFn = .const D ls) (hX : Denotes M.cval env φ τ dom X)
    (hPs : DenotesList M.cval env φ τ (dom.getAppArgs.take nP) Ps) (hPl : Ps.length = nP)
    (hm : (Ps' ++ Fs).foldl app (M.cval c ψ) ∈ˢ X) :
    ∃ K, Denotes M.cval env φ ρ (.const c ls) K ∧
      (Ps' ++ Fs).foldl app (M.cval c ψ) = (Ps ++ Fs).foldl app K ∧
      ∃ σ R, Fits M.cval env φ ρ (cvC.type.instantiateLevelParams cvC.levelParams ls) (Ps ++ Fs)
        σ R := by
  obtain ⟨ls'', hls''⟩ : ∃ ls'' : List Level,
      ls'' = cvC.levelParams.map fun q => lvlOf (ψ q) := ⟨_, rfl⟩
  have hψ : ∀ q ∈ cvC.levelParams, Level.substFn φ cvC.levelParams ls'' q = ψ q := by
    intro q hq
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hq
    rw [substFn_at φ cvC.levelParams ls'' i q (lvlOf (ψ q)) hnd hi
      (by rw [hls'', List.getElem?_map, hi]; rfl), eval_lvlOf]
  have hK' : Denotes M.cval env φ ρ (.const c ls'') (M.cval c ψ) := by
    have h1 : Denotes M.cval env φ ρ (.const c ls'')
        (M.cval c (Level.substFn φ cvC.levelParams ls'')) :=
      Denotes.const (ci := .ctorInfo cvC nP nF) hcC (by rw [hls'', List.length_map]; rfl)
    rwa [hL.cval_params _ _ hcC (Level.substFn φ cvC.levelParams ls'') ψ
      fun q hq => hψ q hq] at h1
  have hK : Denotes M.cval env φ ρ (.const c ls)
      (M.cval c (Level.substFn φ cvC.levelParams ls)) :=
    Denotes.const (ci := .ctorInfo cvC nP nF) hcC (by rw [← hls]; rfl)
  obtain ⟨σ2, hfit2⟩ := fits_agree hfit (ρ' := ρ) fun i hi =>
    absurd (lt_of_bvarsLt hcl hi) (Nat.not_lt_zero i)
  have hfit3 := fits_inst M hL hψ hfit2 hdef
  have hR'head : (Rc.instantiateLevelParams cvC.levelParams ls'').getAppFn = .const D ls'' := by
    rw [getAppFn_inst, fits_piBody hfit2, List.length_append, hPl', hFl, hhead]
    simp only [Expr.instantiateLevelParams]
    rw [subst_params hnd (by rw [hls'', List.length_map])]
  obtain ⟨cvD, capsD, sD, hfD, hsD, hnvD⟩ := hN
  obtain ⟨heqK, σ3, R3, hFC⟩ := hcc c cvC nP nF hcC D cvD capsD sD ls ls'' φ ρ τ σ2 dom
    _ Ps Ps' Fs _ _ X hfD hsD (eval_ne_zero_of_never hnvD _) (eval_ne_zero_of_never hnvD _) hPl
    hPl' hFl hK hK' (by simpa using hfit3) hR'head hdom hX hPs hm
  exact ⟨_, hK, heqK, σ3, R3, hFC⟩

/-! ## F2 -/

variable {M : Model V env} {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
  {S : CId → Prop} {Ok : CId → Levels → Prop}

private theorem atLevels_ordinaryO (ls : Levels) :
    IxCC.Src.RecKind.atLevels ls .ordinary = .ordinary := rfl

/-- **F2 at a recursor of class `ordinary`** (W-c): the major forced, a constructor value of the
recursor's inductive (no literal: the pinned `Nat` has no parameter); the rule of its constructor;
its body (peeled of the prefix's and the fields' λs) evaluated by SrcEval in the slots of the
arguments before the major and the fields. The body runs (`runs_of_corr`, `runs_peel`) as at
`noParams`; ι and β by `paramsBlindIotaG` at the constructor's own parameters, the fields bound in
the rule's λ-domains by the law's spine; the constructor value's image at the major domain's levels
by `OrdLevels`. Takes `force` and `eval` at the smaller clock (the fundamental lemma's induction
hypothesis), the class's decided facts, and `OrdLevels`. -/
theorem fire_ordinaryK (H : FundHypsK M p κ lpsOf S Ok) {k' : Nat}
    (hforce : ∀ (s : Slot) (v : Value) (X : V), IxCC.Src.force p k' s = .ok v →
      RelSlot M p κ lpsOf S Ok s X → RelV M p κ lpsOf S Ok v X)
    (heval : ∀ (lps : List Nat) (ls : Levels) (φ : LevelParam → Nat) (σ : Sig) (Γ : List KExpr)
      (t : Term) (e : KExpr), Runs M κ Ok lps ls φ σ Γ t e →
      ∀ (ρ : IxCC.Src.Env) (ρk : BVarIdx → V) (v : Value),
      ConstsIn S t → LvAt φ lps ls → RelEnv M p κ lpsOf S Ok φ ρ σ ρk → CtxSat M φ Γ ρk →
      IxCC.Src.eval p k' ls ρ t = .ok v →
      ∃ X, Denotes M.cval env φ ρk e X ∧ RelV M p κ lpsOf S Ok v X)
    {r : CId} (hcl : recClassB p env κ r = some .ordinary)
    (hF : RecTele env (κ r) ∧ RecProg p κ S r ∧ RecCtorsRaw p env κ r ∧ RecOrdRules env (κ r) ∧
      RecBodies p env κ lpsOf r ∧ RecSites p env κ lpsOf r)
    (hO : OrdLevels M p κ lpsOf Ok r)
    {ls : Levels} {args : List Slot} {v : Value} {φ : LevelParam → Nat} {T : KExpr}
    {ρ σ : BVarIdx → V} {R : KExpr} {As : List V}
    (hrun : IxCC.Src.fire p (k' + 1) (.recr r) ls args = .ok v)
    (hargs : RelSlots M p κ lpsOf S Ok args As) (hh : HeadAt M p κ lpsOf S Ok (.recr r) ls φ (κ r) T)
    (hfit : Fits M.cval env φ ρ T As σ R) (hlen : args.length = p.headArity (.recr r))
    (hlast : LastSiteOk (M.cval (κ r) φ) As) :
    RelV M p κ lpsOf S Ok v (As.foldl app (M.cval (κ r) φ)) := by
  have hN := H.natBasis
  cases hh with
  | @recr _ _ _ ci hSr hlv hfind hOkr =>
  rw [IxCC.Src.fire_recr, later_succ] at hrun
  obtain ⟨hkind, sf, kk', lvls, np, nmot, nmin, ind, rules, ty, hd, hnv, hnp⟩ :=
    recClassB_ordinary hcl
  obtain ⟨hTele, hProg, hCtors, hRules, hBodies, hSites⟩ := hF
  -- the checked shape (`RecStored`)
  obtain ⟨⟨_, _, _, np', nmot', nmin', ni', _, rules', _, cvr, krules, hdS, hfS, _, _, hlenS,
    hruleS⟩⟩ := H.faith.recs.stored r hSr _ _ _ _ _ _ _ _ _ _ hd
  rw [hd] at hdS
  simp only [Option.some.injEq, IxCC.Src.Decl.recr.injEq] at hdS
  obtain ⟨-, -, -, rfl, rfl, rfl, rfl, -, rfl, -⟩ := hdS
  have hmI : np + nmot + nmin + 0 = np + nmot + nmin := by omega
  rw [hmI] at hfS
  rw [hfS] at hfind
  cases hfind
  have hfit : Fits M.cval env φ ρ cvr.type As σ R := hfit
  -- the rules' telescopes (`RecTele`)
  obtain ⟨cvr1, mI1, rP1, krules1, tbs, C, hf1, hty, htbs, hruleT⟩ := hTele
  rw [hfS] at hf1
  injection hf1 with hf1
  injection hf1 with e1 e2 e3 e4
  subst e1 e2 e3 e4
  -- the rules' constructors (`RecCtorsRaw`)
  obtain ⟨_, _, _, np2, _, _, _, ind2, _, _, cvr2, mI2, rP2, krules2, dom, body, mb, ls0, hd2, hf2,
    hpb, hdom, hctors⟩ := hCtors
  rw [hd] at hd2
  simp only [Option.some.injEq, IxCC.Src.Decl.recr.injEq] at hd2
  obtain ⟨-, -, -, rfl, -, -, -, rfl, -, -⟩ := hd2
  rw [hfS] at hf2
  injection hf2 with hf2
  injection hf2 with e1 e2 e3 e4
  subst e1 e2 e3 e4
  have hdomE : dom.getAppFn = .const (κ ind) ls0 := by rw [hdom, getAppFn_mkAppN]; rfl
  -- the rules, as ι with parameters reads them (`RecOrdRules`)
  obtain ⟨cvr6, mI6, rP6, krules6, dom6, body6, m6, hf6, hpb6, hrls⟩ := hRules
  rw [hfS] at hf6
  injection hf6 with hf6
  injection hf6 with e1 e2 e3 e4
  subst e1 e2 e3 e4
  rw [hpb] at hpb6
  injection hpb6 with e5 e6 e7
  subst e5 e6 e7
  -- the rule bodies (`RecBodies`)
  obtain ⟨_, _, _, np4, nmot4, nmin4, _, _, rules4, _, cvr4, mI4, rP4, krules4, hd4, hf4, hbodies,
    hclosed⟩ := hBodies
  rw [hd] at hd4
  simp only [Option.some.injEq, IxCC.Src.Decl.recr.injEq] at hd4
  obtain ⟨-, -, -, rfl, rfl, rfl, -, -, rfl, -⟩ := hd4
  rw [hfS] at hf4
  injection hf4 with hf4
  injection hf4 with e1 e2 e3 e4
  subst e1 e2 e3 e4
  -- the rule bodies' sites (`RecSites`)
  obtain ⟨_, _, _, _, _, _, _, _, rules5, _, cvr5, mI5, rP5, krules5, dom5, body5, m5, hd5, hf5,
    hpb5, hpwd, hrefs⟩ := hSites
  rw [hd] at hd5
  simp only [Option.some.injEq, IxCC.Src.Decl.recr.injEq] at hd5
  obtain ⟨-, -, -, -, -, -, -, -, rfl, -⟩ := hd5
  rw [hfS] at hf5
  injection hf5 with hf5
  injection hf5 with e1 e2 e3 e4
  subst e1 e2 e3 e4
  rw [hpb] at hpb5
  injection hpb5 with e5 e6 e7
  subst e5 e6 e7
  -- the program side (`RecProg`)
  obtain ⟨_, _, _, np3, _, _, _, ind3, rules3, _, hd3, hctP, hnat⟩ := hProg
  rw [hd] at hd3
  simp only [Option.some.injEq, IxCC.Src.Decl.recr.injEq] at hd3
  obtain ⟨-, -, -, rfl, -, -, -, rfl, rfl, -⟩ := hd3
  -- SrcEval's F2: the major, forced; the rule of its constructor
  have harity : args.length = np + nmot + nmin + 1 := by
    rw [hlen]; simp [Program.headArity, hd, IxCC.Src.Decl.recArity]
  have hAsl : As.length = np + nmot + nmin + 1 := by rw [relSlots_length hargs, harity]
  simp only [hd, hkind, Option.map_some, atLevels_ordinaryO, IxCC.Src.recChosen] at hrun
  obtain ⟨⟨j, fields⟩, hsel, hrest⟩ := Result.bind_eq_ok_iff.mp hrun
  obtain ⟨major, hmaj, hsel'⟩ := Result.bind_eq_ok_iff.mp hsel
  obtain ⟨sM, hsM⟩ : ∃ s, args[np + nmot + nmin]? = some s :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨Tm, hTm, hrelM⟩ := relSlots_get hargs hsM
  rw [List.getD_eq_getElem?_getD, hmI, hsM, Option.getD_some] at hmaj
  have hmajR := hforce _ _ _ hmaj hrelM
  have hsel2 := ofOption_eq_ok.mp hsel'
  unfold Program.selectRule at hsel2
  -- the arguments before the major, and the major's domain
  have hxl : (As.take (np + nmot + nmin)).length = np + nmot + nmin := by simp; omega
  have hsplitA : As = As.take (np + nmot + nmin) ++ [Tm] := by
    have hdrop : As.drop (np + nmot + nmin) = [Tm] := by
      rw [List.getElem?_eq_getElem (by omega)] at hTm
      rw [List.drop_eq_getElem_cons (by omega), Option.some.inj hTm,
        List.drop_eq_nil_of_le (by omega)]
    rw [← hdrop, List.take_append_drop]
  have hfitA := hfit
  rw [hsplitA] at hfitA
  obtain ⟨σ1, R1, hfp, hfm⟩ := fits_append hfitA
  have hR1 : R1 = .forallE dom body mb := by rw [fits_piBody hfp, hxl, hpb]
  subst hR1
  obtain ⟨X, hX, hTmX⟩ : ∃ X, Denotes M.cval env φ σ1 dom X ∧ Tm ∈ˢ X := by
    cases hfm with
    | cons hA hx _ => exact ⟨_, hA, hx⟩
  -- the regime at the major premise's binder, from the graph-regime site that saturated the head
  obtain ⟨vv, AA, BB, hvv, hXm, -⟩ := hlast (As.take (np + nmot + nmin)) Tm hsplitA
  obtain ⟨TT, hTT, hHT⟩ := mem_key M hfS φ ρ
  have hTT' : Denotes M.cval env φ ρ cvr.type TT := hTT
  have hreg : regime φ mb.pw ≠ 0 := last_regime hfp hTT' hHT hvv hXm
  -- the common part: ι and β, the body runs, SrcEval's value related
  have tail : ∀ (j : Nat) (fields : List Slot) (rl : IxCC.Src.Rule) (krl : RecRule .anon)
      (cvC : ConstantVal .anon) (K : V) (ys : List V) (σC : BVarIdx → V) (RC : KExpr),
      rules[j]? = some rl → krules[j]? = some krl →
      env.find? krl.ctor = some (.ctorInfo cvC np krl.nfields) →
      Denotes M.cval env φ ρ (.const krl.ctor ls0) K →
      Fits M.cval env φ ρ (cvC.type.instantiateLevelParams cvC.levelParams ls0) ys σC RC →
      ys.length = np + krl.nfields → Tm = ys.foldl app K →
      RelSlots M p κ lpsOf S Ok fields (ys.drop np) →
      (∀ t', IxCC.Src.peelLams (args.take (np + nmot + nmin) ++ fields).length rl.rhs = some t' →
        IxCC.Src.eval p k' ls (args.take (np + nmot + nmin) ++ fields).reverse t' = .ok v) →
      RelV M p κ lpsOf S Ok v (As.foldl app (M.cval (κ r) φ)) := by
    intro j fields rl krl cvC K ys σC RC hrl hkrl hcC hK hys hyl hTmK hrelF hev
    have hkm := List.mem_of_getElem? hkrl
    have hrm := List.mem_of_getElem? hrl
    obtain ⟨hkc, hknf, hcorr⟩ := hruleS j rl krl hrl hkrl
    obtain ⟨bs, b, hrhs, hbsl, -⟩ := hruleT krl hkm
    obtain ⟨hcmp, hpwR, -⟩ := hrls krl hkm
    have hregs : ∀ q ∈ bs, regime φ q.2.pw ≠ 0 := fun q hq => by
      rw [hpwR bs b hrhs hbsl q hq]; exact hreg
    -- ι and β, along the law's spine
    have hTm' : As[np + nmot + nmin]? = some (ys.foldl app K) := by rw [hTm, hTmK]
    obtain ⟨Hs, Y, hH, hY, heqY, hfitsB⟩ := paramsBlindIotaG M H.laws.iota_rule hfS hkm hcmp hcC
      hrhs hbsl hregs hfit hAsl hpb hdomE hK hys hyl hTm'
    have hxsl : (As.take (np + nmot + nmin) ++ ys.drop np).length = bs.length := by
      simp only [List.length_append, List.length_take, List.length_drop]; omega
    have hctx := ctxSat_of_fits (M := M) bs b (Γ0 := []) .nil (hfitsB b) hxsl
    -- the body runs
    obtain ⟨⟨t', ht', hnoc⟩, hrels⟩ := hbodies rl hrm
    have hden : DenotesIn M φ [] krl.rhs := fun ρ' _ => ⟨Hs, den_closed (hclosed krl hkm) hH⟩
    have hsites := ruleSites_ok H.laws hN hlv hrels hpwd hreg hden (hrefs j rl krl hrl hkrl)
    have hruns : Runs M κ Ok (lpsOf r) ls φ (idσ 0) [] rl.rhs krl.rhs :=
      runs_of_corr (termCorrS_of_termCorr hcorr (hclosed krl hkm)) hden hsites (fun d us hdu => by
        rw [evalConsts_peel ls _ rl.rhs t' ht'] at hdu
        have hm := evalConsts_mentions ls t' hdu
        rw [hnoc d] at hm
        cases hm) (fun A h => by rw [witDoms_of_termCorr hcorr] at h; cases h)
    rw [hrhs] at hruns
    have hpeel : IxCC.Src.peelLams bs.length rl.rhs = some t' := by
      rw [show bs.length = np + nmot + nmin + rl.fields by omega]; exact ht'
    have hrunsB := runs_peel bs hruns hpeel
    -- SrcEval: the body, in the slots of the arguments before the major and the fields
    have hslen : (args.take (np + nmot + nmin) ++ fields).length = bs.length := by
      rw [List.length_append, ← relSlots_length hrelF]; simp only [List.length_take,
        List.length_drop]; omega
    have hev' := hev t' (by rw [hslen]; exact hpeel)
    have henv : RelEnv M p κ lpsOf S Ok φ (args.take (np + nmot + nmin) ++ fields).reverse
        (idσ (0 + bs.length)) (pushAll (As.take (np + nmot + nmin) ++ ys.drop np) ρ) := by
      rw [Nat.zero_add, ← hslen]
      exact relEnv_pushAll (relSlots_append (relSlots_take (np + nmot + nmin) hargs) hrelF)
    have hcs : ConstsIn S t' := fun c hc => by rw [hnoc c] at hc; cases hc
    obtain ⟨X', hX', hrelX⟩ := heval (lpsOf r) ls φ _ _ t' b hrunsB _ _ v hcs hlv henv
      (by simpa using hctx) hev'
    rw [heqY]
    rwa [Denotes_functional hX' hY] at hrelX
  cases major with
  | lit n =>
    -- a literal major only at the pinned `Nat`, which has no parameter
    simp only at hsel2
    split at hsel2
    · rename_i hnatc
      exact absurd (hnat (by simpa using hnatc)).1 hnp
    · simp at hsel2
  | con c lsc ps fs =>
    simp only at hsel2
    cases hdc : p.decl? c with
    | none => simp [hdc] at hsel2
    | some dc =>
      cases dc with
      | ctor sfc lvc indc cidx npc nfc tyc =>
        simp only [hdc] at hsel2
        split at hsel2
        · rename_i hcond
          simp only [Option.some.injEq, Prod.mk.injEq] at hsel2
          obtain ⟨rfl, rfl⟩ := hsel2
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          obtain ⟨rfl, -⟩ := hcond
          cases hmajR with
          | @con _ _ _ _ ψ cvC' np'' nf'' Ps Fs ρc σc Rc hSc' hlvψ hfc' hPl hFl _ hfs' hfitc
              hOkv =>
          obtain ⟨hnpc, rl, hrl, hkey, hnF⟩ := hctP c hSc' sfc lvc cidx npc nfc tyc hdc
          obtain ⟨cv, hfcv, _⟩ := H.faith.ctor c hSc' sfc lvc _ cidx npc nfc tyc hdc
          rw [hfcv] at hfc'
          simp only [Option.some.injEq, ConstantInfo.ctorInfo.injEq] at hfc'
          obtain ⟨rfl, rfl, rfl⟩ := hfc'
          subst npc
          -- the stored rule at the constructor's index
          obtain ⟨krl, hkrl⟩ : ∃ krl, krules[cidx]? = some krl := by
            have hlt : cidx < krules.length := by
              rw [← hlenS]; exact (List.getElem?_eq_some_iff.mp hrl).1
            exact ⟨_, List.getElem?_eq_getElem hlt⟩
          obtain ⟨hkc, hknf, -⟩ := hruleS cidx rl krl hrl hkrl
          have hkc' : krl.ctor = κ c := hkc.symm.trans hkey
          have hkm := List.mem_of_getElem? hkrl
          -- the constructor: its parameter count, levels and codomain (`RecCtorsRaw`), closed and
          -- covered (`RecOrdRules`)
          obtain ⟨cvH, nFH, hfH, hlsC, hhead, -⟩ := hctors krl hkm
          rw [hkc', hfcv] at hfH
          simp only [Option.some.injEq, ConstantInfo.ctorInfo.injEq] at hfH
          obtain ⟨rfl, -, rfl⟩ := hfH
          have hnfk : nfc = krl.nfields := by rw [← hnF, hknf]
          have hcC : env.find? krl.ctor = some (.ctorInfo cv np krl.nfields) := by
            rw [hkc', hfcv, hnfk]
          obtain ⟨-, -, cvF, nPF, nFF, hfF, hcl, hdef⟩ := hrls krl hkm
          rw [hcC] at hfF
          simp only [Option.some.injEq, ConstantInfo.ctorInfo.injEq] at hfF
          obtain ⟨rfl, -, -⟩ := hfF
          have hlpsC : cv.levelParams = lpsOf c := by
            obtain ⟨ci, hci, hlps⟩ := H.faith.stored c hSc'
            rw [hfcv] at hci
            cases hci
            exact hlps
          have hnd : cv.levelParams.Nodup := by rw [hlpsC]; exact H.faith.nodup c hSc'
          have hFlk : Fs.length = krl.nfields := by rw [hFl, hnfk]
          rw [hrl] at hrest
          simp only at hrest
          -- the major's set, as the constructor's image at the major domain's levels applied to
          -- arguments that fit there and end in the value's fields
          obtain ⟨K, ys, σC, RC, hK, hys, hyl, hTmK, hyd⟩ : ∃ (K : V) (ys : List V)
              (σC : BVarIdx → V) (RC : KExpr),
              Denotes M.cval env φ ρ (.const krl.ctor ls0) K ∧
              Fits M.cval env φ ρ (cv.type.instantiateLevelParams cv.levelParams ls0) ys σC RC ∧
              ys.length = np + krl.nfields ∧
              (Ps ++ Fs).foldl app (M.cval (κ c) ψ) = ys.foldl app K ∧ ys.drop np = Fs := by
            have viaAgree : LevelsAgree cv.levelParams ls0 φ ψ → ∃ (K : V) (ys : List V)
                (σC : BVarIdx → V) (RC : KExpr),
                Denotes M.cval env φ ρ (.const krl.ctor ls0) K ∧
                Fits M.cval env φ ρ (cv.type.instantiateLevelParams cv.levelParams ls0) ys σC RC ∧
                ys.length = np + krl.nfields ∧
                (Ps ++ Fs).foldl app (M.cval (κ c) ψ) = ys.foldl app K ∧ ys.drop np = Fs := by
              intro hag
              obtain ⟨⟨K, hK, heqK⟩, σC, RC, hys⟩ :=
                majorAt_of_agree M H.laws.cval_params hfcv hcl hdef hnd hag hfitc ρ
              exact ⟨K, Ps ++ Fs, σC, RC, by rw [hkc']; exact hK, hys,
                by rw [List.length_append, hPl, hFlk], heqK, List.drop_left' hPl⟩
            by_cases hlp : cv.levelParams = []
            · -- no level parameter: the agreement is vacuous
              exact viaAgree ⟨hlsC.symm, fun k q l hq _ => by simp [hlp] at hq⟩
            · rcases hO.2 with hcc | hnl | hagr
              · -- canonicity (the legacy laws): the image at the domain's levels and parameters
                have hX' := hX
                rw [hdom] at hX'
                obtain ⟨F0, Es, -, hEs, -⟩ := (den_mkAppN _).mp hX'
                have hbl : (bvarsFrom (np + nmot + nmin - np) np).length = np := by
                  simp [bvarsFrom]
                have hEl : Es.length = np := by rw [denotesList_length hEs, hbl]
                have hargsD : dom.getAppArgs.take np = bvarsFrom (np + nmot + nmin - np) np := by
                  have h0 : ∀ (k : KKey) (l : List Level), (Expr.const k l : KExpr).getAppArgs = [] :=
                    fun _ _ => by simp [Expr.getAppArgs]
                  rw [hdom, getAppArgs_mkAppN, h0, List.nil_append,
                    List.take_of_length_le (Nat.le_of_eq hbl)]
                obtain ⟨K, hK, heqK, σ', R', hFC⟩ := ctorFields_canonP M H.laws hcc hfcv hnd hcl
                  hdef hhead (neverProp_of_check hnv) hlsC hfitc hPl hFl hdomE hX
                  (by rw [hargsD]; exact hEs) hEl hTmX
                exact ⟨K, Es ++ Fs, σ', R', by rw [hkc']; exact hK, hFC,
                  by rw [List.length_append, hEl, hFlk], heqK, List.drop_left' hEl⟩
              · exact absurd (recNoLevels_ctor hnl hfS hkm hcC) hlp
              · -- level agreement at the F2 site: the recursor head's `Ok` and the value's
                have hOkc : Ok c lsc := hOkv.resolve_left fun h => hlp (by rw [hlpsC]; exact h)
                obtain ⟨-, hl2⟩ := hagr _ _ _ _ _ _ _ _ _ _ hd _ _ _ _ _ _ _ _ _ hfS hpb hdomE ls φ
                  hOkr hlv c lsc _ _ _ _ _ _ hdc hOkc
                exact viaAgree ⟨hlsC.symm, fun k q l hq hl => by
                  rw [hlvψ k q (by rw [← hlpsC]; exact hq), List.getD_eq_getElem?_getD, hl2 k l hl,
                    Option.getD_some]⟩
          exact tail cidx (fs.map .val) rl krl cv K ys σC RC hrl hkrl hcC hK hys hyl hTmK
            (by rw [hyd]; exact relSlots_of_relVs hfs') (fun t' ht => by rw [ht] at hrest; exact hrest)
        · simp at hsel2
      | _ => simp [hdc] at hsel2
  | _ => simp at hsel2

end Sem

end IxCC.Grounding
