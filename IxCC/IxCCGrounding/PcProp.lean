import IxCCGrounding.PcRoot

/-!
# Discharging `pcInstB` at `Prop` (`IxCCGrounding.PcProp`, step Pc-Prop)

`IxCCGrounding.PcRoot` admits `PUnit.casesOn` (`subsingleton`-kind `case` entries in the PUnit
shape) at its ordinary instances, requiring `pcInstB p Inst = true` to exclude the `Prop` instance
(`w.holds ls = true`) where `SrcEval` takes the subsingleton branch (returning minor 0 directly
without forcing the major).

This module discharges `pcInstB` completely for `PUnit.casesOn` directly over `Ix.Kernel.Model`,
with no new model law and no constructor canonicity:

1. At an instance `ls` where `w.holds ls = true`, `pwNamed sh.lps w` matches
   `Level.zeronessOf (Level.subst cvD.levelParams sh.indLevels s)` (`punitShapeB`), so
   `Level.eval (Level.substFn φ cvD.levelParams sh.indLevels) s = 0` (`pwNamed_holds_zero`,
   `holds_zeronessOf`, `Level.eval_subst`).
2. Since `sh.ind`'s stored type is directly `.sort s` (`punitSortB`), `M.mem` puts the major
   domain's denotation `X` in `univ 0`.
3. `M.mem` on the unique nullary constructor `cs` (`sh.nP = 0`, `cs.nF = 0`) puts its image `K`
   in `X` as well (`den_inst_exact_cv`).
4. By proof irrelevance in `univ 0` (`mem_univ_zero`), both the major `Tm ∈ˢ X` and `K ∈ˢ X`
   equal `pt`, hence `Tm = K`.
5. `caseIotaGWith` then evaluates `casesOn` applied to `As` directly to minor 0 (`CaseSubFires`),
   matching `SrcEval`'s subsingleton branch without forcing the major.

**`rootSound_678AGpWPP_of_check`** has the exact statement of `rootSound_678AGpWP_of_check` with
`groundCheckWPP` (`groundCheckWP` plus `punitSortB`) and **without `pcInstB`**.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Src (Value Slot Term CId Program Levels)

universe w

/-! ## The PUnit `Prop`-branch shape and check -/

/-- The stored PUnit shape needed for the `Prop` subsingleton branch: zero parameters, one nullary
constructor, the inductive's stored type directly `.sort s`, and `w` equal to `zeronessOf` of `s`
at the shape's levels. -/
structure PUnitPropShape (env : KEnv) (sh : CaseShape) (w : IxCC.Src.PropWhen) : Prop where
  nP0 : sh.nP = 0
  ctors : ∃ cs, sh.ctors = [cs] ∧ cs.nF = 0
  indSort : ∃ (cvD : ConstantVal .anon) (caps : IndCaps .anon) (s : Level),
    env.find? sh.ind = some (.indInfo cvD caps) ∧ cvD.type = .sort s ∧
    pwNamed sh.lps w = some (Level.zeronessOf (Level.subst cvD.levelParams sh.indLevels s))

/-- Every `subsingleton`-kind `case` entry of `S` has `PUnitPropShape` at the shape the check reads. -/
def PUnitPropFacts (p : Program) (env : KEnv) (κ : CId → KKey) (S : CId → Prop) : Prop :=
  ∀ c r w srcs, S c → p.table.resolveOf c = some (.case r) →
    p.table.recKindOf r = some (.subsingleton w srcs) →
    ∃ sh, caseShape? env (κ c) (κ r) = some sh ∧ PUnitPropShape env sh w

/-- At a `subsingleton`-kind `case` entry, check that the inductive's stored type is directly
`.sort s` (no leading `∀` binders). -/
def punitSortB (p : Program) (env : KEnv) (κ : CId → KKey) (c : CId) : Bool :=
  match p.table.resolveOf c with
  | some (.case r) =>
    match p.table.recKindOf r with
    | some (.subsingleton _ _) =>
      match caseShape? env (κ c) (κ r) with
      | some sh =>
        match env.find? sh.ind with
        | some (.indInfo cvD _) =>
          match cvD.type with
          | .sort _ => true
          | _ => false
        | _ => false
      | none => false
    | _ => true
  | _ => true

/-- **The Pc-Prop family's check**: `groundCheckWP` plus `punitSortB` on `Sl`. -/
def groundCheckWPP (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (ann : IxCC.Src.Relevance.Ann) (Sl : List CId) : Bool :=
  groundCheckWP p env κ lpsOf ann Sl && Sl.all (punitSortB p env κ)

theorem groundCheckWP_of_WPP {p : Program} {env : KEnv} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    (h : groundCheckWPP p env κ lpsOf ann Sl = true) :
    groundCheckWP p env κ lpsOf ann Sl = true :=
  (Bool.and_eq_true _ _ ▸ h).1

theorem punitSort_of_checkWPP {p : Program} {env : KEnv} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    (h : groundCheckWPP p env κ lpsOf ann Sl = true) :
    ∀ c, c ∈ Sl → punitSortB p env κ c = true :=
  List.all_eq_true.mp (Bool.and_eq_true _ _ ▸ h).2

/-- **`groundCheckWPP` gives `PUnitPropFacts`**: every `subsingleton`-kind `case` entry of `Sl` has
the PUnit shape with `.sort s` stored directly as the inductive's type. -/
theorem punitPropFacts_of_checkWPP {p : Program} {env : KEnv} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    (h : groundCheckWPP p env κ lpsOf ann Sl = true) :
    PUnitPropFacts p env κ (· ∈ Sl) := by
  intro c r w srcs hc hr hk
  have hrec := caseRecP_of_checkWP (groundCheckWP_of_WPP h) c hc
  simp only [caseRecPB, hr, hk, Bool.and_eq_true] at hrec
  have hpu : punitShapeB p env κ ann Sl c r w srcs = true := hrec.1
  have hps := punitSort_of_checkWPP h c hc
  simp only [punitSortB, hr, hk] at hps
  cases hsh : caseShape? env (κ c) (κ r) with
  | none => rw [hsh] at hps; cases hps
  | some sh =>
    simp only [hsh] at hps
    cases hfd : env.find? sh.ind with
    | none => rw [hfd] at hps; cases hps
    | some ciD =>
      simp only [hfd] at hps
      cases ciD with
      | indInfo cvD caps =>
        simp only at hps
        cases htyD : cvD.type with
        | sort s =>
          -- read the declaration and clauses from `punitShapeB`
          have hcl := List.all_eq_true.mp hpu
          cases hdr : p.decl? r with
          | none =>
            have hf := hcl ("recrDecl", false) (by simp [punitClauses, hsh, hdr])
            cases hf
          | some dr =>
            cases dr with
            | recr sf kk lvls np nmot nmin ni ind rules ty =>
              have hnp : (np == 0 && sh.nP == 0) = true :=
                hcl ("np", np == 0 && sh.nP == 0) (by simp [punitClauses, hsh, hdr])
              have hnP0 : sh.nP = 0 := by
                simp only [Bool.and_eq_true, beq_iff_eq] at hnp
                exact hnp.2
              have hct : (sh.ctors.map (·.nF) == [0]) = true :=
                hcl ("oneCtorNoField", sh.ctors.map (·.nF) == [0]) (by simp [punitClauses, hsh, hdr])
              have hct' : sh.ctors.map (·.nF) = [0] := beq_iff_eq.mp hct
              have hctors : ∃ cs, sh.ctors = [cs] ∧ cs.nF = 0 := by
                cases hcs : sh.ctors with
                | nil => rw [hcs] at hct'; cases hct'
                | cons cs rest =>
                  rw [hcs] at hct'
                  cases rest with
                  | nil =>
                    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hct'
                    exact ⟨cs, rfl, hct'⟩
                  | cons _ _ => simp at hct'
              have hfam : famSort? env sh.ind = some (cvD.levelParams, s) := by
                simp [famSort?, hfd, htyD, finalSort]
              have hw := hcl ("w", pwNamed sh.lps w ==
                  some (Level.zeronessOf (Level.subst cvD.levelParams sh.indLevels s))) (by
                simp [punitClauses, hsh, hdr, hfam])
              exact ⟨sh, rfl, ⟨hnP0, hctors, ⟨cvD, caps, s, hfd, htyD, beq_iff_eq.mp hw⟩⟩⟩
            | _ =>
              have hf := hcl ("recrDecl", false) (by simp [punitClauses, hsh, hdr])
              cases hf
        | _ => rw [htyD] at hps; cases hps
      | _ => cases hps

/-! ## Level evaluation for `pwNamed` -/

theorem mapM_getElem?_mem : ∀ {lps : List Nat} {ps qs : List Nat},
    ps.mapM (fun q => lps[q]?) = some qs → ∀ p ∈ qs, ∃ q ∈ ps, lps[q]? = some p
  | _, [], _, h, p, hp => by simp at h; subst h; simp at hp
  | lps, q :: ps, qs, h, p, hp => by
    simp only [List.mapM_cons, bind, Option.bind] at h
    cases hq : lps[q]? with
    | none => rw [hq] at h; cases h
    | some a =>
      rw [hq] at h
      cases hrest : ps.mapM (fun q => lps[q]?) with
      | none => rw [hrest] at h; cases h
      | some as =>
        rw [hrest] at h
        simp only [pure, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact ⟨q, List.mem_cons_self .., hq⟩
        · obtain ⟨q', hq'm, hq'e⟩ := mapM_getElem?_mem hrest p hp'
          exact ⟨q', List.mem_cons_of_mem _ hq'm, hq'e⟩

/-- If `w` holds at `ls`, `φ` agrees with `ls` on `lps`, and `pwNamed lps w = some pw`, then `pw`
holds at `φ`. -/
theorem pwNamed_holds_zero {φ : LevelParam → Nat} {lps : List Nat} {ls : Levels}
    {w : IxCC.Src.PropWhen} {pw : PropWhen}
    (hlv : LvAt φ lps ls) (hn : pwNamed lps w = some pw) (hh : w.holds ls = true) :
    pw.holds φ = true := by
  cases w with
  | never => simp [IxCC.Src.PropWhen.holds] at hh
  | allZero ps =>
    simp only [pwNamed, Option.map_eq_some_iff] at hn
    obtain ⟨qs, hqs, rfl⟩ := hn
    rw [PropWhen.holds_ifAllZero, List.all_eq_true]
    intro p hp
    obtain ⟨q, hqm, hqe⟩ := mapM_getElem?_mem hqs p hp
    have hls0 : ls.getD q 0 = 0 := by
      have := List.all_eq_true.mp hh q hqm
      simpa using this
    have hφ0 : φ p = 0 := (hlv q p hqe).trans hls0
    simp [hφ0]

/-! ## `CaseSubFires` for `PUnit.casesOn` at `Prop` -/

section Sem

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv} {M : Model V env}

/-- `major_dom` generalized over any sort clause `Srt`. -/
theorem major_dom_with {cval : KKey → (LevelParam → Nat) → V} {φ : LevelParam → Nat}
    {kc kr : KKey} {sh : CaseShape} {Srt : KEnv → KKey → Prop}
    (hst : CaseStoredWith Srt env kc kr sh) {cvc : ConstantVal .anon}
    (hty : cvc.type = piTele sh.binders (.app (.bvar (sh.nM + 1)) (.bvar sh.nM)))
    {ρ σ : BVarIdx → V} {R : KExpr} {As : List V} (hfit : Fits cval env φ ρ cvc.type As σ R)
    (hlen : As.length = sh.nP + 2 + sh.nM) {Tm : V} (hTm : As[sh.nP + 1]? = some Tm) :
    ∃ τ X, Denotes cval env φ τ (Expr.mkAppN (.const sh.ind sh.indLevels) (bvarsFrom 1 sh.nP)) X ∧
      Tm ∈ˢ X ∧ DenotesList cval env φ τ (bvarsFrom 1 sh.nP) (As.take sh.nP) := by
  obtain ⟨ps, mo, t, mins, rfl, hps, _⟩ := split_ctx As sh.nP sh.nM hlen
  obtain ⟨bP, bMo, bMaj, bMin, hbs, hbP, _⟩ := split_ctx sh.binders sh.nP sh.nM hst.arity.1
  obtain ⟨mmaj, hbmaj⟩ := hst.major
  have hbm : bMaj = (Expr.mkAppN (.const sh.ind sh.indLevels) (bvarsFrom 1 sh.nP), mmaj) := by
    have := get_ctx1 bP bMin bMo bMaj
    rw [hbP, ← hbs, hbmaj] at this
    exact (Option.some.inj this).symm
  subst hbm
  rw [hty, hbs] at hfit
  obtain ⟨_, _, ⟨X, hX, htX⟩, _⟩ := fits_ctx (by omega) hfit
  rw [← hps, get_ctx1] at hTm
  obtain rfl := Option.some.inj hTm
  refine ⟨_, X, hX, htX, ?_⟩
  rw [← hps, take_left_ctx]
  have := den_bvarsFrom (cval := cval) (env := env) (φ := φ) ρ [mo] ps []
  simpa using this

/-- **`CaseSubFires` at a `PUnit.casesOn`-shaped entry**: at any instance `ls` where `w.holds ls`
is true, the major domain `X` lies in `univ 0`, so proof irrelevance identifies the major `Tm ∈ˢ X`
with the unique nullary constructor `K ∈ˢ X`, and `caseIotaGWith` reduces `casesOn` applied to `As`
directly to minor 0. Directly over `Ix.Kernel.Model` (δ, guarded ι, `CvalParams`, `M.mem`). -/
theorem caseSubFires_of_punit (hδ : DefnValue M) (hι : IotaLaw M.cval env) (hcv : CvalParams M)
    {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat} {S : CId → Prop}
    {Ok : CId → Levels → Prop} {R Wd : Prop} {Kd : CId → Prop}
    (hF : FaithWithK R Wd Kd p env κ lpsOf S) {c r : CId} {w0 : IxCC.Src.PropWhen} {sh : CaseShape}
    (hSc : S c) (hres : p.table.resolveOf c = some (.case r))
    (hk : p.table.recKindOf r = some (.subsingleton w0 []))
    (hst : CaseStoredWith (fun _ _ => True) env (κ c) (κ r) sh)
    (hpr : CaseProg p κ S r sh) (hB : CaseRulesBlind env (κ r))
    (hPS : PUnitPropShape env sh w0) :
    CaseSubFires M p κ lpsOf S Ok c := by
  intro r' sf kk lvls np nmot nmin ni ind rules ty w hres' hd ls φ T ρ σ R' As hkind hh hfit
    hAsl hlast
  have hrr : r' = r := by rw [hres] at hres'; cases hres'; rfl
  subst hrr
  obtain ⟨sf0, kk0, lvls0, ind0, rules0, ty0, hd0, -, -⟩ := hpr.recr
  rw [hd0] at hd
  simp only [Option.some.injEq, IxCC.Src.Decl.recr.injEq] at hd
  obtain ⟨-, -, -, rfl, rfl, rfl, rfl, rfl, -, -⟩ := hd
  -- `w0.holds ls = true` and `w = w0`
  have hw0 : w0.holds ls = true := by
    rw [hk] at hkind
    simp only [Option.map_some, IxCC.Src.RecKind.atLevels] at hkind
    cases hwh : w0.holds ls with
    | true => rfl
    | false => rw [hwh] at hkind; simp at hkind
  -- `casesOn` stored declaration and level parameters
  obtain ⟨cvc, hint, hfc, hlps_sh, hty⟩ := hst.casesOnStored
  cases hh with
  | cases _ hlv hfind _ =>
  rw [hfc] at hfind
  cases hfind
  have hfit' : Fits M.cval env φ ρ cvc.type As σ R' := hfit
  have hlps_eq : lpsOf c = sh.lps := by
    obtain ⟨ci', hci', hlps'⟩ := hF.stored c hSc
    rw [hfc] at hci'
    cases hci'
    exact hlps'.symm.trans hlps_sh
  have hlv_sh : LvAt φ sh.lps ls := hlps_eq ▸ hlv
  -- unpack PUnitPropShape
  obtain ⟨hnP0, ⟨cs, hctors, hcsnF⟩, ⟨cvD, caps, s, hfD, htyD, hpw⟩⟩ := hPS
  have hnM1 : sh.nM = 1 := by simp [CaseShape.nM, hctors]
  have hlen : As.length = sh.nP + 2 + sh.nM := by omega
  -- `Level.eval (Level.substFn φ cvD.levelParams sh.indLevels) s = 0`
  have hs0 : Level.eval (Level.substFn φ cvD.levelParams sh.indLevels) s = 0 := by
    have hph := pwNamed_holds_zero hlv_sh hpw hw0
    rw [holds_zeronessOf, beq_iff_eq, Level.eval_subst] at hph
    exact hph
  -- the major `Tm` lies in `X = M.cval sh.ind (Level.substFn φ cvD.levelParams sh.indLevels)`
  obtain ⟨Tm, hTm⟩ : ∃ Tm, As[sh.nP + 1]? = some Tm :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨τ, X, hX, hTmX, -⟩ := major_dom_with hst hty hfit' hlen hTm
  rw [hnP0] at hX
  simp only [bvarsFrom] at hX
  have hXeq : X = M.cval sh.ind (Level.substFn φ cvD.levelParams sh.indLevels) := by
    cases hX with
    | const hfD' _ =>
      rw [hfD] at hfD'; cases hfD'; rfl
  -- `X ∈ˢ univ 0` via `M.mem` on `sh.ind`
  have hX0 : X ∈ˢ (univ 0 : V) := by
    obtain ⟨TD, hTD, hXTD⟩ := mem_key M hfD (Level.substFn φ cvD.levelParams sh.indLevels) ρ
    simp only [ConstantInfo.toConstantVal, htyD] at hTD
    rw [den_sort.mp hTD, hs0] at hXTD
    rwa [hXeq]
  -- the unique nullary constructor `cs` has image `K ∈ˢ X`
  have hcs0 : sh.ctors[0]? = some cs := by rw [hctors]; rfl
  obtain ⟨cvC, pbs, fbs, hfC, hCinst, hpbs, hfbs⟩ := hst.ctors 0 cs hcs0
  obtain ⟨cvC', hfC', hlenC, -, -, -⟩ := hst.wf.ctorRaw 0 cs hcs0
  rw [hfC] at hfC'
  cases hfC'
  obtain ⟨-, -, hfl⟩ := hst.minors 0 cs hcs0
  have hpbs0 : pbs = [] := by
    have h1 := congrArg List.length hpbs
    simp [hnP0] at h1
    exact h1
  have hfbs0 : fbs = [] := by
    have h1 := congrArg List.length hfbs
    simp [liftTele_length, hfl, hcsnF] at h1
    exact h1
  rw [hpbs0, hfbs0, hnP0, hcsnF] at hCinst
  simp only [piTele, bvarsFrom] at hCinst
  let K : V := M.cval cs.key (Level.substFn φ cvC.levelParams sh.indLevels)
  have hK : Denotes M.cval env φ ρ (.const cs.key sh.indLevels) K :=
    Denotes.const hfC hlenC.symm
  have hKX : K ∈ˢ X := by
    obtain ⟨TC, hTC, hKTC⟩ := mem_key M hfC (Level.substFn φ cvC.levelParams sh.indLevels) ρ
    simp only [ConstantInfo.toConstantVal] at hTC
    have hTC' := den_inst_exact_cv M hcv hTC
    rw [hCinst] at hTC'
    have hXρ : Denotes M.cval env φ ρ (.const sh.ind sh.indLevels) X := den_const_env hX
    rwa [Denotes_functional hTC' hXρ] at hKTC
  -- proof irrelevance in `univ 0`: `Tm = pt = K`
  have hTmK : Tm = K := (mem_univ_zero hX0 hTmX).trans (mem_univ_zero hX0 hKX).symm
  -- apply `caseIotaGWith` at constructor 0 with `Ps = []`, `Fs = []`
  have hmaj : As[sh.nP + 1]? = some (([] ++ []).foldl app K) := by
    rw [hTm, hTmK]; rfl
  obtain ⟨Mn, hMn, heq, -⟩ :=
    caseIotaGWith M hδ hι hcv hst hB cvc _ hint hfc φ ρ σ R' As hfit' hlen hlast 0 cs cvC K [] []
      ρ _ hcs0 hfC hK .nil (by simp [hnP0]) (by simp [hcsnF]) hmaj
  refine ⟨Mn, ?_, heq⟩
  rw [show sh.nP + 1 + 0 + 1 = sh.nP + 2 + 0 by omega]
  exact hMn

/-! ## The root theorem stack without `pcInstB` -/

/-- `CaseSubFires` at every `subsingleton`-kind `case` entry of `S`, from `CaseFactsReadP`,
`NoCanonA`, and `PUnitPropFacts`. -/
theorem caseSubFires_of_instWPP (hδ : DefnValue M) (hι : IotaLaw M.cval env) (hcv : CvalParams M)
    {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat} {S : CId → Prop}
    {Ok : CId → Levels → Prop} {R Wd : Prop} {Kd : CId → Prop}
    (hF : FaithWithK R Wd Kd p env κ lpsOf S) (hC : CaseFactsReadP p env κ S)
    (hNC : NoCanonA p env κ S) (hPU : PUnitPropFacts p env κ S) :
    ∀ c r w, S c → p.table.resolveOf c = some (.case r) →
      p.table.recKindOf r = some (.subsingleton w []) →
      CaseSubFires M p κ lpsOf S Ok c := by
  intro c r w hSc hr hk
  obtain ⟨sh, hsh, hst, hpr⟩ := hC c r hSc hr (by rw [hk]; simp)
  obtain ⟨sh', hsh', hps⟩ := hPU c r w [] hSc hr hk
  rw [hsh] at hsh'
  cases hsh'
  exact caseSubFires_of_punit hδ hι hcv hF hSc hr hk hst hpr (hNC.cases c r hSc hr) hps

/-- **The fundamental lemma's hypotheses at `OkIn`, without `PcInst`**: at every `OkIn` instance
of a `subsingleton w []` `case` entry, `w.holds ls` either fails (`ordinary`, handled by `CaseFires`)
or holds (`subsingleton w []`, handled by `CaseSubFires`). -/
theorem fundHypsK_of_instWPP (hL : LawsCore M) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {S : CId → Prop}
    {Inst : List (CId × Levels)} {Wd : Prop}
    (hcanon : CtorCanon M ∨ ∀ r, S r →
      (recClassB p env κ r = some .flat ∨ recClassB p env κ r = some .noParams) →
        RecNoLevels env (κ r))
    (hG : GroundFactsWithK (RecFacts p env κ lpsOf S) Wd (KindsP p) p env κ lpsOf ann S)
    (hT : SitesOk M p κ lpsOf ann S) (hI : InstClosed p Inst) (hU : InstUniform p env κ lpsOf Inst)
    (hcases : ∀ c r, S c → p.table.resolveOf c = some (.case r) →
      p.table.recKindOf r ≠ some .empty → CaseFires M p κ lpsOf S (OkIn p ann Inst) c)
    (hsub : ∀ c r w, S c → p.table.resolveOf c = some (.case r) →
      p.table.recKindOf r = some (.subsingleton w []) →
      CaseSubFires M p κ lpsOf S (OkIn p ann Inst) c)
    (hW : WordFires M p κ lpsOf S (OkIn p ann Inst)) :
    FundHypsK M p κ lpsOf S (OkIn p ann Inst) where
  laws := hL
  canon := hcanon
  ordinary := fun r hr hk => ⟨fun _ hOk => hOk.1.1.trans (hG.faith.lvls r hr),
    .inr (.inr (recLevelAgree_of_mem hU.2 (fun _ _ h => h.2) hk))⟩
  natBasis := hG.natBasis
  faith := (hG.faith.monoW fun _ => trivial).monoK fun _ _ => trivial
  words := hW
  kindAt := fun c r ls hS hr _ => by
    rcases (hG.faith.caseRec c r hS hr).1 with hk | hk | ⟨w, hk⟩
    · exact .inl (by rw [hk]; rfl)
    · exact .inr (.inl hk)
    · rw [hk]
      simp only [Option.map_some, IxCC.Src.RecKind.atLevels]
      cases hwh : w.holds ls with
      | true => exact .inr (.inr ⟨w, rfl⟩)
      | false => exact .inl rfl
  cases := fun c r hS hr ⟨ls, _, hk⟩ => hcases c r hS hr fun he => by
    rw [he] at hk
    simp [IxCC.Src.RecKind.atLevels] at hk
  subCases := fun c r hS hr ⟨ls, w, _, hk⟩ => by
    rcases (hG.faith.caseRec c r hS hr).1 with hk' | hk' | ⟨w', hk'⟩
    · simp [hk', IxCC.Src.RecKind.atLevels] at hk
    · simp [hk', IxCC.Src.RecKind.atLevels] at hk
    · exact hsub c r w' hS hr hk'
  eqn := fun c thm body hS hr => by
    obtain ⟨⟨d, hsh⟩, _⟩ := hG.eqns c thm body hS hr
    exact ⟨d.body, fun φ ρ X hX => Denotes_functional (eqn_den M hsh φ ρ) hX,
      fun ls φ hOk hlv => runs_of_sitesInWK hL hG hT hI hS hOk (.eqn hr hsh) hlv⟩
  value := fun c ls _ _ _ _ _ _ hS hOk hr hd hf φ hlv =>
    runs_of_sitesInWK hL hG hT hI hS hOk (.value hr hd hf) hlv

/-- `rootSound_678ASWP` without `PcInst`, directly over `Ix.Kernel.Model`. -/
theorem rootSound_678ASWPP {p : Program}
    {κ : CId → KKey} {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    {root : CId} {args : List FoTy} {res : FoTy} {Inst : List (CId × Levels)}
    (hG : GroundFactsWithK (RecFacts p env κ lpsOf (· ∈ Sl)) (WordFacts p env κ lpsOf (· ∈ Sl))
      (KindsP p) p env κ lpsOf ann (· ∈ Sl))
    (hC : CaseFactsReadP p env κ (· ∈ Sl))
    (hPU : PUnitPropFacts p env κ (· ∈ Sl))
    (hNC : NoCanonA p env κ (· ∈ Sl)) (hLD : LitDefs env)
    (hI : InstClosed p Inst) (hU : InstUniform p env κ lpsOf Inst) (hroot : (root, []) ∈ Inst)
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    (hT : SitesOk M p κ lpsOf ann (· ∈ Sl))
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X :=
  have hLN := lawsNoCanon_of_model M hLD
  rootSound_coreWK hLN.core hG hR
    (allPK (fundHypsK_of_instWPP hLN.core (.inr hNC.recs) hG hT hI hU
      (caseFires_of_instWP hLN.defn_value hLN.iota_rule hLN.cval_params hG.faith hG.natBasis hC
        hNC hU)
      (caseSubFires_of_instWPP hLN.defn_value hLN.iota_rule hLN.cval_params hG.faith hC hNC hPU)
      (wordFires_of_facts hLN.core M.proj_law M.graded hG.natBasis hG.faith.words)))
    ⟨hR.ok, hroot⟩ hA hrun hrb hRT hO φ ρ X hX

/-- `rootSound_678ASWPP` with every site typed from `M.graded`. -/
theorem rootSound_678AGWPP {p : Program}
    {κ : CId → KKey} {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    {root : CId} {args : List FoTy} {res : FoTy} {Inst : List (CId × Levels)}
    (hG : GroundFactsWithK (RecFacts p env κ lpsOf (· ∈ Sl)) (WordFacts p env κ lpsOf (· ∈ Sl))
      (KindsP p) p env κ lpsOf ann (· ∈ Sl))
    (hC : CaseFactsReadP p env κ (· ∈ Sl))
    (hPU : PUnitPropFacts p env κ (· ∈ Sl))
    (hNC : NoCanonA p env κ (· ∈ Sl)) (hLD : LitDefs env)
    (hI : InstClosed p Inst) (hU : InstUniform p env κ lpsOf Inst) (hroot : (root, []) ∈ Inst)
    (hH : HeadRegime p env κ lpsOf ann (· ∈ Sl))
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X :=
  rootSound_678ASWPP hG hC hPU hNC hLD hI hU hroot hR
    (sitesOk_of_headRegime M.defn_value M.graded hH) hA hrun hrb hRT hO φ ρ X hX

/-- `rootSound_678AGWP_of_check` with `groundCheckWPP` and **without `pcInstB`**. -/
theorem rootSound_678AGWPP_of_check {p : Program}
    {κ : CId → KKey} {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    {root : CId} {args : List FoTy} {res : FoTy} {Inst : List (CId × Levels)}
    (hchk : groundCheckWPP p env κ lpsOf ann Sl = true) (hnc : noCanonAB p env κ Sl = true)
    (hld : litDefsB env = true) (hinst : instCheckB p env κ lpsOf [root] Inst = true)
    (hhr : headRegimeSB p env κ lpsOf ann Sl = true)
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X := by
  obtain ⟨hseeds, hI, hU⟩ := instFacts_of_check hinst
  have hwp := groundCheckWP_of_WPP hchk
  exact rootSound_678AGWPP (groundFactsWP_of_check hwp) (caseFactsReadP_of_checkWP hwp)
    (punitPropFacts_of_checkWPP hchk) (noCanonA_of_check hnc) (litDefs_of_check hld) hI hU
    (hseeds root (List.mem_singleton_self _))
    (headRegimeS_of_sansK (sansK_of_checkWP hwp) hhr) hR hA hrun hrb hRT hO φ ρ X hX

/-- **The Pc-Prop root theorem**, directly over `Ix.Kernel.Model`: `rootSound_678AGpWP_of_check`
with `groundCheckWPP` and **`pcInstB` completely discharged** (admitting `PUnit.casesOn` at both
ordinary and `Prop` instances). -/
theorem rootSound_678AGpWPP_of_check {p : Program}
    {κ : CId → KKey} {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    {root : CId} {args : List FoTy} {res : FoTy} {Inst : List (CId × Levels)}
    (hchk : groundCheckWPP p (selEnv p env κ Sl) κ lpsOf ann Sl = true)
    (hnc : noCanonAB p (selEnv p env κ Sl) κ Sl = true)
    (hld : litDefsB (selEnv p env κ Sl) = true)
    (hinst : instCheckB p (selEnv p env κ Sl) κ lpsOf [root] Inst = true)
    (hhr : headRegimeSB p (selEnv p env κ Sl) κ lpsOf ann Sl = true)
    (hR : RootFacts p (selEnv p env κ Sl) κ ann (· ∈ Sl) root args res)
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o)
    (hRT : ResultTag p (selEnv p env κ Sl) κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X := by
  have hS := selRetype_selEnv p env κ Sl
  obtain ⟨M', hc⟩ := model_selRetype M hS
  have hden := denotes_selRetype hS M.cval φ
  have h := rootSound_678AGWPP_of_check (M := M') hchk hnc hld hinst hhr hR hA hrun hrb hRT
    hO φ ρ X (by rw [hc, hden]; exact hX)
  rw [hc, hden] at h
  exact h

end Sem

end IxCC.Grounding
