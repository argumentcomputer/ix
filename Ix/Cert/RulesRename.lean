import IxC.Kernel.Rules.Rel
import IxC.Kernel.Verify.Rename.Core7
import IxC.Kernel.Verify.Rename.Native3
import IxC.Kernel.Verify.Leaves

/-! # The rules tier commutes with renaming

The six relations of the rules tier (`Rules.Red`, `Rules.DefEq`, `Rules.Infer`,
`Rules.Certs`, `Rules.DefEqList`, `Rules.EtaProjCerts`) are preserved by a renaming
of the input keys, `Expr.mapKeys f`, between environments related as the renaming
walk relates them (`EnvRelG`). This is the derivation-level counterpart of the
run-level simulations (`IxC/Kernel/Verify/Rename/Core*.lean`), and it reuses their
per-helper commutations.

**The hypotheses (`Renaming`).**
* The environments are related at the trivial link: every lookup at a good key is
  answered alike, renamed.
* Every key the source environment answers is good. A rescue rule reads a recursor
  that its subject does not mention, so its key's goodness cannot come from the
  subject.
* The scope allows every role.

**What each relation's renaming states.**
* A reduction or inference keeps goodness: a good subject has a good reduct or
  type.
* The other relations take their subjects' goodness as premises.

So `f` only ever meets good keys, on which it is injective. -/

namespace Ix.Cert.RulesRename

open Ix.Kernel Ix.Kernel.Rules

variable {md md' : Mode} {f : md.Id → md'.Id} {P : KeyScope md}

/-- **Environments related by a renaming, for the rules tier** (see the module
docstring). -/
structure Renaming (P : KeyScope md) (f : md.Id → md'.Id) (env : Env md) (env' : Env md') : Prop where
  rel : EnvRelG P f TrueLink env env'
  found : ∀ (k : Key md) (c : ConstantInfo md), env.find? k = some c → k.Good P
  roles : P.All

variable {env : Env md} {env' : Env md'}

namespace Renaming

theorem find (hR : Renaming P f env env') {k : Key md} {c : ConstantInfo md}
    (h : env.find? k = some c) : env'.find? (k.map f) = some (c.mapKeys f) := by
  rw [hR.rel.find k (hR.found k c h), h]
  rfl

theorem good (hR : Renaming P f env env') {k : Key md} {c : ConstantInfo md}
    (h : env.find? k = some c) : c.Good P :=
  hR.rel.good k c (hR.found k c h) h

end Renaming

/-! ## Helpers -/

theorem head_map {e : Expr md} {c : Key md} {us : List Level} (h : e.getAppFn = .const c us) :
    (e.mapKeys f).getAppFn = .const (c.map f) us := by
  rw [← Expr.mapKeys_getAppFn, h]
  rfl

theorem head_good {e : Expr md} {c : Key md} {us : List Level} (he : e.Good P)
    (h : e.getAppFn = .const c us) : c.Good P := by
  have hg := Expr.Good.getAppFn he
  rw [h] at hg
  exact hg

/-- A body opened at a good binder domain is good. -/
theorem good_inst_fvar {body ty : Expr md} {d : Nat} (hb : body.Good P) (ht : ty.Good P) :
    (body.instantiate1 (.fvar d ty)).Good P :=
  Expr.Good.instantiate1 (v := .fvar d ty) hb ht 0

theorem natBinOpNames_contains_map (k : Key md) :
    (natBinOpNames (md := md')).contains (k.map f) = (natBinOpNames (md := md)).contains k := by
  simp [natBinOpNames, natDivModNames]

theorem natBinOpNames_mem_map {k : Key md} (h : k ∈ (natBinOpNames (md := md))) :
    k.map f ∈ (natBinOpNames (md := md')) := by
  rw [← List.contains_iff_mem, natBinOpNames_contains_map, List.contains_iff_mem]
  exact h

/-- The parameter comparands of a fired rule are good. -/
theorem comparands_good {rl : RecRule md} (hrl : rl.Good P) (lps : List LevelParam)
    (us : List Level) (cvjLps : List LevelParam) {args : List (Expr md)}
    (hargs : Expr.GoodList P args) (rP : Nat) :
    Expr.GoodList P (recFireComparands rl lps us cvjLps args rP).2 := by
  unfold recFireComparands
  cases hfire : rl.fire with
  | nested lvls pins =>
    have hp : Expr.GoodList P pins := by
      have := hrl.2.1
      rw [hfire] at this
      exact this
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨p, hp', rfl⟩ := hx
    exact Expr.Good.instSpine (hargs.take rP) (Expr.Good.instantiateLevelParams (hp p hp') _ _)
  | inert => exact hargs.take _
  | plain => exact hargs.take _

/-! ## The renaming -/

mutual

/-- **A reduction, renamed**: a good subject has a good reduct, and the renamed
subject reduces to the renamed reduct. -/
theorem red_rename (hR : Renaming P f env env') :
    ∀ {d : Nat} {e e' : Expr md}, Red env d e e' → e.Good P →
      e'.Good P ∧ Red env' d (e.mapKeys f) (e'.mapKeys f)
  | _, _, _, .refl, he => ⟨he, .refl⟩
  | _, _, _, .trans h₁ h₂, he => by
    obtain ⟨g₁, r₁⟩ := red_rename hR h₁ he
    obtain ⟨g₂, r₂⟩ := red_rename hR h₂ g₁
    exact ⟨g₂, .trans r₁ r₂⟩
  | _, _, _, .appFn h, he => by
    obtain ⟨g, r⟩ := red_rename hR h he.1
    exact ⟨⟨g, he.2⟩, .appFn r⟩
  | _, _, _, .projArg h, he => by
    obtain ⟨g, r⟩ := red_rename hR h he.2
    exact ⟨⟨he.1, g⟩, .projArg r⟩
  | _, _, _, .betaGate hnev, he => by
    refine ⟨Expr.Good.instantiate1 he.1.2 he.2 0, ?_⟩
    rw [Expr.mapKeys_instantiate1]
    exact .betaGate hnev
  | _, _, _, .beta hta hd, he => by
    obtain ⟨gta, ita⟩ := infer_rename hR hta he.2
    refine ⟨Expr.Good.instantiate1 he.1.2 he.2 0, ?_⟩
    rw [Expr.mapKeys_instantiate1]
    exact .beta ita (defEq_rename hR hd gta he.1.1)
  | _, _, _, .delta hu, he =>
    ⟨unfoldDefinition_good hR.rel he hu,
      .delta (by rw [unfoldDefinition_ren hR.rel he, hu]; rfl)⟩
  | _, _, _, .natLit h, _ => by
    refine ⟨natLitToConstructor_good hR.roles.pre _, ?_⟩
    rw [natLitToConstructor_mapKeys]
    exact .natLit (by rw [natLitSupported_ren hR.rel]; exact h)
  | _, _, _, .strLit h, _ => by
    refine ⟨strLitToConstructor_good hR.roles.pre hR.roles.str _, ?_⟩
    rw [strLitToConstructor_mapKeys]
    exact .strLit (by rw [strLitSupported_ren hR.rel hR.roles.str]; exact h)
  | _, _, _, .natSucc hsup hw hn, he => by
    obtain ⟨-, rw'⟩ := red_rename hR hw he.2
    exact ⟨trivial, .natSucc (by rw [natLitSupported_ren hR.rel]; exact hsup) rw'
      (by rw [rawNatLit?_mapKeys]; exact hn)⟩
  | _, _, _, .natOp (c := c) hc hst hwa hn₁ hwb hn₂ hr, he => by
    obtain ⟨⟨hcg, ha⟩, hb⟩ := he
    obtain ⟨-, rwa⟩ := red_rename hR hwa ha
    obtain ⟨-, rwb⟩ := red_rename hR hwb hb
    refine ⟨natOpResult_good hR.roles.pre c _ _ _ hr, ?_⟩
    exact .natOp (natBinOpNames_mem_map hc) (by rw [natOpStored_ren hR.rel hcg]; exact hst) rwa
      (by rw [rawNatLit?_mapKeys]; exact hn₁) rwb (by rw [rawNatLit?_mapKeys]; exact hn₂)
      (by rw [natOpResult_map, hr]; rfl)
  | _, _, _, .proj (sn := sn) (e := u) (entry := entry) (cvC := cvC) hent hhead hi hlen hus hfire
      hctor hcerts, he => by
    obtain ⟨hsn, hu⟩ := he
    have hargs := Expr.Good.getAppArgs hu
    refine ⟨Expr.GoodList.getD hargs _, ?_⟩
    have hcerts' := certs_rename hR hcerts
      (Expr.Good.instantiateLevelParams (hR.good hctor).2 _ _) hargs
    have key := Red.proj (env := env') (sn := sn.map f) (e := u.mapKeys f)
      (entry := entry.mapKeys f) (cvC := cvC.mapKeys f)
      (by rw [hR.rel.findProj? hsn, hent]; rfl) (head_map hhead) hi
      (by rw [Expr.getAppArgs_mapKeys, List.length_map]; exact hlen) hus
      (by rw [ProjEntry.fireOk_mapKeys]; exact hfire) (hR.find hctor)
      (by simpa [Expr.getAppArgs_mapKeys] using hcerts')
    rw [Expr.getAppArgs_mapKeys, List.getD_map_bvar] at key
    exact key
  | _, _, _, .iota (e := e) (c := c) (us := us) (cv := cv) (mI := mI) (rP := rP) (rules := rules)
      (major := major) (cj := cj) (usj := usj) (cvj := cvj) (rl := rl) (residual := residual)
      hhead hrec hlen hus hmajor hmhead hctor hrule hmlen hfire hlv hparams hcertR hcertC hres
      hidx, he => by
    have hargs := Expr.Good.getAppArgs he
    have hcG := hR.good hrec
    obtain ⟨gmaj, rmaj⟩ := red_rename hR hmajor (Expr.GoodList.getD hargs mI)
    have hmargs := Expr.Good.getAppArgs gmaj
    have hcjG := hR.good hctor
    have hrlG : rl.Good P := hcG.2 rl (List.mem_of_find?_eq_some hrule)
    have hcj : cj.Good P := hR.found _ _ hctor
    have hcmp := comparands_good hrlG cv.levelParams us cvj.levelParams hargs rP
    refine ⟨Expr.Good.mkAppN (Expr.Good.instantiateLevelParams hrlG.2.2 _ _)
      (by simp only [Expr.goodList_append]; exact ⟨hargs.take _, hmargs.drop _⟩), ?_⟩
    have key := Red.iota (env := env') (d := _) (e := e.mapKeys f) (c := c.map f) (us := us)
      (cv := cv.mapKeys f) (mI := mI) (rP := rP) (rules := rules.map (RecRule.mapKeys f))
      (major := major.mapKeys f) (cj := cj.map f) (usj := usj) (cvj := cvj.mapKeys f)
      (rl := rl.mapKeys f) (residual := residual.mapKeys f)
      (head_map hhead) (hR.find hrec)
      (by rw [Expr.getAppArgs_mapKeys, List.length_map]; exact hlen) hus
      (by rw [Expr.getAppArgs_mapKeys, List.getD_map_bvar]; exact rmaj)
      (head_map hmhead) (hR.find hctor)
      (by rw [rules_find?_ren hR.rel.inj hcG.2 hcj, hrule]; rfl)
      (by rw [Expr.getAppArgs_mapKeys, List.length_map]; exact hmlen)
      (by simpa using hfire)
      (by simpa only [Expr.getAppArgs_mapKeys, ConstantVal.mapKeys_levelParams,
        recFireComparands_mapKeys] using hlv)
      (fun hc => by
        have := defEqList_rename hR (hparams (by simpa using hc)) (hmargs.take _) hcmp
        simpa only [Expr.getAppArgs_mapKeys, ConstantVal.mapKeys_levelParams,
          recFireComparands_mapKeys, RecRule.mapKeys_ctorParams, List.map_take] using this)
      (by
        have := certs_rename hR hcertR (Expr.Good.instantiateLevelParams hcG.1.2 _ _)
          (by simp only [Expr.goodList_append, Expr.goodList_cons, Expr.goodList_nil, and_true]
              exact ⟨hargs.take _, gmaj⟩)
        simpa [Expr.getAppArgs_mapKeys] using this)
      (by
        have := certs_rename hR hcertC (Expr.Good.instantiateLevelParams hcjG.2 _ _) hmargs
        simpa [Expr.getAppArgs_mapKeys] using this)
      (fun hne => by
        simp only [ConstantVal.mapKeys_type, ConstantVal.mapKeys_levelParams,
          ← Expr.mapKeys_instantiateLevelParams, Expr.getAppArgs_mapKeys, piResidual_mapKeys,
          hres hne, Option.map_some])
      (fun hne => by
        have hresG := piResidual_good (Expr.Good.instantiateLevelParams hcjG.2 _ _) hmargs
          (hres hne)
        have := defEqList_rename hR (hidx hne) ((Expr.Good.getAppArgs hresG).drop _)
          ((hargs.take _).drop _)
        rw [Expr.getAppArgs_mapKeys, Expr.getAppArgs_mapKeys, RecRule.mapKeys_ctorParams,
          ← List.map_take, ← List.map_drop, ← List.map_drop]
        exact this)
    simpa [Expr.getAppArgs_mapKeys] using key
  | _, _, _, .rescueK (major := major) (fab := fab) (tmaj := tmaj) (rl := rl) (cnP := cnP)
      (ust := ust) hrec hk hctor hres hind htm htmaj hthead hlv hnP hfab hws hb hlv' hcerts htf hdt
      hpi, he => by
    have hrlG : rl.Good P := (hR.good hrec).2 rl (List.mem_singleton_self rl)
    have hcvjG := hR.good hctor
    obtain ⟨gtm, itm⟩ := infer_rename hR htm he
    obtain ⟨gtmaj, rtmaj⟩ := red_rename hR htmaj gtm
    have htargs := Expr.Good.getAppArgs gtmaj
    have hfabG : fab.Good P := by
      rw [hfab]
      exact Expr.Good.mkAppN hrlG.1 (htargs.take _)
    obtain ⟨gtf, itf⟩ := infer_rename hR htf hfabG
    refine ⟨hfabG, ?_⟩
    have hcerts' := certs_rename hR hcerts (Expr.Good.instantiateLevelParams hcvjG.2 _ _)
      (htargs.take _)
    exact Red.rescueK (env := env') (hR.find hrec) hk (hR.find hctor)
      (by rw [ConstantVal.mapKeys_type, ← Expr.mapKeys_piResult, ← Expr.mapKeys_getAppFn, hres]; rfl)
      (hR.find hind) itm rtmaj (head_map hthead) hlv
      (by rw [Expr.getAppArgs_mapKeys, List.length_map]; exact hnP)
      (by rw [hfab, Expr.mapKeys_mkAppN, Expr.getAppArgs_mapKeys, List.map_take]; rfl)
      (by rw [Expr.wscopedB_mapKeys]; exact hws) (by rw [Expr.looseBVarsBounded_mapKeys]; exact hb)
      (by rw [fvarLeaves_all_contains_ren hR.rel.inj hfabG he]; exact hlv')
      (by simpa only [Expr.getAppArgs_mapKeys, List.map_take, ConstantVal.mapKeys_type,
            ConstantVal.mapKeys_levelParams, Expr.mapKeys_instantiateLevelParams] using hcerts')
      itf (defEq_rename hR hdt gtmaj gtf) (defEq_rename hR hpi hfabG he)
  | _, _, _, .rescueEta (major := major) (fab := fab) (tmaj := tmaj) (rl := rl) (T := T)
      (ust := ust) (caps := caps) hrec heta hctor hres hind htm htmaj hthead hlen hlv hnz hfab hws
      hb hlv' hcerts hproj hpi, he => by
    have hrlG : rl.Good P := (hR.good hrec).2 rl (List.mem_singleton_self rl)
    have hcvjG := hR.good hctor
    have hT : T.Good P := hR.found _ _ hind
    obtain ⟨gtm, itm⟩ := infer_rename hR htm he
    obtain ⟨gtmaj, rtmaj⟩ := red_rename hR htmaj gtm
    have htargs := Expr.Good.getAppArgs gtmaj
    have hfargs : Expr.GoodList P (etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields) := by
      unfold etaFabArgsE
      simp only [Expr.goodList_append]
      exact ⟨htargs, etaProjs_good hT htargs he _⟩
    have hfabG : fab.Good P := by
      rw [hfab]
      exact Expr.Good.mkAppN hrlG.1 hfargs
    refine ⟨hfabG, ?_⟩
    have hcerts' := certs_rename hR hcerts (Expr.Good.instantiateLevelParams hcvjG.2 _ _) hfargs
    have hargsE : (etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields).map (Expr.mapKeys f) =
        etaFabArgsE env' (T.map f) ust (tmaj.mapKeys f).getAppArgs (major.mapKeys f)
          (caps.mapKeys f).etaFields := by
      rw [Expr.getAppArgs_mapKeys, etaFabArgsE_ren hR.rel hT]
      rfl
    exact Red.rescueEta (env := env') (hR.find hrec) heta (hR.find hctor)
      (by rw [ConstantVal.mapKeys_type, ← Expr.mapKeys_piResult, ← Expr.mapKeys_getAppFn, hres]; rfl)
      (hR.find hind) itm rtmaj (head_map hthead)
      (by rw [Expr.getAppArgs_mapKeys, List.length_map]; exact hlen) hlv hnz
      (by rw [hfab, Expr.mapKeys_mkAppN, hargsE]; rfl)
      (by rw [Expr.wscopedB_mapKeys]; exact hws) (by rw [Expr.looseBVarsBounded_mapKeys]; exact hb)
      (by rw [fvarLeaves_all_contains_ren hR.rel.inj hfabG he]; exact hlv')
      (by
        rw [← hargsE]
        simpa only [ConstantVal.mapKeys_type, ConstantVal.mapKeys_levelParams,
          Expr.mapKeys_instantiateLevelParams] using hcerts')
      (fun hno => by
        have hno' : towerSlotsAll env T caps.etaFields = false := by
          rw [← towerSlotsAll_ren hR.rel hT]; exact hno
        have := etaProjCerts_rename hR (hproj hno') hT htargs he
        rw [Expr.getAppArgs_mapKeys]
        exact this)
      (defEq_rename hR hpi hfabG he)
  | _, _, _, .rescueAnd (major := major) (fab := fab) (tmaj := tmaj) (rl := rl) (ust := ust)
      hrec hctor hres hind htm htmaj hthead hlen hlv hslots hfab hws hb hlv' hcerts htf hdt hpi,
      he => by
    have hrlG : rl.Good P := (hR.good hrec).2 rl (List.mem_singleton_self rl)
    have hcvjG := hR.good hctor
    have hand : (andName : Key md).Good P := hR.roles _
    obtain ⟨gtm, itm⟩ := infer_rename hR htm he
    obtain ⟨gtmaj, rtmaj⟩ := red_rename hR htmaj gtm
    have htargs := Expr.Good.getAppArgs gtmaj
    have hfargs : Expr.GoodList P
        (tmaj.getAppArgs ++ [.proj andName 0 major, .proj andName 1 major]) := by
      simp only [Expr.goodList_append, Expr.goodList_cons, Expr.goodList_nil, and_true]
      exact ⟨htargs, ⟨hand, he⟩, ⟨hand, he⟩⟩
    have hfabG : fab.Good P := by
      rw [hfab]
      exact Expr.Good.mkAppN hrlG.1 hfargs
    obtain ⟨gtf, itf⟩ := infer_rename hR htf hfabG
    refine ⟨hfabG, ?_⟩
    have hcerts' := certs_rename hR hcerts (Expr.Good.instantiateLevelParams hcvjG.2 _ _) hfargs
    exact Red.rescueAnd (env := env') (hR.find hrec) (hR.find hctor)
      (by rw [ConstantVal.mapKeys_type, ← Expr.mapKeys_piResult, ← Expr.mapKeys_getAppFn, hres]; rfl)
      (hR.find hind) itm rtmaj (head_map hthead)
      (by rw [Expr.getAppArgs_mapKeys, List.length_map]; exact hlen) hlv
      (by rw [RecRule.mapKeys_ctor, andRescueSlots_ren hR.rel hrlG.1]; exact hslots)
      (by rw [hfab, Expr.mapKeys_mkAppN, List.map_append, Expr.getAppArgs_mapKeys]; rfl)
      (by rw [Expr.wscopedB_mapKeys]; exact hws) (by rw [Expr.looseBVarsBounded_mapKeys]; exact hb)
      (by rw [fvarLeaves_all_contains_ren hR.rel.inj hfabG he]; exact hlv')
      (by rw [Expr.getAppArgs_mapKeys]; simp only [List.map_append, List.map_cons, List.map_nil,
            Expr.mapKeys_instantiateLevelParams] at hcerts'; exact hcerts')
      itf (defEq_rename hR hdt gtmaj gtf) (defEq_rename hR hpi hfabG he)

/-- **A conversion between good terms, renamed.** -/
theorem defEq_rename (hR : Renaming P f env env') :
    ∀ {d : Nat} {a b : Expr md}, DefEq env d a b → a.Good P → b.Good P →
      DefEq env' d (a.mapKeys f) (b.mapKeys f)
  | _, _, _, .refl, _, _ => .refl
  | _, _, _, .symm h, ha, hb => .symm (defEq_rename hR h hb ha)
  | _, _, _, .redL hr h, ha, hb => by
    obtain ⟨g, r⟩ := red_rename hR hr ha
    exact .redL r (defEq_rename hR h g hb)
  | _, _, _, .sort h, _, _ => .sort h
  | _, _, _, .fvar, _, _ => .fvar
  | _, _, _, .const h, _, _ => .const h
  | _, _, _, .natZero, _, _ => .natZero
  | _, _, _, .natSucc h, _, hb => .natSucc (defEq_rename hR h trivial hb.2)
  | _, _, _, .forallE hty hbody hpw hc, ha, hb => by
    have h1 := defEq_rename hR hty ha.1 hb.1
    have h2 := defEq_rename hR hbody (good_inst_fvar ha.2 hb.1)
      (good_inst_fvar hb.2 hb.1)
    simp only [Expr.mapKeys_instantiate1, Expr.mapKeys] at h2
    exact .forallE h1 h2 hpw hc
  | _, _, _, .lam hty hbody hpw hc, ha, hb => by
    have h1 := defEq_rename hR hty ha.1 hb.1
    have h2 := defEq_rename hR hbody (good_inst_fvar ha.2 hb.1)
      (good_inst_fvar hb.2 hb.1)
    simp only [Expr.mapKeys_instantiate1, Expr.mapKeys] at h2
    exact .lam h1 h2 hpw hc
  | _, _, _, .app hf ha', ha, hb => .app (defEq_rename hR hf ha.1 hb.1) (defEq_rename hR ha' ha.2 hb.2)
  | _, _, _, .proj h, ha, hb => .proj (defEq_rename hR h ha.2 hb.2)
  | _, _, _, .eta htb hwtb hty hbody hpw hc, ha, hb => by
    obtain ⟨gtb, itb⟩ := infer_rename hR htb hb
    obtain ⟨gw, rw'⟩ := red_rename hR hwtb gtb
    have h1 := defEq_rename hR hty gw.1 ha.1
    have h2 := defEq_rename hR hbody (good_inst_fvar ha.2 ha.1) ⟨hb, ha.1⟩
    simp only [Expr.mapKeys_instantiate1, Expr.mapKeys] at h2
    exact .eta itb rw' h1 h2 hpw hc
  | _, _, _, .proofFast h₁ h₂, ha, hb =>
    .proofFast (by rw [isProofFast_ren hR.rel ha]; exact h₁) (by rw [isProofFast_ren hR.rel hb]; exact h₂)
  | _, _, _, .proofIrrel hta htta hu hu0 htb httb hv hv0, ha, hb => by
    obtain ⟨g1, i1⟩ := infer_rename hR hta ha
    obtain ⟨g2, i2⟩ := infer_rename hR htta g1
    obtain ⟨-, r1⟩ := red_rename hR hu g2
    obtain ⟨g3, i3⟩ := infer_rename hR htb hb
    obtain ⟨g4, i4⟩ := infer_rename hR httb g3
    obtain ⟨-, r2⟩ := red_rename hR hv g4
    exact .proofIrrel i1 i2 r1 hu0 i3 i4 r2 hv0
  | _, _, _, .unitLike hta hwta hua htb hwtb hub, ha, hb => by
    obtain ⟨g1, i1⟩ := infer_rename hR hta ha
    obtain ⟨g2, r1⟩ := red_rename hR hwta g1
    obtain ⟨g3, i3⟩ := infer_rename hR htb hb
    obtain ⟨g4, r2⟩ := red_rename hR hwtb g3
    exact .unitLike i1 r1 (by rw [isUnitLikeTy_ren hR.rel g2]; exact hua) i3 r2
      (by rw [isUnitLikeTy_ren hR.rel g4]; exact hub)
  | _, _, _, .structEta (T := T) (caps := caps) htb hwtb hhead hctor hlen hthead hind heta hetaCtor
      hresT hresc htlen hlv hlps hslots hus hcerts hproj hparams hfields, ha, hb => by
    obtain ⟨gtb, itb⟩ := infer_rename hR htb hb
    obtain ⟨gw, rw'⟩ := red_rename hR hwtb gtb
    have hT : T.Good P := hR.found _ _ hind
    have hwargs := Expr.Good.getAppArgs gw
    have haargs := Expr.Good.getAppArgs ha
    have hcerts' := certs_rename hR hcerts
      (Expr.Good.instantiateLevelParams (hR.good hind).1.2 _ _) hwargs
    have hparams' := defEqList_rename hR hparams (haargs.take _) hwargs
    have hfields' := defEqList_rename hR hfields (haargs.drop _) (etaProjs_good hT hwargs hb _)
    refine .structEta itb rw' (head_map hhead) (hR.find hctor)
      (by rw [Expr.getAppArgs_mapKeys, List.length_map]; exact hlen) (head_map hthead)
      (hR.find hind) heta (by show caps.etaCtor.map (Key.map f) = _; rw [hetaCtor]; rfl)
      (by rw [reservedBasisNames_contains_map]; exact hresT)
      (by rw [reservedBasisNames_contains_map]; exact hresc)
      (by rw [Expr.getAppArgs_mapKeys, List.length_map]; exact htlen) hlv hlps
      (by rw [towerSlotsAll_ren hR.rel hT, recSlotsAll_ren hR.rel hT]; exact hslots) hus
      (by simpa [Expr.getAppArgs_mapKeys] using hcerts')
      (fun hno => by
        have hno' : towerSlotsAll env T caps.etaFields = false := by
          rw [← towerSlotsAll_ren hR.rel hT]; exact hno
        have := etaProjCerts_rename hR (hproj hno') hT hwargs hb
        rw [Expr.getAppArgs_mapKeys]
        exact this)
      (by rw [Expr.getAppArgs_mapKeys, Expr.getAppArgs_mapKeys, ← List.map_take]; exact hparams')
      (by
        rw [Expr.getAppArgs_mapKeys, Expr.getAppArgs_mapKeys, ← List.map_drop,
          etaProjs_ren hR.rel hT]
        exact hfields')
  | _, _, _, .structUnit (T := T) hta hwta hthead hind hunit hresT htlen hlv htb hwtb hd hcerts,
      ha, hb => by
    obtain ⟨g1, i1⟩ := infer_rename hR hta ha
    obtain ⟨g2, r1⟩ := red_rename hR hwta g1
    obtain ⟨g3, i3⟩ := infer_rename hR htb hb
    obtain ⟨g4, r2⟩ := red_rename hR hwtb g3
    have hcerts' := certs_rename hR hcerts
      (Expr.Good.instantiateLevelParams (hR.good hind).1.2 _ _) (Expr.Good.getAppArgs g2)
    exact .structUnit i1 r1 (head_map hthead) (hR.find hind) hunit
      (by rw [reservedBasisNames_contains_map]; exact hresT)
      (by rw [Expr.getAppArgs_mapKeys, List.length_map]; exact htlen) hlv i3 r2
      (defEq_rename hR hd g2 g4) (by simpa [Expr.getAppArgs_mapKeys] using hcerts')

/-- **An inference, renamed**: a good subject has a good type, and the renamed
subject infers the renamed type. -/
theorem infer_rename (hR : Renaming P f env env') :
    ∀ {g : Grade} {d : Nat} {e t : Expr md}, Infer env g d e t → e.Good P →
      t.Good P ∧ Infer env' g d (e.mapKeys f) (t.mapKeys f)
  | _, _, _, _, .sort, _ => ⟨trivial, .sort⟩
  | _, _, _, _, .fvar h, he => ⟨he, .fvar h⟩
  | g, d, _, _, .const hf htower hus, _ => by
    refine ⟨Expr.Good.instantiateLevelParams (hR.good hf).toConstantVal.2 _ _, ?_⟩
    have key := Infer.const (env := env') (g := g) (d := d) (hR.find hf)
      (by rw [ConstantInfo.isTowerEntry_mapKeys]; exact htower)
      (by rw [ConstantInfo.mapKeys_toConstantVal, ConstantVal.mapKeys_levelParams]; exact hus)
    rw [ConstantInfo.mapKeys_toConstantVal, ConstantVal.mapKeys_type,
      ConstantVal.mapKeys_levelParams, ← Expr.mapKeys_instantiateLevelParams] at key
    exact key
  | _, _, _, _, .natLit h, _ =>
    ⟨hR.roles _, .natLit (by rw [natLitSupported_ren hR.rel]; exact h)⟩
  | _, _, _, _, .strLit h, _ =>
    ⟨hR.roles _, .strLit (by rw [strLitSupported_ren hR.rel hR.roles.str]; exact h)⟩
  | _, _, _, _, .forallE hs hu hbs hv hz, he => by
    obtain ⟨gs, is⟩ := infer_rename hR hs he.1
    obtain ⟨-, ru⟩ := red_rename hR hu gs
    obtain ⟨gbs, ibs⟩ := infer_rename hR hbs (good_inst_fvar he.2 he.1)
    obtain ⟨-, rv⟩ := red_rename hR hv gbs
    simp only [Expr.mapKeys_instantiate1, Expr.mapKeys] at ibs
    exact ⟨trivial, .forallE is ru ibs rv hz⟩
  | _, _, _, _, .lam (body := body) hs hu hbt hchain hbtt hv hz, he => by
    obtain ⟨gbt, ibt⟩ := infer_rename hR hbt (good_inst_fvar he.2 he.1)
    simp only [Expr.mapKeys_instantiate1, Expr.mapKeys] at ibt
    refine ⟨⟨he.1, Expr.Good.abstract1 gbt _ _⟩, ?_⟩
    have hn : ∀ h : (body.mapKeys f).lamPw = none, body.lamPw = none := fun h => by
      rwa [Expr.lamPw_mapKeys] at h
    have key := Infer.lam (env := env')
      (fun hg => (infer_rename hR (hs hg) he.1).2)
      (fun hg => (red_rename hR (hu hg) (infer_rename hR (hs hg) he.1).1).2)
      ibt
      (fun pwI h => hchain pwI (by rwa [Expr.lamPw_mapKeys] at h))
      (fun h => (infer_rename hR (hbtt (hn h)) gbt).2)
      (fun h => (red_rename hR (hv (hn h)) (infer_rename hR (hbtt (hn h)) gbt).1).2)
      (fun h => hz (hn h))
    simpa using key
  | _, _, _, _, .app htf hw hta hd, he => by
    obtain ⟨gtf, itf⟩ := infer_rename hR htf he.1
    obtain ⟨gw, rw'⟩ := red_rename hR hw gtf
    obtain ⟨gta, ita⟩ := infer_rename hR hta he.2
    refine ⟨Expr.Good.instantiate1 gw.2 he.2 0, ?_⟩
    rw [Expr.mapKeys_instantiate1]
    exact .app itf rw' ita (defEq_rename hR hd gta gw.1)
  | _, _, _, _, .appSkip htf hw hnev, he => by
    obtain ⟨gtf, itf⟩ := infer_rename hR htf he.1
    obtain ⟨gw, rw'⟩ := red_rename hR hw gtf
    refine ⟨Expr.Good.instantiate1 gw.2 he.2 0, ?_⟩
    rw [Expr.mapKeys_instantiate1]
    exact .appSkip itf rw' hnev
  | _, _, _, _, .proj htpe hte hhead hent hlen hus hprop, he => by
    obtain ⟨hsn, hpe⟩ := he
    obtain ⟨gt, it⟩ := infer_rename hR htpe hpe
    obtain ⟨gte, rte⟩ := red_rename hR hte gt
    refine ⟨ProjEntry.typeAt_good (hR.rel.findProj?_good hsn hent) _
      (Expr.Good.getAppArgs gte) hpe, ?_⟩
    have key := Infer.proj (env := env') it rte (head_map hhead)
      (by rw [hR.rel.findProj? hsn, hent]; rfl)
      (by rw [Expr.getAppArgs_mapKeys, List.length_map]; exact hlen) hus hprop
    simpa [Expr.getAppArgs_mapKeys] using key

/-- **A telescope certificate, renamed.** -/
theorem certs_rename (hR : Renaming P f env env') :
    ∀ {d : Nat} {lic : Bool} {ty : Expr md} {args : List (Expr md)},
      Certs env d lic ty args → ty.Good P → Expr.GoodList P args →
        Certs env' d lic (ty.mapKeys f) (args.map (Expr.mapKeys f))
  | _, _, _, _, .nil, _, _ => .nil
  | _, _, _, _, .skip hlic hnev hrest, hty, hargs => by
    simp only [Expr.goodList_cons] at hargs
    have h := certs_rename hR hrest (Expr.Good.instantiate1 hty.2 hargs.1 0) hargs.2
    rw [Expr.mapKeys_instantiate1] at h
    exact .skip hlic hnev h
  | _, _, _, _, .cert hta hd hrest, hty, hargs => by
    simp only [Expr.goodList_cons] at hargs
    obtain ⟨gta, ita⟩ := infer_rename hR hta hargs.1
    have h := certs_rename hR hrest (Expr.Good.instantiate1 hty.2 hargs.1 0) hargs.2
    rw [Expr.mapKeys_instantiate1] at h
    exact .cert ita (defEq_rename hR hd gta hty.1) h

/-- **A pairwise conversion, renamed.** -/
theorem defEqList_rename (hR : Renaming P f env env') :
    ∀ {d : Nat} {as bs : List (Expr md)}, DefEqList env d as bs → Expr.GoodList P as →
      Expr.GoodList P bs → DefEqList env' d (as.map (Expr.mapKeys f)) (bs.map (Expr.mapKeys f))
  | _, _, _, .nil, _, _ => .nil
  | _, _, _, .cons h hs, ha, hb => by
    simp only [Expr.goodList_cons] at ha hb
    exact .cons (defEq_rename hR h ha.1 hb.1) (defEqList_rename hR hs ha.2 hb.2)

/-- **The per-field certificates of a projection-function family, renamed.** -/
theorem etaProjCerts_rename (hR : Renaming P f env env') :
    ∀ {d : Nat} {T : Key md} {us' : List Level} {targs : List (Expr md)} {b : Expr md}
      {lpsT : List LevelParam} {idxs : List Nat},
      EtaProjCerts env d T us' targs b lpsT idxs → T.Good P → Expr.GoodList P targs → b.Good P →
        EtaProjCerts env' d (T.map f) us' (targs.map (Expr.mapKeys f)) (b.mapKeys f) lpsT idxs
  | _, _, _, _, _, _, _, .nil, _, _, _ => .nil
  | _, _, _, _, _, _, _, .cons hf hlps hstrip hcerts hrest, hT, ht, hb => by
    have hcerts' := certs_rename hR hcerts (Expr.Good.instantiateLevelParams (hR.good hf).1.2 _ _)
      (by simp only [Expr.goodList_append, Expr.goodList_cons, Expr.goodList_nil, and_true]
          exact ⟨ht, hb⟩)
    refine .cons (by rw [← projFnName_map]; exact hR.find hf) hlps (by simpa using hstrip)
      (by simpa using hcerts') (etaProjCerts_rename hR hrest hT ht hb)

end

/-! ## Typed terms are good -/

/-- Instantiation keeps every key of the instantiated term. -/
theorem good_of_instantiate1 {v : Expr md} :
    ∀ (e : Expr md) (k : Nat), (e.instantiate1 v k).Good P → e.Good P := by
  intro e
  induction e with
  | bvar => intros; trivial
  | fvar i t _ => intro k h; simpa [Expr.instantiate1] using h
  | sort => intros; trivial
  | const n us => intro k h; simpa [Expr.instantiate1] using h
  | app a b iha ihb =>
    intro k h
    simp only [Expr.instantiate1, Expr.Good] at h
    exact ⟨iha k h.1, ihb k h.2⟩
  | lam t b m iht ihb =>
    intro k h
    simp only [Expr.instantiate1, Expr.Good] at h
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | forallE t b m iht ihb =>
    intro k h
    simp only [Expr.instantiate1, Expr.Good] at h
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE t v' b l iht ihv ihb =>
    intro k h
    simp only [Expr.instantiate1, Expr.Good] at h
    exact ⟨iht k h.1, ihv k h.2.1, ihb (k + 1) h.2.2⟩
  | lit l => intro k h; simpa [Expr.instantiate1] using h
  | proj s i e ih =>
    intro k h
    simp only [Expr.instantiate1, Expr.Good] at h
    exact ⟨h.1, ih k h.2⟩

/-- **A term typed at the full grade is good**, when every key the environment
answers is good, every role is allowed, and the term's free variables carry good
types. Full-grade typing checks every subterm: constants are found, projections
go through a stored table, and binder domains are typed. -/
theorem infer_good (found : ∀ (k : Key md) (c : ConstantInfo md), env.find? k = some c → k.Good P)
    (roles : P.All) :
    ∀ {g : Grade} {d : Nat} {e t : Expr md}, Infer env g d e t → g = .full →
      (∀ l ∈ e.fvarLeaves, l.2.Good P) → e.Good P
  | _, _, _, _, .sort, _, _ => trivial
  | _, _, _, _, .fvar (idx := idx) (ty := ty) _, _, hl => hl (idx, ty) (by simp [Expr.fvarLeaves])
  | _, _, _, _, .const hf _ _, _, _ => found _ _ hf
  | _, _, _, _, .natLit _, _, _ => trivial
  | _, _, _, _, .strLit _, _, _ => roles.str
  | _, _, _, _, .forallE hs _ hbs _ _, hg, hl => by
    have hty := infer_good found roles hs hg
      (fun l h => hl l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl h))
    refine ⟨hty, good_of_instantiate1 _ 0 (infer_good found roles hbs hg fun l h => ?_)⟩
    rcases Expr.fvarLeaves_instantiate1 _ 0 h with h' | h'
    · exact hl l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inr h')
    · simp only [Expr.fvarLeaves, List.mem_cons] at h'
      rcases h' with rfl | h'
      · exact hty
      · exact hl l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl h')
  | _, _, _, _, .lam hs _ hbt _ _ _ _, hg, hl => by
    have hty := infer_good found roles (hs hg) rfl
      (fun l h => hl l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl h))
    refine ⟨hty, good_of_instantiate1 _ 0 (infer_good found roles hbt hg fun l h => ?_)⟩
    rcases Expr.fvarLeaves_instantiate1 _ 0 h with h' | h'
    · exact hl l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inr h')
    · simp only [Expr.fvarLeaves, List.mem_cons] at h'
      rcases h' with rfl | h'
      · exact hty
      · exact hl l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl h')
  | _, _, _, _, .app htf _ hta _, hg, hl =>
    ⟨infer_good found roles htf hg
      (fun l h => hl l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl h)),
     infer_good found roles hta hg
      (fun l h => hl l (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inr h))⟩
  | _, _, _, _, .appSkip _ _ _, hg, _ => nomatch hg
  | _, _, _, _, .proj htpe _ _ hent _ _ _, hg, hl => by
    refine ⟨?_, infer_good found roles htpe hg (fun l h => hl l (by simpa [Expr.fvarLeaves] using h))⟩
    unfold Env.findProj? at hent
    split at hent
    · rename_i tbl htbl
      simpa [projTableName, auxKey] using found _ _ htbl
    · exact nomatch hent

end Ix.Cert.RulesRename
