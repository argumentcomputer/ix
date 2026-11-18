import IxVMRefinement.FamilyAlias.Clause
import IxVMRefinement.FamilyAlias.RecsRecord
import IxC.Kernel.Model.StoreArLate
import IxC.Kernel.Verify.Extend.Iota

/-! # The arity of the stored terms across the family step

`FamilyKeepsStoreAr` (`Clause.lean`): across an alias group over the prefix and IxC's renamed
record over the family package, the stored terms stay arity-correct and resolving
(`StoreArR`). Proved here (`familyKeepsStoreAr`).

* **An alias** is a definition whose value is a stored constant at as many level parameters as
  it has; its declared type, renamed by the group's map and put at positions, is a stored type,
  so it is arity-correct where the map sends each alias it moves to a constant with as many level
  parameters (`AliasEnv`), which the group gives (`storeArR_aliasGroup`).
* **A member's checked type and a rule's right-hand side** are typed by the renamed family
  package: a full-grade derivation of the term renamed by the block renaming (or not) and by the
  group's map, at positions. The derivation gives the renamed term's arity
  (`Ix.Kernel.Model.infer_full_arOk`); positions do not change arity; and a renaming that sends
  each stored constant it moves to a stored constant with as many level parameters reflects it
  (`arOk_of_renameConsts`). For the block renaming that is: every member stored so far has its
  model key stored at its own level parameters (`ModelLen`), which each member's front door
  checks, and which holds where the record starts because the block's names are fresh there.
* **A nested rule's pins** are arguments of the recursor's major-premise domain, lifted past the
  index binders (`Ix.Kernel.nestedRuleShape_inv`), so they inherit the recursor type's arity.
* Each term is checked at an environment of the record's run; what it resolves to there is
  found after the block at the same level count (`LenExt`): the members are kept, and each
  recursor provisioned without rules is stored again with its rules at the same parameters.
* **The `Bool` clause**: the step stores no definition at a comparison's key (an alias is at a
  derived key, the record stores inductives, constructors and recursors). -/

namespace IxVM.Refinement.Decl.FamilyAlias

open IxVM.Refinement.Core
open Ix.Kernel (Env Expr Key ConstantInfo ConstantVal RecRule LevelParam EnvExt IndCaps auxKey)
open Ix.Kernel.Semantics (Judgements DeclIndRenRunJ IndMembersRunJ ProvisionRecsRunJ
  IndRecsFoldRenRunJ IotaRuleRenRunJ IotaRulesRenRunJ MemberValRunJ renameJ)
open Ix.Kernel.Model (ArRes ConstArR StoreArR)

set_option linter.unusedVariables false

/-! ## Lookups kept at their level counts -/

/-- **Every lookup of `env` is found by `env₂` at the same level count.** -/
def LenExt (env env₂ : Env .anon) : Prop :=
  ∀ {n : KKey} {ci : ConstantInfo .anon}, env.find? n = some ci →
    ∃ ci', env₂.find? n = some ci' ∧
      ci'.toConstantVal.levelParams.length = ci.toConstantVal.levelParams.length

theorem LenExt.of_find {env env₂ : Env .anon}
    (h : ∀ {n : KKey} {ci : ConstantInfo .anon}, env.find? n = some ci →
      env₂.find? n = some ci) : LenExt env env₂ :=
  fun hf => ⟨_, h hf, rfl⟩

theorem LenExt.trans {e₁ e₂ e₃ : Env .anon} (h₁ : LenExt e₁ e₂) (h₂ : LenExt e₂ e₃) :
    LenExt e₁ e₃ := by
  intro n ci hf
  obtain ⟨ci₂, hf₂, hl₂⟩ := h₁ hf
  obtain ⟨ci₃, hf₃, hl₃⟩ := h₂ hf₂
  exact ⟨ci₃, hf₃, hl₃.trans hl₂⟩

/-- Two conses whose heads have one name and one level count. -/
theorem LenExt.cons {env env₂ : Env .anon} (h : LenExt env env₂) {a b : ConstantInfo .anon}
    (hn : a.name = b.name)
    (hl : a.toConstantVal.levelParams.length = b.toConstantVal.levelParams.length) :
    LenExt ⟨a :: env.consts⟩ ⟨b :: env₂.consts⟩ := by
  intro n ci hf
  rw [Ix.Kernel.Env.find?_cons] at hf
  split at hf
  · rename_i ha
    obtain rfl := Option.some.inj hf
    refine ⟨b, ?_, hl.symm⟩
    rw [← ha, hn]
    exact Ix.Kernel.Env.find?_cons_self b env₂
  · rename_i ha
    obtain ⟨ci', hf', hl'⟩ := h hf
    refine ⟨ci', ?_, hl'⟩
    rw [Ix.Kernel.EnvExt.find?_cons_ne (fun e => ha (hn.trans e))]
    exact hf'

/-- Arity and resolution are kept where lookups are kept at their level counts. -/
theorem arRes_lenExt {env env₂ : Env .anon} (h : LenExt env env₂) {e : KExpr}
    (he : ArRes env e) : ArRes env₂ e :=
  Ix.Kernel.Model.arRes_mono_len (fun hf => h hf) he

/-! ## Renamings that keep level counts -/

/-- **A renaming sends each stored constant it moves to a stored constant with as many level
parameters.** -/
def RenLen (env : Env .anon) (f : KKey → KKey) : Prop :=
  ∀ (k : KKey) (ci : ConstantInfo .anon), env.find? k = some ci → f k ≠ k →
    ∃ ci', env.find? (f k) = some ci' ∧
      ci'.toConstantVal.levelParams.length = ci.toConstantVal.levelParams.length

/-- **Such a renaming reflects arity.** -/
theorem arOk_of_renameConsts {env : Env .anon} {f : KKey → KKey} (hf : RenLen env f) :
    ∀ {e : KExpr}, Expr.arOk env (e.renameConsts f) = true → Expr.arOk env e = true := by
  intro e
  induction e with
  | bvar _ => intro _; rfl
  | sort _ => intro _; rfl
  | lit _ => intro _; rfl
  | const c us =>
    intro h
    simp only [Expr.renameConsts] at h
    refine Ix.Kernel.LevelRen.arOk_const_of (fun ci hci => ?_)
    by_cases hc : f c = c
    · rw [hc] at h
      exact Ix.Kernel.LevelRen.arOk_const h hci
    · obtain ⟨ci', hci', hlen⟩ := hf c ci hci hc
      rw [← hlen]
      exact Ix.Kernel.LevelRen.arOk_const h hci'
  | fvar i ty ih =>
    intro h
    simp only [Expr.renameConsts, Expr.arOk] at h ⊢
    exact ih h
  | app a b iha ihb =>
    intro h
    simp only [Expr.renameConsts, Expr.arOk, Bool.and_eq_true] at h ⊢
    exact ⟨iha h.1, ihb h.2⟩
  | lam ty b m iht ihb =>
    intro h
    simp only [Expr.renameConsts, Expr.arOk, Bool.and_eq_true] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | forallE ty b m iht ihb =>
    intro h
    simp only [Expr.renameConsts, Expr.arOk, Bool.and_eq_true] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | letE ty v b m iht ihv ihb =>
    intro h
    simp only [Expr.renameConsts, Expr.arOk, Bool.and_eq_true] at h ⊢
    exact ⟨⟨iht h.1.1, ihv h.1.2⟩, ihb h.2⟩
  | proj s i e ih =>
    intro h
    simp only [Expr.renameConsts, Expr.arOk] at h ⊢
    exact ih h

/-- The map of stored aliases keeps level counts. -/
theorem renLen_of_aliasEnv {env : Env .anon} {h : KKey → KKey} (hA : AliasEnv env h) :
    RenLen env h := by
  intro k ci hk hne
  obtain ⟨lps, ty, hint, ci', hfk, -, hft, hlt⟩ := hA k hne
  rw [hfk] at hk
  obtain rfl := Option.some.inj hk
  refine ⟨ci', hft, ?_⟩
  rw [hlt, List.length_range]
  rfl

/-- **Every block name stored has its model key stored at as many level parameters.** -/
def ModelLen (env : Env .anon) (bn : List KKey) : Prop :=
  ∀ k, k ∈ bn → ∀ ci, env.find? k = some ci →
    ∃ ci', env.find? (auxKey k .model) = some ci' ∧
      ci'.toConstantVal.levelParams.length = ci.toConstantVal.levelParams.length

/-- The block renaming keeps level counts where the model keys are stored. -/
theorem renLen_bren {env : Env .anon} {bn : List KKey} (h : ModelLen env bn) :
    RenLen env (fun n => if bn.contains n then auxKey n .model else n) := by
  intro k ci hk hne
  cases hb : bn.contains k with
  | false =>
    exfalso
    apply hne
    show (if bn.contains k = true then auxKey k .model else k) = k
    rw [hb]
    rfl
  | true =>
    have e : (if bn.contains k = true then auxKey k .model else k) = auxKey k .model := by
      rw [hb]
      rfl
    show ∃ ci', env.find? (if bn.contains k = true then auxKey k .model else k) = some ci' ∧ _
    rw [e]
    exact h k (by simpa using hb) ci hk

/-- A fresh member that is no model key keeps `ModelLen`, its own model key being stored. -/
theorem modelLen_cons {env : Env .anon} {bn : List KKey} (h : ModelLen env bn)
    {c : ConstantInfo .anon} (hsuf : c.name.isModelSuffix = false)
    (hm : ∃ cm, env.find? (auxKey c.name .model) = some cm ∧
      cm.toConstantVal.levelParams.length = c.toConstantVal.levelParams.length) :
    ModelLen ⟨c :: env.consts⟩ bn := by
  have hne : ∀ k' : KKey, c.name ≠ auxKey k' .model := by
    intro k' he
    have h1 : (auxKey k' .model : KKey).isModelSuffix = true := rfl
    rw [← he, hsuf] at h1
    exact Bool.false_ne_true h1
  intro k hk ci hf
  rw [Ix.Kernel.Env.find?_cons] at hf
  split at hf
  · rename_i hck
    obtain rfl := Option.some.inj hf
    obtain ⟨cm, hcm, hl⟩ := hm
    refine ⟨cm, ?_, hl⟩
    rw [Ix.Kernel.EnvExt.find?_cons_ne (hne k), ← hck]
    exact hcm
  · obtain ⟨ci', hf', hl⟩ := h k hk ci hf
    refine ⟨ci', ?_, hl⟩
    rw [Ix.Kernel.EnvExt.find?_cons_ne (hne k)]
    exact hf'

/-! ## A term the family package types -/

/-- **A closed term the family package types is arity-correct.** -/
theorem arOk_of_famJ_infer {env : Env .anon} {h : KKey → KKey} {e t : KExpr}
    (hfv : e.hasFvar = false) (hinf : (famJ h).infer env 0 e t) : Expr.arOk env e = true := by
  obtain ⟨hA, -, ps, -, hInf⟩ := hinf
  have hfv2 : (posOf ps (e.renameConsts h)).hasFvar = false := by
    unfold posOf
    rw [Ix.Kernel.Expr.hasFvar_instantiateLevelParams, Ix.Kernel.hasFvar_renameConsts]
    exact hfv
  have h1 := Ix.Kernel.Model.infer_full_arOk hInf rfl (fun l hl => by
    rw [Ix.Kernel.Rules.fvarLeaves_nil_of_hasFvar hfv2] at hl
    exact nomatch hl)
  unfold posOf at h1
  rw [Ix.Kernel.LevelRen.arOk_inst] at h1
  exact arOk_of_renameConsts (renLen_of_aliasEnv hA) h1

/-- **A closed term the renamed family package types is arity-correct**, where the renaming
keeps level counts. -/
theorem arOk_of_renameJ_famJ {env : Env .anon} {f h : KKey → KKey} {e t : KExpr}
    (hfv : e.hasFvar = false) (hf : RenLen env f)
    (hinf : (renameJ f (famJ h)).infer env 0 e t) : Expr.arOk env e = true := by
  rcases hinf with hi | ⟨-, hi⟩
  · exact arOk_of_famJ_infer hfv hi
  · exact arOk_of_renameConsts hf
      (arOk_of_famJ_infer (by rw [Ix.Kernel.hasFvar_renameConsts]; exact hfv) hi)

/-! ## The block's names are fresh where the record starts -/

theorem indMembersRunJ_fresh {J : Judgements .anon} {bn : List KKey} {caps : IndCaps .anon}
    {E : Env .anon} :
    ∀ {env' : Env .anon} {ms : List (ConstantInfo .anon)} {envM : Env .anon},
      IndMembersRunJ J bn caps env' ms envM →
      (∀ {k : KKey} {c : ConstantInfo .anon}, E.find? k = some c → env'.find? k = some c) →
      ∀ ci ∈ ms, E.find? ci.name = none
  | _, [], _, _, _, _, hm => nomatch hm
  | env', ci :: rest, envM, hrun, hE, ci', hm => by
    obtain ⟨cvA, hmv, hrest⟩ := hrun
    have hfr : (env'.find? ci.toConstantVal.name).isNone = true := by
      obtain ⟨type', hcv, -⟩ := hmv
      exact hcv.1
    rcases List.mem_cons.mp hm with he | hm'
    · rw [he, show ci.name = ci.toConstantVal.name from rfl]
      cases hc : E.find? ci.toConstantVal.name with
      | none => rfl
      | some c =>
        rw [hE hc] at hfr
        simp at hfr
    · cases ci with
      | indInfo cv caps' =>
        exact indMembersRunJ_fresh hrest
          (fun hk => (Ix.Kernel.Semantics.envExt_of_memberValRunJ (c := .indInfo cvA caps) hmv
            rfl).find (hE hk)) ci' hm'
      | ctorInfo cv nP nF =>
        exact indMembersRunJ_fresh hrest
          (fun hk => (Ix.Kernel.Semantics.envExt_of_memberValRunJ (c := .ctorInfo cvA nP nF)
            hmv rfl).find (hE hk)) ci' hm'
      | axiomInfo _ => exact hrest.elim
      | defnInfo _ _ _ => exact hrest.elim
      | thmInfo _ _ => exact hrest.elim
      | recInfo _ _ _ _ => exact hrest.elim
      | projInfo _ => exact hrest.elim

theorem provisionRecsRunJ_fresh {J : Judgements .anon} {bn : List KKey} {E : Env .anon} :
    ∀ {envAcc : Env .anon} {recs : List (ConstantInfo .anon)} {envSelf : Env .anon}
      {checked : List (ConstantVal .anon × Nat × Nat × List (RecRule .anon))},
      ProvisionRecsRunJ J bn envAcc recs envSelf checked →
      (∀ {k : KKey} {c : ConstantInfo .anon}, E.find? k = some c → envAcc.find? k = some c) →
      ∀ ci ∈ recs, E.find? ci.name = none
  | _, [], _, _, _, _, _, hm => nomatch hm
  | envAcc, ci :: rest, envSelf, checked, hrun, hE, ci', hm => by
    obtain ⟨cvA, mI, rP, rules, rest', -, hmv, hprov, -⟩ := hrun
    have hfr : (envAcc.find? ci.toConstantVal.name).isNone = true := by
      obtain ⟨type', hcv, -⟩ := hmv
      exact hcv.1
    rcases List.mem_cons.mp hm with he | hm'
    · rw [he, show ci.name = ci.toConstantVal.name from rfl]
      cases hc : E.find? ci.toConstantVal.name with
      | none => rfl
      | some c =>
        rw [hE hc] at hfr
        simp at hfr
    · exact provisionRecsRunJ_fresh hprov
        (fun hk => (Ix.Kernel.Semantics.envExt_of_memberValRunJ (c := .recInfo cvA mI rP [])
          hmv rfl).find (hE hk)) ci' hm'

/-! ## The record's walk -/

section Walk

variable {h : KKey → KKey} {bn : List KKey} {env₂ : Env .anon}

/-- **A member's front door over the renamed family package**: its checked type is
arity-correct and resolves where the block renaming keeps level counts, and its model key is
stored with its level parameters. -/
theorem memberValRunJ_arRes {env' : Env .anon} {cv cvA : ConstantVal .anon}
    (hmv : MemberValRunJ
      (renameJ (fun n => if bn.contains n then auxKey n .model else n) (famJ h))
      env' bn cv cvA)
    (hML : ModelLen env' bn) :
    ArRes env' cvA.type ∧ cvA.name.isModelSuffix = false ∧
      ∃ cm, env'.find? (auxKey cvA.name .model) = some cm ∧
        cm.toConstantVal.levelParams = cvA.levelParams := by
  obtain ⟨type', hcv, rfl, hsuf, cvm, mval, hint, hfm, hlps, -⟩ := hmv
  obtain ⟨-, -, -, -, hlb, hfv, hann, -, hres, stype, u, hinf, -⟩ := hcv
  have hann' : (famJ h).annot env' 0 cv.type type' := hann
  obtain ⟨hfv', -⟩ := (judgeFrames_famJ h env').annot_syntax hann' hfv hlb
  exact ⟨⟨arOk_of_renameJ_famJ hfv' (renLen_bren hML) hinf, hres⟩, hsuf, _, hfm, hlps⟩

/-- **The members' walk**: `ModelLen` is kept, and every member stored has arity-correct terms
after the block. -/
theorem indMembersRunJ_storeAr :
    ∀ {env' : Env .anon} {ms : List (ConstantInfo .anon)} {envM : Env .anon},
      IndMembersRunJ (renameJ (fun n => if bn.contains n then auxKey n .model else n) (famJ h))
        bn {} env' ms envM →
      ModelLen env' bn → LenExt envM env₂ →
      ModelLen envM bn ∧ Ix.Kernel.Model.NewSat env' envM (ConstArR env₂)
  | env', [], envM, hrun, hML, _ => by
    have e : envM = env' := hrun
    subst e
    exact ⟨hML, Ix.Kernel.Model.NewSat.refl _ _⟩
  | env', ci :: rest, envM, hrun, hML, hlen => by
    obtain ⟨cvA, hmv, hrest⟩ := hrun
    obtain ⟨har, hsuf, cm, hcm, hcml⟩ := memberValRunJ_arRes hmv hML
    have key : ∀ c : ConstantInfo .anon, c.toConstantVal = cvA →
        IndMembersRunJ (renameJ (fun n => if bn.contains n then auxKey n .model else n)
          (famJ h)) bn {} ⟨c :: env'.consts⟩ rest envM →
        (ModelLen ⟨c :: env'.consts⟩ bn →
          ModelLen envM bn ∧ Ix.Kernel.Model.NewSat ⟨c :: env'.consts⟩ envM (ConstArR env₂)) →
        (ArRes env₂ cvA.type → ConstArR env₂ c) →
        ModelLen envM bn ∧ Ix.Kernel.Model.NewSat env' envM (ConstArR env₂) := by
      intro c hc hrest' hrec hcar
      have hcn : c.name = cvA.name := congrArg ConstantVal.name hc
      have hext : EnvExt env' ⟨c :: env'.consts⟩ :=
        Ix.Kernel.Semantics.envExt_of_memberValRunJ hmv hcn
      have hML' : ModelLen ⟨c :: env'.consts⟩ bn :=
        modelLen_cons hML (by rw [hcn]; exact hsuf)
          ⟨cm, by rw [hcn]; exact hcm, by rw [hcml, hc]⟩
      obtain ⟨hML₂, hns⟩ := hrec hML'
      have hlen' : LenExt env' env₂ :=
        LenExt.trans (LenExt.of_find hext.find)
          (LenExt.trans (LenExt.of_find (Ix.Kernel.Semantics.indMembersRunJ_envExt hrest').find)
            hlen)
      exact ⟨hML₂, (Ix.Kernel.Model.NewSat.cons (hcar (arRes_lenExt hlen' har))).trans hns⟩
    cases ci with
    | indInfo cv caps' =>
      exact key (.indInfo cvA {}) rfl hrest (fun hML' => indMembersRunJ_storeAr hrest hML' hlen)
        Ix.Kernel.Model.ConstArR.of_ind
    | ctorInfo cv nP nF =>
      exact key (.ctorInfo cvA nP nF) rfl hrest
        (fun hML' => indMembersRunJ_storeAr hrest hML' hlen) Ix.Kernel.Model.ConstArR.of_ctor
    | axiomInfo _ => exact hrest.elim
    | defnInfo _ _ _ => exact hrest.elim
    | thmInfo _ _ => exact hrest.elim
    | recInfo _ _ _ _ => exact hrest.elim
    | projInfo _ => exact hrest.elim

/-- **The recursors' provisioning walk**: `ModelLen` is kept, and every provisioned recursor's
checked type is arity-correct after the block. -/
theorem provisionRecsRunJ_storeAr :
    ∀ {envAcc : Env .anon} {recs : List (ConstantInfo .anon)} {envSelf : Env .anon}
      {checked : List (ConstantVal .anon × Nat × Nat × List (RecRule .anon))},
      ProvisionRecsRunJ (renameJ (fun n => if bn.contains n then auxKey n .model else n)
        (famJ h)) bn envAcc recs envSelf checked →
      ModelLen envAcc bn → LenExt envSelf env₂ →
      ModelLen envSelf bn ∧ ∀ c ∈ checked, ArRes env₂ c.1.type
  | envAcc, [], envSelf, checked, ⟨hs, hc⟩, hML, _ => by
    subst hs
    subst hc
    exact ⟨hML, fun _ hm => nomatch hm⟩
  | envAcc, ci :: rest, envSelf, checked, ⟨cvA, mI, rP, rules, rest', -, hmv, hprov, hchk⟩,
      hML, hlen => by
    obtain ⟨har, hsuf, cm, hcm, hcml⟩ := memberValRunJ_arRes hmv hML
    have hML' : ModelLen ⟨.recInfo cvA mI rP [] :: envAcc.consts⟩ bn :=
      modelLen_cons hML hsuf ⟨cm, hcm, congrArg List.length hcml⟩
    obtain ⟨hML₂, hall⟩ := provisionRecsRunJ_storeAr hprov hML' hlen
    have hext : EnvExt envAcc ⟨.recInfo cvA mI rP [] :: envAcc.consts⟩ :=
      Ix.Kernel.Semantics.envExt_of_memberValRunJ hmv rfl
    have hlen' : LenExt envAcc env₂ :=
      LenExt.trans (LenExt.of_find hext.find)
        (LenExt.trans (LenExt.of_find (provisionRecsRunJ_envExt hprov).find) hlen)
    refine ⟨hML₂, ?_⟩
    subst hchk
    intro c hc
    rcases List.mem_cons.mp hc with he | hc'
    · rw [he]
      exact arRes_lenExt hlen' har
    · exact hall c hc'

/-- **A rule of the renamed record** has an arity-correct right-hand side after the block, and
so do a nested rule's pins: they are arguments of the recursor type's major-premise domain. -/
theorem iotaRuleRenRunJ_storeAr {f : KKey → KKey} {env' envSelf : Env .anon} {cvName : KKey}
    {lps : List LevelParam} {tyA : KExpr} {mI rP j : Nat} {r r' : RecRule .anon}
    (hf : RenLen envSelf f) (hlen : LenExt envSelf env₂)
    (htyA : Expr.arOk env₂ tyA = true)
    (hr : IotaRuleRenRunJ (famJ h) env' envSelf f cvName lps tyA mI rP j r r') :
    ArRes env₂ r'.rhs ∧
      ∀ lvls pins, r'.fire = .nested lvls pins → ∀ p ∈ pins, ArRes env₂ p := by
  obtain ⟨cvj, cnP, cnF, rhsA, -, -, hlb, hfv, hann, -, hres, -, ⟨t', hinf⟩, fire, rfl, hbr⟩ :=
    hr
  have hann' : (famJ h).annot envSelf 0 r.rhs rhsA := hann
  obtain ⟨hfv', -⟩ := (judgeFrames_famJ h envSelf).annot_syntax hann' hfv hlb
  refine ⟨arRes_lenExt hlen ⟨arOk_of_renameJ_famJ hfv' hf hinf, hres⟩, ?_⟩
  intro lvls pins hfire p hp
  have hfire' : fire = .nested lvls pins := hfire
  rcases hbr with ⟨-, hpl, -⟩ | ⟨-, lvls', pins', hfe, hthm⟩
  · rw [hpl] at hfire'
    exact nomatch hfire'
  · rw [hfe] at hfire'
    injection hfire' with hl hpn
    subst hpn
    obtain ⟨-, -, hpins, pre, dom, body, bm, D, hstrip, -, hargs, -⟩ :=
      Ix.Kernel.nestedRuleShape_inv hthm.1
    have hT : Ix.Kernel.Model.ArP env₂ (Expr.forallE dom body bm) :=
      (Ix.Kernel.Model.arP_stripPis ((Ix.Kernel.Model.arP_iff tyA).mpr htyA) hstrip).2
    have hD : Ix.Kernel.Model.ArP env₂ dom := by
      simp only [Ix.Kernel.Model.ArP] at hT
      exact hT.1
    have hmem : Ix.Kernel.Expr.liftLooseBVars (mI - rP) 0 p ∈ dom.getAppArgs := by
      rw [hargs]
      exact List.mem_append_left _ (List.mem_map_of_mem hp)
    have hlift := (Ix.Kernel.Model.arP_iff _).mp (Ix.Kernel.Model.ArP.getAppArgs hD _ hmem)
    rw [Ix.Kernel.Model.arOk_liftLooseBVars] at hlift
    refine ⟨hlift, Ix.Kernel.Expr.constsResolve_of_find (fun n hn => ?_) (hpins p hp).2.2.1⟩
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
    obtain ⟨ci', h2, -⟩ := hlen hci
    rw [h2]
    rfl

theorem iotaRulesRenRunJ_storeAr {f : KKey → KKey} {env' envSelf : Env .anon} {cvName : KKey}
    {lps : List LevelParam} {tyA : KExpr} {mI rP : Nat}
    (hf : RenLen envSelf f) (hlen : LenExt envSelf env₂)
    (htyA : Expr.arOk env₂ tyA = true) :
    ∀ {j : Nat} {rules rules' : List (RecRule .anon)},
      IotaRulesRenRunJ (famJ h) env' envSelf f cvName lps tyA mI rP j rules rules' →
      ∀ rl ∈ rules', ArRes env₂ rl.rhs ∧
        ∀ lvls pins, rl.fire = .nested lvls pins → ∀ p ∈ pins, ArRes env₂ p
  | j, [], rules', hout => by
    intro rl hrl
    have e : rules' = [] := hout
    rw [e] at hrl
    exact nomatch hrl
  | j, r :: rest, out, ⟨r', rest', hr, hrest, hout⟩ => by
    intro rl hrl
    rw [hout] at hrl
    rcases List.mem_cons.mp hrl with he | hrl'
    · rw [he]
      exact iotaRuleRenRunJ_storeAr hf hlen htyA hr
    · exact iotaRulesRenRunJ_storeAr hf hlen htyA hrest rl hrl'

/-- **The recursors' install fold**: every recursor stored with its rules is arity-correct
after the block. -/
theorem indRecsFoldRenRunJ_storeAr {envBase envSelf : Env .anon}
    (hf : RenLen envSelf (fun n => if bn.contains n then auxKey n .model else n))
    (hlen : LenExt envSelf env₂) :
    ∀ {acc : Env .anon} {checked : List (ConstantVal .anon × Nat × Nat × List (RecRule .anon))}
      {out : Env .anon},
      IndRecsFoldRenRunJ (famJ h) bn envBase envSelf acc checked out →
      (∀ c ∈ checked, ArRes env₂ c.1.type) →
      Ix.Kernel.Model.NewSat acc out (ConstArR env₂)
  | acc, [], out, hout, _ => by
    have e : out = acc := hout
    rw [e]
    exact Ix.Kernel.Model.NewSat.refl _ _
  | acc, c :: rest, out, ⟨rules', hrules, hrest⟩, hty => by
    have hc := hty c List.mem_cons_self
    exact (Ix.Kernel.Model.NewSat.cons (Ix.Kernel.Model.ConstArR.of_rec (mI := c.2.1)
      (rP := c.2.2.1) hc
      (iotaRulesRenRunJ_storeAr hf hlen hc.ar hrules))).trans
      (indRecsFoldRenRunJ_storeAr hf hlen hrest
        (fun c' hc' => hty c' (List.mem_cons_of_mem _ hc')))

end Walk

/-- **Provisioning and the install fold store the same names at the same level counts**: each
recursor provisioned without rules is stored again with its rules. -/
theorem lenExt_provision_fold {J J' : Judgements .anon} {bn : List KKey}
    {envBase envSelf₀ : Env .anon} :
    ∀ {envP : Env .anon} {recs : List (ConstantInfo .anon)} {envSelf : Env .anon}
      {checked : List (ConstantVal .anon × Nat × Nat × List (RecRule .anon))}
      {envF out : Env .anon},
      ProvisionRecsRunJ J bn envP recs envSelf checked →
      IndRecsFoldRenRunJ J' bn envBase envSelf₀ envF checked out →
      LenExt envP envF → LenExt envSelf out
  | envP, [], envSelf, checked, envF, out, ⟨hs, hc⟩, hfold, hlen => by
    subst hs
    subst hc
    have hfo : out = envF := hfold
    rw [hfo]
    exact hlen
  | envP, ci :: rest, envSelf, checked, envF, out,
      ⟨cvA, mI, rP, rules, rest', -, hmv, hprov, hchk⟩, hfold, hlen => by
    subst hchk
    obtain ⟨rules', -, hfold'⟩ := hfold
    exact lenExt_provision_fold hprov hfold' (LenExt.cons hlen rfl rfl)

/-- **Every constant the renamed record stores is arity-correct after the block.** -/
theorem famRecord_newSat {env env₂ : Env .anon} {h : KKey → KKey}
    {block : List (ConstantInfo .anon)}
    (hd : DeclIndRenRunJ (famJ h) env block env₂) :
    Ix.Kernel.Model.NewSat env env₂ (ConstArR env₂) := by
  obtain ⟨hsplit, envM, hmem, hrecs⟩ := hd
  have hfrM := indMembersRunJ_fresh (E := env) hmem (fun hk => hk)
  have hextM : EnvExt env envM := Ix.Kernel.Semantics.indMembersRunJ_envExt hmem
  have hML₀ : ModelLen env (block.map (·.name)) := by
    intro k hk ci hf
    exfalso
    obtain ⟨ci₀, hci₀, hk₀⟩ := List.mem_map.mp hk
    have hfresh : env.find? ci₀.name = none := by
      rw [hsplit] at hci₀
      rcases List.mem_append.mp hci₀ with h1 | h1
      · exact hfrM ci₀ h1
      · rcases hrecs with ⟨hnil, -⟩ | ⟨-, -, envSelf, checked, hprov, -⟩
        · rw [hnil] at h1
          exact nomatch h1
        · exact provisionRecsRunJ_fresh hprov hextM.find ci₀ h1
    have hk₁ : ci₀.name = k := hk₀
    rw [hk₁, hf] at hfresh
    exact nomatch hfresh
  rcases hrecs with ⟨hnil, rfl⟩ | ⟨-, -, envSelf, checked, hprov, hfold⟩
  · exact (indMembersRunJ_storeAr hmem hML₀ (LenExt.of_find fun hx => hx)).2
  · have hlenS : LenExt envSelf env₂ :=
      lenExt_provision_fold hprov hfold (LenExt.of_find fun hx => hx)
    have hlenM : LenExt envM env₂ :=
      LenExt.trans (LenExt.of_find (provisionRecsRunJ_envExt hprov).find) hlenS
    obtain ⟨hMLM, hnsM⟩ := indMembersRunJ_storeAr hmem hML₀ hlenM
    obtain ⟨hMLS, hty⟩ := provisionRecsRunJ_storeAr hprov hMLM hlenS
    exact hnsM.trans (indRecsFoldRenRunJ_storeAr (renLen_bren hMLS) hlenS hfold hty)

/-! ## The aliases -/

/-- **An alias group keeps `StoreArR`.** -/
theorem storeArR_aliasGroup {env : Env .anon} {h : KKey → KKey} {as : List (ConstantInfo .anon)}
    (hg : AliasGroup env h as) (hA : StoreArR env) : StoreArR ⟨as ++ env.consts⟩ := by
  induction hg with
  | nil _ => exact hA
  | @cons h₀ h' as' n d lps ty tgt ci hg' hperm hfresh hnpt hsrc hlps htf htp htr htb hty hk'
      hrest ih =>
    have hAl : AliasEnv ⟨as' ++ env.consts⟩ h₀ := hg'.aliasEnv
    have hci : ConstArR ⟨as' ++ env.consts⟩ ci := ih.const hsrc
    have harT : Expr.arOk (⟨as' ++ env.consts⟩ : Env .anon) ty = true := by
      have h1 := hci.type.ar
      rw [← hty] at h1
      unfold posOf at h1
      rw [Ix.Kernel.LevelRen.arOk_inst] at h1
      exact arOk_of_renameConsts (renLen_of_aliasEnv hAl) h1
    have hfx : ∀ {k : KKey} {x : ConstantInfo .anon},
        (⟨as' ++ env.consts⟩ : Env .anon).find? k = some x →
          (⟨ConstantInfo.defnInfo ⟨auxKey n d, lps, ty⟩ (.const tgt (lps.map .param))
            .abbrev :: (as' ++ env.consts)⟩ : Env .anon).find? k = some x :=
      fun hx => Ix.Kernel.Env.find?_cons_of_fresh hfresh hx
    have hval : ArRes (⟨as' ++ env.consts⟩ : Env .anon) (.const tgt (lps.map .param)) := by
      refine ⟨Ix.Kernel.LevelRen.arOk_const_of (fun ci' hf' => ?_), ?_⟩
      · rw [hsrc] at hf'
        obtain rfl := Option.some.inj hf'
        rw [hlps]
        simp
      · simp [Expr.constsResolve, hsrc]
    refine Ix.Kernel.Model.storeArR_cons ih hfresh
      (Ix.Kernel.Model.ConstArR.of_defn (Ix.Kernel.Model.ArRes.mono hfx ⟨harT, htr⟩)
        (Ix.Kernel.Model.ArRes.mono hfx hval)) ?_
    intro _ hn
    exfalso
    rcases hn with hn | hn
    · exact Ix.Kernel.auxKey_ne_roleKey n d _ hn
    · exact Ix.Kernel.auxKey_ne_roleKey n d _ hn

/-! ## The step -/

/-- **`FamilyKeepsStoreAr`** (module docstring). -/
theorem familyKeepsStoreAr : FamilyKeepsStoreAr := by
  intro env env₂ h aliases block hg hd hA
  have hA₀ : StoreArR (⟨aliases ++ env.consts⟩ : Env .anon) := storeArR_aliasGroup hg hA
  have hext : EnvExt ⟨aliases ++ env.consts⟩ env₂ := Ix.Kernel.Semantics.declIndRenRunJ_envExt hd
  have hnew := famRecord_newSat hd
  have hnd : Ix.Kernel.Model.NewSat ⟨aliases ++ env.consts⟩ env₂
      (fun ci => ∀ cv v hint, ci ≠ .defnInfo cv v hint) :=
    Ix.Kernel.Model.modeled_newSat (fun _ _ _ _ he => nomatch he)
      (fun _ _ _ _ _ _ he => nomatch he) (fun _ _ _ _ _ _ _ he => nomatch he) hd.shape
  refine hA₀.step hext.find ?_ ?_
  · intro n ci hf hn
    rcases hnew n ci hf with hold | hc
    · rw [hn] at hold
      exact nomatch hold
    · exact hc
  · intro c hst hn hcb
    exfalso
    unfold Ix.Kernel.natOpStored at hst
    cases hfc : env₂.find? c with
    | none =>
      rw [hfc] at hst
      exact nomatch hst
    | some ci =>
      rw [hfc] at hst
      rcases hnd c ci hfc with hold | hnd'
      · rw [hn] at hold
        exact nomatch hold
      · cases ci with
        | defnInfo cv v hint => exact hnd' cv v hint rfl
        | _ => simp at hst

end IxVM.Refinement.Decl.FamilyAlias
