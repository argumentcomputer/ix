import IxVMRefinement.TwinFamily.Target
import IxCK.Kernel.Semantics.Inductives.WrapRelFacts
import IxCK.Kernel.Semantics.Inductives.DeclRecTwinExtJ

/-! # The arity of the stored terms across the twin record

`TwinKeepsStoreAr` (`Target.lean`): IxCK's twin record at the positional package keeps
`StoreArR` (every stored term arity-correct and resolving). IxCK has no lemma for the twin route;
this module proves it (`twinKeepsStoreAr`). The new constants are of two kinds:

* a model copy is a stored model companion under another name: its terms are the companion's;
* a twin recursor's checked type is inferred at positions, so it is arity-correct
  (`infer_full_arOk` through `posOf`, which keeps every level list's length); a rule's
  right-hand side is the declared side of `WrapRel` against the generated right-hand side renamed
  to the twin's peers. The generated one is the canonical rule's (stored) or is inferred at
  positions; the renaming sends a canonical recursor to its twin, which has as many level
  parameters (`arRes_renameConsts`); and the declared side of `WrapRel` at a term without `let`
  inherits the generated side's arity, since a consumed wrapper leaves its first argument
  (`wrapT_arOk`). A rule's resolution is the record's own (it resolves where the twins are
  provisioned, whose names are the twins'). A nested rule's pins are the canonical rule's. -/

namespace IxVM.Refinement.Typing.TwinFamily

open Ix.Kernel (Env Expr Key ConstantInfo ConstantVal RecRule)
open Ix.Kernel.Semantics (WrapRel WrapT ConsumeStar DeclRecTwinRunJ TwinRecPart twinRecs
  twinModels twinProv Forall₂ LamDomAlong TwinRuleMatch stripLams)
open Ix.Kernel.Model (ArRes ConstArR StoreArR)
open IxVM.Refinement.Decl (twinPosRulesJ judgeFrames_twinPosRulesJ)

set_option linter.unusedVariables false

/-! ## Lists -/

theorem forall₂_length {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, Forall₂ R l₁ l₂ → l₁.length = l₂.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by rw [List.length_cons, List.length_cons, forall₂_length h]

theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, Forall₂ R l₁ l₂ → ∀ {a : α}, a ∈ l₁ → ∃ b ∈ l₂, R a b
  | _, _, .nil, _, h => nomatch h
  | _, _, .cons hab h, a, hm => by
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, hr⟩ := forall₂_mem_left h hm
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

theorem exists_mem_zip_right {α β : Type} :
    ∀ {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length → ∀ {b : β}, b ∈ l₂ →
      ∃ a, (a, b) ∈ l₁.zip l₂
  | [], [], _, _, h => nomatch h
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl
  | a :: l₁, b' :: l₂, hl, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, by simp⟩
    · obtain ⟨a', ha'⟩ := exists_mem_zip_right (l₁ := l₁) (by simpa using hl) hb
      exact ⟨a', by simp [ha']⟩

/-- A lookup that succeeds in an environment succeeds with constants put in front. -/
theorem find_isSome_append {rest : List (ConstantInfo .anon)} {n : Key .anon}
    (h : (Env.find? ⟨rest⟩ n).isSome = true) :
    ∀ cs : List (ConstantInfo .anon), (Env.find? ⟨cs ++ rest⟩ n).isSome = true
  | [] => h
  | c :: cs => by
    show (Env.find? ⟨c :: (cs ++ rest)⟩ n).isSome = true
    rw [Env.find?_cons]
    split
    · rfl
    · exact find_isSome_append h cs

/-! ## Arity along the relations -/

/-- **The declared side of `WrapRel` (at a term without `let`, read as `WrapT`) is
arity-correct where the generated side is**: a consumed wrapper leaves its first argument. -/
theorem wrapT_arOk {find? : Key .anon → Option (ConstantInfo .anon)} {env : Env .anon}
    {g d : Expr .anon} (h : WrapT find? g d) (hd : d.hasFvar = false)
    (hg : Expr.arOk env g = true) : Expr.arOk env d = true := by
  have hP : ∀ f x : Expr .anon,
      (fun e : Expr .anon => Expr.arOk env e = true) (.app f x) →
      (fun e : Expr .anon => Expr.arOk env e = true) f ∧
      (fun e : Expr .anon => Expr.arOk env e = true) x := by
    intro f x h
    simp only [Expr.arOk, Bool.and_eq_true] at h
    exact h
  induction h with
  | bvar | lit => exact hg
  | sort => rfl
  | const hus =>
    simp only [Expr.arOk] at hg ⊢
    rw [← forall₂_length hus]
    exact hg
  | fvar => simp [Expr.hasFvar] at hd
  | app _ _ ihf iha =>
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hd
    simp only [Expr.arOk, Bool.and_eq_true] at hg ⊢
    exact ⟨ihf hd.1 hg.1, iha hd.2 hg.2⟩
  | lam _ hs _ _ ihw ihb =>
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hd
    simp only [Expr.arOk, Bool.and_eq_true] at hg ⊢
    exact ⟨ihw hd.1 (hs.of (P := fun e : Expr .anon => Expr.arOk env e = true) hP hg.1),
      ihb hd.2 hg.2⟩
  | forallE _ hs _ _ ihw ihb =>
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hd
    simp only [Expr.arOk, Bool.and_eq_true] at hg ⊢
    exact ⟨ihw hd.1 (hs.of (P := fun e : Expr .anon => Expr.arOk env e = true) hP hg.1),
      ihb hd.2 hg.2⟩
  | proj _ ih =>
    simp only [Expr.hasFvar] at hd
    simp only [Expr.arOk] at hg ⊢
    exact ih hd hg

/-- **Renaming constants to constants with as many level parameters** keeps a term
arity-correct and resolving. -/
theorem arRes_renameConsts {env : Env .anon} {f : Key .anon → Key .anon}
    (hf : ∀ k ci, env.find? k = some ci → ∃ ci', env.find? (f k) = some ci' ∧
      ci'.toConstantVal.levelParams.length = ci.toConstantVal.levelParams.length) :
    ∀ {e : Expr .anon}, Expr.arOk env e = true → e.constsResolve env = true →
      Expr.arOk env (e.renameConsts f) = true ∧ (e.renameConsts f).constsResolve env = true := by
  intro e
  induction e with
  | bvar _ => intro _ _; exact ⟨rfl, rfl⟩
  | sort _ => intro _ _; exact ⟨rfl, rfl⟩
  | lit l => intro ha hr; exact ⟨ha, hr⟩
  | const c us =>
    intro ha hr
    simp only [Expr.constsResolve, Option.isSome_iff_exists] at hr
    obtain ⟨ci, hci⟩ := hr
    obtain ⟨ci', hci', hlen⟩ := hf c ci hci
    simp only [Expr.arOk, hci] at ha
    simp only [Expr.renameConsts, Expr.arOk, Expr.constsResolve, hci', hlen,
      Option.isSome_some, and_true]
    exact ha
  | fvar i ty ih =>
    intro ha hr
    simp only [Expr.renameConsts, Expr.arOk, Expr.constsResolve] at ha hr ⊢
    exact ih ha hr
  | app a b iha ihb =>
    intro ha hr
    simp only [Expr.renameConsts, Expr.arOk, Expr.constsResolve, Bool.and_eq_true] at ha hr ⊢
    obtain ⟨h1, h2⟩ := iha ha.1 hr.1
    obtain ⟨h3, h4⟩ := ihb ha.2 hr.2
    exact ⟨⟨h1, h3⟩, h2, h4⟩
  | lam ty b m iht ihb =>
    intro ha hr
    simp only [Expr.renameConsts, Expr.arOk, Expr.constsResolve, Bool.and_eq_true] at ha hr ⊢
    obtain ⟨h1, h2⟩ := iht ha.1 hr.1
    obtain ⟨h3, h4⟩ := ihb ha.2 hr.2
    exact ⟨⟨h1, h3⟩, h2, h4⟩
  | forallE ty b m iht ihb =>
    intro ha hr
    simp only [Expr.renameConsts, Expr.arOk, Expr.constsResolve, Bool.and_eq_true] at ha hr ⊢
    obtain ⟨h1, h2⟩ := iht ha.1 hr.1
    obtain ⟨h3, h4⟩ := ihb ha.2 hr.2
    exact ⟨⟨h1, h3⟩, h2, h4⟩
  | letE ty v b m iht ihv ihb =>
    intro ha hr
    simp only [Expr.renameConsts, Expr.arOk, Expr.constsResolve, Bool.and_eq_true] at ha hr ⊢
    obtain ⟨⟨a1, a2⟩, a3⟩ := ha
    obtain ⟨⟨r1, r2⟩, r3⟩ := hr
    obtain ⟨h1, h2⟩ := iht a1 r1
    obtain ⟨h3, h4⟩ := ihv a2 r2
    obtain ⟨h5, h6⟩ := ihb a3 r3
    exact ⟨⟨⟨h1, h3⟩, h5⟩, ⟨h2, h4⟩, h6⟩
  | proj s i e ih =>
    intro ha hr
    simp only [Expr.renameConsts, Expr.arOk, Expr.constsResolve, Bool.and_eq_true] at ha hr ⊢
    obtain ⟨h1, h2⟩ := ih ha hr.2
    exact ⟨h1, hr.1, h2⟩

/-- A term inferred at the positional package (closed) is arity-correct. -/
theorem arOk_of_twinPosInfer {env : Env .anon} {e t : Expr .anon} (hfv : e.hasFvar = false)
    (h : twinPosRulesJ.infer env 0 e t) : Expr.arOk env e = true := by
  obtain ⟨ps, -, hinf⟩ := h
  have h1 := Ix.Kernel.Model.infer_full_arOk hinf rfl (fun l hl => by
    rw [Ix.Kernel.Rules.fvarLeaves_nil_of_hasFvar (by
      unfold Core.posOf
      rw [Ix.Kernel.Expr.hasFvar_instantiateLevelParams]
      exact hfv)] at hl
    exact nomatch hl)
  unfold Core.posOf at h1
  rwa [Ix.Kernel.LevelRen.arOk_inst] at h1

private theorem arOk_liftLooseBVars (env : Env .anon) :
    ∀ (e : Expr .anon) (n c : Nat), Expr.arOk env (e.liftLooseBVars n c) = Expr.arOk env e
  | .bvar i, n, c => by simp only [Expr.liftLooseBVars]; split <;> rfl
  | .fvar _ _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, n, c => by
    simp [Expr.liftLooseBVars, Expr.arOk, arOk_liftLooseBVars env f n c,
      arOk_liftLooseBVars env a n c]
  | .lam t b _, n, c => by
    simp [Expr.liftLooseBVars, Expr.arOk, arOk_liftLooseBVars env t n c,
      arOk_liftLooseBVars env b n (c + 1)]
  | .forallE t b _, n, c => by
    simp [Expr.liftLooseBVars, Expr.arOk, arOk_liftLooseBVars env t n c,
      arOk_liftLooseBVars env b n (c + 1)]
  | .letE t v b _, n, c => by
    simp [Expr.liftLooseBVars, Expr.arOk, arOk_liftLooseBVars env t n c,
      arOk_liftLooseBVars env v n c, arOk_liftLooseBVars env b n (c + 1)]
  | .proj _ _ e, n, c => arOk_liftLooseBVars env e n c

private theorem arOk_of_stripPis {env : Env .anon} :
    ∀ (n : Nat) {e rest : Expr .anon} {bs : List (Expr .anon × Ix.Kernel.BinderMeta)},
      e.stripPis n = some (bs, rest) → Expr.arOk env e = true → Expr.arOk env rest = true
  | 0, _, _, _, hs, ha => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, rfl⟩ := hs
    exact ha
  | n + 1, _, _, _, hs, ha => by
    obtain ⟨_, _, _, _, rfl, hs0⟩ := Ix.Kernel.Semantics.stripPis_succ_inv hs
    simp only [Expr.arOk, Bool.and_eq_true] at ha
    exact arOk_of_stripPis n hs0 ha.2

private theorem arOk_of_stripLams {env : Env .anon} :
    ∀ (n : Nat) {e rest : Expr .anon},
      stripLams n e = some rest → Expr.arOk env e = true → Expr.arOk env rest = true
  | 0, _, _, hs, ha => by
    simp only [stripLams, Option.some.injEq] at hs; subst hs; exact ha
  | n + 1, .lam _ _ _, _, hs, ha => by
    simp only [stripLams] at hs
    simp only [Expr.arOk, Bool.and_eq_true] at ha
    exact arOk_of_stripLams n hs ha.2
  | _ + 1, .bvar _, _, hs, _ | _ + 1, .fvar _ _, _, hs, _ | _ + 1, .sort _, _, hs, _
  | _ + 1, .const _ _, _, hs, _ | _ + 1, .app _ _, _, hs, _ | _ + 1, .forallE _ _ _, _, hs, _
  | _ + 1, .letE _ _ _ _, _, hs, _ | _ + 1, .lit _, _, hs, _ | _ + 1, .proj _ _ _, _, hs, _ => by
    simp [stripLams] at hs

private theorem hasFvar_of_lamDomAlong {n : Nat} {l p r : Expr .anon}
    (h : LamDomAlong n l p r) (hl : l.hasFvar = false) : r.hasFvar = false := by
  induction h with
  | zero => exact hl
  | succ _ _ ih =>
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hl
    exact ih hl.2

private theorem arOk_of_lamDomAlong {env : Env .anon} {n : Nat} {l p r : Expr .anon}
    (h : LamDomAlong n l p r) (hl : l.hasFvar = false)
    (hp : Expr.arOk env p = true) (hr : Expr.arOk env r = true) : Expr.arOk env l = true := by
  induction h with
  | zero => exact hr
  | succ hdom _ ih =>
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hl
    simp only [Expr.arOk, Bool.and_eq_true] at hp ⊢
    exact ⟨wrapT_arOk hdom.symm_empty hl.1 hp.1, ih hl.2 hp.2 hr⟩

private theorem arOk_of_twinRuleMatch {find? : Key .anon → Option (ConstantInfo .anon)}
    {env : Env .anon} {f : Key .anon → Key .anon}
    {tyW' rhsC rhsW' : Expr .anon} (h : TwinRuleMatch find? f tyW' rhsC rhsW')
    (hfvW : rhsW'.hasFvar = false) (hty : Expr.arOk env tyW' = true)
    (hrc : Expr.arOk env (rhsC.renameConsts f) = true) : Expr.arOk env rhsW' = true := by
  obtain ⟨-, nPre, nf, afterW, sbW, sbC, hLam1, hMid, hSC, hBase⟩ := h
  have hfvAfter : afterW.hasFvar = false := hasFvar_of_lamDomAlong hLam1 hfvW
  have harSbC : Expr.arOk env sbC = true := arOk_of_stripLams (nPre + nf) hSC hrc
  have harAfter : Expr.arOk env afterW = true := by
    rcases hMid with ⟨rfl, rfl⟩ | ⟨iMin, bs, mdomW, restW, mmW, -, hStripP, hLam2⟩
    · exact wrapT_arOk hBase hfvAfter harSbC
    · have hfvSbW : sbW.hasFvar = false := hasFvar_of_lamDomAlong hLam2 hfvAfter
      have harSbW : Expr.arOk env sbW = true := wrapT_arOk hBase hfvSbW harSbC
      have harMdom : Expr.arOk env mdomW = true := by
        have h1 := arOk_of_stripPis iMin hStripP hty
        simp only [Expr.arOk, Bool.and_eq_true] at h1
        exact h1.1
      have harLift : Expr.arOk env (mdomW.liftLooseBVars (nPre - iMin) 0) = true := by
        rw [arOk_liftLooseBVars]; exact harMdom
      exact arOk_of_lamDomAlong hLam2 hfvAfter harLift harSbW
  exact arOk_of_lamDomAlong hLam1 hfvW hty harAfter

/-! ## The twin record keeps `StoreArR` -/

/-- **`TwinKeepsStoreAr`** (module docstring). -/
theorem twinKeepsStoreAr : TwinKeepsStoreAr := by
  intro env env₂ block hrun hA
  have hext : Ix.Kernel.EnvExt env env₂ := Ix.Kernel.Semantics.declRecTwinRunJ_envExt hrun
  obtain ⟨ws, f, -, -, henv, hnd, hfr, hfk, hall⟩ := hrun
  have henv' : env₂ = ⟨(twinRecs ws ++ twinModels ws) ++ env.consts⟩ := by
    rw [henv]
    exact congrArg Env.mk (List.append_assoc _ _ _).symm
  have hlpW : ∀ w ∈ ws, w.cvW'.levelParams = w.cvW.levelParams := by
    intro w hw
    obtain ⟨-, -, -, -, -, -, type, stype, lv, -, -, -, -, -, h⟩ := (hall w hw).1.inv
    rw [h]
  have hfindRec : ∀ w ∈ ws,
      env₂.find? w.cvW.name = some (.recInfo w.cvW' w.mI w.rP w.rulesW') := by
    intro w hw
    have hm : ConstantInfo.recInfo w.cvW' w.mI w.rP w.rulesW' ∈ twinRecs ws ++ twinModels ws :=
      List.mem_append_left _ (List.mem_map.mpr ⟨w, hw, rfl⟩)
    have h := Ix.Kernel.Semantics.find?_mem_of_nodup (rest := env.consts) hnd hm
    rw [henv', ← (hall w hw).1.name_eq]
    exact h
  refine hA.step hext.find ?_ ?_
  · intro n ci hf hn
    rw [henv'] at hf
    rcases Ix.Kernel.Semantics.find?_append_inv hf with hold | ⟨hmem, -⟩
    · rw [hn] at hold
      cases hold
    rcases List.mem_append.mp hmem with hrec | hmod
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hrec
      have hcv := (hall w hw).1
      have hcC : ConstArR env (.recInfo w.cvC w.mI w.rP w.rulesC) := hA.const (hall w hw).2.2.1
      have hTyW'₂ : ArRes env₂ w.cvW'.type := by
        obtain ⟨-, -, -, -, hlb, hfv, type, stype, lv, hann, hlp, hres, hinf, -, hcv'⟩ := hcv.inv
        obtain ⟨hfv', -⟩ := (judgeFrames_twinPosRulesJ env).annot_syntax hann hfv hlb
        have h : ArRes env w.cvW'.type := by
          rw [hcv']
          exact ⟨arOk_of_twinPosInfer hfv' hinf, hres⟩
        exact h.mono hext.find
      refine { type := hTyW'₂, defn := fun _ _ _ he => (nomatch he), thm := fun _ _ he => (nomatch he),
               rhs := ?_, proj := fun _ he => nomatch he }
      · intro cv mI rP rules he rl hrl
        cases he
        obtain ⟨rW, hz⟩ := exists_mem_zip_right (hall w hw).2.2.2.2.2.2.1 hrl
        obtain ⟨rC, hrC, hJ⟩ := forall₂_mem_left (hall w hw).2.2.2.2.2.2.2 hz
        obtain ⟨-, -, hlbW, hfvW, hannR, -, hresSelf, hlf, -, -, -, hfire, -, -, -, -, -, rhsG,
          -, hwW, hgen⟩ := hJ
        have hfvR : rl.rhs.hasFvar = false :=
          ((judgeFrames_twinPosRulesJ _).annot_syntax hannR hfvW hlbW).1
        have hrC' := hcC.rhs _ _ _ _ rfl rC hrC
        have hren : ∀ k ci, env₂.find? k = some ci → ∃ ci', env₂.find? (f k) = some ci' ∧
            ci'.toConstantVal.levelParams.length = ci.toConstantVal.levelParams.length := by
          intro k ci hci
          rcases hfk k with he | ⟨w', hw', rfl, hfe⟩
          · exact ⟨ci, by rw [he]; exact hci, rfl⟩
          · have h1 := hext.find (hall w' hw').2.2.1
            rw [h1] at hci
            cases hci
            refine ⟨.recInfo w'.cvW' w'.mI w'.rP w'.rulesW', by rw [hfe]; exact hfindRec w' hw', ?_⟩
            show w'.cvW'.levelParams.length = w'.cvC.levelParams.length
            rw [hlpW w' hw', (hall w' hw').2.2.2.1]
        have harW : Expr.arOk env₂ rl.rhs = true := by
          rcases hgen with rfl | ⟨hfvG, -, hresG, -, rty, hinfG⟩ | hMatch
          · have hG₂ := hrC'.1.mono hext.find
            obtain ⟨harR, -⟩ := arRes_renameConsts hren hG₂.1 hG₂.2
            exact wrapT_arOk (WrapRel.toWrapT hwW hlf) hfvR harR
          · have hG₂ := (⟨arOk_of_twinPosInfer hfvG hinfG, hresG⟩ : ArRes env rhsG).mono hext.find
            obtain ⟨harR, -⟩ := arRes_renameConsts hren hG₂.1 hG₂.2
            exact wrapT_arOk (WrapRel.toWrapT hwW hlf) hfvR harR
          · have hC₂ := hrC'.1.mono hext.find
            obtain ⟨harRenC, -⟩ := arRes_renameConsts hren hC₂.1 hC₂.2
            exact arOk_of_twinRuleMatch hMatch hfvR hTyW'₂.1 harRenC
        refine ⟨⟨harW, ?_⟩, ?_⟩
        · refine Ix.Kernel.Expr.constsResolve_of_find (fun n hn => ?_) hresSelf
          obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
          rcases Ix.Kernel.Semantics.find?_append_inv (cs := twinProv ws) hci with hold | ⟨hm, hname⟩
          · rw [henv]
            have hold' : (Env.find? ⟨twinModels ws ++ env.consts⟩ n).isSome = true := by
              simp only [Option.isSome_iff_exists]
              exact ⟨ci, hold⟩
            exact find_isSome_append hold' (twinRecs ws)
          · obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hm
            rw [← hname]
            show (env₂.find? w'.cvW'.name).isSome = true
            rw [(hall w' hw').1.name_eq, hfindRec w' hw']
            rfl
        · intro lvls pins hnest p hp
          have hfire' : rl.fire = rC.fire := hfire
          exact (hrC'.2 lvls pins (hfire'.symm.trans hnest) p hp).mono hext.find
    · obtain ⟨w, hw, hmi⟩ := List.mem_filterMap.mp hmod
      unfold TwinRecPart.modelInfo? at hmi
      obtain ⟨⟨cvm, mval, hint⟩, hmod', rfl⟩ := Option.map_eq_some_iff.mp hmi
      have hm := (hall w hw).2.2.2.2.1
      simp only [hmod'] at hm
      have hc : ConstArR env (.defnInfo cvm mval hint) := hA.const hm
      exact
        { type := hc.type.mono hext.find
          defn := fun cv v h he => by
            cases he
            exact (hc.defn _ _ _ rfl).mono hext.find
          thm := fun _ _ he => nomatch he
          rhs := fun _ _ _ _ he => nomatch he
          proj := fun _ he => nomatch he }
  · intro c hst hn hcb
    exfalso
    unfold Ix.Kernel.natOpStored at hst
    cases hfc : env₂.find? c with
    | none =>
      rw [hfc] at hst
      cases hst
    | some ci =>
      rw [hfc] at hst
      rw [henv'] at hfc
      rcases Ix.Kernel.Semantics.find?_append_inv hfc with hold | ⟨hmem, hname⟩
      · rw [hn] at hold
        cases hold
      rcases List.mem_append.mp hmem with hrec | hmod
      · obtain ⟨w, -, rfl⟩ := List.mem_map.mp hrec
        simp at hst
      · obtain ⟨w, -, hmi⟩ := List.mem_filterMap.mp hmod
        unfold TwinRecPart.modelInfo? at hmi
        obtain ⟨⟨cvm, mval, hint⟩, -, rfl⟩ := Option.map_eq_some_iff.mp hmi
        rcases hcb with rfl | rfl <;> cases hname

end IxVM.Refinement.Typing.TwinFamily
