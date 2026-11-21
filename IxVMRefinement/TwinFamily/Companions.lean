import IxVMRefinement.TwinFamily.Step

/-! # The scoped core's companions after a twin record

The fold's clause carries the role and record companions of the scoped core
(`Decl.CoreCompanions`). The twin record adds twin recursors and model copies (definitions), so
the role fields are kept by the extension and the record fields ask, of each twin recursor, the
four facts a recursor owes: its major premise's record, its rules' constructors, its plain
rules' major premise, and its rules' constructor heads. Each twin recursor has the counts and
the rule constructors of its canonical recursor, which is stored before the step and owes the
same facts; what carries them over is that the two major-premise domains have one head, and the
same arguments where the canonical's are bound variables.

* `coreCompanions_append`: the companions after constants none of which is a constructor, from
  those before and the four facts of each new recursor;
* `TwinCompanionFacts`: what a twin part gives for that: its canonical recursor stored, its
  rules' constructors and fire modes the canonical's, the major-premise domains;
* `coreCompanions_twin`: the companions after a twin record's constants.
-/

namespace IxVM.Refinement.Typing.TwinFamily

open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal RecRule Key)
open Ix.Kernel.Semantics (TwinRecPart twinModels twinRecs)

set_option linter.unusedVariables false

/-! ## Lists -/

theorem lforall₂_map_eq {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ}
    (hR : ∀ a b, R a b → f a = g b) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → l₁.map f = l₂.map g
  | _, _, .nil => rfl
  | _, _, .cons hab h => by
    rw [List.map_cons, List.map_cons, hR _ _ hab, lforall₂_map_eq hR h]

theorem lforall₂_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {a : α}, a ∈ l₁ → ∃ b ∈ l₂, R a b
  | _, _, .nil, _, h => nomatch h
  | _, _, .cons hab h, a, hm => by
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, hr⟩ := lforall₂_mem_left h hm
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

theorem lforall₂_ne_nil {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → l₁ ≠ [] → l₂ ≠ []
  | _, _, .nil, h => absurd rfl h
  | _, _, .cons _ _, _ => List.cons_ne_nil _ _

/-! ## The companions after constants that are no constructor -/

/-- **The companions after constants none of which is a constructor**, from those before, the
extension, and, for each new recursor, its four facts (constructors read at the prefix: none
is new). -/
theorem coreCompanions_append {c : Core.Ctx} (h : Decl.CoreCompanions c)
    {new : List (ConstantInfo .anon)}
    (hext : Ix.Kernel.EnvExt c.env ⟨new ++ c.env.consts⟩)
    (hnoctor : ∀ ci ∈ new, ∀ cv nP nF, ci ≠ .ctorInfo cv nP nF)
    (hrec : ∀ cv mI rP rls, ConstantInfo.recInfo cv mI rP rls ∈ new →
      (∀ (p : _root_.Address) (us : List Core.KLevel), rls ≠ [] →
        (Core.piDomAt mI cv.type).map (·.getAppFn) = some (.const (c.κ p) us) →
        ∃ cm, Ix.Cert.recordAt c.E p = some cm) ∧
      ((rls.map (·.ctor)).Nodup ∧
        ∀ (p : _root_.Address) (cm : Ixon.Constant) (ip : Ixon.InductiveProj)
          (us : List Core.KLevel),
          (Core.piDomAt mI cv.type).map (·.getAppFn) = some (.const (c.κ p) us) →
          Ix.Cert.recordAt c.E p = some cm → cm.info = .iPrj ip →
          ∀ j rl, rls[j]? = some rl → rl.ctor = c.κ (Core.cprjAddr ip.block ip.idx.toNat j)) ∧
      (∀ (rl : RecRule .anon) (cvj : ConstantVal .anon) (nP nF : Nat), rl ∈ rls →
        rl.fire = .plain → c.env.find? rl.ctor = some (.ctorInfo cvj nP nF) →
        ∃ D T, Core.piDomAt mI cv.type = some D ∧
          D.getAppFn = .const T (cvj.levelParams.map .param) ∧
          D.getAppArgs.take nP = (List.range nP).map (fun i => .bvar (mI - 1 - i)) ∧
          D.getAppArgs.drop nP = (List.range (mI - rP)).map fun i => .bvar (mI - rP - 1 - i)) ∧
      ((∀ (rl : RecRule .anon) (cvj : ConstantVal .anon) (nP nF : Nat) (T : Key .anon)
          (us : List Core.KLevel), rl ∈ rls →
          c.env.find? rl.ctor = some (.ctorInfo cvj nP nF) →
          (Core.piDomAt mI cv.type).map (·.getAppFn) = some (.const T us) →
          ∃ tus, (Ix.Kernel.Expr.piResult cvj.type).getAppFn = .const T tus) ∨
        Core.RecNotKAt c.E cv.name)) :
    Decl.CoreCompanions ⟨c.E, ⟨new ++ c.env.consts⟩, c.t, c.lim⟩ := by
  have hctor_old : ∀ {k : Key .anon} {cvj : ConstantVal .anon} {nP nF : Nat},
      (⟨new ++ c.env.consts⟩ : Ix.Kernel.Env .anon).find? k = some (.ctorInfo cvj nP nF) →
        c.env.find? k = some (.ctorInfo cvj nP nF) := by
    intro k cvj nP nF hf
    rcases find?_append_cases new hf with hm | ho
    · exact (hnoctor _ hm cvj nP nF rfl).elim
    · exact ho
  exact
    { natLit := fun h1 h2 h3 => hext.natLitSupported_mono (h.natLit h1 h2 h3)
      strLit := fun h1 => hext.strLitSupported_mono (h.strLit h1)
      natOps := fun r hr hm => hext.natOpStored_mono (h.natOps r hr hm)
      natAdd := fun h1 => hext.opt_mono (p := Ix.Kernel.Rules.natAddTyOk) (h.natAdd h1) rfl
      eqStored := fun h1 =>
        let ⟨ci', hci'⟩ := h.eqStored h1
        ⟨ci', hext.find hci'⟩
      primEqn := fun h1 => (h.primEqn h1).weaken hext
      quotBasis := fun h1 ci' hm => hext.find (h.quotBasis h1 ci' hm)
      recMajorRecord := by
        intro k cv mI rP rls p us hf hne hdom
        rcases find?_append_cases new hf with hm | hf'
        · exact (hrec cv mI rP rls hm).1 p us hne hdom
        · exact h.recMajorRecord k cv mI rP rls p us hf' hne hdom
      recRulesNodupAndProj := by
        intro k cv mI rP rls hf
        rcases find?_append_cases new hf with hm | hf'
        · exact (hrec cv mI rP rls hm).2.1
        · exact h.recRulesNodupAndProj k cv mI rP rls hf'
      recPlain := by
        intro k cv mI rP rls rl cvj nP nF hf hrl hfire hc
        rcases find?_append_cases new hf with hm | hf'
        · exact (hrec cv mI rP rls hm).2.2.1 rl cvj nP nF hrl hfire (hctor_old hc)
        · exact h.recPlain k cv mI rP rls rl cvj nP nF hf' hrl hfire (hctor_old hc)
      ruleCtorHead := by
        intro k cv mI rP rls hf
        have hkn : cv.name = k := Ix.Kernel.Semantics.Env.find?_name hf
        rcases find?_append_cases new hf with hm | hf'
        · exact (hrec cv mI rP rls hm).2.2.2.imp
            (fun hh rl cvj nP nF T us hrl hc hdom => hh rl cvj nP nF T us hrl (hctor_old hc) hdom)
            (fun hnk => hkn ▸ hnk)
        · exact (h.ruleCtorHead k cv mI rP rls hf').imp
            (fun hh rl cvj nP nF T us hrl hc hdom => hh rl cvj nP nF T us hrl (hctor_old hc) hdom)
            id }

/-! ## The twin record's constants -/

/-- **What a twin part gives the companions**: its canonical recursor stored; each rule's
constructor and fire mode the canonical rule's; and the major-premise domains of the twin's
checked type and of the canonical type, with one head, and the same arguments where the
canonical's are bound variables. -/
structure TwinCompanionFacts (env : Ix.Kernel.Env .anon) (w : TwinRecPart .anon) : Prop where
  canonical : env.find? w.kC = some (.recInfo w.cvC w.mI w.rP w.rulesC)
  rules : List.Forall₂ (fun rW' rC : RecRule .anon => rW'.ctor = rC.ctor ∧ rW'.fire = rC.fire)
    w.rulesW' w.rulesC
  major : ∃ DW DC, Core.piDomAt w.mI w.cvW'.type = some DW ∧
    Core.piDomAt w.mI w.cvC.type = some DC ∧ DW.getAppFn = DC.getAppFn ∧
    ((∀ a ∈ DC.getAppArgs, ∃ i, a = .bvar i) → DW.getAppArgs = DC.getAppArgs)

/-- **The companions after a twin record's constants** (module docstring). -/
theorem coreCompanions_twin {c : Core.Ctx} (h : Decl.CoreCompanions c)
    {ws : List (TwinRecPart .anon)}
    (hext : Ix.Kernel.EnvExt c.env ⟨twinRecs ws ++ (twinModels ws ++ c.env.consts)⟩)
    (hpart : ∀ w ∈ ws, TwinCompanionFacts c.env w)
    (hnoK : ∀ w ∈ ws, Core.RecNotKAt c.E w.cvW'.name) :
    Decl.CoreCompanions ⟨c.E, ⟨twinRecs ws ++ (twinModels ws ++ c.env.consts)⟩, c.t, c.lim⟩ := by
  have hmodel : ∀ ci ∈ twinModels ws, ∃ cv v hint, ci = .defnInfo cv v hint := by
    intro ci hm
    obtain ⟨w, -, hmi⟩ := List.mem_filterMap.mp hm
    unfold TwinRecPart.modelInfo? at hmi
    obtain ⟨⟨cvm, mval, hint⟩, -, rfl⟩ := Option.map_eq_some_iff.mp hmi
    exact ⟨_, _, _, rfl⟩
  have hnoctor : ∀ ci ∈ twinRecs ws ++ twinModels ws, ∀ cv nP nF, ci ≠ .ctorInfo cv nP nF := by
    intro ci hci cv nP nF he
    rcases List.mem_append.mp hci with hr | hm
    · obtain ⟨w, -, hw⟩ := List.mem_map.mp hr
      subst hw
      cases he
    · obtain ⟨cv', v, hint, rfl⟩ := hmodel ci hm
      cases he
  have henv : (⟨twinRecs ws ++ (twinModels ws ++ c.env.consts)⟩ : Ix.Kernel.Env .anon) =
      ⟨(twinRecs ws ++ twinModels ws) ++ c.env.consts⟩ := by
    rw [List.append_assoc]
  rw [henv] at hext ⊢
  refine coreCompanions_append h hext hnoctor ?_
  intro cv mI rP rls hm
  obtain ⟨w, hw, hwe⟩ : ∃ w ∈ ws,
      ConstantInfo.recInfo w.cvW' w.mI w.rP w.rulesW' = .recInfo cv mI rP rls := by
    rcases List.mem_append.mp hm with hr | hmo
    · exact List.mem_map.mp hr
    · obtain ⟨cv', v, hint, he⟩ := hmodel _ hmo
      cases he
  injection hwe with e1 e2 e3 e4
  subst e1 e2 e3 e4
  obtain ⟨hcan, hrules, DW, DC, hDW, hDC, hfn, hargs⟩ := hpart w hw
  have hmapctor : w.rulesW'.map (·.ctor) = w.rulesC.map (·.ctor) :=
    lforall₂_map_eq (fun _ _ hr => hr.1) hrules
  have hhead : ∀ e : Core.KExpr, (Core.piDomAt w.mI w.cvW'.type).map (·.getAppFn) = some e →
      (Core.piDomAt w.mI w.cvC.type).map (·.getAppFn) = some e := by
    intro e he
    rw [hDW] at he
    rw [hDC]
    have he' : DW.getAppFn = e := Option.some.inj he
    show some DC.getAppFn = some e
    rw [← hfn, he']
  have hcanR := h.recRulesNodupAndProj w.kC w.cvC w.mI w.rP w.rulesC hcan
  refine ⟨fun p us hne hdom => h.recMajorRecord w.kC w.cvC w.mI w.rP w.rulesC p us hcan
      (lforall₂_ne_nil hrules hne) (hhead _ hdom), ⟨?_, ?_⟩, ?_, Or.inr (hnoK w hw)⟩
  · rw [hmapctor]
    exact hcanR.1
  · intro p cm ip us hdom hcm hip j rl hj
    have hj' : (w.rulesW'.map (·.ctor))[j]? = some rl.ctor := by
      simp [hj]
    rw [hmapctor, List.getElem?_map] at hj'
    obtain ⟨rC, hjC, hcC⟩ := Option.map_eq_some_iff.mp hj'
    rw [← hcC]
    exact hcanR.2 p cm ip us (hhead _ hdom) hcm hip j rC hjC
  · intro rl cvj nP nF hrl hfire hc
    obtain ⟨rC, hrC, hct, hfi⟩ := lforall₂_mem_left hrules hrl
    obtain ⟨D, T, hD, hDT, htake, hdrop⟩ := h.recPlain w.kC w.cvC w.mI w.rP w.rulesC rC cvj nP nF
      hcan hrC (hfi.symm.trans hfire) (by rw [← hct]; exact hc)
    rw [hDC] at hD
    have hDD : DC = D := Option.some.inj hD
    rw [← hDD] at hDT htake hdrop
    have hall : ∀ a ∈ DC.getAppArgs, ∃ i, a = .bvar i := by
      intro a ha
      rw [← List.take_append_drop nP DC.getAppArgs, htake, hdrop] at ha
      rcases List.mem_append.mp ha with h1 | h1
      · obtain ⟨i, -, rfl⟩ := List.mem_map.mp h1
        exact ⟨_, rfl⟩
      · obtain ⟨i, -, rfl⟩ := List.mem_map.mp h1
        exact ⟨_, rfl⟩
    refine ⟨DW, T, hDW, hfn.trans hDT, ?_, ?_⟩
    · rw [hargs hall]
      exact htake
    · rw [hargs hall]
      exact hdrop

end IxVM.Refinement.Typing.TwinFamily
