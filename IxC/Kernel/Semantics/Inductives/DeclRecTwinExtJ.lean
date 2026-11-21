module

public import IxC.Kernel.Semantics.Inductives.DeclRecTwinJ
public import IxC.Kernel.Semantics.DeclExt

@[expose] public section

/-! # Extension and eta closure for checked recursor twins -/

namespace Ix.Kernel.Semantics

open Ix.Kernel (Env Expr Key ConstantVal ConstantInfo IndCaps EnvExt EtaFamiliesClosed projTableName)

/-- A fresh cons over an extension of `env` is an extension of `env` when it is not
the table of a structure stored in `env`. -/
theorem EnvExt.cons_over {env X : Env md} {c : ConstantInfo md} (hX : EnvExt env X)
    (hfresh : X.find? c.name = none)
    (hnt : ∀ {T : Key md} {cv : ConstantVal md} {caps : IndCaps md},
      env.find? T = some (.indInfo cv caps) → c.name ≠ projTableName T) :
    EnvExt env ⟨c :: X.consts⟩ where
  find := fun {k} {c'} h => by
    have h' := hX.find h
    have hne : c.name ≠ k := fun e => by
      rw [e, h'] at hfresh
      exact nomatch hfresh
    rw [EnvExt.find?_cons_ne hne]
    exact h'
  tables := fun hT => by
    rw [EnvExt.find?_cons_ne (hnt hT)]
    exact hX.tables hT

/-- A name that passes the front door's shape test is no projection table. -/
theorem ne_projTableName_of_shape {n : Key md} (h : n.isProjFnShape = false) (T : Key md) :
    n ≠ projTableName T := by
  intro e
  rw [e, projTableName_isProjFnShape] at h
  exact nomatch h

/-! ## The twin recursor route -/

theorem find?_append_of_not_mem {env : Env md} {k : Key md} :
    ∀ {cs : List (ConstantInfo md)}, k ∉ cs.map (·.name) →
      (⟨cs ++ env.consts⟩ : Env md).find? k = env.find? k
  | [], _ => rfl
  | c :: cs, hnm => by
    simp only [List.map_cons, List.mem_cons, not_or] at hnm
    show Env.find? ⟨c :: (cs ++ env.consts)⟩ k = env.find? k
    rw [Ix.Kernel.Env.find?_cons, if_neg (Ne.symm hnm.1)]
    exact find?_append_of_not_mem hnm.2

theorem find?_append_none_of_not_mem {env : Env md} {k : Key md} :
    ∀ {cs : List (ConstantInfo md)}, k ∉ cs.map (·.name) → env.find? k = none →
      (⟨cs ++ env.consts⟩ : Env md).find? k = none
  | [], _, hf => hf
  | c :: cs, hnm, hf => by
    simp only [List.map_cons, List.mem_cons, not_or] at hnm
    show (c :: (cs ++ env.consts)).find? (·.name == k) = none
    rw [List.find?_cons_of_neg (by simp [Ne.symm hnm.1])]
    exact find?_append_none_of_not_mem hnm.2 hf

theorem find?_mem_of_nodup {rest : List (ConstantInfo md)} :
    ∀ {cs : List (ConstantInfo md)} {x : ConstantInfo md},
      (cs.map (·.name)).Nodup → x ∈ cs →
      (⟨cs ++ rest⟩ : Env md).find? x.name = some x
  | [], _, _, hx => nomatch hx
  | c :: cs, x, hnd, hx => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hx with heq | hx
    · subst heq
      exact Ix.Kernel.Env.find?_cons_self x ⟨cs ++ rest⟩
    · have hne : c.name ≠ x.name := fun heq => hnd.1 (heq ▸ List.mem_map.mpr ⟨x, hx, rfl⟩)
      show Env.find? ⟨c :: (cs ++ rest)⟩ x.name = some x
      rw [Ix.Kernel.Env.find?_cons, if_neg hne]
      exact find?_mem_of_nodup hnd.2 hx

theorem find?_append_inv {env : Env md} {n : Key md} {x : ConstantInfo md} :
    ∀ {cs : List (ConstantInfo md)},
      (⟨cs ++ env.consts⟩ : Env md).find? n = some x →
      env.find? n = some x ∨ (x ∈ cs ∧ x.name = n)
  | [], hf => Or.inl hf
  | c :: cs, hf => by
    change Env.find? ⟨c :: (cs ++ env.consts)⟩ n = some x at hf
    rw [Ix.Kernel.Env.find?_cons] at hf
    split at hf
    · next heq =>
      obtain rfl := Option.some.inj hf
      exact Or.inr ⟨List.mem_cons_self, heq⟩
    · rcases find?_append_inv hf with hold | ⟨hmem, hn⟩
      · exact Or.inl hold
      · exact Or.inr ⟨List.mem_cons_of_mem c hmem, hn⟩

/-- **Unpacking a new recursor stored by the twin recursor route.** -/
theorem declRecTwinRunJ_newRec {J : Judgements md} {env env₂ : Env md}
    {block : List (ConstantInfo md)} (h : DeclRecTwinRunJ J env block env₂)
    {n : Key md} {cv : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)}
    (hf : env₂.find? n = some (.recInfo cv mI rP rules)) (hn : env.find? n = none) :
    ∃ (ws : List (TwinRecPart md)) (f : Key md → Key md) (w : TwinRecPart md),
      w ∈ ws ∧ n = w.cvW.name ∧ cv = w.cvW' ∧ mI = w.mI ∧ rP = w.rP ∧ rules = w.rulesW' ∧
      ConstantValCheckJ J env w.cvW w.cvW' ∧
      env.find? w.kC = some (.recInfo w.cvC w.mI w.rP w.rulesC) ∧
      w.cvW.levelParams = w.cvC.levelParams ∧
      (∀ cvm mval hint, w.model? = some (cvm, mval, hint) →
        env₂.find? (Ix.Kernel.auxKey n .model) = some
          (.defnInfo ⟨Ix.Kernel.auxKey n .model, cvm.levelParams, cvm.type⟩ mval hint)) ∧
      (w.model? = none →
        (∀ cvm mval hint,
          env.find? (Ix.Kernel.auxKey w.kC .model) ≠ some (.defnInfo cvm mval hint)) ∧
        (∀ bsW domW bodyW bmW,
          w.cvW'.type.stripPis w.mI = some (bsW, .forallE domW bodyW bmW) →
          ∃ bsC domC bodyC bmC,
            w.cvC.type.stripPis w.mI = some (bsC, .forallE domC bodyC bmC) ∧
            domW.getAppFn = domC.getAppFn ∧
            domW.getAppArgs = domC.getAppArgs)) ∧
      w.rulesW.length = w.rulesW'.length ∧
      Forall₂ (fun (p : RecRule md × RecRule md) rC =>
        TwinRuleJ J env ⟨twinProv ws ++ (twinModels ws ++ env.consts)⟩
          f w.cvW.name w.cvC.levelParams w.cvW' w.mI w.rP p.1 p.2 rC)
        (w.rulesW.zip w.rulesW') w.rulesC := by
  obtain ⟨ws, f, -, -, rfl, hnd, -, -, hall⟩ := h
  have hf' : (⟨(twinRecs ws ++ twinModels ws) ++ env.consts⟩ : Env md).find? n
      = some (.recInfo cv mI rP rules) := by
    simpa [List.append_assoc] using hf
  rcases find?_append_inv hf' with hold | ⟨hmem, hname⟩
  · rw [hold] at hn
    exact nomatch hn
  · rcases List.mem_append.mp hmem with hrec | hmod
    · obtain ⟨w, hw, heq⟩ := List.mem_map.mp hrec
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ConstantInfo.recInfo.inj heq.symm
      obtain ⟨hcv, -, hfkC, hlps, hmodSpec, -, hlenW, hrules⟩ := hall w hw
      have hn' : n = w.cvW.name := by
        have h1 : w.cvW'.name = n := hname
        rw [hcv.name_eq] at h1
        exact h1.symm
      refine ⟨ws, f, w, hw, hn', rfl, rfl, rfl, rfl, hcv, hfkC, hlps, ?_, ?_, hlenW, hrules⟩
      · intro cvm mval hint hm
        subst hn'
        have hmemM : ConstantInfo.defnInfo
            ⟨Ix.Kernel.auxKey w.cvW.name .model, cvm.levelParams, cvm.type⟩ mval hint
            ∈ twinRecs ws ++ twinModels ws :=
          List.mem_append_right _
            (List.mem_filterMap.mpr ⟨w, hw, by simp [TwinRecPart.modelInfo?, hm]⟩)
        have hfindM := find?_mem_of_nodup (rest := env.consts) hnd hmemM
        simpa [List.append_assoc, ConstantInfo.name, ConstantInfo.toConstantVal] using hfindM
      · intro hnone
        rw [hnone] at hmodSpec
        exact hmodSpec
    · obtain ⟨w, -, hw⟩ := List.mem_filterMap.mp hmod
      unfold TwinRecPart.modelInfo? at hw
      obtain ⟨⟨_, _, _⟩, -, hcon⟩ := Option.map_eq_some_iff.mp hw
      exact nomatch hcon

theorem etaClosed_append_nonind {env : Env md} (hE : EtaFamiliesClosed env) :
    ∀ {cs : List (ConstantInfo md)},
      (cs.map (·.name)).Nodup →
      (∀ c ∈ cs, env.find? c.name = none) →
      (∀ c ∈ cs, ∀ cv caps, c ≠ .indInfo cv caps) →
      EtaFamiliesClosed ⟨cs ++ env.consts⟩
  | [], _, _, _ => hE
  | c :: cs, hnd, hfr, hni => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hE' := etaClosed_append_nonind hE hnd.2
      (fun x hx => hfr x (List.mem_cons_of_mem c hx))
      (fun x hx => hni x (List.mem_cons_of_mem c hx))
    exact EtaFamiliesClosed.cons_nonind hE'
      (find?_append_none_of_not_mem hnd.1 (hfr c List.mem_cons_self))
      (fun cv caps heq _ => absurd heq (hni c List.mem_cons_self cv caps))

theorem envExt_append_shape {env : Env md} :
    ∀ {cs : List (ConstantInfo md)},
      (cs.map (·.name)).Nodup →
      (∀ c ∈ cs, env.find? c.name = none) →
      (∀ c ∈ cs, c.name.isProjFnShape = false) →
      EnvExt env ⟨cs ++ env.consts⟩
  | [], _, _, _ => EnvExt.refl env
  | c :: cs, hnd, hfr, hsh => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hX := envExt_append_shape hnd.2
      (fun x hx => hfr x (List.mem_cons_of_mem c hx))
      (fun x hx => hsh x (List.mem_cons_of_mem c hx))
    refine EnvExt.cons_over hX
      (find?_append_none_of_not_mem hnd.1 (hfr c List.mem_cons_self)) ?_
    intro T _ _ _
    exact ne_projTableName_of_shape (hsh c List.mem_cons_self) T

/-- **The twin recursor route keeps the η-families closed**, over a package. -/
theorem declRecTwinRunJ_etaClosed {J : Judgements md} {env env₂ : Env md}
    {block : List (ConstantInfo md)} (hE : EtaFamiliesClosed env)
    (h : DeclRecTwinRunJ J env block env₂) : EtaFamiliesClosed env₂ := by
  obtain ⟨ws, f, -, -, rfl, hnd, hfr, -, -⟩ := h
  rw [← List.append_assoc]
  refine etaClosed_append_nonind hE hnd hfr ?_
  intro c hc cv caps heq
  rcases List.mem_append.mp hc with hrec | hmod
  · obtain ⟨w, -, hw⟩ := List.mem_map.mp hrec
    rw [← hw] at heq
    exact nomatch heq
  · obtain ⟨w, -, hw⟩ := List.mem_filterMap.mp hmod
    unfold TwinRecPart.modelInfo? at hw
    obtain ⟨⟨cvm, mval, hint⟩, -, rfl⟩ := Option.map_eq_some_iff.mp hw
    exact nomatch heq

/-- **The twin recursor route extends the environment**, over a package. -/
theorem declRecTwinRunJ_envExt {J : Judgements md} {env env₂ : Env md}
    {block : List (ConstantInfo md)} (h : DeclRecTwinRunJ J env block env₂) :
    EnvExt env env₂ := by
  obtain ⟨ws, f, -, -, rfl, hnd, hfr, -, hall⟩ := h
  rw [← List.append_assoc]
  refine envExt_append_shape hnd hfr ?_
  intro c hc
  rcases List.mem_append.mp hc with hrec | hmod
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hrec
    have hcv := (hall w hw).1
    show w.cvW'.name.isProjFnShape = false
    rw [hcv.name_eq]
    exact hcv.shape
  · obtain ⟨w, -, hw⟩ := List.mem_filterMap.mp hmod
    unfold TwinRecPart.modelInfo? at hw
    obtain ⟨⟨cvm, mval, hint⟩, -, rfl⟩ := Option.map_eq_some_iff.mp hw
    rfl

end Ix.Kernel.Semantics
