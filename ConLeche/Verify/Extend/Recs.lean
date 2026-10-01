module

public import ConLeche.Verify.Extend.Ind

public section

/-!
# Recs

The recursor-group install's bookkeeping: the `ProvFacts` /
`SwapShList` / `RulesChain` inductive records of what `provisionRecs`
and the rule fold did, and the `provisionRecs_*` / `checkIndRecs_*`
families reading the resulting environment (names, kinds,
monotonicity, freshness, preservation).

All of it is stated over `Env`/`Expr` alone; the runs that read a
valuation are assembled from these records one tier up
(`ConLeche/Semantics/IndBlockFacts.lean`).
-/

set_option linter.unusedSimpArgs false

namespace ConLeche

variable {mode : CheckMode}

open Expr

/-- The per-item facts of the provisioning phase, chaining the
provisional environments. -/
inductive ProvFacts (F : Nat) (blockNames : List Name) :
    Env → Env →
    List (ConstantVal × Nat × Nat × List RecRule) → Prop
  | nil {env : Env} : ProvFacts F blockNames env env []
  | cons {envAcc envSelf : Env} {cvA : ConstantVal}
      {mI rP : Nat} {rules : List RecRule}
      {rest : List (ConstantVal × Nat × Nat × List RecRule)} :
      envAcc.find? cvA.name = none →
      reservedBasisNames.contains cvA.name = false →
      cvA.name.isProjFnShape = false →
      cvA.name.isModelSuffix = false →
      blockNames.contains cvA.name = true →
      cvA.type.hasFvar = false →
      cvA.type.looseBVarsBounded 0 = true →
      cvA.type.allLevelParamsDefined cvA.levelParams = true →
      cvA.type.constsResolve envAcc = true →
      (∃ cvm mval hmcvm, envAcc.find? (cvA.name.str "_model") =
        some (.defnInfo cvm mval hmcvm) ∧
        cvm.levelParams = cvA.levelParams ∧
        ((cvA.type.renameConsts (fun n =>
          if blockNames.contains n then n.str "_model" else n))
          == cvm.type) = true) →
      ProvFacts F blockNames
        ⟨.recInfo cvA mI rP [] :: envAcc.consts⟩ envSelf rest →
      ProvFacts F blockNames envAcc envSelf
        ((cvA, mI, rP, rules) :: rest)

/-- Lookups below the provisional chain are preserved. -/
theorem ProvFacts.find?_preserved {F : Nat} {blockNames : List Name} :
    ∀ {envAcc envSelf : Env}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      ProvFacts F blockNames envAcc envSelf checked →
      ∀ (n : Name) (ci : ConstantInfo), envAcc.find? n = some ci →
        envSelf.find? n = some ci := by
  intro envAcc envSelf checked h
  induction h with
  | nil => intro n ci h; exact h
  | @cons envAcc envSelf cvA mI rP rules rest hfresh _ _ _ _ _ _ _
      _ _ _ ih =>
    intro n ci hf
    refine ih n ci ?_
    rw [Env.find?_cons_of_isSome hfresh (by rw [hf]; rfl)]
    exact hf

/-- The shape-level swap pair (no obligations). -/
@[expose] def SwapPairSh (c₀ c₃ : ConstantInfo) : Prop :=
  c₀ = c₃ ∨
  ∃ cv mI rP rules,
    c₀ = .recInfo cv mI rP [] ∧ c₃ = .recInfo cv mI rP rules

/-- Pointwise shape-level swap of two constant lists. -/
inductive SwapShList : List ConstantInfo → List ConstantInfo → Prop
  | nil : SwapShList [] []
  | cons {c₀ c₃ : ConstantInfo} {rest₀ rest₃ : List ConstantInfo} :
      SwapPairSh c₀ c₃ → SwapShList rest₀ rest₃ →
      SwapShList (c₀ :: rest₀) (c₃ :: rest₃)

theorem SwapShList.of_eq : ∀ (l : List ConstantInfo), SwapShList l l
  | [] => SwapShList.nil
  | _c :: l => SwapShList.cons (Or.inl rfl) (SwapShList.of_eq l)

theorem SwapPairSh.name_eq {c₀ c₃ : ConstantInfo}
    (h : SwapPairSh c₀ c₃) : c₀.name = c₃.name := by
  rcases h with rfl | ⟨cv, mI, rP, rules, rfl, rfl⟩
  · rfl
  · rfl

/-- The lookup correspondence of a shape-level swap. -/
theorem swapSh_find?_corr :
    ∀ {consts₀ consts₃ : List ConstantInfo},
    SwapShList consts₀ consts₃ →
    ∀ n : Name,
    (Env.mk consts₃).find? n = (Env.mk consts₀).find? n ∨
    ∃ cv mI rP rules,
      (Env.mk consts₀).find? n = some (.recInfo cv mI rP []) ∧
      (Env.mk consts₃).find? n = some (.recInfo cv mI rP rules) ∧
      cv.name = n := by
  intro consts₀ consts₃ hsw
  induction hsw with
  | nil => intro n; exact Or.inl rfl
  | @cons c₀ c₃ rest₀ rest₃ hpair hrest ih =>
    intro n
    by_cases hn : c₃.name = n
    · have hn₀ : c₀.name = n := by rw [SwapPairSh.name_eq hpair, hn]
      have h₃ : (Env.mk (c₃ :: rest₃)).find? n = some c₃ := by
        show (c₃ :: rest₃).find? (·.name == n) = some c₃
        rw [List.find?_cons_of_pos (by simp [hn])]
      have h₀ : (Env.mk (c₀ :: rest₀)).find? n = some c₀ := by
        show (c₀ :: rest₀).find? (·.name == n) = some c₀
        rw [List.find?_cons_of_pos (by simp [hn₀])]
      rcases hpair with rfl | ⟨cv, mI, rP, rules, rfl, rfl⟩
      · exact Or.inl (h₃.trans h₀.symm)
      · exact Or.inr ⟨cv, mI, rP, rules, h₀, h₃,
          (show cv.name = n from hn)⟩
    · have hn₀ : ¬c₀.name = n := by
        rw [SwapPairSh.name_eq hpair]
        exact hn
      have h₃ : (Env.mk (c₃ :: rest₃)).find? n =
          (Env.mk rest₃).find? n := by
        show (c₃ :: rest₃).find? (·.name == n) =
          rest₃.find? (·.name == n)
        rw [List.find?_cons_of_neg (by simp [hn])]
      have h₀ : (Env.mk (c₀ :: rest₀)).find? n =
          (Env.mk rest₀).find? n := by
        show (c₀ :: rest₀).find? (·.name == n) =
          rest₀.find? (·.name == n)
        rw [List.find?_cons_of_neg (by simp [hn₀])]
      rw [h₃, h₀]
      exact ih n

/-- The rule-checking fold's per-item facts, chaining the final
environments; the list pairs each provisioned item with its checked
rule list. -/
inductive RulesChain (mode : CheckMode) (F : Nat)
    (env' envS : Env) (f : Name → Name) :
    Env → Env →
    List ((ConstantVal × Nat × Nat × List RecRule) ×
      List RecRule) → Prop
  | nil {env : Env} : RulesChain mode F env' envS f env env []
  | cons {envAcc env₃ : Env} {cvA : ConstantVal} {mI rP : Nat}
      {rules rules' : List RecRule}
      {rest : List ((ConstantVal × Nat × Nat × List RecRule) × List RecRule)} :
      checkIotaRules mode (fueledOps mode F) env' envS f cvA.name cvA.levelParams
        cvA.type mI rP 0 rules = .ok rules' →
      RulesChain mode F env' envS f
        ⟨.recInfo cvA mI rP rules' :: envAcc.consts⟩ env₃ rest →
      RulesChain mode F env' envS f envAcc env₃
        (((cvA, mI, rP, rules), rules') :: rest)

/-- Invert the rule-checking fold into its chain. -/
theorem rulesFold_inv {F : Nat} {env' envS : Env} {f : Name → Name} :
    ∀ (checked : List (ConstantVal × Nat × Nat × List RecRule)) (envAcc env₃ : Env),
    checked.foldlM (fun (acc : Env) c => do
        let rules' ← checkIotaRules mode (fueledOps mode F) env' envS f c.1.name
          c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
        pure (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.consts⟩ : Env)) envAcc = .ok env₃ →
    ∃ zipped, zipped.map Prod.fst = checked ∧
      RulesChain mode F env' envS f envAcc env₃ zipped
  | [], envAcc, env₃, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨[], rfl, RulesChain.nil⟩
  | c :: rest, envAcc, env₃, h => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    revert h
    cases hcir : checkIotaRules mode (fueledOps mode F) env' envS f c.1.name
        c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2 with
    | error e => intro h; exact nomatch h
    | ok rules' => ?_
    intro h
    try dsimp only at h
    obtain ⟨zipped, hmap, hchain⟩ := rulesFold_inv rest _ env₃ h
    exact ⟨(c, rules') :: zipped, by rw [List.map_cons, hmap], by
      obtain ⟨cvA, mI, rP, rules⟩ := c
      exact RulesChain.cons hcir hchain⟩

/-- The two chains' environments correspond pointwise (shape level). -/
theorem chains_swapSh {F : Nat} {blockNames : List Name}
    {env' envS : Env} {f : Name → Name} :
    ∀ {zipped : List ((ConstantVal × Nat × Nat × List RecRule) × List RecRule)}
      {accS acc₃ envSelf env₃ : Env},
      ProvFacts F blockNames accS envSelf (zipped.map Prod.fst) →
      RulesChain mode F env' envS f acc₃ env₃ zipped →
      SwapShList accS.consts acc₃.consts →
      SwapShList envSelf.consts env₃.consts := by
  intro zipped
  induction zipped with
  | nil =>
    intro accS acc₃ envSelf env₃ hp hr hacc
    cases hp
    cases hr
    exact hacc
  | cons z rest ih =>
    intro accS acc₃ envSelf env₃ hp hr hacc
    obtain ⟨⟨cvA, mI, rP, rules⟩, rules'⟩ := z
    cases hp with
    | cons hfresh hnres hshape hms hbn htyf htyb htlp htres hmodel hp' =>
      cases hr with
      | cons hcir hr' =>
        exact ih hp' hr'
          (SwapShList.cons (Or.inr ⟨cvA, mI, rP, rules', rfl,
            rfl⟩) hacc)

/-- Per-item extraction from the rule chain. -/
theorem RulesChain.mem_facts {F : Nat} {env' envS : Env}
    {f : Name → Name} :
    ∀ {envAcc env₃ : Env}
      {zipped : List ((ConstantVal × Nat × Nat × List RecRule) × List RecRule)},
      RulesChain mode F env' envS f envAcc env₃ zipped →
      ∀ z ∈ zipped,
        checkIotaRules mode (fueledOps mode F) env' envS f z.1.1.name
          z.1.1.levelParams z.1.1.type z.1.2.1 z.1.2.2.1
          0 z.1.2.2.2 = .ok z.2 := by
  intro envAcc env₃ zipped h
  induction h with
  | nil => intro z hz; exact nomatch hz
  | cons hcir hrest ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hcir
    · exact ih z hz

/-- Per-item extraction from the provisioning chain: each item's
recorded facts, its stored provisional recursor, and the embedding of
its own environment into the final provisional one. -/
theorem ProvFacts.mem_facts {F : Nat} {blockNames : List Name} :
    ∀ {envAcc envSelf : Env}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      ProvFacts F blockNames envAcc envSelf checked →
      ∀ c ∈ checked,
        reservedBasisNames.contains c.1.name = false ∧
        c.1.name.isProjFnShape = false ∧
        c.1.name.isModelSuffix = false ∧
        blockNames.contains c.1.name = true ∧
        c.1.type.hasFvar = false ∧
        c.1.type.looseBVarsBounded 0 = true ∧
        c.1.type.allLevelParamsDefined c.1.levelParams = true ∧
        c.1.type.constsResolve envSelf = true ∧
        (∃ cvm mval hmcvm, envSelf.find? (c.1.name.str "_model") =
          some (.defnInfo cvm mval hmcvm) ∧
          cvm.levelParams = c.1.levelParams ∧
          ((c.1.type.renameConsts (fun n =>
            if blockNames.contains n then n.str "_model" else n))
            == cvm.type) = true) ∧
        envSelf.find? c.1.name =
          some (.recInfo c.1 c.2.1 c.2.2.1 []) := by
  intro envAcc envSelf checked h
  induction h with
  | nil => intro c hc; exact nomatch hc
  | @cons envAcc envSelf cvA mI rP rules rest hfresh hnres hshape
      hms hbnc htyf htyb htlp htres hmodel hrest ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · have hupN : ∀ (n : Name) (ci : ConstantInfo),
          (⟨.recInfo cvA mI rP [] ::
            envAcc.consts⟩ : Env).find? n = some ci →
          envSelf.find? n = some ci :=
        ProvFacts.find?_preserved hrest
      have hself : envSelf.find? cvA.name =
          some (.recInfo cvA mI rP []) := by
        refine hupN cvA.name _ ?_
        rw [Env.find?_cons,
          if_pos (show (ConstantInfo.recInfo cvA mI rP
            []).name = cvA.name from rfl)]
      obtain ⟨cvm, mval, hmcvm, hfm, hlps, hren⟩ := hmodel
      refine ⟨hnres, hshape, hms, hbnc, htyf, htyb, htlp, ?_, ?_, hself⟩
      · refine Expr.constsResolve_le ?_ htres
        intro n hn
        cases hf : envAcc.find? n with
        | none => rw [hf] at hn; exact nomatch hn
        | some ci =>
          have h1 : (⟨.recInfo cvA mI rP [] ::
              envAcc.consts⟩ : Env).find? n = some ci := by
            rw [Env.find?_cons_of_isSome hfresh (by rw [hf]; rfl)]
            exact hf
          rw [hupN n ci h1]
          rfl
      · refine ⟨cvm, mval, hmcvm, ?_, hlps, hren⟩
        refine hupN _ _ ?_
        rw [Env.find?_cons_of_isSome hfresh (by rw [hfm]; rfl)]
        exact hfm
    · exact ih c hc

/-- Every input recursor is represented in the provisioned list. -/
theorem provisionRecs_names {F : Nat} {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) (envAcc : Env)
      (p : Env × List (ConstantVal × Nat × Nat × List RecRule)),
    provisionRecs (fueledOps mode F) blockNames envAcc recs = .ok p →
    ∀ ci ∈ recs, ∃ c ∈ p.2, c.1.name = ci.name
  | [], envAcc, p, h, ci, hci => nomatch hci
  | ci₀ :: rest, envAcc, p, h, ci, hci => by
    obtain ⟨cv, mI, rP, rules, cvA, p', rfl, hcmv, hrec, rfl⟩ :=
      provisionRecs_cons_inv h
    obtain ⟨hccv, -, -, -, -, -, -⟩ := checkMemberVal_inv hcmv
    obtain ⟨-, -, -, -, -, -, tyA, stype, u, -, -, -, -, -, hcvA⟩ :=
      checkConstantVal_inv hccv
    rcases List.mem_cons.mp hci with rfl | hci
    · refine ⟨(cvA, mI, rP, rules), List.mem_cons_self, ?_⟩
      rw [hcvA]
      rfl
    · obtain ⟨c, hc, hcn⟩ := provisionRecs_names rest _ p' hrec ci hci
      exact ⟨c, List.mem_cons_of_mem _ hc, hcn⟩

/-- Provisioning only extends the environment. -/
theorem provisionRecs_mono {F : Nat} {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) (envAcc : Env)
      (p : Env × List (ConstantVal × Nat × Nat × List RecRule)),
    provisionRecs (fueledOps mode F) blockNames envAcc recs = .ok p →
    ∀ n, (envAcc.find? n).isSome = true → (p.1.find? n).isSome = true
  | [], envAcc, p, h, n, hn => by
    simp only [provisionRecs, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact hn
  | ci :: rest, envAcc, p, h, n, hn => by
    obtain ⟨cv, mI, rP, rules, cvA, p', rfl, hcmv, hrec, rfl⟩ :=
      provisionRecs_cons_inv h
    refine provisionRecs_mono rest _ p' hrec n ?_
    rw [Env.find?_cons]
    by_cases hh : (ConstantInfo.recInfo cvA mI rP []).name = n
    · rw [if_pos hh]
      rfl
    · rw [if_neg hh]
      exact hn

/-- Every input recursor was fresh at the base of the provisioning
chain. -/
theorem provisionRecs_fresh {F : Nat} {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) (envAcc : Env)
      (p : Env × List (ConstantVal × Nat × Nat × List RecRule)),
    provisionRecs (fueledOps mode F) blockNames envAcc recs = .ok p →
    ∀ ci ∈ recs, envAcc.find? ci.name = none
  | [], _, _, _, ci, hci => nomatch hci
  | ci₀ :: rest, envAcc, p, h, ci, hci => by
    obtain ⟨cv, mI, rP, rules, cvA, p', rfl, hcmv, hrec, rfl⟩ :=
      provisionRecs_cons_inv h
    obtain ⟨hccv, -, -, -, -, -, -⟩ := checkMemberVal_inv hcmv
    obtain ⟨hfind0, -, -, -, -, -, tyA, stype, u, -, -, -, -, -, -⟩ :=
      checkConstantVal_inv hccv
    rcases List.mem_cons.mp hci with rfl | hci
    · exact hfind0
    · have h1 := provisionRecs_fresh rest _ p' hrec ci hci
      rw [Env.find?_cons] at h1
      split at h1
      · exact nomatch h1
      · exact h1

/-- Provisioned recursors never carry a model-shaped name
(`checkMemberVal` rejects them). -/
theorem provisionRecs_modelfree {F : Nat} {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) (envAcc : Env)
      (p : Env × List (ConstantVal × Nat × Nat × List RecRule)),
    provisionRecs (fueledOps mode F) blockNames envAcc recs = .ok p →
    ∀ ci ∈ recs, ci.name.isModelSuffix = false
  | [], _, _, _, ci, hci => nomatch hci
  | ci₀ :: rest, envAcc, p, h, ci, hci => by
    obtain ⟨cv, mI, rP, rules, cvA, p', rfl, hcmv, hrec, rfl⟩ :=
      provisionRecs_cons_inv h
    rcases List.mem_cons.mp hci with rfl | hci
    · obtain ⟨hccv, hms, -⟩ := checkMemberVal_inv hcmv
      obtain ⟨-, -, -, -, -, -, tyA, stype, u, -, -, -, -, -, hcvA⟩ :=
        checkConstantVal_inv hccv
      rw [hcvA] at hms
      exact hms
    · exact provisionRecs_modelfree rest _ p' hrec ci hci


/-- The provisioning chain's facts, model-free (for the run-level
`EnvWF` threading). -/
theorem provisionRecs_facts {F : Nat} {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) (envAcc : Env)
      (p : Env × List (ConstantVal × Nat × Nat × List RecRule)),
    provisionRecs (fueledOps mode F) blockNames envAcc recs = .ok p →
    (∀ ci ∈ recs, blockNames.contains ci.name = true) →
    ProvFacts F blockNames envAcc p.1 p.2
  | [], envAcc, p, h, _ => by
    simp only [provisionRecs, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ProvFacts.nil
  | ci :: rest, envAcc, p, h, hbn => by
    obtain ⟨cv, mI, rP, rules, cvA, p', rfl, hcmv, hrec, rfl⟩ :=
      provisionRecs_cons_inv h
    obtain ⟨hccv, hms, cvm, mval, hmcvm, hfm, hlps, hrenf⟩ :=
      checkMemberVal_inv hcmv
    obtain ⟨hfind0raw, hnres0raw, hpshape0raw, hnd, hlb, hfv, tyA, stype,
      u, hann, hlp, hres, hst, hsort, hcvA⟩ := checkConstantVal_inv hccv
    have hnameA : cvA.name = cv.name := by rw [hcvA]; rfl
    have hfind0 : envAcc.find? cvA.name = none := by
      rw [hnameA]
      exact hfind0raw
    have hnres0 : reservedBasisNames.contains cvA.name = false := by
      rw [hnameA]
      exact hnres0raw
    have hpshape0 : cvA.name.isProjFnShape = false := by
      rw [hnameA]
      exact hpshape0raw
    have hbnA : blockNames.contains cvA.name = true := by
      rw [hnameA]
      exact hbn (ConstantInfo.recInfo cv mI rP rules)
        List.mem_cons_self
    have htyf : cvA.type.hasFvar = false := by
      rw [hcvA]
      exact not_hasFvar_of_fvarsBelow_zero
        ((annotateCore_WScoped F _ hann
          (WScoped.of_not_hasFvar hfv)).fvarsBelow)
    have htyb : cvA.type.looseBVarsBounded 0 = true := by
      rw [hcvA]
      exact annotateCore_looseBVars F _ hann hlb
    have htlp : cvA.type.allLevelParamsDefined cvA.levelParams =
        true := by
      rw [hcvA]
      exact hlp
    have htres : cvA.type.constsResolve envAcc = true := by
      rw [hcvA]
      exact hres
    exact ProvFacts.cons hfind0 hnres0 hpshape0 hms hbnA htyf htyb htlp
      htres ⟨cvm, mval, hmcvm, hfm, hlps, hrenf⟩
      (provisionRecs_facts rest _ p' hrec
        (fun cj hcj => hbn cj (List.mem_cons_of_mem _ hcj)))

/-- Every member of the swapped list corresponds to a member of the
original. -/
theorem swapSh_mem_corr :
    ∀ {consts₀ consts₃ : List ConstantInfo},
      SwapShList consts₀ consts₃ →
      ∀ c₃ ∈ consts₃, ∃ c₀ ∈ consts₀, SwapPairSh c₀ c₃ := by
  intro consts₀ consts₃ hsw
  induction hsw with
  | nil => intro c₃ hc; exact nomatch hc
  | cons hpair hrest ih =>
    intro c₃ hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨_, List.mem_cons_self, hpair⟩
    · obtain ⟨c₀, hc₀, hp⟩ := ih c₃ hc
      exact ⟨c₀, List.mem_cons_of_mem _ hc₀, hp⟩

/-- Membership in the rule-checking fold's final environment: either
an accumulator constant or an installed recursor of the chain. -/
theorem rulesChain_mem {F : Nat} {env' envS : Env} {f : Name → Name} :
    ∀ {envAcc env₃ : Env}
      {zipped : List ((ConstantVal × Nat × Nat × List RecRule) × List RecRule)},
      RulesChain mode F env' envS f envAcc env₃ zipped →
      ∀ c ∈ env₃.consts, c ∈ envAcc.consts ∨
        ∃ z ∈ zipped, c = .recInfo z.1.1 z.1.2.1 z.1.2.2.1 z.2 := by
  intro envAcc env₃ zipped h
  induction h with
  | nil => intro c hc; exact Or.inl hc
  | @cons envAcc env₃ cvA mI rP rules rules' rest hcir hrest ih =>
    intro c hc
    rcases ih c hc with hc' | ⟨z, hz, rfl⟩
    · rcases List.mem_cons.mp hc' with rfl | hc''
      · exact Or.inr ⟨((cvA, mI, rP, rules), rules'),
          List.mem_cons_self, rfl⟩
      · exact Or.inl hc''
    · exact Or.inr ⟨z, List.mem_cons_of_mem _ hz, rfl⟩


/-- Provisioned recursors never carry a projection-function-shaped
name (`checkConstantVal` rejects the shape). -/
theorem provisionRecs_projshape {F : Nat} {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) (envAcc : Env)
      (p : Env × List (ConstantVal × Nat × Nat × List RecRule)),
    provisionRecs (fueledOps mode F) blockNames envAcc recs = .ok p →
    ∀ ci ∈ recs, ci.name.isProjFnShape = false
  | [], _, _, _, ci, hci => nomatch hci
  | ci₀ :: rest, envAcc, p, h, ci, hci => by
    obtain ⟨cv, mI, rP, rules, cvA, p', rfl, hcmv, hrec, rfl⟩ :=
      provisionRecs_cons_inv h
    rcases List.mem_cons.mp hci with rfl | hci
    · obtain ⟨hccv, hms, -⟩ := checkMemberVal_inv hcmv
      obtain ⟨-, -, hpshape0, -, -, -, tyA, stype, u, -, -, -, -, -,
        hcvA⟩ := checkConstantVal_inv hccv
      exact hpshape0
    · exact provisionRecs_projshape rest _ p' hrec ci hci

/-- Provisioning adds only recursor-kind constants. -/
theorem provisionRecs_find_new {F : Nat} {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) (envAcc : Env)
      (p : Env × List (ConstantVal × Nat × Nat × List RecRule)),
    provisionRecs (fueledOps mode F) blockNames envAcc recs = .ok p →
    ∀ (n : Name) (ci : ConstantInfo), p.1.find? n = some ci →
    envAcc.find? n = some ci ∨
      ∃ cv mI rP rules, ci = .recInfo cv mI rP rules
  | [], envAcc, p, h, n, ci, hf => by
    simp only [provisionRecs, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact Or.inl hf
  | ci₀ :: rest, envAcc, p, h, n, ci, hf => by
    obtain ⟨cv, mI, rP, rules, cvA, p', rfl, hcmv, hrec, rfl⟩ :=
      provisionRecs_cons_inv h
    rcases provisionRecs_find_new rest _ p' hrec n ci hf with hf' | hk
    · rw [Env.find?_cons] at hf'
      split at hf'
      · exact Or.inr ⟨cvA, mI, rP, [], Option.some.inj hf'.symm ▸ rfl⟩
      · exact Or.inl hf'
    · exact Or.inr hk


/-- Provisioning preserves stored lookups exactly (every cons is
fresh). -/
theorem provisionRecs_find_preserved {F : Nat} {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) (envAcc : Env)
      (p : Env × List (ConstantVal × Nat × Nat × List RecRule)),
    provisionRecs (fueledOps mode F) blockNames envAcc recs = .ok p →
    ∀ (n : Name) (ci : ConstantInfo), envAcc.find? n = some ci →
    p.1.find? n = some ci
  | [], envAcc, p, h, n, ci, hf => by
    simp only [provisionRecs, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact hf
  | ci₀ :: rest, envAcc, p, h, n, ci, hf => by
    obtain ⟨cv, mI, rP, rules, cvA, p', rfl, hcmv, hrec, rfl⟩ :=
      provisionRecs_cons_inv h
    obtain ⟨hccv, -⟩ := checkMemberVal_inv hcmv
    obtain ⟨hfind0, -, -, -, -, -, tyA, stype, u, -, -, -, -, -,
      hcvA⟩ := checkConstantVal_inv hccv
    have hfindA : envAcc.find?
        (ConstantInfo.recInfo cvA mI rP []).name = none := by
      show envAcc.find? cvA.name = none
      rw [show cvA.name = cv.name from by rw [hcvA]; rfl]
      exact hfind0
    refine provisionRecs_find_preserved rest _ p' hrec n ci ?_
    rw [Env.find?_cons_of_isSome hfindA (by rw [hf]; rfl)]
    exact hf

/-! ## The congruences a shape-level swap induces

Everything `denote` and the environment guards read is invariant under
replacing a rule-less recursor's rule list, because they read the
environment only through `find?`-`toConstantVal`.  Bundled here (task
#148, T5 stage 3) so both lanes' swap transports consume one object;
the TT lane's `EnvTT.swap` still carries an inline copy of these
`have`s, which this supersedes for any future consumer. -/

/-- The environment congruences of a shape-level rule-list swap. -/
structure SwapCongr (env₀ env₃ : Env) : Prop where
  /-- Stored level parameters are unchanged. -/
  levelsEq : ∀ n, (env₀.find? n).map (fun ci => ci.toConstantVal.levelParams)
    = (env₃.find? n).map (fun ci => ci.toConstantVal.levelParams)
  /-- The set of stored names is unchanged. -/
  isSomeEq : ∀ n, (env₀.find? n).isSome = (env₃.find? n).isSome
  /-- The two literal guards are unchanged. -/
  natEq : natLitSupported env₀ = natLitSupported env₃
  strEq : strLitSupported env₀ = strLitSupported env₃
  /-- The `Nat`-operation guards are unchanged. -/
  guardEq : ∀ c, natOpGuard env₀ c = natOpGuard env₃ c
  /-- A non-recursor lookup transports down. -/
  findDown : ∀ (n : Name) (ci : ConstantInfo), env₃.find? n = some ci →
    (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
    env₀.find? n = some ci
  /-- …and up. -/
  findUp : ∀ (n : Name) (ci : ConstantInfo), env₀.find? n = some ci →
    (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
    env₃.find? n = some ci

/-- Projection-table lookups transport across the swap: a `projInfo`
is never a recursor, so `findDown`/`findUp` move it both ways (task
#175 wiring W3 — `denote`'s `.proj` clause now reads the entry
kind). -/
theorem SwapCongr.projEq {env₀ env₃ : Env} (hcg : SwapCongr env₀ env₃) :
    ∀ (sn : Name) (i : Nat), env₀.findProj? sn i = env₃.findProj? sn i := by
  intro sn i
  unfold Env.findProj?
  cases h0 : env₀.find? (projTableName sn) with
  | none =>
    cases h3 : env₃.find? (projTableName sn) with
    | none => rfl
    | some ci =>
      have := hcg.isSomeEq (projTableName sn)
      rw [h0, h3] at this
      exact nomatch this
  | some ci =>
    cases ci with
    | projInfo e =>
      rw [hcg.findUp _ _ h0 (fun _ _ _ _ h => nomatch h)]
    | recInfo cv mI rP rules =>
      cases h3 : env₃.find? (projTableName sn) with
      | none => rfl
      | some ci₃ =>
        cases ci₃ with
        | projInfo e₃ =>
          have := hcg.findDown _ _ h3 (fun _ _ _ _ h => nomatch h)
          rw [h0] at this
          exact nomatch this
        | axiomInfo cv₃ => rfl
        | defnInfo cv₃ v₃ h₃ => rfl
        | thmInfo cv₃ v₃ => rfl
        | indInfo cv₃ caps₃ => rfl
        | ctorInfo cv₃ np₃ nf₃ => rfl
        | recInfo cv₃ mI₃ rP₃ rules₃ => rfl
    | axiomInfo cv =>
      rw [hcg.findUp _ _ h0 (fun _ _ _ _ h => nomatch h)]
    | defnInfo cv v hint =>
      rw [hcg.findUp _ _ h0 (fun _ _ _ _ h => nomatch h)]
    | thmInfo cv v =>
      rw [hcg.findUp _ _ h0 (fun _ _ _ _ h => nomatch h)]
    | indInfo cv caps =>
      rw [hcg.findUp _ _ h0 (fun _ _ _ _ h => nomatch h)]
    | ctorInfo cv np nf =>
      rw [hcg.findUp _ _ h0 (fun _ _ _ _ h => nomatch h)]

/-- A shape-level swap induces the congruences. -/
theorem SwapShList.congr {consts₀ consts₃ : List ConstantInfo}
    (hsw : SwapShList consts₀ consts₃) :
    SwapCongr (Env.mk consts₀) (Env.mk consts₃) := by
  have hcorr := swapSh_find?_corr hsw
  have hchk : ∀ (chk : Option ConstantInfo → Bool),
      (∀ cv mI rP rules rules',
        chk (some (.recInfo cv mI rP rules)) =
        chk (some (.recInfo cv mI rP rules'))) →
      ∀ n, chk ((Env.mk consts₀).find? n) = chk ((Env.mk consts₃).find? n) := by
    intro chk hins n
    rcases hcorr n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
    · rw [heq]
    · rw [h₀, h₃]
      exact hins cv mI rP [] rules
  have hnat : natLitSupported (Env.mk consts₀)
      = natLitSupported (Env.mk consts₃) := by
    unfold natLitSupported
    rw [hchk natIndOk (fun _ _ _ _ _ => rfl) natName,
      hchk natZeroOk (fun _ _ _ _ _ => rfl) natZeroName,
      hchk natSuccOk (fun _ _ _ _ _ => rfl) natSuccName]
  refine ⟨?_, ?_, hnat, ?_, ?_, ?_, ?_⟩
  · intro n
    rcases hcorr n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
    · rw [heq]
    · rw [h₀, h₃]; rfl
  · intro n
    rcases hcorr n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
    · rw [heq]
    · rw [h₀, h₃]; rfl
  · unfold strLitSupported
    rw [hnat,
      hchk stringTyOk (fun _ _ _ _ _ => rfl) stringName,
      hchk stringOfListTyOk (fun _ _ _ _ _ => rfl) stringOfListName,
      hchk listTyOk (fun _ _ _ _ _ => rfl) listName,
      hchk listNilTyOk (fun _ _ _ _ _ => rfl) listNilName,
      hchk listConsTyOk (fun _ _ _ _ _ => rfl) listConsName,
      hchk charTyOk (fun _ _ _ _ _ => rfl) charName,
      hchk charOfNatTyOk (fun _ _ _ _ _ => rfl) charOfNatName]
  · intro c
    unfold natOpGuard
    rw [hnat]
    congr 1
    · congr 1
      refine congrArg (List.all (natOpDeps c)) (funext fun n => ?_)
      rcases hcorr n with heq | ⟨cv2, a, b, c2, h₀, h₃, -⟩
      · rw [heq]
      · rw [h₀, h₃]
    · split
      · congr 1
        · rcases hcorr boolTrueName with heq | ⟨cv2, a, b, c2, h₀, h₃, -⟩
          · rw [heq]
          · rw [h₀, h₃]; rfl
        · rcases hcorr boolFalseName with heq | ⟨cv2, a, b, c2, h₀, h₃, -⟩
          · rw [heq]
          · rw [h₀, h₃]; rfl
      · rfl
  · intro n ci hf hnr
    rcases hcorr n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
    · rw [← heq]; exact hf
    · rw [h₃] at hf
      obtain rfl := Option.some.inj hf
      exact absurd rfl (hnr cv mI rP rules)
  · intro n ci hf hnr
    rcases hcorr n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
    · rw [heq]; exact hf
    · rw [h₀] at hf
      obtain rfl := Option.some.inj hf
      exact absurd rfl (hnr cv mI rP [])

/-- **Every recursor of the group is fresh at the phase's own input.**
The checker-side twin of `indRecsR_fresh`, which the *bridge* needs
(the install derives its base invariant from the relation; the bridge
has to derive it from the checker — task #148 T6). -/
theorem checkIndRecs_fresh {F : Nat} {blockNames : List Name}
    {env₂ env₃ : Env} {recs : List ConstantInfo}
    (h : checkIndRecs mode (fueledOps mode F) blockNames env₂ recs
      = .ok env₃) :
    ∀ ci ∈ recs, env₂.find? ci.name = none := by
  simp only [checkIndRecs] at h
  by_cases hemp : recs.isEmpty = true
  · intro ci hci
    rw [List.isEmpty_iff.mp hemp] at hci
    exact nomatch hci
  rw [if_neg hemp] at h
  simp only [Bind.bind, Except.bind] at h
  revert h
  by_cases heqf : env₂.find? eqName = some eqA
  case neg =>
    rw [if_neg heqf]
    intro h
    exact nomatch h
  rw [if_pos heqf]
  intro h
  revert h
  cases hp : provisionRecs (fueledOps mode F) blockNames env₂ recs with
  | error e => intro h; exact nomatch h
  | ok p => intro _; exact provisionRecs_fresh recs env₂ p hp

end ConLeche
