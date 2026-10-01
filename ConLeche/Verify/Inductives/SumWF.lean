module

import ConLeche.Verify.Inductives.StructWF
public import ConLeche.Verify.Inductives.SumInv

public section

/-!
# The direct sum install: environment well-formedness (task #175
sum-types, indexed)

`EnvWF` for the environments `checkSum` walks through, read off
the stages' own guards (as `StructWF.lean` for the structure route):
the former's cons, the constructors' conses (`consSumCtors`, each a
checked constant), the recursor's cons with its rules (each rule's
right-hand side scoped by `checkSumRules`, never `.nested`).
Task #175 indexed: the recursor's cons is generic over its major index
and rule prefix (`p.majorIdx`/`p.rulePrefix` at the install).
-/

namespace ConLeche

variable {mode : CheckMode}

/-- Stage 1 at the run level. -/
theorem direct_sum_ind_wf {env env₁ : Env} (henv : EnvWF env)
    {p p' : InductiveShape} {cvTa : ConstantVal} {F : Nat} {capsOf : InductiveShape → IndCaps}
    (h : checkSumInd (fueledOps mode F) env p capsOf = .ok (env₁, cvTa, p'))
    -- the capability record names the parameter count as
    -- its arity (both records do: `nativeCaps`, and the empty one)
    (hcapsOf : ∀ q : InductiveShape,
      ((capsOf q).unitlike = true → (capsOf q).unitParams = q.nP) ∧
      ((capsOf q).eta = true → (capsOf q).etaParams = q.nP)) :
    EnvWF env₁ ∧ cvTa.type.hasFvar = false := by
  obtain ⟨cvT, s, -, -, hccv, rfl, rfl, bs, hstrip⟩ := checkSumInd_shape h
  have hsome : (cvTa.type.stripPis (p.nP + p.nIdx)).isSome = true := by
    rw [hstrip]; rfl
  refine ⟨envWF_cons_ind henv hccv (IndCapsWF.of_caps ?_ ?_),
    (checkConstantVal_typeWF hccv).1⟩
  · intro hu
    rw [(hcapsOf _).1 hu, InductiveShape.withSort_nP]
    exact stripPis_isSome_of_le (Nat.le_add_right _ _) hsome
  · intro he
    rw [(hcapsOf _).2 he, InductiveShape.withSort_nP]
    exact stripPis_isSome_of_le (Nat.le_add_right _ _) hsome

/-- A constructor's run at the former's environment: its type is
closed and bounded. -/
theorem direct_sum_ctor_typeWF {env₀ env : Env} {T : Name} {lps : List Name}
    {nP nIdx : Nat} {resSort : Level} {isProp large : Bool} {cvC cvTa cvCa : ConstantVal}
    {nF : Nat} {F : Nat} {sorts : List Level}
    (h : checkSumCtor (fueledOps mode F) env₀ env T lps nP nIdx resSort isProp large
      cvC nF cvTa = .ok (cvCa, sorts)) :
    cvCa.type.hasFvar = false ∧ cvCa.type.allLevelParamsDefined cvCa.levelParams = true ∧
    cvCa.type.constsResolve env = true ∧ cvCa.type.looseBVarsBounded 0 = true := by
  obtain ⟨⟨_, hccv⟩, -, -⟩ := checkSumCtor_shape h
  exact checkConstantVal_typeWF hccv

/-- A name fresh above the constructors' conses is fresh below them
(task #210 Part A). -/
theorem consSumCtors_find?_none {nP : Nat} {n : Name} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {env : Env},
      (consSumCtors nP ctorsA env).find? n = none → env.find? n = none
  | [], _, h => h
  | c :: cs, env, h => by
    simp only [consSumCtors] at h
    have h' := consSumCtors_find?_none h
    rw [Env.find?_cons] at h'
    split at h'
    · exact nomatch h'
    · exact h'

/-- The constructors' conses keep well-formedness: every consed
constructor's type resolves at the environment it is consed onto
(resolution is monotone along the conses). -/
theorem envWF_consSumCtors {nP : Nat} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {env : Env},
      EnvWF env →
      (∀ c ∈ ctorsA, c.1.type.hasFvar = false ∧
        c.1.type.allLevelParamsDefined c.1.levelParams = true ∧
        c.1.type.constsResolve env = true ∧ c.1.type.looseBVarsBounded 0 = true) →
      EnvWF (consSumCtors nP ctorsA env)
  | [], _, henv, _ => henv
  | c :: cs, env, henv, hall => by
    simp only [consSumCtors]
    obtain ⟨htf, htp, htr, htb⟩ := hall c List.mem_cons_self
    refine envWF_consSumCtors ?_ ?_
    · exact EnvWF.cons henv (structConstWF htf htp (Expr.constsResolve_mono htr) htb
        (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq))
    · intro c' hc'
      obtain ⟨h1, h2, h3, h4⟩ := hall c' (List.mem_cons_of_mem _ hc')
      exact ⟨h1, h2, Expr.constsResolve_mono h3, h4⟩

/-- The stored rules carry the generated right-hand sides and are
never `.nested`. -/
theorem sumRules_mem {find? : Name → Option ConstantInfo} {recName : Name}
    {nP mI rP : Nat} {recTy : Expr} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {rhss : List Expr} {r : RecRule},
      r ∈ sumRules find? recName nP mI rP recTy ctorsA rhss →
      r.rhs ∈ rhss ∧ ∀ lvls pins, r.fire ≠ .nested lvls pins
  | [], _, r, h => by simp [sumRules] at h
  | _ :: _, [], r, h => by simp [sumRules] at h
  | c :: cs, rhs :: rhss, r, h => by
    simp only [sumRules, List.mem_cons] at h
    rcases h with rfl | h
    · refine ⟨List.mem_cons_self, fun lvls pins => ?_⟩
      show (if Expr.recRulePlain recTy mI rP nP then RecRuleFire.plain else .inert) ≠ _
      split <;> simp
    · obtain ⟨hm, hf⟩ := sumRules_mem h
      exact ⟨List.mem_cons_of_mem _ hm, hf⟩

/-- Every stored rule of the fixpoint route carries the two rescue
bits its own install-time lookup computes. -/
theorem sumRules_bits {find? : Name → Option ConstantInfo} {recName : Name}
    {nP mI rP : Nat} {recTy : Expr} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {rhss : List Expr} {r : RecRule},
      r ∈ sumRules find? recName nP mI rP recTy ctorsA rhss →
      r.k = recRuleKOf find? r.ctor ∧
        r.eta = recRuleEtaOf find? recName r.ctor
  | [], _, r, h => by simp [sumRules] at h
  | _ :: _, [], r, h => by simp [sumRules] at h
  | _ :: cs, _ :: rhss, r, h => by
    simp only [sumRules, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨rfl, rfl⟩
    · exact sumRules_bits h

end ConLeche
