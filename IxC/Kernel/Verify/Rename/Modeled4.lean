module

public import IxC.Kernel.Verify.Rename.Modeled3

@[expose] public section

/-!
# The renaming walk through the modeled route: the members and the recursors (step 7.3, chunk (iii))

The per-rule checks (`checkIotaRule`, `checkIotaRules`), the member checks
against the `_model` artifacts (`checkMemberVal`, `checkIndMember`) and the
recursor group (`provisionRecs`, `checkIndRecs`), at a renamed block over related
environments.
-/

set_option linter.unusedSimpArgs false

set_option linter.unusedSectionVars false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : KeyScope md}
variable {L : Env md → Env md' → Prop} [LinkPush P f L]
variable {ops : (CheckerOps md) (CheckM md)} {ops' : (CheckerOps md') (CheckM md')}

/-- A left fold whose steps are simulated, over a list and its image. -/
theorem SimR.foldlM_map {ε ε' α α' β β' : Type} {R : α → α' → Prop} {g : β → β'}
    {step : α → β → Except ε α} {step' : α' → β' → Except ε' α'} {G : β → Prop}
    (hstep : ∀ a a' b, R a a' → G b → SimR R (step a b) (step' a' (g b))) :
    ∀ (l : List β), (∀ b ∈ l, G b) → ∀ {a : α} {a' : α'}, R a a' →
      SimR R (l.foldlM step a) ((l.map g).foldlM step' a')
  | [], _, _, _, h => SimR.pure' h
  | b :: bs, hl, _, _, h => by
    simp only [List.map_cons, List.foldlM_cons]
    exact SimR.bind (hstep _ _ b h (hl b List.mem_cons_self))
      (fun _ _ hR => SimR.foldlM_map hstep bs (fun b' hb' => hl b' (List.mem_cons_of_mem _ hb')) hR)

/-! ## The rules -/

/-- **One modeled rule at a renamed recursor.** -/
theorem checkIotaRule_sim (mode : CheckMode) (hops : OpsSim P f L ops ops')
    {env₁ envS : Env md} {env₁' envS' : Env md'} (hE₁ : EnvRelG P f L env₁ env₁')
    (hES : EnvRelG P f L envS envS') {ρ : Key md → Key md} {ρ' : Key md' → Key md'}
    (hρ : ∀ k : Key md, k.Good P → (ρ k).map f = ρ' (k.map f))
    (hρg : ∀ k : Key md, k.Good P → (ρ k).Good P)
    {cvName : Key md} (hn : cvName.Good P) (lps : List LevelParam) {tyA : Expr md}
    (hty : tyA.Good P) (mI rP j : Nat) {r : RecRule md} (hr : r.Good P) :
    SimE (RecRule.Good P) (RecRule.mapKeys f)
      (checkIotaRule mode ops env₁ envS ρ cvName lps tyA mI rP j r)
      (checkIotaRule mode ops' env₁' envS' ρ' (cvName.map f) lps (tyA.mapKeys f) mI rP j
        (r.mapKeys f)) := by
  unfold checkIotaRule
  have hctor : (r.mapKeys f).ctor = r.ctor.map f := rfl
  rw [hctor, hE₁.find r.ctor hr.1]
  cases hc : env₁.find? r.ctor with
  | none => exact SimE.throw'
  | some c =>
    have hcg : c.Good P := hE₁.good r.ctor c hr.1 hc
    cases c with
    | ctorInfo cvj cnP cnF =>
      simp only [Option.map_some, ConstantInfo.mapKeys]
      have hnf : (r.mapKeys f).nfields = r.nfields := rfl
      have hrhs : (r.mapKeys f).rhs = r.rhs.mapKeys f := rfl
      simp only [hnf, hrhs, Expr.looseBVarsBounded_mapKeys, Expr.hasFvar_mapKeys]
      refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
      refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
      refine SimE.ite Iff.rfl (fun _ => SimE.throw_bind) (fun _ => ?_)
      refine SimE.bind (hops.annotate hES 0 r.rhs hr.2.2) (fun rhsA hrhsA => ?_)
      simp only [Expr.allLevelParamsDefined_mapKeys, constsResolve_ren hES hrhsA,
        Expr.stripLams_mapKeys, Option.isSome_map]
      refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
      refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
      refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
      refine SimE.bind (hops.inferType hES 0 rhsA hrhsA) (fun _ _ => ?_)
      simp only [Expr.recRulePlain_mapKeys]
      have hfinal : ∀ fire : RecRuleFire md, RecRuleFire.Good P fire →
          SimE (RecRule.Good P) (RecRule.mapKeys f)
            (pure (recRuleBits env₁.find? cvName
              { r with rhs := rhsA, ctorParams := cnP, fire := fire, paramsBlind := false }) :
              CheckM md (RecRule md))
            (pure (recRuleBits env₁'.find? (cvName.map f)
              { r.mapKeys f with rhs := rhsA.mapKeys f, ctorParams := cnP,
                                 fire := fire.mapKeys f, paramsBlind := false }) :
              CheckM md' (RecRule md')) := by
        intro fire hfire
        have hrl : RecRule.Good P
            { r with rhs := rhsA, ctorParams := cnP, fire := fire, paramsBlind := false } :=
          ⟨hr.1, hfire, hrhsA⟩
        have h := recRuleBits_ren hE₁ (recName := cvName) hrl
        refine SimE.pure' ?_ ?_
        · simp only [recRuleBits]
          exact hrl
        · rw [← h]
          rfl
      refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => ?_)
      · refine SimE.bind (checkIotaThm_sim mode hops hE₁ hES hρ hρg hn lps hty mI rP j hr hcg
          cnP cnF hrhsA) (fun _ _ => ?_)
        exact hfinal .plain trivial
      · refine SimE.bind (checkIotaThmN_sim mode hops hE₁ hES hρ hρg hn lps hty mI rP j hr hcg
          cnP cnF hrhsA) (fun fire hfire => ?_)
        exact hfinal fire hfire
    | _ => exact SimE.throw'

theorem checkIotaRules_sim (mode : CheckMode) (hops : OpsSim P f L ops ops')
    {env₁ envS : Env md} {env₁' envS' : Env md'} (hE₁ : EnvRelG P f L env₁ env₁')
    (hES : EnvRelG P f L envS envS') {ρ : Key md → Key md} {ρ' : Key md' → Key md'}
    (hρ : ∀ k : Key md, k.Good P → (ρ k).map f = ρ' (k.map f))
    (hρg : ∀ k : Key md, k.Good P → (ρ k).Good P)
    {cvName : Key md} (hn : cvName.Good P) (lps : List LevelParam) {tyA : Expr md}
    (hty : tyA.Good P) (mI rP : Nat) :
    ∀ (j : Nat) (rules : List (RecRule md)), (∀ r ∈ rules, r.Good P) →
      SimE (fun rs : List (RecRule md) => ∀ r ∈ rs, r.Good P) (List.map (RecRule.mapKeys f))
        (checkIotaRules mode ops env₁ envS ρ cvName lps tyA mI rP j rules)
        (checkIotaRules mode ops' env₁' envS' ρ' (cvName.map f) lps (tyA.mapKeys f) mI rP j
          (rules.map (RecRule.mapKeys f)))
  | _, [], _ => SimE.pure' (fun _ h => (nomatch h)) rfl
  | j, r :: rs, hrs => by
    simp only [List.map_cons, checkIotaRules]
    refine SimE.bind (checkIotaRule_sim mode hops hE₁ hES hρ hρg hn lps hty mI rP j
      (hrs r List.mem_cons_self)) (fun r' hr' => ?_)
    refine SimE.bind (checkIotaRules_sim mode hops hE₁ hES hρ hρg hn lps hty mI rP (j + 1) rs
      (fun r'' h => hrs r'' (List.mem_cons_of_mem _ h))) (fun rest hrest => ?_)
    refine SimE.pure' ?_ rfl
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hr'
    · exact hrest x hx

/-! ## The members -/

/-- **A member's check against its model, at a renamed member.** -/
theorem checkMemberVal_sim (hops : OpsSim P f L ops ops') {env : Env md} {env' : Env md'}
    (hE : EnvRelG P f L env env') {blockNames : List (Key md)} (hb : ∀ k ∈ blockNames, k.Good P)
    {cv : ConstantVal md} (hcv : cv.Good P) :
    SimE (ConstantVal.Good P) (ConstantVal.mapKeys f)
      (checkMemberVal ops blockNames env cv)
      (checkMemberVal ops' (blockNames.map (Key.map f)) env' (cv.mapKeys f)) := by
  unfold checkMemberVal
  refine SimE.bind (checkConstantVal_sim hops hE hcv) (fun cvA hcvA => ?_)
  simp only [ConstantVal.mapKeys_name, Key.map_isModelSuffix]
  refine SimE.ite Iff.rfl (fun _ => SimE.throw_bind) (fun _ => ?_)
  have hk : (auxKey cvA.name .model).Good P := hcvA.1
  rw [show auxKey (cvA.name.map f) .model = (auxKey cvA.name .model).map f from rfl,
    hE.find _ hk]
  cases hm : env.find? (auxKey cvA.name .model) with
  | none => exact SimE.throw'
  | some c =>
    have hcg : c.Good P := hE.good _ c hk hm
    cases c with
    | defnInfo cvm mval hint =>
      simp only [Option.map_some, ConstantInfo.mapKeys, ConstantVal.mapKeys_levelParams,
        ConstantVal.mapKeys_type]
      refine SimE.ite Iff.rfl (fun _ => ?_) (fun _ => SimE.throw_bind)
      simp only [← mapKeys_renameConsts_good (ρ := modelRen blockNames) (modelRen_map hE.inj hb) hcvA.2]
      rw [
        Expr.mapKeys_beq hE.inj (Expr.Good.renameConsts modelRen_good hcvA.2) hcg.1.2]
      refine SimE.ite Iff.rfl (fun _ => SimE.pure' hcvA rfl) (fun _ => SimE.throw_bind)
    | _ => exact SimE.throw'

theorem blockNames_good {block : List (ConstantInfo md)} (hb : ∀ c ∈ block, c.Good P) :
    ∀ k ∈ block.map (·.name), k.Good P := by
  intro k hk
  simp only [List.mem_map] at hk
  obtain ⟨c, hc, rfl⟩ := hk
  exact (hb c hc).toConstantVal.1

theorem blockNames_map (block : List (ConstantInfo md)) :
    (block.map (ConstantInfo.mapKeys f)).map (·.name) = (block.map (·.name)).map (Key.map f) := by
  simp [List.map_map, Function.comp_def]

/-- One non-recursor member, at a renamed member. -/
theorem checkIndMember_sim (hops : OpsSim P f L ops ops') {blockNames : List (Key md)}
    (hb : ∀ k ∈ blockNames, k.Good P) {caps : IndCaps md} (hcaps : caps.Good P)
    {env : Env md} {env' : Env md'} (hE : EnvRelG P f L env env') {ci : ConstantInfo md}
    (hci : ci.Good P) :
    SimR (EnvRelG P f L) (checkIndMember ops blockNames caps env ci)
      (checkIndMember ops' (blockNames.map (Key.map f)) (caps.mapKeys f) env'
        (ci.mapKeys f)) := by
  unfold checkIndMember
  rw [ConstantInfo.mapKeys_toConstantVal]
  refine SimR.bindE (checkMemberVal_sim hops hE hb hci.toConstantVal) (fun cvA hcvA => ?_)
  cases ci with
  | indInfo _ _ =>
    exact SimR.pure' (hE.push (c := .indInfo cvA caps) ⟨hcvA, hcaps⟩)
  | ctorInfo _ nP nF =>
    exact SimR.pure' (hE.push (c := .ctorInfo cvA nP nF) hcvA)
  | _ => exact SimR.throw'


/-! ## The recursor group -/

/-- A provisioned recursor's record, renamed. -/
def provMap (f : md.Id → md'.Id) (c : ConstantVal md × Nat × Nat × List (RecRule md)) :
    ConstantVal md' × Nat × Nat × List (RecRule md') :=
  (c.1.mapKeys f, c.2.1, c.2.2.1, c.2.2.2.map (RecRule.mapKeys f))

def provGood (P : KeyScope md) (c : ConstantVal md × Nat × Nat × List (RecRule md)) : Prop :=
  c.1.Good P ∧ ∀ r ∈ c.2.2.2, r.Good P

theorem provisionRecs_sim (hops : OpsSim P f L ops ops') {blockNames : List (Key md)}
    (hb : ∀ k ∈ blockNames, k.Good P) :
    ∀ (recs : List (ConstantInfo md)), (∀ c ∈ recs, c.Good P) →
      ∀ {envAcc : Env md} {envAcc' : Env md'}, EnvRelG P f L envAcc envAcc' →
        SimR (fun (r : Env md × List (ConstantVal md × Nat × Nat × List (RecRule md)))
            (r' : Env md' × List (ConstantVal md' × Nat × Nat × List (RecRule md'))) =>
            EnvRelG P f L r.1 r'.1 ∧ (∀ c ∈ r.2, provGood P c) ∧ r'.2 = r.2.map (provMap f))
          (provisionRecs ops blockNames envAcc recs)
          (provisionRecs ops' (blockNames.map (Key.map f)) envAcc'
            (recs.map (ConstantInfo.mapKeys f)))
  | [], _, _, _, hE => SimR.pure' ⟨hE, fun _ h => (nomatch h), rfl⟩
  | ci :: rest, hrs, _, _, hE => by
    have hci := hrs ci List.mem_cons_self
    simp only [List.map_cons, provisionRecs]
    cases ci with
    | recInfo cv mI rP rules =>
      simp only [ConstantInfo.mapKeys]
      refine SimR.bindE (checkMemberVal_sim hops hE hb (cv := cv) hci.1) (fun cvA hcvA => ?_)
      refine SimR.bind (provisionRecs_sim hops hb rest
        (fun c h => hrs c (List.mem_cons_of_mem _ h))
        (hE.push (c := .recInfo cvA mI rP []) ⟨hcvA, fun _ h => (nomatch h)⟩))
        (fun r r' hr => ?_)
      obtain ⟨envSelf, others⟩ := r
      obtain ⟨envSelf', others'⟩ := r'
      obtain ⟨hES, hgood, rfl⟩ := hr
      refine SimR.pure' ⟨hES, ?_, rfl⟩
      intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact ⟨hcvA, hci.2⟩
      · exact hgood c hc
    | _ => exact SimR.throw'

/-- **The recursor group at a renamed block.** -/
theorem checkIndRecs_sim (mode : CheckMode) (hops : OpsSim P f L ops ops')
    {blockNames : List (Key md)} (hb : ∀ k ∈ blockNames, k.Good P) {env₂ : Env md}
    {env₂' : Env md'} (hE₂ : EnvRelG P f L env₂ env₂') {recs : List (ConstantInfo md)}
    (hrs : ∀ c ∈ recs, c.Good P) :
    SimR (EnvRelG P f L) (checkIndRecs mode ops blockNames env₂ recs)
      (checkIndRecs mode ops' (blockNames.map (Key.map f)) env₂'
        (recs.map (ConstantInfo.mapKeys f))) := by
  unfold checkIndRecs
  simp only [List.isEmpty_map]
  refine SimR.ite Iff.rfl (fun _ => SimR.pure' hE₂) (fun _ => ?_)
  have heq := find_eq_pin_ren hE₂ (k := eqName) (hE₂.pre .eq (by decide)) (pin := eqA)
    (ConstantInfo.good_of_pinIn hE₂.pre eqA_pinIn)
  simp only [eqA_mapKeys] at heq
  refine SimR.ite (decide_eq_decide.mp heq.symm) (fun _ => ?_) (fun _ => SimR.throw_bind)
  refine SimR.bind (provisionRecs_sim hops hb recs hrs hE₂) (fun r r' hr => ?_)
  obtain ⟨envSelf, checked⟩ := r
  obtain ⟨envSelf', checked'⟩ := r'
  obtain ⟨hES, hgood, rfl⟩ := hr
  simp only []
  refine SimR.foldlM_map (G := provGood P) ?_ checked hgood hE₂
  intro acc acc' c hacc hc
  simp only [provMap, ConstantVal.mapKeys_name, ConstantVal.mapKeys_levelParams,
    ConstantVal.mapKeys_type]
  refine SimR.bindE (checkIotaRules_sim mode hops hE₂ hES (modelRen_map hE₂.inj hb)
    modelRen_good hc.1.1 _ hc.1.2 _ _ 0 _ hc.2) (fun rules' hrules' => ?_)
  exact SimR.pure' (hacc.push (c := .recInfo c.1 c.2.1 c.2.2.1 rules') ⟨hc.1, hrules'⟩)

end Ix.Kernel
