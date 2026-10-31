module

public import IxC.Kernel.Verify.Rename.Modeled6

@[expose] public section

/-!
# The renaming walk through the modeled route: the block (step 7.3, chunk (iii))

`checkModeled` at a renamed block over related environments: the block's
tag filters commute with the renaming, the recursor-suffix decision is a
function of the tags, and every phase (members, recursors, the eta
residual gate, the projection name family, the projection installs) is
simulated by the lemmas of `Modeled4`–`Modeled6`.
-/

set_option linter.unusedSimpArgs false

set_option linter.unusedSectionVars false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : KeyScope md}
variable {L : Env md → Env md' → Prop} [LinkPush P f L]
variable {ops : (CheckerOps md) (CheckM md)} {ops' : (CheckerOps md') (CheckM md')}

/-- A tag filter (a predicate given at every mode that the renaming does not
move) commutes with renaming the block. -/
theorem filter_map_mapKeys (p : (m : Mode) → ConstantInfo m → Bool)
    (hp : ∀ c : ConstantInfo md, p md' (c.mapKeys f) = p md c) (l : List (ConstantInfo md)) :
    (l.map (ConstantInfo.mapKeys f)).filter (p md') =
      (l.filter (p md)).map (ConstantInfo.mapKeys f) := by
  rw [List.filter_map]
  congr 1
  exact List.filter_congr fun c _ => hp c

theorem isRecInfo_mapKeys (c : ConstantInfo md) : (c.mapKeys f).isRecInfo = c.isRecInfo := by
  cases c <;> rfl

theorem recsFormSuffix_map : ∀ block : List (ConstantInfo md),
    recsFormSuffix (block.map (ConstantInfo.mapKeys f)) = recsFormSuffix block
  | [] => rfl
  | c :: rest => by
    simp only [List.map_cons, recsFormSuffix, isRecInfo_mapKeys, List.all_map,
      Function.comp_def, recsFormSuffix_map rest]

/-- The recursor-suffix decision is the tag pass. -/
theorem blockRecSuffix_decide (block : List (ConstantInfo md)) :
    @decide _ (blockRecSuffixDec block) = recsFormSuffix block := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact (recsFormSuffix_iff block).symm

/-- A left fold over one list whose steps are simulated. -/
theorem SimR.foldlM_same {ε ε' α α' β : Type} {R : α → α' → Prop}
    {step : α → β → Except ε α} {step' : α' → β → Except ε' α'}
    (hstep : ∀ a a' b, R a a' → SimR R (step a b) (step' a' b)) :
    ∀ (l : List β) {a : α} {a' : α'}, R a a' → SimR R (l.foldlM step a) (l.foldlM step' a')
  | [], _, _, h => SimR.pure' h
  | b :: bs, _, _, h => by
    simp only [List.foldlM_cons]
    exact SimR.bind (hstep _ _ b h) (fun _ _ hr => SimR.foldlM_same hstep bs hr)

theorem map_eq_ind_singleton {Is : List (ConstantInfo md)} {cvT' : ConstantVal md'}
    {caps' : IndCaps md'} (h : Is.map (ConstantInfo.mapKeys f) = [.indInfo cvT' caps']) :
    ∃ cvT caps, Is = [.indInfo cvT caps] := by
  rcases Is with _ | ⟨c, _ | ⟨d, rest⟩⟩
  · cases h
  · cases c <;> first | exact ⟨_, _, rfl⟩ | cases h
  · simp at h

theorem map_eq_ctor_singleton {Cs : List (ConstantInfo md)} {cvC' : ConstantVal md'}
    {nP' nF' : Nat} (h : Cs.map (ConstantInfo.mapKeys f) = [.ctorInfo cvC' nP' nF']) :
    ∃ cvC nP nF, Cs = [.ctorInfo cvC nP nF] := by
  rcases Cs with _ | ⟨c, _ | ⟨d, rest⟩⟩
  · cases h
  · cases c <;> first | exact ⟨_, _, _, rfl⟩ | cases h
  · simp at h

/-- **The modeled route at a renamed block.** -/
theorem checkModeled_sim (mode : CheckMode) (hops : OpsSim P f L ops ops') {env : Env md}
    {env' : Env md'} (hE : EnvRelG P f L env env') {block : List (ConstantInfo md)}
    (hb : ∀ c ∈ block, c.Good P) :
    SimR (EnvRelG P f L) (checkModeled mode ops env block)
      (checkModeled mode ops' env' (block.map (ConstantInfo.mapKeys f))) := by
  have hf := hE.inj
  unfold checkModeled
  simp only [blockRecSuffix_decide, recsFormSuffix_map]
  rw [filter_map_mapKeys (f := f)
      (fun m ci => @checkModeled.match_1 m (fun _ => Bool) ci (fun _ _ => true) (fun _ => false))
      (fun c => by cases c <;> rfl),
    filter_map_mapKeys (f := f)
      (fun m ci => @checkModeled.match_4 m (fun _ => Bool) ci (fun _ _ _ => true) (fun _ => false))
      (fun c => by cases c <;> rfl),
    filter_map_mapKeys (f := f)
      (fun m ci => @provisionRecs.match_3 m (fun _ => Bool) ci (fun _ _ _ _ => true) (fun _ => false))
      (fun c => by cases c <;> rfl),
    filter_map_mapKeys (f := f)
      (fun m ci => @provisionRecs.match_3 m (fun _ => Bool) ci (fun _ _ _ _ => false) (fun _ => true))
      (fun c => by cases c <;> rfl)]
  have hbn := blockNames_good hb
  have hN : ∀ c ∈ List.filter (fun ci => @provisionRecs.match_3 md (fun _ => Bool) ci
      (fun _ _ _ _ => false) (fun _ => true)) block, c.Good P :=
    fun c hc => hb c (List.mem_filter.1 hc).1
  have hR : ∀ c ∈ List.filter (fun ci => @provisionRecs.match_3 md (fun _ => Bool) ci
      (fun _ _ _ _ => true) (fun _ => false)) block, c.Good P :=
    fun c hc => hb c (List.mem_filter.1 hc).1
  refine SimR.ite Iff.rfl (fun _ => ?_) (fun _ => SimR.throw_bind)
  have hIs := fun c (hc : c ∈ List.filter (fun ci => @checkModeled.match_1 md (fun _ => Bool) ci
    (fun _ _ => true) (fun _ => false)) block) => hb c (List.mem_filter.1 hc).1
  have hCs := fun c (hc : c ∈ List.filter (fun ci => @checkModeled.match_4 md (fun _ => Bool) ci
    (fun _ _ _ => true) (fun _ => false)) block) => hb c (List.mem_filter.1 hc).1
  generalize List.filter (fun ci => @checkModeled.match_1 md (fun _ => Bool) ci
    (fun _ _ => true) (fun _ => false)) block = Is at hIs ⊢
  generalize List.filter (fun ci => @checkModeled.match_4 md (fun _ => Bool) ci
    (fun _ _ _ => true) (fun _ => false)) block = Cs at hCs ⊢
  split
  · rename_i cvT caps₀ cvC nP nF
    have hT : cvT.Good P := (hIs _ List.mem_cons_self).1
    have hC : cvC.Good P := hCs _ List.mem_cons_self
    simp only [List.map_cons, List.map_nil, ConstantInfo.mapKeys, blockNames_map]
    refine SimR.bindE (G := IndCaps.Good P) (m := IndCaps.mapKeys f)
      (SimE.pure' (indBlockCaps_good mode env hC nP nF) (indBlockCaps_map mode hE hT hC nP nF))
      (fun caps hcaps => ?_)
    have hstep := fun (a : Env md) (a' : Env md') (b : ConstantInfo md) (ha : EnvRelG P f L a a')
      (hb' : b.Good P) => checkIndMember_sim (ops := ops) (ops' := ops') hops hbn hcaps ha hb'
    have hfold := SimR.foldlM_map hstep _ hN hE
    refine SimR.bind hfold (fun env₂ env₂' hE₂ => ?_)
    have hrecs := checkIndRecs_sim mode hops hbn hE₂ hR
    refine SimR.bind hrecs (fun env₃ env₃' hE₃ => ?_)
    refine SimR.ite (by
      simp only [IndCaps.mapKeys, ConstantVal.mapKeys_name, ConstantVal.mapKeys_levelParams,
        ctorResidualOk_map mode hE₃ hT.1 hC.1]) (fun _ => ?_) (fun _ => SimR.throw_bind)
    refine SimR.ite (by
      simp only [ConstantVal.mapKeys_name, projFamFree_map hE₃ hT.1])
      (fun _ => ?_) (fun _ => SimR.throw_bind)
    have hproj := SimR.foldlM_same
      (fun a a' i ha => installProjFnStep_sim mode hops hT.1 hC.1 cvT.levelParams nP nF ha i)
      (List.range nF) hE₃
    refine SimR.ite (by
      simp only [ConstantVal.mapKeys_name, ConstantVal.mapKeys_levelParams,
        ConstantVal.mapKeys_type, ctorTargetsFam_map hf hC.2 hT.1])
      (fun _ => ?_) (fun _ => SimR.pure' hE₃)
    simp only [ConstantVal.mapKeys_name, ConstantVal.mapKeys_levelParams]
    exact hproj
  · split
    · rename_i hne _ _ cvT' caps' cvC' nP' nF' hI' hC'
      obtain ⟨cvT, caps, rfl⟩ := map_eq_ind_singleton hI'
      obtain ⟨cvC, nP, nF, rfl⟩ := map_eq_ctor_singleton hC'
      exact (hne _ _ _ _ _ rfl rfl).elim
    · simp only [blockNames_map]
      have hstep := fun (a : Env md) (a' : Env md') (b : ConstantInfo md) (ha : EnvRelG P f L a a')
        (hb' : b.Good P) => checkIndMember_sim (ops := ops) (ops' := ops') (caps := {}) hops hbn
          (by intro k hk; cases hk) ha hb'
      have hfold := SimR.foldlM_map hstep _ hN hE
      refine SimR.bind hfold (fun env₂ env₂' hE₂ => ?_)
      exact checkIndRecs_sim mode hops hbn hE₂ hR
