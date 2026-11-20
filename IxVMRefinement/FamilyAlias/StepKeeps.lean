import IxVMRefinement.FamilyAlias.StepFamily
import IxVMRefinement.FamilyAlias.StoreAr
import IxVMRefinement.Assembly.NativeBlockLoads

/-! # The fold's clause across the family step

The family row's step (`unitStepFamily_of_facts`) takes the keeping of the prefix invariant and
of the fold's clause beside it (`FoldExtra`) across the step's record. This module proves it
(`famStepKeeps_foldExtra`), field by field of `FoldClauseWith`:

* proved from the record: the model in every set theory (`envModelN_famStep`), the store facts
  (`foldStoreInv_famStep`), the theorems' level parameters (`thmLevels_famStep`), the arity of
  the stored terms (`familyKeepsStoreAr`), the registry's families (the extension keeps them), the
  store keys, the roots (`auxRootSynced_famStep`), the unresolved key, the table, and η stability:
  the record stores its inductives at the empty capability record, so none is η-capable
  (`etaStable_famStep`);
* from named premises, each the circuit side's:
  - `hsz`: the family's constant addresses have 32 bytes (the hash of a projection record;
    `constAddr_hash_size_of_block` at the two block records);
  - `hmod`: no inductive the step stores is at an address whose projection record names a block
    the circuit treats as native (the route fact `ModeledAt` at the family's block);
  - `hrecs`: the four facts a stored recursor owes the companions (`RecCompanionFacts`), for each
    recursor the step stores;
  - `hloads`: the load contract's facts that reach the step's new constants (`NewLoads`).

`coreCompanions_append_recs` gives the companions after constants put in front of the prefix,
constructors and recursors among them, from those before and each new recursor's four facts. -/

universe u

namespace IxVM.Refinement.Typing.FamilyAlias

open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal RecRule Key)
open Ix.Kernel.Semantics (NativeFam DeclIndRenRunJ)
open IxVM.Refinement.Decl.FamilyAlias (AliasGroup famJ)

set_option linter.unusedVariables false

/-! ## The aliases -/

/-- An alias of a group is a definition, at no projection table's key. -/
theorem AliasGroup.defn_of_mem {env : Ix.Kernel.Env .anon}
    {h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon} {as : List (ConstantInfo .anon)}
    (hg : AliasGroup env h as) :
    ∀ a ∈ as, (∃ cv v hint, a = ConstantInfo.defnInfo cv v hint) ∧
      ∀ T, a.name ≠ Ix.Kernel.projTableName T := by
  induction hg with
  | nil _ => exact fun _ ha => nomatch ha
  | @cons h₀ h' as' n d lps ty tgt ci hg' _ _ hnpt _ _ _ _ _ _ _ _ _ ih =>
    intro a ha
    rcases List.mem_cons.mp ha with he | ha'
    · rw [he]
      exact ⟨⟨_, _, _, rfl⟩, hnpt⟩
    · exact ih a ha'

/-! ## η stability -/

/-- **η stability across the family step**: the record stores its inductives at the empty
capability record, so a stored η-capable family is the prefix's, with its constructor. -/
theorem etaStable_famStep {env env₂ : Ix.Kernel.Env .anon}
    {h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon} {aliases blk : List (ConstantInfo .anon)}
    (hS : Decl.EtaStable env) (hC : Decl.EtaCtorStored env) (hg : AliasGroup env h aliases)
    (hd : DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ blk env₂) : Decl.EtaStable env₂ := by
  have hext : Ix.Kernel.EnvExt env env₂ :=
    (Decl.FamilyAlias.AliasGroup.envExt hg).trans (Ix.Kernel.Semantics.declIndRenRunJ_envExt hd)
  have hQ : Ix.Kernel.Model.NewSat ⟨aliases ++ env.consts⟩ env₂
      (fun ci => ∀ cv caps, ci = .indInfo cv caps → caps.eta = false) :=
    Ix.Kernel.Model.modeled_newSat
      (fun cv cv' caps he => by
        injection he with _ hc
        subst hc
        rfl)
      (fun _ _ _ _ _ he => nomatch he) (fun _ _ _ _ _ _ he => nomatch he) hd.shape
  intro T kc cvT cvc caps nP nF hT heta hkc hCt env' hext'
  have hT₀ : env.find? T = some (.indInfo cvT caps) := by
    rcases hQ T _ hT with h0 | hq
    · rcases find?_append_cases aliases h0 with hm | ho
      · obtain ⟨⟨cv, v, hint, he⟩, -⟩ := AliasGroup.defn_of_mem hg _ hm
        exact nomatch he
      · exact ho
    · rw [hq cvT caps rfl] at heta
      exact nomatch heta
  have hkc₀ : env.find? kc = some (.ctorInfo cvc nP nF) := by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hC T cvT caps kc hT₀ heta hkc)
    exact hx.trans ((hext.find hx).symm.trans hCt)
  exact hS T kc cvT cvc caps nP nF hT₀ heta hkc hkc₀ env' (hext.trans hext')

/-! ## The companions -/

/-- **The four facts a stored recursor owes the companions** at the context `c`: its major
premise's record, its rules' constructors, its plain rules' major premise, and its rules'
constructor heads (the record fields of `Decl.CoreCompanions`, at one recursor). -/
structure RecCompanionFacts (c : Core.Ctx) (cv : ConstantVal .anon) (mI rP : Nat)
    (rls : List (RecRule .anon)) : Prop where
  major : ∀ (p : _root_.Address) (us : List Core.KLevel), rls ≠ [] →
    (Core.piDomAt mI cv.type).map (·.getAppFn) = some (.const (c.κ p) us) →
    ∃ cm, Ix.Cert.recordAt c.E p = some cm
  rules : (rls.map (·.ctor)).Nodup ∧
    ∀ (p : _root_.Address) (cm : Ixon.Constant) (ip : Ixon.InductiveProj)
      (us : List Core.KLevel),
      (Core.piDomAt mI cv.type).map (·.getAppFn) = some (.const (c.κ p) us) →
      Ix.Cert.recordAt c.E p = some cm → cm.info = .iPrj ip →
      ∀ j rl, rls[j]? = some rl → rl.ctor = c.κ (Core.cprjAddr ip.block ip.idx.toNat j)
  plain : ∀ (rl : RecRule .anon) (cvj : ConstantVal .anon) (nP nF : Nat), rl ∈ rls →
    rl.fire = .plain → c.env.find? rl.ctor = some (.ctorInfo cvj nP nF) →
    ∃ D T, Core.piDomAt mI cv.type = some D ∧
      D.getAppFn = .const T (cvj.levelParams.map .param) ∧
      D.getAppArgs.take nP = (List.range nP).map (fun i => .bvar (mI - 1 - i)) ∧
      D.getAppArgs.drop nP = (List.range (mI - rP)).map fun i => .bvar (mI - rP - 1 - i)
  noK : Core.RecNotKAt c.E cv.name
  notNative : ∀ (a : _root_.Address) (cHost : Ixon.Constant) (rc : Ixon.Recursor)
      (n : Nat) (p : _root_.Address) (cmP : Ixon.Constant) (ipP : Ixon.InductiveProj),
    cv.name = keyOf c.t a →
    RecHostAt c.E a cHost rc →
    recMotiveCarrierAt cHost rc 0 n = some p →
    Ix.Cert.recordAt c.E p = some cmP → cmP.info = .iPrj ipP →
    ¬ NativeAt c.E ipP.block

/-- **The companions after constants put in front of the prefix**, constructors and recursors
among them: the role fields are monotone along the extension; a recursor of the prefix keeps its
facts (the constructors its rules name are the prefix's, `StoreInv.recRules_fire`); each new
recursor brings its four facts at the longer environment. -/
theorem coreCompanions_append_recs {c : Core.Ctx} (h : Decl.CoreCompanions c)
    (hstore : Ix.Kernel.Open.StoreInv c.env) {new : List (ConstantInfo .anon)}
    (hext : Ix.Kernel.EnvExt c.env ⟨new ++ c.env.consts⟩)
    (hrec : ∀ cv mI rP rls, ConstantInfo.recInfo cv mI rP rls ∈ new →
      RecCompanionFacts ⟨c.E, ⟨new ++ c.env.consts⟩, c.t, c.lim⟩ cv mI rP rls) :
    Decl.CoreCompanions ⟨c.E, ⟨new ++ c.env.consts⟩, c.t, c.lim⟩ := by
  have oldRuleCtor : ∀ {k : Key .anon} {cv : ConstantVal .anon} {mI rP : Nat}
      {rls : List (RecRule .anon)} {rl : RecRule .anon}
      {cvj : ConstantVal .anon} {nP nF : Nat},
      c.env.find? k = some (.recInfo cv mI rP rls) → rl ∈ rls →
      (⟨new ++ c.env.consts⟩ : Ix.Kernel.Env .anon).find? rl.ctor =
        some (.ctorInfo cvj nP nF) →
      c.env.find? rl.ctor = some (.ctorInfo cvj nP nF) := by
    intro k cv mI rP rls rl cvj nP nF hk hrl hc
    obtain ⟨-, cvj', nF', hc'⟩ := hstore.recRules_fire hk hrl
    exact hc'.trans ((hext.find hc').symm.trans hc)
  exact
    { natLit := fun h1 h2 h3 => hext.natLitSupported_mono (h.natLit h1 h2 h3)
      strLit := fun h1 => hext.strLitSupported_mono (h.strLit h1)
      natOps := fun r hr hm => hext.natOpStored_mono (h.natOps r hr hm)
      natAdd := fun h1 => hext.opt_mono (p := Ix.Kernel.Rules.natAddTyOk) (h.natAdd h1) rfl
      eqStored := fun h1 =>
        let ⟨ci', hci'⟩ := h.eqStored h1
        ⟨ci', hext.find hci'⟩
      quotBasis := fun h1 ci' hm => hext.find (h.quotBasis h1 ci' hm)
      recMajorRecord := by
        intro k cv mI rP rls p us hf hne hdom
        rcases find?_append_cases new hf with hm | hf'
        · exact (hrec cv mI rP rls hm).major p us hne hdom
        · exact h.recMajorRecord k cv mI rP rls p us hf' hne hdom
      recRulesNodupAndProj := by
        intro k cv mI rP rls hf
        rcases find?_append_cases new hf with hm | hf'
        · exact (hrec cv mI rP rls hm).rules
        · exact h.recRulesNodupAndProj k cv mI rP rls hf'
      recPlain := by
        intro k cv mI rP rls rl cvj nP nF hf hrl hfire hc
        rcases find?_append_cases new hf with hm | hf'
        · exact (hrec cv mI rP rls hm).plain rl cvj nP nF hrl hfire hc
        · exact h.recPlain k cv mI rP rls rl cvj nP nF hf' hrl hfire (oldRuleCtor hf' hrl hc)
      ruleCtorHead := by
        intro k cv mI rP rls hf
        have hkn : cv.name = k := Ix.Kernel.Semantics.Env.find?_name hf
        rcases find?_append_cases new hf with hm | hf'
        · exact Or.inr (hkn ▸ (hrec cv mI rP rls hm).noK)
        · exact (h.ruleCtorHead k cv mI rP rls hf').imp
            (fun hh rl cvj nP nF T us hrl hc hdom =>
              hh rl cvj nP nF T us hrl (oldRuleCtor hf' hrl hc) hdom)
            id }

/-- **η stability across the family step with projection-table installation**: the record stores its
inductives at the empty capability record and `pcs` adds no inductive, so any stored η-capable
family is the prefix's, with its constructor. -/
theorem etaStable_famStep_proj {env env₂ : Ix.Kernel.Env .anon}
    {h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon} {aliases blk pcs : List (ConstantInfo .anon)}
    (hS : Decl.EtaStable env) (hC : Decl.EtaCtorStored env) (hg : AliasGroup env h aliases)
    (hd : DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ blk env₂)
    (hext : Ix.Kernel.EnvExt env ⟨pcs ++ env₂.consts⟩)
    (hnoInd : ∀ c ∈ pcs, ∀ cv caps, c ≠ .indInfo cv caps) :
    Decl.EtaStable ⟨pcs ++ env₂.consts⟩ := by
  have hQ : Ix.Kernel.Model.NewSat ⟨aliases ++ env.consts⟩ env₂
      (fun ci => ∀ cv caps, ci = .indInfo cv caps → caps.eta = false) :=
    Ix.Kernel.Model.modeled_newSat
      (fun cv cv' caps he => by
        injection he with _ hc
        subst hc
        rfl)
      (fun _ _ _ _ _ he => nomatch he) (fun _ _ _ _ _ _ he => nomatch he) hd.shape
  intro T kc cvT cvc caps nP nF hT heta hkc hCt env' hext'
  have hT₂ : env₂.find? T = some (.indInfo cvT caps) := by
    rcases find?_append_cases (env := env₂) pcs hT with hm | ho
    · exact (hnoInd _ hm cvT caps rfl).elim
    · exact ho
  have hT₀ : env.find? T = some (.indInfo cvT caps) := by
    rcases hQ T _ hT₂ with h0 | hq
    · rcases find?_append_cases aliases h0 with hm | ho
      · obtain ⟨⟨cv, v, hint, he⟩, -⟩ := AliasGroup.defn_of_mem hg _ hm
        exact nomatch he
      · exact ho
    · rw [hq cvT caps rfl] at heta
      exact nomatch heta
  have hkc₀ : env.find? kc = some (.ctorInfo cvc nP nF) := by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hC T cvT caps kc hT₀ heta hkc)
    exact hx.trans ((hext.find hx).symm.trans hCt)
  exact hS T kc cvT cvc caps nP nF hT₀ heta hkc hkc₀ env' (hext.trans hext')

/-- Lift `RecCompanionFacts` across prepended constants that contain no constructors. -/
theorem RecCompanionFacts.of_append_noCtor {E : Ixon.Env} {env₂ : Ix.Kernel.Env .anon}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} {pcs : List (ConstantInfo .anon)}
    {cv : ConstantVal .anon} {mI rP : Nat} {rls : List (RecRule .anon)}
    (hnoCtor : ∀ c ∈ pcs, ∀ cv' nP' nF', c ≠ .ctorInfo cv' nP' nF')
    (h : RecCompanionFacts ⟨E, env₂, t, lim⟩ cv mI rP rls) :
    RecCompanionFacts ⟨E, ⟨pcs ++ env₂.consts⟩, t, lim⟩ cv mI rP rls where
  major := h.major
  rules := h.rules
  plain rl cvj nP nF hrl hfire hc := by
    rcases find?_append_cases (env := env₂) pcs hc with hm | ho
    · exact (hnoCtor _ hm cvj nP nF rfl).elim
    · exact h.plain rl cvj nP nF hrl hfire ho
  noK := h.noK
  notNative := h.notNative

/-! ## The keeping -/

/-- **The fold's clause across the family step with modeled projection tables, at one registry**:
the clause at the prefix with the registry `Reg` gives the clause after the step with the same
registry, from the record, the projection-table installation `hres`, the addresses' length, the
companion facts of each new recursor, and the load facts at the new constants `pcs ++ new`. -/
theorem famStepKeeps_with {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {lim : Option Nat} {A rb : _root_.Address} {c crb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {elig : Nat → Bool}
    (hsz : ∀ x, FamAddr A c rb crb x → x.hash.size = 32)
    (hmod : ∀ x, FamAddr A c rb crb x → ∀ (cm : Ixon.Constant) (ip : Ixon.InductiveProj),
      Ix.Cert.recordAt E x = some cm → cm.info = .iPrj ip → ¬ NativeAt E ip.block)
    (hmodCtor : ∀ x, FamAddr A c rb crb x → ∀ (cm : Ixon.Constant) (cp : Ixon.ConstructorProj),
      Ix.Cert.recordAt E x = some cm → cm.info = .cPrj cp → ¬ NativeAt E cp.block)
    {env : Ix.Kernel.Env .anon} {Reg : NativeFam .anon → Prop}
    {h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon} {as blk new pcs : List (ConstantInfo .anon)}
    (hC : FoldClauseWith.{u} L t E lim env Reg) (hg : AliasGroup env h as)
    (hroots : ∀ a ∈ as, ∃ ci ∈ blk, a.name.base = ci.name)
    (hreads : FamDeclReads t E₀ A c rb crb blk)
    (hd : DeclIndRenRunJ (famJ h) ⟨as ++ env.consts⟩ blk ⟨new ++ env.consts⟩)
    (hres : BlockProjInstallResult.{u} t env ⟨new ++ env.consts⟩ Reg A ms elig pcs)
    (hrecs : ∀ cv mI rP rls, ConstantInfo.recInfo cv mI rP rls ∈ new →
      RecCompanionFacts ⟨E, ⟨new ++ env.consts⟩, t, lim⟩ cv mI rP rls)
    (hloads : NewLoads (appCtx ⟨E, env, t, lim⟩ (pcs ++ new)).stored (pcs ++ new)) :
    FoldClauseWith.{u} L t E lim ⟨(pcs ++ new) ++ env.consts⟩ Reg := by
  have hna : ∀ ci ∈ blk, Decl.NonAuxKey ci.name := fun ci hci => by
    obtain ⟨x, -, hk, -⟩ := hreads.2.1 ci hci
    rw [hk]
    exact Decl.isBaseKey_iff_nonAuxKey.mp (Decl.isBaseKey_keyOf t x)
  obtain ⟨new', henv, hnewN, hallBlk⟩ := famStep_consts hd
  have hnew : new = new' ++ as := by
    have h2 : new ++ env.consts = (new' ++ as) ++ env.consts :=
      congrArg Ix.Kernel.Env.consts henv
    exact List.append_cancel_right h2
  subst hnew
  have hassoc : (⟨(pcs ++ (new' ++ as)) ++ env.consts⟩ : Ix.Kernel.Env .anon) =
      ⟨pcs ++ ((new' ++ as) ++ env.consts)⟩ := by
    simp [List.append_assoc]
  have hnoInd : ∀ cn ∈ pcs, ∀ cv caps, cn ≠ .indInfo cv caps := by
    intro cn hcn cv caps heq
    obtain ⟨_, _, _, ⟨_, h1, -⟩ | ⟨_, h1, -⟩⟩ := hres.kindAndName cn hcn
    · rw [h1] at heq; cases heq
    · rw [h1] at heq; cases heq
  have hnoCtor : ∀ cn ∈ pcs, ∀ cv nP nF, cn ≠ .ctorInfo cv nP nF := by
    intro cn hcn cv nP nF heq
    obtain ⟨_, _, _, ⟨_, h1, -⟩ | ⟨_, h1, -⟩⟩ := hres.kindAndName cn hcn
    · rw [h1] at heq; cases heq
    · rw [h1] at heq; cases heq
  have hnoDefn : ∀ cn ∈ pcs, ∀ cv v hint, cn ≠ .defnInfo cv v hint := by
    intro cn hcn cv v hint heq
    obtain ⟨_, _, _, ⟨_, h1, -⟩ | ⟨_, h1, -⟩⟩ := hres.kindAndName cn hcn
    · rw [h1] at heq; cases heq
    · rw [h1] at heq; cases heq
  have hnoRec : ∀ cn ∈ pcs, ∀ cv mI rP rls, cn ≠ .recInfo cv mI rP rls := by
    intro cn hcn cv mI rP rls heq
    obtain ⟨_, _, _, ⟨_, h1, -⟩ | ⟨_, h1, -⟩⟩ := hres.kindAndName cn hcn
    · rw [h1] at heq; cases heq
    · rw [h1] at heq; cases heq
  have hpcsAux : ∀ cn ∈ pcs, ∃ pos < ms.size,
      cn.name = Ix.Kernel.auxKey (Core.keyOf t (Core.iprjAddr A pos)) .projTable ∨
        ∃ j, cn.name = Ix.Kernel.auxKey (Ix.Kernel.projTableName (Core.keyOf t (Core.iprjAddr A pos))) (.projFn j) := by
    intro cn hcn
    obtain ⟨pos, hpos, _, ⟨_, _, hnm, -⟩ | ⟨j, _, hnm⟩⟩ := hres.kindAndName cn hcn
    · exact ⟨pos, hpos, Or.inl hnm⟩
    · exact ⟨pos, hpos, Or.inr ⟨j, hnm⟩⟩
  have hext : Ix.Kernel.EnvExt env ⟨(pcs ++ (new' ++ as)) ++ env.consts⟩ := by
    rw [hassoc]; exact hres.envExt
  have hS₃ : Decl.FoldStoreInv ⟨(pcs ++ (new' ++ as)) ++ env.consts⟩ := by
    rw [hassoc]; exact hres.foldStore
  have hAr : Ix.Kernel.Model.StoreArR ⟨(pcs ++ (new' ++ as)) ++ env.consts⟩ := by
    rw [hassoc]; exact hres.storeArR
  have hTL : Ix.Kernel.ThmLevels ⟨(pcs ++ (new' ++ as)) ++ env.consts⟩ := by
    rw [hassoc]; exact hres.thmLevels
  have hroot : Decl.AuxRootSynced ⟨(pcs ++ (new' ++ as)) ++ env.consts⟩ := by
    rw [hassoc]; exact hres.auxRoot
  have hES : Decl.EtaStable ⟨(pcs ++ (new' ++ as)) ++ env.consts⟩ := by
    rw [hassoc]
    exact etaStable_famStep_proj hC.etaStable hC.etaCtorStored hg hd hres.envExt hnoInd
  have hmemName : ∀ ci ∈ new', ∃ x, FamAddr A c rb crb x ∧ ci.name = keyOf t x := by
    intro ci hci
    obtain ⟨ci₀, hci₀, hn⟩ := hnewN ci hci
    obtain ⟨x, hx, hk, -⟩ := hreads.2.1 ci₀ hci₀
    exact ⟨x, hx, hn.trans hk⟩
  have hAl := AliasGroup.defn_of_mem hg
  have hnres : ∀ cn ∈ pcs ++ (new' ++ as), cn.name ≠ Core.unresolvedKey := by
    intro cn hcn
    rcases List.mem_append.mp hcn with hm | hm
    · obtain ⟨pos, -, hnm | ⟨j, hnm⟩⟩ := hpcsAux cn hm
      · intro he
        rw [hnm] at he
        have h1 : Core.keyOf t (Core.iprjAddr A pos) = .aux (.role default) .projTable :=
          (Ix.Kernel.Key.aux.inj he).1
        have hbase := Decl.isBaseKey_keyOf t (Core.iprjAddr A pos)
        rw [h1] at hbase
        exact Bool.false_ne_true hbase
      · intro he
        rw [hnm] at he
        have h2 := (Ix.Kernel.Key.aux.inj he).2
        cases h2
    · rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨x, -, hk⟩ := hmemName cn hm
        rw [hk]
        exact (Core.Resolved.ne : Core.keyOf t x ≠ Core.unresolvedKey)
      · intro he
        exact (hAl cn hm).2 (.aux (.role default) .projTable) he
  exact
    { model := fun V _ => by rw [hassoc]; exact hres.model V (hC.model V)
      store := hS₃.store
      recShape := hS₃.recShape
      recK := hS₃.recK
      thmTyped := hS₃.thmTyped
      defnTyped := hS₃.defnTyped
      etaTowers := hS₃.etaTowers
      thmLevels := hTL
      storeArR := hAr
      strong := hS₃.strongProps
      fams := fun f hf => (hC.fams f hf).ext hL hext
      complete := by
        intro P cm ip cv caps hf hr hcm hinfo hnat
        cases hold : env.find? (keyOf t P) with
        | some ci =>
          have h₂ := hext.find hold
          rw [hf] at h₂
          obtain rfl := Option.some.inj h₂
          exact hC.complete P cm ip cv caps hold hr hcm hinfo hnat
        | none =>
          exfalso
          rcases find?_append_cases (pcs ++ (new' ++ as)) hf with hm | ho
          · rcases List.mem_append.mp hm with hmp | hm'
            · exact hnoInd _ hmp cv caps rfl
            · rcases List.mem_append.mp hm' with hm'' | hm''
              · obtain ⟨x, hx, hk⟩ := hmemName _ hm''
                have hP : P = x :=
                  Core.keyOf_inj hC.tableWf ((Core.WhnfAux.name_of_find hf).symm.trans hk)
                subst hP
                exact hmod P hx cm ip hcm hinfo hnat
              · obtain ⟨⟨cv', v, hint, he⟩, -⟩ := hAl _ hm''
                exact nomatch he
          · rw [hold] at ho
            exact nomatch ho
      completeCtor := by
        intro C cm cp cv nP nF hf hr hcm hinfo hnat
        cases hold : env.find? (keyOf t C) with
        | some ci =>
          have h₂ := hext.find hold
          rw [hf] at h₂
          obtain rfl := Option.some.inj h₂
          exact hC.completeCtor C cm cp cv nP nF hold hr hcm hinfo hnat
        | none =>
          exfalso
          rcases find?_append_cases (pcs ++ (new' ++ as)) hf with hm | ho
          · rcases List.mem_append.mp hm with hmp | hm'
            · exact hnoCtor _ hmp cv nP nF rfl
            · rcases List.mem_append.mp hm' with hm'' | hm''
              · obtain ⟨x, hx, hk⟩ := hmemName _ hm''
                have hCeq : C = x :=
                  Core.keyOf_inj hC.tableWf ((Core.WhnfAux.name_of_find hf).symm.trans hk)
                subst hCeq
                exact hmodCtor C hx cm cp hcm hinfo hnat
              · obtain ⟨⟨cv', v, hint, he⟩, -⟩ := hAl _ hm''
                exact nomatch he
          · rw [hold] at ho
            exact nomatch ho
      recRhsPw := recRhsPwNoModel_step hext hC.recRhsPw (by
        intro k cv mI rP rls hf hold _ hnm
        exfalso
        have hf_a : (⟨pcs ++ ((new' ++ as) ++ env.consts)⟩ : Ix.Kernel.Env .anon).find? k =
            some (.recInfo cv mI rP rls) := by
          rw [← hassoc]; exact hf
        have hf₂ : (⟨(new' ++ as) ++ env.consts⟩ : Ix.Kernel.Env .anon).find? k =
            some (.recInfo cv mI rP rls) := by
          rcases find?_append_cases (env := ⟨(new' ++ as) ++ env.consts⟩) pcs hf_a with hmp | ho
          · exact (hnoRec _ hmp cv mI rP rls rfl).elim
          · exact ho
        have hnone_as : (⟨as ++ env.consts⟩ : Ix.Kernel.Env .anon).find? k = none := by
          cases hfa : (⟨as ++ env.consts⟩ : Ix.Kernel.Env .anon).find? k with
          | none => rfl
          | some ci =>
            rcases find?_append_cases as hfa with hma | hoa
            · have hki : ci.name = k := Core.WhnfAux.name_of_find hfa
              rcases find?_append_cases (new' ++ as) hf₂ with hmn | hon
              · rcases List.mem_append.mp hmn with hmn' | hma'
                · obtain ⟨x, -, hkx⟩ := hmemName _ hmn'
                  obtain ⟨n, d, hka⟩ := AliasGroup.name_aux hg ci hma
                  exact (keyOf_nonAux t x n d
                    (hkx.symm.trans ((Core.WhnfAux.name_of_find hf₂).trans (hki.symm.trans hka)))).elim
                · obtain ⟨⟨_, _, _, he⟩, -⟩ := hAl _ hma'
                  exact nomatch he
              · rw [hold] at hon; cases hon
            · rw [hold] at hoa; cases hoa
        obtain ⟨cvm, mv, hint, hm₂⟩ := Decl.FamilyAlias.hasModel_declIndRenJ hd hf₂ hnone_as
        have hm₃ := hres.find₂ hm₂
        rw [← hassoc] at hm₃
        exact hnm ⟨cvm, mv, hint, hm₃⟩)
      recModelNotNative := recHasModelNotNative_step hext hC.recModelNotNative (by
        intro a cv mI rP rls cHost rc n p cmP ipP hf hm hcase hrc hmc hcmP hipP
        cases hold : env.find? (keyOf t a) with
        | none =>
          rcases find?_append_cases (pcs ++ (new' ++ as)) hf with hmn | ho
          · rcases List.mem_append.mp hmn with hmp | hmn'
            · exact (hnoRec _ hmp cv mI rP rls rfl).elim
            · exact (hrecs cv mI rP rls hmn').notNative a cHost rc n p cmP ipP
                (Core.WhnfAux.name_of_find hf) hrc hmc hcmP hipP
          · rw [hold] at ho; cases ho
        | some ci_old =>
          exfalso
          have hnm₀ : ¬ Ix.Kernel.Model.HasModel env (keyOf t a) := by
            rcases hcase with hnone | hnm₀
            · rw [hold] at hnone; cases hnone
            · exact hnm₀
          obtain ⟨cvm, mv, hint, hfm⟩ := hm
          rcases find?_append_cases (pcs ++ (new' ++ as)) hfm with hmn | ho
          · rcases List.mem_append.mp hmn with hmp | hmn'
            · exact hnoDefn _ hmp cvm mv hint rfl
            · rcases List.mem_append.mp hmn' with hmn'' | hma
              · obtain ⟨x, -, hkx⟩ := hmemName _ hmn''
                exact keyOf_nonAux t x (keyOf t a) .model
                  (hkx.symm.trans (Core.WhnfAux.name_of_find hfm))
              · obtain ⟨ci_b, hci_b, hbase⟩ := hroots _ hma
                have hfm_name : (ConstantInfo.defnInfo cvm mv hint).name =
                    Ix.Kernel.auxKey (keyOf t a) .model := Core.WhnfAux.name_of_find hfm
                rw [hfm_name] at hbase
                have hba : (Ix.Kernel.auxKey (keyOf t a) .model).base = keyOf t a :=
                  Decl.base_of_isBaseKey (Decl.isBaseKey_keyOf t a)
                rw [hba] at hbase
                have hblk_fresh : ∀ ci ∈ blk, env.find? ci.name = none := by
                  have hmem_fresh : ∀ {J : Ix.Kernel.Semantics.Judgements .anon}
                      {env₁ env₂' : Ix.Kernel.Env .anon} {ns : List (Key .anon)}
                      {caps : Ix.Kernel.IndCaps .anon} {xs : List (ConstantInfo .anon)},
                      Ix.Kernel.Semantics.IndMembersRunJ J ns caps env₁ xs env₂' →
                      ∀ ci ∈ xs, env₁.find? ci.name = none := by
                    intro J env₁ env₂' ns caps xs hm
                    induction xs generalizing env₁ with
                    | nil => intro _ h; cases h
                    | cons c rest ih =>
                      obtain ⟨cvA, hmv, hrest⟩ := hm
                      obtain ⟨type', hcv, hcvA, -⟩ := hmv
                      have hc_fr : env₁.find? c.toConstantVal.name = none :=
                        Option.isNone_iff_eq_none.mp hcv.1
                      intro ci hci
                      cases c with
                      | indInfo _ _ =>
                        have hc_ext : Ix.Kernel.EnvExt env₁ ⟨.indInfo cvA caps :: env₁.consts⟩ :=
                          Ix.Kernel.Semantics.envExt_of_constantValRunJ hcv (by rw [hcvA]; rfl)
                        rcases List.mem_cons.mp hci with rfl | hci'
                        · exact hc_fr
                        · have hr := ih hrest ci hci'
                          cases hf' : env₁.find? ci.name with
                          | none => rfl
                          | some x =>
                            have h2 := hc_ext.find hf'
                            rw [hr] at h2; cases h2
                      | ctorInfo _ nP nF =>
                        have hc_ext : Ix.Kernel.EnvExt env₁ ⟨.ctorInfo cvA nP nF :: env₁.consts⟩ :=
                          Ix.Kernel.Semantics.envExt_of_constantValRunJ hcv (by rw [hcvA]; rfl)
                        rcases List.mem_cons.mp hci with rfl | hci'
                        · exact hc_fr
                        · have hr := ih hrest ci hci'
                          cases hf' : env₁.find? ci.name with
                          | none => rfl
                          | some x =>
                            have h2 := hc_ext.find hf'
                            rw [hr] at h2; cases h2
                      | _ => exact hrest.elim
                  have hprov_fresh : ∀ {J : Ix.Kernel.Semantics.Judgements .anon}
                      {env₁ envS : Ix.Kernel.Env .anon} {ns : List (Key .anon)}
                      {xs : List (ConstantInfo .anon)} {chk},
                      Ix.Kernel.Semantics.ProvisionRecsRunJ J ns env₁ xs envS chk →
                      ∀ ci ∈ xs, env₁.find? ci.name = none := by
                    intro J env₁ envS ns xs chk hp
                    induction xs generalizing env₁ chk with
                    | nil => intro _ h; cases h
                    | cons c rest ih =>
                      obtain ⟨cvA, mI', rP', rls', rest', hc_eq, hmv, hrest, -⟩ := hp
                      obtain ⟨type', hcv, hcvA, -⟩ := hmv
                      have hc_fr : env₁.find? c.name = none := by
                        rw [hc_eq]; exact Option.isNone_iff_eq_none.mp hcv.1
                      have hc_ext : Ix.Kernel.EnvExt env₁ ⟨.recInfo cvA mI' rP' [] :: env₁.consts⟩ :=
                        Ix.Kernel.Semantics.envExt_of_constantValRunJ hcv (by rw [hcvA]; rfl)
                      intro ci hci
                      rcases List.mem_cons.mp hci with rfl | hci'
                      · exact hc_fr
                      · have hr := ih hrest ci hci'
                        cases hf' : env₁.find? ci.name with
                        | none => rfl
                        | some x =>
                          have h2 := hc_ext.find hf'
                          rw [hr] at h2; cases h2
                  obtain ⟨hsplit, envM, hmemR, hrecsR⟩ := hd.shape
                  have hmem_ext : Ix.Kernel.EnvExt ⟨as ++ env.consts⟩ envM :=
                    Ix.Kernel.Semantics.indMembersRunJ_envExt hmemR
                  intro ci hci
                  have hext_as : Ix.Kernel.EnvExt env ⟨as ++ env.consts⟩ :=
                    Decl.FamilyAlias.AliasGroup.envExt hg
                  rw [hsplit] at hci
                  rcases List.mem_append.mp hci with hm | hr
                  · have hfr_as := hmem_fresh hmemR ci hm
                    cases hf' : env.find? ci.name with
                    | none => rfl
                    | some x =>
                      have h2 := hext_as.find hf'
                      rw [hfr_as] at h2; cases h2
                  · rcases hrecsR with ⟨hnil, -⟩ | ⟨-, -, _, _, hprov, -⟩
                    · rw [hnil] at hr; cases hr
                    · have hfr_M := hprov_fresh hprov ci hr
                      cases hf' : env.find? ci.name with
                      | none => rfl
                      | some x =>
                        have h2 := (hext_as.trans hmem_ext).find hf'
                        rw [hfr_M] at h2; cases h2
                have hfr_b := hblk_fresh ci_b hci_b
                rw [← hbase, hold] at hfr_b
                cases hfr_b
          · exact hnm₀ ⟨cvm, mv, hint, ho⟩)
      hashKeyed := HashKeyed.append hC.tableWf hC.hashKeyed (fun ci hci => by
        rcases List.mem_append.mp hci with hmp | hm
        · obtain ⟨pos, -, hnm | ⟨j, hnm⟩⟩ := hpcsAux ci hmp
          · exact Or.inr fun y he => keyOf_nonAux t y _ .projTable (he.symm.trans hnm)
          · exact Or.inr fun y he => keyOf_nonAux t y _ (.projFn j) (he.symm.trans hnm)
        · rcases List.mem_append.mp hm with hm' | hm'
          · obtain ⟨x, hx, hk⟩ := hmemName ci hm'
            exact Or.inl ⟨x, hk, hsz x hx⟩
          · obtain ⟨n, d, hn⟩ := AliasGroup.name_aux hg ci hm'
            exact Or.inr fun y he => keyOf_nonAux t y n d (he.symm.trans hn))
      auxRoot := hroot
      etaCtorStored := hS₃.etaCtorStored
      etaShape := hS₃.etaShape
      etaStable := hES
      unresolved := unresolved_append hC.unresolved hnres
      tableWf := hC.tableWf
      companions := coreCompanions_append_recs (c := ⟨E, env, t, lim⟩) hC.companions hC.store
        hext (fun cv mI rP rls hm => by
          rcases List.mem_append.mp hm with hmp | hmn
          · exact (hnoRec _ hmp cv mI rP rls rfl).elim
          · rw [hassoc]
            exact (hrecs cv mI rP rls hmn).of_append_noCtor hnoCtor)
      loads := storedLoads_append (c := ⟨E, env, t, lim⟩) hC.loads hext hnres hC.etaStable
        hloads }

/-- **The keeping the family row's step takes** (`hkeeps` of `unitStepFamily_of_facts`), at the
fold's clause (module docstring), at the record that installs the family check's selected forms
and modeled projection tables, with the check's facts and a fact `Sel` of the selected forms
handed to `hrecs` and `hloads`. -/
theorem famStepKeeps_foldExtra
    (hL : LinkLaws FormerOpenTraceAt) {t : Ix.Kernel.RoleTable} {envT : Ix.Kernel.Env .anon}
    {E₀ E : Ixon.Env} {lim : Option Nat} {A rb : _root_.Address} {c crb : Ixon.Constant}
    {ms : Array Ixon.MutConst}
    {Sel : Ix.Kernel.Env .anon → List (ConstantInfo .anon) → Decl.FamilyAlias.FamilyAdvice →
      List IxVM.Refinement.Core.KExpr → List (List IxVM.Refinement.Core.KExpr) → Prop}
    (hsz : ∀ x, FamAddr A c rb crb x → x.hash.size = 32)
    (hmod : ∀ x, FamAddr A c rb crb x → ∀ (cm : Ixon.Constant) (ip : Ixon.InductiveProj),
      Ix.Cert.recordAt E x = some cm → cm.info = .iPrj ip → ¬ NativeAt E ip.block)
    (hmodCtor : ∀ x, FamAddr A c rb crb x → ∀ (cm : Ixon.Constant) (cp : Ixon.ConstructorProj),
      Ix.Cert.recordAt E x = some cm → cm.info = .cPrj cp → ¬ NativeAt E cp.block)
    (hrecs : ∀ (env : Ix.Kernel.Env .anon) (h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon)
      (aliases blk new : List (ConstantInfo .anon)) (adv' : Decl.FamilyAlias.FamilyAdvice)
      (tys : List IxVM.Refinement.Core.KExpr) (rhsss : List (List IxVM.Refinement.Core.KExpr)),
      Decl.PrefixInv.{u} E t lim env → AliasGroup env h aliases →
      FamDeclReads t E₀ A c rb crb blk →
      Decl.FamilyAlias.FamilyCheckFacts env blk adv' tys rhsss → Sel env blk adv' tys rhsss →
      DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ blk ⟨new ++ env.consts⟩ →
      (∀ ci ∈ blk, ∃ c', (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find? ci.name = some c' ∧
        StoredAs c' ci) →
      SelectedInstalled blk tys rhsss ⟨new ++ env.consts⟩ →
      ∀ cv mI rP rls, ConstantInfo.recInfo cv mI rP rls ∈ new →
        RecCompanionFacts ⟨E, ⟨new ++ env.consts⟩, t, lim⟩ cv mI rP rls)
    (hloads : ∀ (env : Ix.Kernel.Env .anon) (Reg : NativeFam .anon → Prop)
      (h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon)
      (aliases blk new : List (ConstantInfo .anon)) (adv' : Decl.FamilyAlias.FamilyAdvice)
      (tys : List IxVM.Refinement.Core.KExpr) (rhsss : List (List IxVM.Refinement.Core.KExpr))
      (bpf : BlockProjFacts t E₀ E env A c ms blk tys adv'.ren)
      (pcs : List (ConstantInfo .anon)),
      Decl.PrefixInv.{u} E t lim env → (∀ ci ∈ envT.consts, ci ∈ env.consts) →
      (∀ x, UsedRef E₀ A x ∨ UsedRef E₀ rb x →
        (env.find? (keyOf t x)).isSome = true ∨ FamAddr A c rb crb x ∨ ¬ NeedOk E₀ x) →
      (∀ x, FamAddr A c rb crb x → env.find? (keyOf t x) = none) →
      AliasGroup env h aliases →
      FamDeclReads t E₀ A c rb crb blk →
      Decl.FamilyAlias.FamilyCheckFacts env blk adv' tys rhsss → Sel env blk adv' tys rhsss →
      DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ blk ⟨new ++ env.consts⟩ →
      (∀ ci ∈ blk, ∃ c', (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find? ci.name = some c' ∧
        StoredAs c' ci) →
      SelectedInstalled blk tys rhsss ⟨new ++ env.consts⟩ →
      BlockProjInstallResult.{u} t env ⟨new ++ env.consts⟩ Reg A ms bpf.elig pcs →
      NewLoads (appCtx ⟨E, env, t, lim⟩ (pcs ++ new)).stored (pcs ++ new)) :
    ∀ (env env₂ : Ix.Kernel.Env .anon) (Reg : NativeFam .anon → Prop)
      (h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon)
      (aliases blk : List (ConstantInfo .anon)) (adv' : Decl.FamilyAlias.FamilyAdvice)
      (tys : List IxVM.Refinement.Core.KExpr) (rhsss : List (List IxVM.Refinement.Core.KExpr))
      (bpf : BlockProjFacts t E₀ E env A c ms blk tys adv'.ren)
      (pcs : List (ConstantInfo .anon)),
      Decl.PrefixInv.{u} E t lim env → FoldExtra.{u} FormerOpenTraceAt t E env →
      FamRegistryWith.{u} FormerOpenTraceAt t E env Reg →
      (∀ ci ∈ envT.consts, ci ∈ env.consts) →
      (∀ x, UsedRef E₀ A x ∨ UsedRef E₀ rb x →
        (env.find? (keyOf t x)).isSome = true ∨ FamAddr A c rb crb x ∨ ¬ NeedOk E₀ x) →
      (∀ x, FamAddr A c rb crb x → env.find? (keyOf t x) = none) →
      AliasGroup env h aliases → (∀ a ∈ aliases, ∃ ci ∈ blk, a.name.base = ci.name) →
      FamDeclReads t E₀ A c rb crb blk →
      Decl.FamilyAlias.FamilyCheckFacts env blk adv' tys rhsss → Sel env blk adv' tys rhsss →
      DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ blk env₂ →
      (∀ ci ∈ blk, ∃ c', env₂.find? ci.name = some c' ∧ StoredAs c' ci) →
      SelectedInstalled blk tys rhsss env₂ →
      BlockProjInstallResult.{u} t env env₂ Reg A ms bpf.elig pcs →
      Decl.PrefixInv.{u} E t lim ⟨pcs ++ env₂.consts⟩ ∧
        FoldExtra.{u} FormerOpenTraceAt t E ⟨pcs ++ env₂.consts⟩ := by
  intro env env₂ Reg h as blk adv' tys rhsss bpf pcs hinv hX hR hextT hrefs hfresh hg hroots
    hreads hF hSel hd hst hI hres
  obtain ⟨⟨⟨-, hkeys⟩, haux⟩, hlv⟩ := hX
  have hC : FoldClauseWith.{u} FormerOpenTraceAt t E lim env Reg :=
    FoldClauseWith.of_prefix hinv hR hkeys haux hlv
  obtain ⟨new, henv, -, -⟩ := famStep_consts hd
  subst henv
  have hassoc : (⟨pcs ++ ((new ++ as) ++ env.consts)⟩ : Ix.Kernel.Env .anon) =
      ⟨(pcs ++ (new ++ as)) ++ env.consts⟩ := by
    simp [List.append_assoc]
  have hC' := famStepKeeps_with hL hsz hmod hmodCtor hC hg hroots hreads hd hres
    (hrecs env h as blk (new ++ as) adv' tys rhsss hinv hg hreads hF hSel hd hst hI)
    (hloads env Reg h as blk (new ++ as) adv' tys rhsss bpf pcs hinv hextT hrefs hfresh hg hreads
      hF hSel hd hst hI hres)
  rw [hassoc]
  exact ⟨hC'.prefixInv, hC'.extra⟩

end IxVM.Refinement.Typing.FamilyAlias
