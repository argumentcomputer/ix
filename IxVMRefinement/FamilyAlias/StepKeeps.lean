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
        have hkn : cv.name = k := beq_iff_eq.mp (List.find?_some hf)
        rcases find?_append_cases new hf with hm | hf'
        · exact Or.inr (hkn ▸ (hrec cv mI rP rls hm).noK)
        · exact (h.ruleCtorHead k cv mI rP rls hf').imp
            (fun hh rl cvj nP nF T us hrl hc hdom =>
              hh rl cvj nP nF T us hrl (oldRuleCtor hf' hrl hc) hdom)
            id }

/-! ## The keeping -/

/-- **The fold's clause across the family step, at one registry**: the clause at the prefix with
the registry `Reg` gives the clause after the step with the same registry (the step registers no
family: no inductive it stores is at an address whose projection record names a block the circuit
treats as native, `hmod`), from the record, the addresses' length, the companion facts of each
new recursor and the load facts at the new constants. -/
theorem famStepKeeps_with {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {lim : Option Nat} {A rb : _root_.Address} {c crb : Ixon.Constant}
    (hsz : ∀ x, FamAddr A c rb crb x → x.hash.size = 32)
    (hmod : ∀ x, FamAddr A c rb crb x → ∀ (cm : Ixon.Constant) (ip : Ixon.InductiveProj),
      Ix.Cert.recordAt E x = some cm → cm.info = .iPrj ip → ¬ NativeAt E ip.block)
    {env : Ix.Kernel.Env .anon} {Reg : NativeFam .anon → Prop}
    {h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon} {as blk new : List (ConstantInfo .anon)}
    (hC : FoldClauseWith.{u} L t E lim env Reg) (hg : AliasGroup env h as)
    (hroots : ∀ a ∈ as, ∃ ci ∈ blk, a.name.base = ci.name)
    (hreads : FamDeclReads t E₀ A c rb crb blk)
    (hd : DeclIndRenRunJ (famJ h) ⟨as ++ env.consts⟩ blk ⟨new ++ env.consts⟩)
    (hrecs : ∀ cv mI rP rls, ConstantInfo.recInfo cv mI rP rls ∈ new →
      RecCompanionFacts ⟨E, ⟨new ++ env.consts⟩, t, lim⟩ cv mI rP rls)
    (hloads : NewLoads (appCtx ⟨E, env, t, lim⟩ new).stored new) :
    FoldClauseWith.{u} L t E lim ⟨new ++ env.consts⟩ Reg := by
  have hna : ∀ ci ∈ blk, Decl.NonAuxKey ci.name := fun ci hci => by
    obtain ⟨x, -, hk, -⟩ := hreads.2.1 ci hci
    rw [hk]
    exact Decl.isBaseKey_iff_nonAuxKey.mp (Decl.isBaseKey_keyOf t x)
  obtain ⟨new', henv, hnewN, -⟩ := famStep_consts hd
  have hnew : new = new' ++ as := by
    have h2 : new ++ env.consts = (new' ++ as) ++ env.consts :=
      congrArg Ix.Kernel.Env.consts henv
    exact List.append_cancel_right h2
  subst hnew
  have hext : Ix.Kernel.EnvExt env ⟨(new' ++ as) ++ env.consts⟩ :=
    (Decl.FamilyAlias.AliasGroup.envExt hg).trans (Ix.Kernel.Semantics.declIndRenRunJ_envExt hd)
  have hS₂ : Decl.FoldStoreInv ⟨(new' ++ as) ++ env.consts⟩ :=
    Decl.FamilyAlias.foldStoreInv_famStep hg hreads.2.2.2 hna hd hC.foldStore
  have hAr : Ix.Kernel.Model.StoreArR ⟨(new' ++ as) ++ env.consts⟩ :=
    Decl.FamilyAlias.familyKeepsStoreAr env _ h as blk hg hd hC.storeArR
  have hTL : Ix.Kernel.ThmLevels ⟨(new' ++ as) ++ env.consts⟩ :=
    Decl.FamilyAlias.thmLevels_famStep hg hd hC.thmLevels
  have hroot : Decl.AuxRootSynced ⟨(new' ++ as) ++ env.consts⟩ :=
    Decl.FamilyAlias.auxRootSynced_famStep hC.auxRoot hna hroots hd
  have hES : Decl.EtaStable ⟨(new' ++ as) ++ env.consts⟩ :=
    etaStable_famStep hC.etaStable hC.etaCtorStored hg hd
  have hmemName : ∀ ci ∈ new', ∃ x, FamAddr A c rb crb x ∧ ci.name = keyOf t x := by
    intro ci hci
    obtain ⟨ci₀, hci₀, hn⟩ := hnewN ci hci
    obtain ⟨x, hx, hk, -⟩ := hreads.2.1 ci₀ hci₀
    exact ⟨x, hx, hn.trans hk⟩
  have hAl := AliasGroup.defn_of_mem hg
  have hnres : ∀ cn ∈ new' ++ as, cn.name ≠ Core.unresolvedKey := by
    intro cn hcn
    rcases List.mem_append.mp hcn with hm | hm
    · obtain ⟨x, -, hk⟩ := hmemName cn hm
      rw [hk]
      exact (Core.Resolved.ne : Core.keyOf t x ≠ Core.unresolvedKey)
    · intro he
      exact (hAl cn hm).2 (.aux (.role default) .projTable) he
  exact
    { model := fun V _ => Decl.FamilyAlias.envModelN_famStep hg hd V (hC.model V)
      store := hS₂.store
      recShape := hS₂.recShape
      recK := hS₂.recK
      thmTyped := hS₂.thmTyped
      etaTowers := hS₂.etaTowers
      thmLevels := hTL
      storeArR := hAr
      strong := hS₂.strongProps
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
          rcases find?_append_cases (new' ++ as) hf with hm | ho
          · rcases List.mem_append.mp hm with hm' | hm'
            · obtain ⟨x, hx, hk⟩ := hmemName _ hm'
              have hP : P = x :=
                Core.keyOf_inj hC.tableWf ((Core.WhnfAux.name_of_find hf).symm.trans hk)
              subst hP
              exact hmod P hx cm ip hcm hinfo hnat
            · obtain ⟨⟨cv', v, hint, he⟩, -⟩ := hAl _ hm'
              exact nomatch he
          · rw [hold] at ho
            exact nomatch ho
      hashKeyed := HashKeyed.append hC.tableWf hC.hashKeyed (fun ci hci => by
        rcases List.mem_append.mp hci with hm | hm
        · obtain ⟨x, hx, hk⟩ := hmemName ci hm
          exact Or.inl ⟨x, hk, hsz x hx⟩
        · obtain ⟨n, d, hn⟩ := AliasGroup.name_aux hg ci hm
          exact Or.inr fun y he => keyOf_nonAux t y n d (he.symm.trans hn))
      auxRoot := hroot
      etaCtorStored := hS₂.etaCtorStored
      etaShape := hS₂.etaShape
      etaStable := hES
      unresolved := unresolved_append hC.unresolved hnres
      tableWf := hC.tableWf
      companions := coreCompanions_append_recs (c := ⟨E, env, t, lim⟩) hC.companions hC.store
        hext hrecs
      loads := storedLoads_append (c := ⟨E, env, t, lim⟩) hC.loads hext hnres hC.etaStable
        hloads }

/-- **The keeping the family row's step takes** (`hkeeps` of `unitStepFamily_of_facts`), at the
fold's clause (module docstring), at the record that installs the family check's selected forms,
with the check's facts and a fact `Sel` of the selected forms handed to `hrecs` and `hloads`. -/
theorem famStepKeeps_foldExtra {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {t : Ix.Kernel.RoleTable} {envT : Ix.Kernel.Env .anon} {E₀ E : Ixon.Env}
    {lim : Option Nat} {A rb : _root_.Address} {c crb : Ixon.Constant}
    {Sel : Ix.Kernel.Env .anon → List (ConstantInfo .anon) → List IxVM.Refinement.Core.KExpr →
      List (List IxVM.Refinement.Core.KExpr) → Prop}
    (hsz : ∀ x, FamAddr A c rb crb x → x.hash.size = 32)
    (hmod : ∀ x, FamAddr A c rb crb x → ∀ (cm : Ixon.Constant) (ip : Ixon.InductiveProj),
      Ix.Cert.recordAt E x = some cm → cm.info = .iPrj ip → ¬ NativeAt E ip.block)
    (hrecs : ∀ (env : Ix.Kernel.Env .anon) (h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon)
      (aliases blk new : List (ConstantInfo .anon)) (adv' : Decl.FamilyAlias.FamilyAdvice)
      (tys : List IxVM.Refinement.Core.KExpr) (rhsss : List (List IxVM.Refinement.Core.KExpr)),
      Decl.PrefixInv.{u} E t lim env → AliasGroup env h aliases →
      FamDeclReads t E₀ A c rb crb blk →
      Decl.FamilyAlias.FamilyCheckFacts env blk adv' tys rhsss → Sel env blk tys rhsss →
      DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ blk ⟨new ++ env.consts⟩ →
      (∀ ci ∈ blk, ∃ c', (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find? ci.name = some c' ∧
        StoredAs c' ci) →
      SelectedInstalled blk tys rhsss ⟨new ++ env.consts⟩ →
      ∀ cv mI rP rls, ConstantInfo.recInfo cv mI rP rls ∈ new →
        RecCompanionFacts ⟨E, ⟨new ++ env.consts⟩, t, lim⟩ cv mI rP rls)
    (hloads : ∀ (env : Ix.Kernel.Env .anon) (h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon)
      (aliases blk new : List (ConstantInfo .anon)) (adv' : Decl.FamilyAlias.FamilyAdvice)
      (tys : List IxVM.Refinement.Core.KExpr) (rhsss : List (List IxVM.Refinement.Core.KExpr)),
      Decl.PrefixInv.{u} E t lim env → (∀ ci ∈ envT.consts, ci ∈ env.consts) →
      (∀ x, UsedRef E₀ A x ∨ UsedRef E₀ rb x →
        (env.find? (keyOf t x)).isSome = true ∨ FamAddr A c rb crb x ∨ ¬ NeedOk E₀ x) →
      AliasGroup env h aliases →
      FamDeclReads t E₀ A c rb crb blk →
      Decl.FamilyAlias.FamilyCheckFacts env blk adv' tys rhsss → Sel env blk tys rhsss →
      DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ blk ⟨new ++ env.consts⟩ →
      (∀ ci ∈ blk, ∃ c', (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find? ci.name = some c' ∧
        StoredAs c' ci) →
      SelectedInstalled blk tys rhsss ⟨new ++ env.consts⟩ →
      NewLoads (appCtx ⟨E, env, t, lim⟩ new).stored new) :
    ∀ (env env₂ : Ix.Kernel.Env .anon) (h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon)
      (aliases blk : List (ConstantInfo .anon)) (adv' : Decl.FamilyAlias.FamilyAdvice)
      (tys : List IxVM.Refinement.Core.KExpr) (rhsss : List (List IxVM.Refinement.Core.KExpr)),
      Decl.PrefixInv.{u} E t lim env → FoldExtra.{u} L t E env →
      (∀ ci ∈ envT.consts, ci ∈ env.consts) →
      (∀ x, UsedRef E₀ A x ∨ UsedRef E₀ rb x →
        (env.find? (keyOf t x)).isSome = true ∨ FamAddr A c rb crb x ∨ ¬ NeedOk E₀ x) →
      AliasGroup env h aliases → (∀ a ∈ aliases, ∃ ci ∈ blk, a.name.base = ci.name) →
      FamDeclReads t E₀ A c rb crb blk →
      Decl.FamilyAlias.FamilyCheckFacts env blk adv' tys rhsss → Sel env blk tys rhsss →
      DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ blk env₂ →
      (∀ ci ∈ blk, ∃ c', env₂.find? ci.name = some c' ∧ StoredAs c' ci) →
      SelectedInstalled blk tys rhsss env₂ →
      Decl.PrefixInv.{u} E t lim env₂ ∧ FoldExtra.{u} L t E env₂ := by
  intro env env₂ h as blk adv' tys rhsss hinv hX hextT hrefs hg hroots hreads hF hSel hd hst hI
  obtain ⟨⟨⟨⟨Reg, hR⟩, hkeys⟩, haux⟩, hlv⟩ := hX
  have hC : FoldClauseWith.{u} L t E lim env Reg := FoldClauseWith.of_prefix hinv hR hkeys haux hlv
  obtain ⟨new, henv, -, -⟩ := famStep_consts hd
  subst henv
  have hC' := famStepKeeps_with hL hsz hmod hC hg hroots hreads hd
    (hrecs env h as blk (new ++ as) adv' tys rhsss hinv hg hreads hF hSel hd hst hI)
    (hloads env h as blk (new ++ as) adv' tys rhsss hinv hextT hrefs hg hreads hF hSel hd hst hI)
  exact ⟨hC'.prefixInv, hC'.extra⟩

end IxVM.Refinement.Typing.FamilyAlias
