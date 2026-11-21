import IxVMRefinement.FamilyAlias.RecsModeledStep
import IxVMRefinement.FamilyAlias.StepOfSeam
import IxVMRefinement.FamilyAlias.Selected
import IxVMRefinement.FamilyAlias.ProjTableInstall
import IxVMRefinement.Assembly.FoldClause

/-! # The family row's step, its model half

`unitStepFamily_of_facts`: a statement of the type of the family row's step (`UnitStepFamily` at
the fold's clause with the family recursors' companions beside it, the type
`FamilyBlockRow` asks), from the target's conclusion assembled at each environment the step is
handed (`famStepConclusion_of_facts`) and these named premises:

* `hseam`: the circuit side's seam at the step's hypotheses (the family as read, the facts of
  the family check at the prefix, and a fact `Sel` of the check's selected annotated types and
  right-hand sides);
* `hkey`: key freedom of the family's addresses at every environment the step is asked at, where
  none of them is stored (the target's hypothesis; `familyKeyFree_of_shape` produces it);
* `heqPin`: the pinned equality at every environment the step is asked at (`eqPin_of_shape`
  with the step context's table shape);
* `hclaim`: a member of the block at the key of a claimed family record's constant address is a
  recursor (a fact of the family graph);
* `hkeeps`: the prefix invariant and the fold's clause across the step's record (the companions,
  load contract and η stability of the prefix invariant, and the arity of the stored terms), at
  the record that installs the selected forms (`SelectedInstalled`), with the check's facts and
  `Sel` at them.

Everything else is proved here: the new constants are the members (a permutation of the block's
names, `declIndRunJ_names_perm`) and the aliases, with distinct names, fresh in the prefix; each
address of the family is stored as its reading; each new constant sits at an address's key or
at a derived key; the companions of the family recursors (`familyRecsModeled_famStep`). The root
synchronization the assembly needs is the clause's (`FoldExtra`'s `AuxRootSynced` part). -/

universe u

namespace IxVM.Refinement.Typing.FamilyAlias

open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)
open Ix.Kernel.Semantics (NativeFam DeclIndRenRunJ DeclIndRunJ Judgements)
open IxVM.Refinement.Typing.TwinFamily (FamilyRecsModeled)
open IxVM.Refinement.Decl.FamilyAlias (AliasGroup famJ FamilyAdvice FamilyCheckFacts isRecursor
  auxKey_ne_of_isBaseKey find?_append_none indMembersRunJ_consts_eq'
  indRecsFoldRunJ_consts_eq' provisionRecsRunJ_names_eq')

set_option linter.unusedVariables false

/-- **The constants a block's record adds** are a permutation of the block's names. -/
theorem declIndRunJ_names_perm {J : Judgements .anon} {env env₂ : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)} (h : DeclIndRunJ J env block env₂) :
    ∃ new, env₂ = ⟨new ++ env.consts⟩ ∧ (new.map (·.name)).Perm (block.map (·.name)) := by
  obtain ⟨hsplit, envM, hmem, hrecs⟩ := h
  obtain ⟨newM, heqM, hnamesM⟩ := indMembersRunJ_consts_eq' _ hmem
  rcases hrecs with ⟨hnil, rfl⟩ | ⟨_, _, envSelf, checked, hprov, hfold⟩
  · refine ⟨newM, heqM, ?_⟩
    rw [hnamesM, List.map_reverse]
    refine (List.reverse_perm _).trans ?_
    conv => rhs; rw [hsplit]
    rw [hnil, List.append_nil]
  · have hfold' : Ix.Kernel.Semantics.IndRecsFoldRunJ J (block.map (·.name)) envM envSelf
        ⟨[] ++ envM.consts⟩ checked env₂ := hfold
    obtain ⟨newR, hout, hnamesR⟩ := indRecsFoldRunJ_consts_eq' checked hfold'
    simp only [List.append_nil] at hout
    refine ⟨newR ++ newM, by rw [hout, heqM]; simp [List.append_assoc], ?_⟩
    rw [List.map_append, hnamesR, hnamesM, List.map_reverse, List.map_reverse,
      provisionRecsRunJ_names_eq' _ hprov]
    conv => rhs; rw [hsplit, List.map_append]
    exact List.perm_append_comm.trans
      (List.Perm.append (List.reverse_perm _) (List.reverse_perm _))

/-- Every alias of a group is fresh in the prefix. -/
theorem AliasGroup.fresh_prefix {env : Ix.Kernel.Env .anon}
    {h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon} {as : List (ConstantInfo .anon)}
    (hg : AliasGroup env h as) : ∀ a ∈ as, env.find? a.name = none := by
  induction hg with
  | nil _ => exact fun _ ha => nomatch ha
  | @cons h₀ h' as' n d lps ty tgt ci hg' _ hfresh _ _ _ _ _ _ _ _ _ _ ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · cases hf : env.find? (Ix.Kernel.auxKey n d) with
      | none => exact hf
      | some c =>
        rw [hg'.find_prefix _ c hf] at hfresh
        exact nomatch hfresh
    · exact ih a ha

/-- The aliases of a group have distinct names. -/
theorem AliasGroup.names_nodup {env : Ix.Kernel.Env .anon}
    {h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon} {as : List (ConstantInfo .anon)}
    (hg : AliasGroup env h as) : (as.map (·.name)).Nodup := by
  induction hg with
  | nil _ => exact List.nodup_nil
  | @cons h₀ h' as' n d lps ty tgt ci hg' _ hfresh _ _ _ _ _ _ _ _ _ _ ih =>
    refine List.nodup_cons.mpr ⟨fun hin => ?_, ih⟩
    obtain ⟨a, ha, hn⟩ := List.mem_map.mp hin
    have h1 := hg'.find_alias a ha
    have hn' : a.name = Ix.Kernel.auxKey n d := hn
    rw [hn', hfresh] at h1
    exact nomatch h1

/-- A constant an environment finds is one of its constants, under the key. -/
theorem find?_mem_name {E : Ix.Kernel.Env .anon} {k : Ix.Kernel.Key .anon}
    {c : ConstantInfo .anon} (h : E.find? k = some c) : c ∈ E.consts ∧ c.name = k := by
  have h' : E.consts.find? (·.name == k) = some c := h
  refine ⟨List.mem_of_find?_eq_some h', ?_⟩
  have hp := List.find?_some h'
  simpa using hp

/-- A constant of an environment makes its key found. -/
theorem find?_isSome_of_mem {E : Ix.Kernel.Env .anon} {c : ConstantInfo .anon}
    (h : c ∈ E.consts) : (E.find? c.name).isSome = true := by
  show (E.consts.find? (·.name == c.name)).isSome = true
  exact List.find?_isSome.mpr ⟨c, h, beq_self_eq_true _⟩

/-- **The family row's step, its model half** (module docstring). -/
theorem unitStepFamily_of_facts
    {t : Ix.Kernel.RoleTable} {envT : Ix.Kernel.Env .anon} {E₀ E : Ixon.Env}
    {lim : Option Nat} {A : _root_.Address} {c : Ixon.Constant} {ms : Array Ixon.MutConst}
    {rb : _root_.Address} {crb : Ixon.Constant} {adv : _root_.Address → Prop}
    {fam : _root_.Address → Option _root_.Address}
    {Sel : Ix.Kernel.Env .anon → List (ConstantInfo .anon) → FamilyAdvice →
      List IxVM.Refinement.Core.KExpr → List (List IxVM.Refinement.Core.KExpr) → Prop}
    (hB : FamBlockRecord E₀ A c ms)
    (hseam : ∀ env : Ix.Kernel.Env .anon,
      (∀ ci ∈ envT.consts, ci ∈ env.consts) → (env.consts.map (·.name)).Nodup →
      Decl.PrefixInv.{u} E t lim env →
      (FoldExtra.{u} FormerOpenTraceAt t E env ∧ FamilyRecsModeled t E₀ fam env) →
      (∀ x, UsedRef E₀ A x ∨ UsedRef E₀ rb x →
        (env.find? (keyOf t x)).isSome = true ∨ FamAddr A c rb crb x ∨ ¬ NeedOk E₀ x) →
      (∀ a, adv a → ∀ ca, recordOf E₀ a = some ca → ∀ x, ConstAddrOf a ca x →
        (env.find? (keyOf t x)).isSome = true) →
      (∀ a, adv a → ∀ x, UsedRef E₀ a x →
        (env.find? (keyOf t x)).isSome = true ∨ FamAddr A c rb crb x ∨ ¬ NeedOk E₀ x) →
      (∀ x, FamAddr A c rb crb x → env.find? (keyOf t x) = none) →
      ∃ (blk : List (ConstantInfo .anon)) (adv' : FamilyAdvice)
        (tys : List IxVM.Refinement.Core.KExpr)
        (rhsss : List (List IxVM.Refinement.Core.KExpr)),
        FamDeclReads t E₀ A c rb crb blk ∧ FamilyCheckFacts env blk adv' tys rhsss ∧
          Sel env blk adv' tys rhsss)
    (hkey : ∀ env : Ix.Kernel.Env .anon, (∀ ci ∈ envT.consts, ci ∈ env.consts) →
      (∀ x, FamAddr A c rb crb x → env.find? (keyOf t x) = none) →
      ∀ x, FamAddr A c rb crb x → Decl.KeyFree (keyOf t x))
    (heqPin : ∀ env : Ix.Kernel.Env .anon,
      (∀ ci ∈ envT.consts, ci ∈ env.consts) → (env.consts.map (·.name)).Nodup →
      env.find? Ix.Kernel.eqName = some Ix.Kernel.eqA)
    (hbasis : ∀ env : Ix.Kernel.Env .anon,
      (∀ ci ∈ envT.consts, ci ∈ env.consts) → (env.consts.map (·.name)).Nodup →
      ∀ ci ∈ IxVM.Refinement.TableInhabit.basisEnv.consts, env.find? ci.name = some ci)
    (hclaim : ∀ blk : List (ConstantInfo .anon), FamDeclReads t E₀ A c rb crb blk →
      ∀ (B' rb' x : _root_.Address) (crb' : Ixon.Constant), fam B' = some rb' →
        recordOf E₀ rb' = some crb' → ConstAddrOf rb' crb' x →
        ∀ ci ∈ blk, ci.name = keyOf t x → isRecursor ci = true)
    (hbpf : ∀ env blk adv' tys rhsss, Sel env blk adv' tys rhsss →
      Nonempty (BlockProjFacts t E₀ E env A c ms blk tys adv'.ren))
    (hkeeps : ∀ (env env₂ : Ix.Kernel.Env .anon) (Reg : NativeFam .anon → Prop)
      (h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon) (aliases blk : List (ConstantInfo .anon))
      (adv' : FamilyAdvice) (tys : List IxVM.Refinement.Core.KExpr)
      (rhsss : List (List IxVM.Refinement.Core.KExpr))
      (bpf : BlockProjFacts t E₀ E env A c ms blk tys adv'.ren)
      (pcs : List (ConstantInfo .anon)),
      Decl.PrefixInv.{u} E t lim env → FoldExtra.{u} FormerOpenTraceAt t E env →
      FamRegistryWith.{u} FormerOpenTraceAt t E env Reg →
      (∀ ci ∈ envT.consts, ci ∈ env.consts) →
      (∀ x, UsedRef E₀ A x ∨ UsedRef E₀ rb x →
        (env.find? (keyOf t x)).isSome = true ∨ FamAddr A c rb crb x ∨ ¬ NeedOk E₀ x) →
      (∀ x, FamAddr A c rb crb x → env.find? (keyOf t x) = none) →
      AliasGroup env h aliases → (∀ a ∈ aliases, ∃ ci ∈ blk, a.name.base = ci.name) →
      FamDeclReads t E₀ A c rb crb blk → FamilyCheckFacts env blk adv' tys rhsss →
      Sel env blk adv' tys rhsss →
      DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ blk env₂ →
      (∀ ci ∈ blk, ∃ c', env₂.find? ci.name = some c' ∧ StoredAs c' ci) →
      SelectedInstalled blk tys rhsss env₂ →
      BlockProjInstallResult.{u} t env env₂ Reg A ms bpf.elig pcs →
      Decl.PrefixInv.{u} E t lim ⟨pcs ++ env₂.consts⟩ ∧
        FoldExtra.{u} FormerOpenTraceAt t E ⟨pcs ++ env₂.consts⟩) :
    UnitStepFamily.{u} (fun env => FoldExtra.{u} FormerOpenTraceAt t E env ∧
        FamilyRecsModeled t E₀ fam env)
      t envT E₀ E lim A c rb crb adv := by
  intro env hext hnd hinv hX hrefs hadv1 hadv2 hfresh
  obtain ⟨blk, adv', tys, rhsss, hreads, hF, hSel⟩ :=
    hseam env hext hnd hinv hX hrefs hadv1 hadv2 hfresh
  obtain ⟨bpf⟩ := hbpf env blk adv' tys rhsss hSel
  obtain ⟨⟨⟨⟨Reg, hReg⟩, -⟩, haux⟩, hthm, har⟩ := hX.1
  obtain ⟨h, as, env₂, hg, hroots, hnames, htgt, hd, hst, hN, hR⟩ :=
    famStepConclusion_installed_full hF hreads hinv.store.store haux (heqPin env hext hnd)
      hfresh (hkey env hext hfresh)
  have hI : SelectedInstalled blk tys rhsss env₂ := ⟨hN, hR⟩
  let pcs := blockProjConsts t env₂ A ms bpf.elig
  have hres : BlockProjInstallResult.{u} t env env₂ Reg A ms bpf.elig pcs :=
    install_block_proj_tables hinv.tableWf (Core.RoleClosure.check_ok_of_wf hinv.tableWf)
      hB hreads hF hg hnames htgt hroots hd hI hinv.store har hthm haux
      (heqPin env hext hnd) (hbasis env hext hnd) hReg hfresh (hkey env hext hfresh) bpf
  obtain ⟨new, henv, hperm⟩ := declIndRunJ_names_perm hd.shape
  have henv₂ : env₂ = ⟨(new ++ as) ++ env.consts⟩ := by
    rw [henv]
    simp [List.append_assoc]
  have henv₃ : (⟨(pcs ++ (new ++ as)) ++ env.consts⟩ : Ix.Kernel.Env .anon) =
      ⟨pcs ++ env₂.consts⟩ := by
    rw [henv₂]
    simp [List.append_assoc]
  -- the members' names
  have hmemb : ∀ ci ∈ new, ∃ x, FamAddr A c rb crb x ∧ ci.name = keyOf t x := by
    intro ci hci
    have hk : ci.name ∈ blk.map (·.name) := hperm.subset (List.mem_map.mpr ⟨ci, hci, rfl⟩)
    obtain ⟨ci₁, hci₁, hn⟩ := List.mem_map.mp hk
    obtain ⟨x, hx, hkx, -⟩ := hreads.2.1 ci₁ hci₁
    exact ⟨x, hx, hn.symm.trans hkx⟩
  have hbaseN : ∀ ci ∈ new, Decl.isBaseKey ci.name = true := by
    intro ci hci
    obtain ⟨x, -, hk⟩ := hmemb ci hci
    rw [hk]
    exact Decl.isBaseKey_keyOf t x
  have hnotalias : ∀ k, Decl.isBaseKey k = true → ∀ a ∈ as, a.name ≠ k := by
    intro k hk a ha hn
    obtain ⟨n, d, hna⟩ := AliasGroup.name_aux hg a ha
    rw [hna] at hn
    exact auxKey_ne_of_isBaseKey hk hn
  have hpcsAux : ∀ ci ∈ pcs, ∃ n d, ci.name = Ix.Kernel.auxKey n d := by
    intro ci hci
    obtain ⟨pos, -, -, ⟨_, _, hnm, -⟩ | ⟨j, _, hnm⟩⟩ := hres.kindAndName ci hci
    · exact ⟨Core.keyOf t (Core.iprjAddr A pos), .projTable, hnm⟩
    · exact ⟨Ix.Kernel.projTableName (Core.keyOf t (Core.iprjAddr A pos)), .projFn j, hnm⟩
  have hndNA : ((new ++ as).map (·.name)).Nodup := by
    rw [List.map_append]
    refine List.nodup_append.mpr ⟨hperm.nodup_iff.mpr hreads.1, AliasGroup.names_nodup hg, ?_⟩
    intro k hk k' hk' heq
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hk
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hk'
    exact hnotalias _ (hbaseN ci hci) a ha heq.symm
  refine ⟨pcs ++ (new ++ as), ?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · -- distinct names
    rw [List.map_append]
    refine List.nodup_append.mpr ⟨hres.nodup, hndNA, ?_⟩
    intro k hk k' hk' heq
    obtain ⟨c1, hc1, rfl⟩ := List.mem_map.mp hk
    obtain ⟨c2, hc2, rfl⟩ := List.mem_map.mp hk'
    have hmem2 : c2 ∈ env₂.consts := by
      rw [henv₂]
      exact List.mem_append_left env.consts hc2
    have hsome := find?_isSome_of_mem (E := env₂) hmem2
    rw [← heq, hres.freshEnv₂ c1 hc1] at hsome
    exact Bool.false_ne_true hsome
  · -- fresh in the prefix
    intro ci hci
    rcases List.mem_append.mp hci with hci | hci
    · exact hres.freshPrefix ci hci
    · rcases List.mem_append.mp hci with hci | hci
      · obtain ⟨x, hx, hk⟩ := hmemb ci hci
        rw [hk]
        exact hfresh x hx
      · exact AliasGroup.fresh_prefix hg ci hci
  · rw [henv₃]
    exact (hkeeps env env₂ Reg h as blk adv' tys rhsss bpf pcs hinv hX.1 hReg hext hrefs hfresh
      hg hroots hreads hF hSel hd hst hI hres).1
  · rw [henv₃]
    exact (hkeeps env env₂ Reg h as blk adv' tys rhsss bpf pcs hinv hX.1 hReg hext hrefs hfresh
      hg hroots hreads hF hSel hd hst hI hres).2
  · rw [henv₃]
    have hFRM₂ : FamilyRecsModeled t E₀ fam env₂ :=
      familyRecsModeled_famStep (A := A) (rb := rb) (c := c) (crb := crb) hX.2 hg hd hst
        (fun ci hci x hk => by
          obtain ⟨x', -, hk', hr⟩ := hreads.2.1 ci hci
          rw [← IxVM.Refinement.Core.keyOf_inj hinv.tableWf (hk'.symm.trans hk)]
          exact hr)
        (hclaim blk hreads)
    refine IxVM.Refinement.Typing.TwinFamily.FamilyRecsModeled.step hFRM₂
      (fun hc => hres.find₂ hc) ?_
    intro B' rb' x crb' _ _ _ hs hold
    exfalso
    have hnone := find?_append_none (env := env₂) pcs (fun a ha heq => by
      obtain ⟨n, d, hn⟩ := hpcsAux a ha
      rw [hn] at heq
      exact auxKey_ne_of_isBaseKey (Decl.isBaseKey_keyOf t x) heq) hold
    rw [hnone] at hs
    exact Bool.false_ne_true hs
  · -- each address of the family, stored as its reading
    intro x hx
    obtain ⟨ci₀, hci₀, hk⟩ := hreads.2.2.1 x hx
    obtain ⟨x', hx', hk', hr⟩ := hreads.2.1 ci₀ hci₀
    have hxx : x' = x := IxVM.Refinement.Core.keyOf_inj hinv.tableWf (hk'.symm.trans hk)
    subst hxx
    obtain ⟨c', hc', hS⟩ := hst ci₀ hci₀
    rw [henv₂] at hc'
    obtain ⟨hmem, hname⟩ := find?_mem_name hc'
    refine ⟨c', ?_, ci₀, hname.trans hk', hr, hS⟩
    rcases List.mem_append.mp hmem with hmem | hmem
    · rcases List.mem_append.mp hmem with hmem | hmem
      · exact List.mem_append_right pcs (List.mem_append_left as hmem)
      · exfalso
        exact hnotalias (keyOf t x') (Decl.isBaseKey_keyOf t x') c' hmem
          (hname.trans hk')
    · exfalso
      have h1 := find?_isSome_of_mem (E := env) hmem
      rw [hname, hk', hfresh x' hx'] at h1
      exact Bool.false_ne_true h1
  · -- each new constant at an address's key or at a derived key
    intro ci hci
    rcases List.mem_append.mp hci with hci | hci
    · exact Or.inr (hpcsAux ci hci)
    · rcases List.mem_append.mp hci with hci | hci
      · exact Or.inl (hmemb ci hci)
      · obtain ⟨n, d, hn⟩ := AliasGroup.name_aux hg ci hci
        exact Or.inr ⟨n, d, hn⟩

end IxVM.Refinement.Typing.FamilyAlias
