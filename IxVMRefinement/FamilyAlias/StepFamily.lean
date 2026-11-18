import IxVMRefinement.FamilyAlias.RecsModeledStep
import IxVMRefinement.FamilyAlias.StepOfSeam
import IxVMRefinement.Assembly.FoldClause

/-! # The family row's step, its model half

`unitStepFamily_of_facts`: a statement of the type of the family row's step (`UnitStepFamily` at
the fold's clause with the family recursors' companions beside it, the type
`FamilyBlockRow` asks), from the target's conclusion assembled at each environment the step is
handed (`famStepConclusion_of_facts`) and these named premises:

* `hseam`: the circuit side's seam at the step's hypotheses (the family as read and the facts of
  the family check at the prefix);
* `hkey`: key freedom of the family's addresses (the target's hypothesis; the row hands none);
* `heqPin`: the pinned equality at every environment the step is asked at (`eqPin_of_shape`
  with the step context's table shape);
* `hclaim`: a member of the block at the key of a claimed family record's constant address is a
  recursor (a fact of the family graph);
* `hkeeps`: the prefix invariant and the fold's clause across the step's record (the companions,
  load contract and η stability of the prefix invariant, and the arity of the stored terms).

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
  have hp : (c.name == k) = true := List.find?_some h'
  exact ⟨List.mem_of_find?_eq_some h', beq_iff_eq.mp hp⟩

/-- A constant of an environment makes its key found. -/
theorem find?_isSome_of_mem {E : Ix.Kernel.Env .anon} {c : ConstantInfo .anon}
    (h : c ∈ E.consts) : (E.find? c.name).isSome = true := by
  show (E.consts.find? (·.name == c.name)).isSome = true
  exact List.find?_isSome.mpr ⟨c, h, beq_self_eq_true _⟩

/-- **The family row's step, its model half** (module docstring). -/
theorem unitStepFamily_of_facts {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {t : Ix.Kernel.RoleTable} {envT : Ix.Kernel.Env .anon} {E₀ E : Ixon.Env}
    {lim : Option Nat} {A : _root_.Address} {c : Ixon.Constant} {rb : _root_.Address}
    {crb : Ixon.Constant} {adv : _root_.Address → Prop}
    {fam : _root_.Address → Option _root_.Address}
    (hseam : ∀ env : Ix.Kernel.Env .anon,
      (∀ ci ∈ envT.consts, ci ∈ env.consts) → (env.consts.map (·.name)).Nodup →
      Decl.PrefixInv.{u} E t lim env →
      (FoldExtra.{u} L t E env ∧ FamilyRecsModeled t E₀ fam env) →
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
        FamDeclReads t E₀ A c rb crb blk ∧ FamilyCheckFacts env blk adv' tys rhsss)
    (hkey : ∀ x, FamAddr A c rb crb x → Decl.KeyFree (keyOf t x))
    (heqPin : ∀ env : Ix.Kernel.Env .anon,
      (∀ ci ∈ envT.consts, ci ∈ env.consts) → (env.consts.map (·.name)).Nodup →
      env.find? Ix.Kernel.eqName = some Ix.Kernel.eqA)
    (hclaim : ∀ blk : List (ConstantInfo .anon), FamDeclReads t E₀ A c rb crb blk →
      ∀ (B' rb' x : _root_.Address) (crb' : Ixon.Constant), fam B' = some rb' →
        recordOf E₀ rb' = some crb' → ConstAddrOf rb' crb' x →
        ∀ ci ∈ blk, ci.name = keyOf t x → isRecursor ci = true)
    (hkeeps : ∀ (env env₂ : Ix.Kernel.Env .anon)
      (h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon) (aliases blk : List (ConstantInfo .anon)),
      Decl.PrefixInv.{u} E t lim env → FoldExtra.{u} L t E env →
      AliasGroup env h aliases → (∀ a ∈ aliases, ∃ ci ∈ blk, a.name.base = ci.name) →
      FamDeclReads t E₀ A c rb crb blk →
      DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ blk env₂ →
      (∀ ci ∈ blk, ∃ c', env₂.find? ci.name = some c' ∧ StoredAs c' ci) →
      Decl.PrefixInv.{u} E t lim env₂ ∧ FoldExtra.{u} L t E env₂) :
    UnitStepFamily.{u} (fun env => FoldExtra.{u} L t E env ∧ FamilyRecsModeled t E₀ fam env)
      t envT E₀ E lim A c rb crb adv := by
  intro env hext hnd hinv hX hrefs hadv1 hadv2 hfresh
  obtain ⟨blk₀, adv', tys, rhsss, hreads₀, hF⟩ :=
    hseam env hext hnd hinv hX hrefs hadv1 hadv2 hfresh
  obtain ⟨h, as, blk, env₂, hg, hroots, hreads, hd, hst⟩ :=
    famStepConclusion_of_facts hF hreads₀ hinv.store.store hX.1.1.2 (heqPin env hext hnd)
      hfresh hkey
  obtain ⟨new, henv, hperm⟩ := declIndRunJ_names_perm hd.shape
  have henv₂ : env₂ = ⟨(new ++ as) ++ env.consts⟩ := by
    rw [henv]
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
  refine ⟨new ++ as, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · -- distinct names
    rw [List.map_append]
    refine List.nodup_append.mpr ⟨hperm.nodup_iff.mpr hreads.1, hg.names_nodup, ?_⟩
    intro k hk k' hk' heq
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hk
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hk'
    exact hnotalias _ (hbaseN ci hci) a ha heq.symm
  · -- fresh in the prefix
    intro ci hci
    rcases List.mem_append.mp hci with hci | hci
    · obtain ⟨x, hx, hk⟩ := hmemb ci hci
      rw [hk]
      exact hfresh x hx
    · exact hg.fresh_prefix ci hci
  · rw [← henv₂]
    exact (hkeeps env env₂ h as blk hinv hX.1 hg hroots hreads hd hst).1
  · rw [← henv₂]
    exact (hkeeps env env₂ h as blk hinv hX.1 hg hroots hreads hd hst).2
  · rw [← henv₂]
    exact familyRecsModeled_famStep hX.2 hg hd hst (hclaim blk hreads)
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
      · exact List.mem_append_left _ hmem
      · exfalso
        exact hnotalias _ (by rw [hk']; exact Decl.isBaseKey_keyOf t x') c' hmem
          (hname.trans hk')
    · exfalso
      have h1 := find?_isSome_of_mem (E := env) hmem
      rw [hname, hk', hfresh x' hx'] at h1
      exact Bool.false_ne_true h1
  · -- each new constant at an address's key or at a derived key
    intro ci hci
    rcases List.mem_append.mp hci with hci | hci
    · exact Or.inl (hmemb ci hci)
    · obtain ⟨n, d, hn⟩ := AliasGroup.name_aux hg ci hci
      exact Or.inr ⟨n, d, hn⟩

end IxVM.Refinement.Typing.FamilyAlias
