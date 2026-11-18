import IxVMRefinement.Decl.DeclSpecs
import IxVMRefinement.FamilyAlias.Step
import IxVMRefinement.FamilyAlias.Install

/-! # Derived-key roots after the family step, and the declaration layer's invariant

An alias sits at a derived key whose root is a member of the block, stored only by the block's
own step, so `AuxRootSynced` fails between the alias group and the block. It holds again after the
block: the modeled record prepends constants named by the block's members (base keys), and every
alias's root is one of them. With the fold invariant across the group and the block this gives
`FullDeclInv` across the whole step (`fullDeclInv_famStep`).

The three lemmas on the record's environment are copies of private lemmas of
`IxVMRefinement/Decl/DeclSpecs.lean` (`indMembersRunJ_consts_eq`, `provisionRecsRunJ_names_eq`,
`indRecsFoldRunJ_consts_eq`). -/

universe u

namespace IxVM.Refinement.Decl.FamilyAlias

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.Core
open Ix.Kernel (Mode Expr Level LevelParam ConstantVal ConstantInfo Declaration RecRule
  BasisKind QuotKind IndCaps NativeParts InductiveShape ProjTable Env EnvExt Key)
open Ix.Kernel.Semantics (Judgements DeclRunJ DeclsRunJ IndRoutesJ DeclIndRunJ IndMembersRunJ
  ProvisionRecsRunJ IndRecsFoldRunJ DeclIndRenRunJ)
open Ix.Kernel.Model (rulesJ EnvModelT EnvModelOk)

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

theorem indMembersRunJ_consts_eq' {J : Judgements .anon} {blockNames : List KKey}
    {caps : IndCaps .anon} :
    ∀ (ms : List (ConstantInfo .anon)) {acc envM : Env .anon},
      IndMembersRunJ J blockNames caps acc ms envM →
      ∃ newM, envM = ⟨newM ++ acc.consts⟩ ∧ newM.map (·.name) = ms.reverse.map (·.name)
  | [], acc, envM, h => ⟨[], by subst h; rfl, rfl⟩
  | ci :: rest, acc, envM, ⟨cvA, hmv, hrest⟩ => by
    obtain ⟨type', _, rfl, _⟩ := hmv
    cases ci with
    | indInfo cvI _ =>
      obtain ⟨newM, heq, hnames⟩ := indMembersRunJ_consts_eq' rest hrest
      refine ⟨newM ++ [.indInfo ⟨cvI.name, cvI.levelParams, type'⟩ caps], ?_, ?_⟩
      · simpa [List.append_assoc, ConstantInfo.toConstantVal] using heq
      · rw [List.map_append, List.reverse_cons, List.map_append, hnames]; rfl
    | ctorInfo cvC nP nF =>
      obtain ⟨newM, heq, hnames⟩ := indMembersRunJ_consts_eq' rest hrest
      refine ⟨newM ++ [.ctorInfo ⟨cvC.name, cvC.levelParams, type'⟩ nP nF], ?_, ?_⟩
      · simpa [List.append_assoc, ConstantInfo.toConstantVal] using heq
      · rw [List.map_append, List.reverse_cons, List.map_append, hnames]; rfl
    | axiomInfo _ | defnInfo _ _ _ | thmInfo _ _ | recInfo _ _ _ _ | projInfo _ =>
      exact hrest.elim

theorem provisionRecsRunJ_names_eq' {J : Judgements .anon} {blockNames : List KKey} :
    ∀ (recs : List (ConstantInfo .anon)) {acc envSelf : Env .anon}
      {checked : List (ConstantVal .anon × Nat × Nat × List (RecRule .anon))},
      ProvisionRecsRunJ J blockNames acc recs envSelf checked →
      checked.map (·.1.name) = recs.map (·.name)
  | [], _, _, _, ⟨_, hchk⟩ => by subst hchk; rfl
  | ci :: rest, _, _, _, ⟨_, _, _, _, _, _, ⟨_, _, rfl, _⟩, hprov, hchk⟩ => by
    subst hchk
    have hci_name : ci.name = ci.toConstantVal.name := by cases ci <;> rfl
    simp [provisionRecsRunJ_names_eq' rest hprov, hci_name]

theorem indRecsFoldRunJ_consts_eq' {J : Judgements .anon} {blockNames : List KKey}
    {envBase envSelf : Env .anon} :
    ∀ (checked : List (ConstantVal .anon × Nat × Nat × List (RecRule .anon)))
      {done : List (ConstantInfo .anon)} {acc out : Env .anon},
      IndRecsFoldRunJ J blockNames envBase envSelf ⟨done ++ acc.consts⟩ checked out →
      ∃ newR, out = ⟨(newR ++ done) ++ acc.consts⟩ ∧
        newR.map (·.name) = checked.reverse.map (·.1.name)
  | [], done, acc, out, h => ⟨[], by subst h; rfl, rfl⟩
  | c :: rest, done, acc, out, ⟨rules', _, hfold⟩ => by
    have hfold' :
        IndRecsFoldRunJ J blockNames envBase envSelf
          ⟨(.recInfo c.1 c.2.1 c.2.2.1 rules' :: done) ++ acc.consts⟩ rest out := hfold
    obtain ⟨newR, hout, hnames⟩ := indRecsFoldRunJ_consts_eq' rest hfold'
    refine ⟨newR ++ [.recInfo c.1 c.2.1 c.2.2.1 rules'], ?_, ?_⟩
    · simpa [List.append_assoc] using hout
    · rw [List.map_append, List.reverse_cons, List.map_append, hnames]
      rfl

/-- **The modeled record prepends constants named by the block's members, one for each.** -/
theorem declIndRunJ_consts_eq {J : Judgements .anon} {env env₂ : Env .anon}
    {block : List (ConstantInfo .anon)} (h : DeclIndRunJ J env block env₂) :
    ∃ new, env₂ = ⟨new ++ env.consts⟩ ∧
      (∀ c ∈ new, ∃ ci ∈ block, c.name = ci.name) ∧
      (∀ ci ∈ block, ∃ c ∈ new, c.name = ci.name) := by
  obtain ⟨hblk_split, envM, hmem, hrecs⟩ := h
  obtain ⟨newM, heqM, hnamesM⟩ := indMembersRunJ_consts_eq' _ hmem
  have hM : ∀ c ∈ newM, ∃ ci ∈ block, c.name = ci.name := by
    intro c hc
    have hk : c.name ∈ newM.map (·.name) := List.mem_map_of_mem hc
    rw [hnamesM] at hk
    obtain ⟨ci₀, hci₀, hnm⟩ := List.mem_map.mp hk
    exact ⟨ci₀, by rw [hblk_split]; exact List.mem_append_left _ (List.mem_reverse.mp hci₀),
      hnm.symm⟩
  rcases hrecs with ⟨hnil, rfl⟩ | ⟨_, _, envSelf, checked, hprov, hfold⟩
  · refine ⟨newM, heqM, hM, fun ci hci => ?_⟩
    rw [hblk_split] at hci
    rcases List.mem_append.mp hci with hci | hci
    · have hk : ci.name ∈ newM.map (·.name) := by
        rw [hnamesM]; exact List.mem_map_of_mem (List.mem_reverse.mpr hci)
      obtain ⟨c, hc, hcn⟩ := List.mem_map.mp hk
      exact ⟨c, hc, hcn⟩
    · rw [hnil] at hci
      simp at hci
  · have hfold' :
        IndRecsFoldRunJ J (block.map (·.name)) envM envSelf ⟨[] ++ envM.consts⟩
          checked env₂ := hfold
    obtain ⟨newR, hout, hnamesR⟩ := indRecsFoldRunJ_consts_eq' checked hfold'
    simp only [List.append_nil] at hout
    refine ⟨newR ++ newM, ?_, ?_, ?_⟩
    · rw [hout, heqM]
      simp [List.append_assoc]
    · intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · have hk : c.name ∈ newR.map (·.name) := List.mem_map_of_mem hc
        rw [hnamesR, List.map_reverse] at hk
        have hk' : c.name ∈ checked.map (·.1.name) := List.mem_reverse.mp hk
        rw [provisionRecsRunJ_names_eq' _ hprov] at hk'
        obtain ⟨ci₀, hci₀, hnm⟩ := List.mem_map.mp hk'
        exact ⟨ci₀, by rw [hblk_split]; exact List.mem_append_right _ hci₀, hnm.symm⟩
      · exact hM c hc
    · intro ci hci
      rw [hblk_split] at hci
      rcases List.mem_append.mp hci with hci | hci
      · have hk : ci.name ∈ newM.map (·.name) := by
          rw [hnamesM]; exact List.mem_map_of_mem (List.mem_reverse.mpr hci)
        obtain ⟨c, hc, hcn⟩ := List.mem_map.mp hk
        exact ⟨c, List.mem_append_right _ hc, hcn⟩
      · have hk : ci.name ∈ newR.map (·.name) := by
          rw [hnamesR, List.map_reverse]
          refine List.mem_reverse.mpr ?_
          rw [provisionRecsRunJ_names_eq' _ hprov]
          exact List.mem_map_of_mem hci
        obtain ⟨c, hc, hcn⟩ := List.mem_map.mp hk
        exact ⟨c, List.mem_append_left _ hc, hcn⟩

/-- **Derived-key roots are stored after the family step**: the prefix keeps its roots, the
block's members are stored under base keys, and each alias's root is a member of the block. -/
theorem auxRootSynced_famStep {J : Judgements .anon} {env env₂ : Env .anon}
    {aliases block : List (ConstantInfo .anon)}
    (haux : AuxRootSynced env)
    (hna : ∀ ci ∈ block, NonAuxKey ci.name)
    (hroots : ∀ a ∈ aliases, ∃ ci ∈ block, a.name.base = ci.name)
    (hd : DeclIndRenRunJ J ⟨aliases ++ env.consts⟩ block env₂) :
    AuxRootSynced env₂ := by
  obtain ⟨new, heq, hnew, hall⟩ := declIndRunJ_consts_eq hd.shape
  have heq' : env₂ = ⟨(new ++ aliases) ++ env.consts⟩ := by
    rw [heq]
    simp [List.append_assoc]
  have hstored : ∀ ci ∈ block,
      (Env.find? ⟨(new ++ aliases) ++ env.consts⟩ ci.name).isSome = true := by
    intro ci hci
    obtain ⟨c, hc, hnm⟩ := hall ci hci
    rw [← hnm]
    exact env_find?_isSome_of_mem_prefix (List.mem_append_left _ hc)
  rw [heq']
  refine haux.of_prepend fun c hc => ?_
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨ci, hci, hnm⟩ := hnew c hc
    rw [hnm, base_of_isBaseKey (isBaseKey_of_nonAuxKey (hna ci hci))]
    exact hstored ci hci
  · obtain ⟨ci, hci, hnm⟩ := hroots c hc
    rw [hnm]
    exact hstored ci hci

/-- **The declaration layer's invariant across the family step with aliases**: from an alias
group over the prefix and IxC's renamed record over the family package, `FullDeclInv` after the
block in every set theory. -/
theorem fullDeclInv_famStep {env env₂ : Env .anon} {h : KKey → KKey}
    {aliases block : List (ConstantInfo .anon)}
    (hg : AliasGroup env h aliases)
    (hpin : Ix.Kernel.basisPinHit block = none)
    (hna : ∀ ci ∈ block, NonAuxKey ci.name)
    (hroots : ∀ a ∈ aliases, ∃ ci ∈ block, a.name.base = ci.name)
    (hd : DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ block env₂) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], FullDeclInv V env → FullDeclInv V env₂ :=
  fun V _ hF =>
    FullDeclInv.ofFoldInv
      (foldInv_step_declIndRenJ (nP := 0) (judgeFrames_famJ h)
        (fun _ _ _ m => judgeSound_famJ_of m h) hpin hna hd V
        (foldInv_aliasGroup hg hF.toFoldInv).1)
      (auxRootSynced_famStep hF.declInvM.auxSynced hna hroots hd)

/-- Stored aliases stay stored aliases along an extension. -/
theorem AliasEnv.mono {env env' : Env .anon} {h : KKey → KKey}
    (hfind : ∀ {k : KKey} {c : ConstantInfo .anon}, env.find? k = some c → env'.find? k = some c)
    (hA : AliasEnv env h) : AliasEnv env' h := by
  intro k hk
  obtain ⟨lps, ty, hint, ci, hfk, hperm, hft, hlt⟩ := hA k hk
  exact ⟨lps, ty, hint, ci, hfind hfk, hperm, hfind hft, hlt⟩

end IxVM.Refinement.Decl.FamilyAlias
