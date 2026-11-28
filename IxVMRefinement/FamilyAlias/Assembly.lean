import IxVMRefinement.FamilyAlias.RecsRecord
import IxVMRefinement.FamilyAlias.FamilyAliasGroup
import IxVMRefinement.FamilyAlias.Target

/-! # The family step's record, assembled from the family check's facts

`familyRecord_of_facts`: from what the family check establishes (`FamilyCheckFacts`) and premises
about the prefix and the family's names only, an alias group at derived keys over the prefix,
each alias rooted at a member, IxCK's renamed record over the family package `famJ h` after the
group, and each member stored after the step as a constant that stores its reading.

The order is the install order: the members' aliases and the rules' aliases
(`aliasGroup_family`); the types and constructors (`indMembersRunJ_of_facts`, with
`membersReady_of_scope` at the prefix with the aliases); the recursors without rules
(`provisionRecsRunJ_of_facts`); the recursors with their rules (`indRecsFoldRenRunJ_of_aliased`,
with `RuleRecordEnv` built here).

`famStepConclusion_of_facts` is the same at the family step's target (`FamilyStepTarget`): its
conclusion from the facts, the family's declaration as read, the prefix's store and root
invariants, and the target's own hypotheses on freshness, key freedom and the pinned
equality. -/

namespace IxVM.Refinement.Decl.FamilyAlias

open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel (Env Expr Key Level ConstantInfo ConstantVal RecRule LevelParam EnvWF EnvExt
  Derived auxKey eqName eqA)

set_option linter.unusedVariables false

/-! ## Lists of members -/

theorem MembersFacts.get {env : Env .anon} {g : KKey → KKey} :
    ∀ {ms : List (ConstantInfo .anon)} {tys : List KExpr} {i : Nat} {ci : ConstantInfo .anon}
      {tyA : KExpr}, MembersFacts env g ms tys → ms[i]? = some ci → tys[i]? = some tyA →
      MemberFacts env g ci tyA
  | [], _, _, _, _, _, hc, _ => by simp at hc
  | _ :: _, [], _, _, _, _, _, ht => by simp at ht
  | c :: ms, t :: tys, 0, ci, tyA, hm, hc, ht => by
    obtain ⟨hF, -⟩ := hm
    obtain rfl := Option.some.inj hc
    obtain rfl := Option.some.inj ht
    exact hF
  | c :: ms, t :: tys, i + 1, ci, tyA, hm, hc, ht => by
    obtain ⟨-, hrest⟩ := hm
    exact MembersFacts.get hrest hc ht

/-- What an environment stores, it stores after members are stored. -/
theorem storeMembers_isSome_keep :
    ∀ (ms : List (ConstantInfo .anon)) (tys : List KExpr) (env' : Env .anon) (k : KKey),
      (env'.find? k).isSome = true → ((storeMembers env' ms tys).find? k).isSome = true
  | [], _, _, _, hk => hk
  | _ :: _, [], _, _, hk => hk
  | ci :: rest, tyA :: tys, env', k, hk => by
    refine storeMembers_isSome_keep rest tys _ k ?_
    by_cases hn : (storedMember ci tyA).name = k
    · rw [← hn, Ix.Kernel.Env.find?_cons_self]
      rfl
    · rw [EnvExt.find?_cons_ne (env := env') hn]
      exact hk

/-- Each member is stored after the members are stored. -/
theorem storeMembers_isSome_mem :
    ∀ (ms : List (ConstantInfo .anon)) (tys : List KExpr) (env' : Env .anon),
      ms.length = tys.length → ∀ ci ∈ ms,
        ((storeMembers env' ms tys).find? ci.name).isSome = true
  | [], _, _, _, _, hci => nomatch hci
  | _ :: _, [], _, hl, _, _ => absurd hl (Nat.succ_ne_zero _)
  | c :: rest, tyA :: tys, env', hl, ci, hci => by
    rcases List.mem_cons.mp hci with rfl | hci
    · refine storeMembers_isSome_keep rest tys _ _ ?_
      have h1 := Ix.Kernel.Env.find?_cons_self (storedMember ci tyA) env'
      rw [storedMember_name] at h1
      rw [h1]
      rfl
    · exact storeMembers_isSome_mem rest tys _ (by simpa using hl) ci hci

/-- A member that is no recursor sits among the block's other members, at the same index. -/
theorem nonrecs_getElem? {blk : List (ConstantInfo .anon)}
    (hsplit : blk = nonrecsOf blk ++ recsOf blk) {i : Nat} {ci : ConstantInfo .anon}
    (hi : blk[i]? = some ci) (hnr : isRecursor ci = false) :
    i < (nonrecsOf blk).length ∧ (nonrecsOf blk)[i]? = some ci := by
  have hlt : i < (nonrecsOf blk).length := by
    refine Nat.lt_of_not_le (fun hle => ?_)
    rw [hsplit, List.getElem?_append_right hle] at hi
    have hmem := List.mem_of_getElem? hi
    obtain ⟨-, hp⟩ := List.mem_filter.mp hmem
    cases ci with
    | recInfo _ _ _ _ => simp [isRecursor] at hnr
    | _ => exact Bool.false_ne_true hp
  refine ⟨hlt, ?_⟩
  rw [hsplit, List.getElem?_append_left hlt] at hi
  exact hi

theorem recsOf_all_isRecursor (blk : List (ConstantInfo .anon)) :
    (recsOf blk).all isRecursor = true := by
  refine List.all_eq_true.mpr (fun x hx => ?_)
  obtain ⟨-, hp⟩ := List.mem_filter.mp hx
  cases x with
  | recInfo _ _ _ _ => rfl
  | _ => exact absurd hp Bool.false_ne_true

/-- A type or a constructor stored at its annotated type stores its reading. -/
theorem storedAs_storedMember {ci : ConstantInfo .anon} {tyA : KExpr}
    (hk : isTypeOrCtor ci = true) (hann : IxVM.Consistency.Annotates tyA ci.toConstantVal.type) :
    IxVM.Consistency.StoredAs (storedMember ci tyA) ci := by
  cases ci with
  | indInfo cv caps => exact ⟨⟨rfl, rfl, hann⟩, trivial⟩
  | ctorInfo cv nP nF => exact ⟨⟨rfl, rfl, hann⟩, rfl, rfl⟩
  | _ => exact absurd hk Bool.false_ne_true

/-- An alias key is no base key. -/
theorem auxKey_ne_of_isBaseKey {k k' : KKey} {d : Derived} (hk : isBaseKey k = true) :
    auxKey k' d ≠ k := by
  intro h
  rw [← h] at hk
  exact Bool.false_ne_true hk

/-! ## The assembly -/

/-- **The family step's record from the family check's facts**, exposing the alias naming shape
and target map alongside the installed constants. -/
theorem familyRecord_of_facts_full {env : Env .anon} {blk : List (ConstantInfo .anon)}
    {adv : FamilyAdvice} {tys : List KExpr} {rhsss : List (List KExpr)}
    (hF : FamilyCheckFacts env blk adv tys rhsss) (hsi : Ix.Kernel.Open.StoreInv env)
    (hnd : (blk.map (·.name)).Nodup)
    (hkey : ∀ ci ∈ blk, isBaseKey ci.name = true ∧
      Ix.Kernel.reservedBasisNames.contains ci.name = false)
    (hfresh : ∀ ci ∈ blk, env.find? ci.name = none)
    (hnewM : ∀ ci ∈ blk, env.find? (auxKey ci.name .model) = none)
    (hnewI : ∀ ci ∈ blk, ∀ j, env.find? (iotaKey ci.name j) = none)
    (heq : env.find? eqName = some eqA) :
    ∃ (h : KKey → KKey) (aliases : List (ConstantInfo .anon)) (env₂ : Env .anon),
      AliasGroup env h aliases ∧
      (∀ a ∈ aliases, ∃ ci ∈ blk, a.name.base = ci.name) ∧
      (∀ a ∈ aliases, ∃ ci ∈ blk,
        a.name = auxKey ci.name .model ∨ ∃ j, a.name = iotaKey ci.name j) ∧
      (∀ ci ∈ blk, h (auxKey ci.name .model) = adv.ren ci.name) ∧
      DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ blk env₂ ∧
      (∀ ci ∈ blk, ∃ c, env₂.find? ci.name = some c ∧ IxVM.Consistency.StoredAs c ci) ∧
      (∀ (i : Nat) (ci : ConstantInfo .anon) (tyA : KExpr), (nonrecsOf blk)[i]? = some ci →
        tys[i]? = some tyA → env₂.find? ci.name = some (storedMember ci tyA)) ∧
      (∀ (i : Nat) (cv : ConstantVal .anon) (mI rP : Nat) (rules : List (RecRule .anon))
        (tyA : KExpr) (rhss : List KExpr),
        (recsOf blk)[i]? = some (.recInfo cv mI rP rules) →
        tys[(nonrecsOf blk).length + i]? = some tyA → rhsss[i]? = some rhss →
        ∃ rules' : List (RecRule .anon),
          env₂.find? cv.name = some (.recInfo ⟨cv.name, cv.levelParams, tyA⟩ mI rP rules') ∧
          List.Forall₂ IxVM.Consistency.RuleStored rules' rules ∧
          List.Forall₂ (fun (r' : RecRule .anon) rhsA => r'.rhs = rhsA) rules' rhss) := by
  have hwf : EnvWF env := hsi.wf
  have htake : ∀ {i : Nat} {ci : ConstantInfo .anon} {tyA : KExpr},
      (nonrecsOf blk)[i]? = some ci → tys[i]? = some tyA →
      (tys.take (nonrecsOf blk).length)[i]? = some tyA := by
    intro i ci tyA hi hty
    rw [List.getElem?_take_of_lt (List.getElem?_eq_some_iff.mp hi).1]
    exact hty
  obtain ⟨as, tbl, hg, htgt, hfindM, hnames, hrecsA⟩ :=
    aliasGroup_family hF hwf hnd hnewM hnewI
  -- names
  have hmemb : ∀ k, (blk.map (·.name)).contains k = true → ∃ ci ∈ blk, ci.name = k := by
    intro k hk
    have hk' : k ∈ blk.map (·.name) := by simpa using hk
    exact List.mem_map.mp hk'
  have hblk : ∀ ci ∈ blk, (blk.map (·.name)).contains ci.name = true := by
    intro ci hci
    have hm : ci.name ∈ blk.map (·.name) := List.mem_map.mpr ⟨ci, hci, rfl⟩
    simpa using hm
  have hout : ∀ k, (blk.map (·.name)).contains k = false → adv.ren k = k := by
    intro k hk
    have hk' : k ∉ blk.map (·.name) := by simpa using hk
    exact aliasMap_of_not_key adv.models k (by rw [hF.table]; exact hk')
  have hnotmem : ∀ k, (env.find? k).isSome = true → k ∉ blk.map (·.name) := by
    intro k hk hin
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hin
    rw [hfresh ci hci] at hk
    exact Bool.false_ne_true hk
  have hgfix : ∀ k, (env.find? k).isSome = true → adv.ren k = k := by
    intro k hk
    refine hout k ?_
    cases hb : (blk.map (·.name)).contains k with
    | false => rfl
    | true => exact absurd (by simpa using hb) (hnotmem k hk)
  have hmoves : ∀ k, (blk.map (·.name)).contains k = true → adv.ren k ≠ k := by
    intro k hk heq'
    obtain ⟨ci, hci, rfl⟩ := hmemb k hk
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hci
    have hlen := MembersFacts.length_eq blk tys hF.members
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨tyA, hty⟩ : ∃ tyA, tys[i]? = some tyA :=
      ⟨tys[i]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨cvm, mval, hint, hfm, -, -⟩ := (MembersFacts.get hF.members hi hty).model
    have h1 : env.find? ci.name = none := hfresh ci hci
    have h2 : env.find? (adv.ren ci.toConstantVal.name) = some (.defnInfo cvm mval hint) := hfm
    have h3 : ci.toConstantVal.name = ci.name := rfl
    rw [h3, heq', h1] at h2
    exact nomatch h2
  have htarget : ∀ k, (blk.map (·.name)).contains k = true →
      aliasMap tbl (auxKey k .model) = adv.ren k := by
    intro k hk
    obtain ⟨ci, hci, rfl⟩ := hmemb k hk
    exact htgt ci hci
  have hfixes : ∀ k, (env.find? k).isSome = true → aliasMap tbl k = k := hg.fixes_prefix
  -- the roots
  have hroots : ∀ a ∈ as, ∃ ci ∈ blk, a.name.base = ci.name := by
    intro a ha
    obtain ⟨ci, hci, hn⟩ := hnames a ha
    refine ⟨ci, hci, ?_⟩
    have hb := base_of_isBaseKey (hkey ci hci).1
    rcases hn with hn | ⟨j, hn⟩
    · rw [hn]
      exact hb
    · rw [hn]
      exact hb
  -- the prefix with the aliases
  have hext0 : EnvExt env ⟨as ++ env.consts⟩ := hg.envExt
  have hA0 : AliasEnv ⟨as ++ env.consts⟩ (aliasMap tbl) := hg.aliasEnv
  have hJ : ∀ k ∈ blk.map (·.name), (⟨as ++ env.consts⟩ : Env .anon).find? k = none := by
    intro k hk
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hk
    refine find?_append_none as (fun a ha heq' => ?_) (hfresh ci hci)
    obtain ⟨c, -, hn⟩ := hnames a ha
    rcases hn with hn | ⟨j, hn⟩
    · rw [hn] at heq'
      exact auxKey_ne_of_isBaseKey (hkey ci hci).1 heq'
    · rw [hn] at heq'
      exact auxKey_ne_of_isBaseKey (hkey ci hci).1 heq'
  have hready : MembersReady adv.ren (aliasMap tbl) (blk.map (·.name)) ⟨as ++ env.consts⟩
      blk tys :=
    membersReady_of_scope hwf hout htarget hfixes blk tys [] _ hF.members hF.typesScoped hnd
      (fun k hk => Or.inr (by simpa using hk)) hkey hg.stored_prefix (fun _ hk => nomatch hk)
      hJ hfindM
  -- the split
  have hlen := MembersFacts.length_eq blk tys hF.members
  have hl2 := congrArg List.length hF.split
  rw [List.length_append] at hl2
  have hsplitT : tys = tys.take (nonrecsOf blk).length ++ tys.drop (nonrecsOf blk).length :=
    (List.take_append_drop _ _).symm
  have hlenN : (nonrecsOf blk).length = (tys.take (nonrecsOf blk).length).length := by
    rw [List.length_take]
    omega
  have hmfs : MembersFacts env adv.ren (nonrecsOf blk) (tys.take (nonrecsOf blk).length) ∧
      MembersFacts env adv.ren (recsOf blk) (tys.drop (nonrecsOf blk).length) := by
    have h0 : MembersFacts env adv.ren (nonrecsOf blk ++ recsOf blk)
        (tys.take (nonrecsOf blk).length ++ tys.drop (nonrecsOf blk).length) := by
      rw [List.take_append_drop, ← hF.split]
      exact hF.members
    exact MembersFacts.split _ _ _ _ hlenN h0
  have hreadys : MembersReady adv.ren (aliasMap tbl) (blk.map (·.name)) ⟨as ++ env.consts⟩
        (nonrecsOf blk) (tys.take (nonrecsOf blk).length) ∧
      MembersReady adv.ren (aliasMap tbl) (blk.map (·.name))
        (storeMembers ⟨as ++ env.consts⟩ (nonrecsOf blk) (tys.take (nonrecsOf blk).length))
        (recsOf blk) (tys.drop (nonrecsOf blk).length) := by
    have h0 : MembersReady adv.ren (aliasMap tbl) (blk.map (·.name)) ⟨as ++ env.consts⟩
        (nonrecsOf blk ++ recsOf blk)
        (tys.take (nonrecsOf blk).length ++ tys.drop (nonrecsOf blk).length) := by
      rw [List.take_append_drop, ← hF.split]
      exact hready
    exact MembersReady.split _ _ _ _ _ hlenN h0
  have hndsplit : ((nonrecsOf blk).map (·.name) ++ (recsOf blk).map (·.name)).Nodup := by
    rw [← List.map_append, ← hF.split]
    exact hnd
  have hRnd : ((recsOf blk).map (·.name)).Nodup := (List.nodup_append.mp hndsplit).2.1
  have hNnd : ((nonrecsOf blk).map (·.name)).Nodup := (List.nodup_append.mp hndsplit).1
  have hdisj : ∀ ci ∈ nonrecsOf blk, ci.name ∉ (recsOf blk).map (·.name) := by
    intro ci hci hin
    exact (List.nodup_append.mp hndsplit).2.2 _ (List.mem_map.mpr ⟨ci, hci, rfl⟩) _ hin rfl
  have hNmem : ∀ ci ∈ nonrecsOf blk, ci ∈ blk := fun ci hci => (List.mem_filter.mp hci).1
  have hRmem : ∀ ci ∈ recsOf blk, ci ∈ blk := fun ci hci => (List.mem_filter.mp hci).1
  -- the types and constructors
  obtain ⟨hmem, hextM, hAM⟩ := indMembersRunJ_of_facts (bn := blk.map (·.name)) hwf
    (nonrecsOf blk) (tys.take (nonrecsOf blk).length) ⟨as ++ env.consts⟩ hF.kinds hmfs.1
    hext0 hA0 hreadys.1
  -- what the environment after the types and constructors finds
  have hkeepM : ∀ k c, (⟨as ++ env.consts⟩ : Env .anon).find? k = some c →
      k ∉ blk.map (·.name) →
      (storeMembers ⟨as ++ env.consts⟩ (nonrecsOf blk)
        (tys.take (nonrecsOf blk).length)).find? k = some c := by
    intro k c hc hk
    refine storeMembers_find_keep _ _ _ k c hc (fun hin => hk ?_)
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hin
    exact List.mem_map.mpr ⟨ci, hNmem ci hci, rfl⟩
  have hnonbase : ∀ k (j : Nat), iotaKey k j ∉ blk.map (·.name) := by
    intro k j hin
    obtain ⟨ci, hci, hn⟩ := List.mem_map.mp hin
    exact auxKey_ne_of_isBaseKey (hkey ci hci).1 hn.symm
  have heqM : (storeMembers ⟨as ++ env.consts⟩ (nonrecsOf blk)
      (tys.take (nonrecsOf blk).length)).find? eqName = some eqA :=
    hkeepM _ _ (hg.find_prefix _ _ heq) (hnotmem _ (by rw [heq]; rfl))
  -- the stored nonrecursive members
  have hstoredN : ∀ ci ∈ nonrecsOf blk, ∃ c,
      (storeMembers ⟨as ++ env.consts⟩ (nonrecsOf blk)
        (tys.take (nonrecsOf blk).length)).find? ci.name = some c ∧
      IxVM.Consistency.StoredAs c ci := by
    intro ci hci
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hci
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hi
    have hlenT := MembersFacts.length_eq _ _ hmfs.1
    obtain ⟨tyA, hty⟩ : ∃ tyA, (tys.take (nonrecsOf blk).length)[i]? = some tyA :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    refine ⟨_, storeMembers_find _ _ _ hNnd i ci tyA hi hty, ?_⟩
    have hk : isTypeOrCtor ci = true := List.all_eq_true.mp hF.kinds ci hci
    exact storedAs_storedMember hk (MembersFacts.get hmfs.1 hi hty).annotated
  by_cases hrecs : recsOf blk = []
  · -- no recursor
    refine ⟨aliasMap tbl, as,
      storeMembers ⟨as ++ env.consts⟩ (nonrecsOf blk) (tys.take (nonrecsOf blk).length), hg,
      hroots, hnames, htgt, ?_, ?_, ?_, ?_⟩
    · set_option smartUnfolding false in
      exact ⟨hF.split, _, hmem, Or.inl ⟨hrecs, rfl⟩⟩
    · intro ci hci
      have hci' : ci ∈ nonrecsOf blk ++ recsOf blk := by rw [← hF.split]; exact hci
      rw [hrecs, List.append_nil] at hci'
      exact hstoredN ci hci'
    · intro i ci tyA hi hty
      exact storeMembers_find _ _ _ hNnd i ci tyA hi (htake hi hty)
    · intro i cv mI rP rules tyA rhss hi
      rw [hrecs] at hi
      simp at hi
  · -- the recursors without rules, then with their rules
    obtain ⟨hprov, hextS, hAS⟩ := provisionRecsRunJ_of_facts (bn := blk.map (·.name)) hwf
      (recsOf blk) (tys.drop (nonrecsOf blk).length) _ (recsOf_all_isRecursor blk) hmfs.2
      hextM hAM hreadys.2
    have hR : RuleRecordEnv env ⟨as ++ env.consts⟩
        (storeMembers ⟨as ++ env.consts⟩ (nonrecsOf blk) (tys.take (nonrecsOf blk).length))
        (storeMembers (storeMembers ⟨as ++ env.consts⟩ (nonrecsOf blk)
          (tys.take (nonrecsOf blk).length)) (recsOf blk) (tys.drop (nonrecsOf blk).length))
        adv.ren (aliasMap tbl) blk tys (blk.map (·.name)) := by
      refine ⟨hwf, hsi, hout, hmoves, htarget, hfixes, hblk, ?_, ?_, hextS, hAS, ?_⟩
      · intro k cvj cnP cnF hc
        rcases hc with hc | ⟨i, cv, tyC, hbi, hti, hname, rfl⟩
        · have hsome : (env.find? k).isSome = true := by rw [hc]; rfl
          refine ⟨hkeepM _ _ (hg.find_prefix _ _ hc) (hnotmem k hsome), ?_⟩
          have hcw := hwf _ (List.mem_of_find?_eq_some hc)
          have hres : cvj.type.constsResolve env = true := hcw.2.2.1
          rw [renameConsts_eq_self_of_constsResolve hgfix _ hres]
          exact hres
        · obtain ⟨hlt, hni⟩ := nonrecs_getElem? hF.split hbi rfl
          have htN : (tys.take (nonrecsOf blk).length)[i]? = some tyC := by
            rw [List.getElem?_take_of_lt hlt]
            exact hti
          refine ⟨?_, (MembersFacts.get hF.members hbi hti).renamed_resolves hwf⟩
          rw [← hname]
          exact storeMembers_find _ _ _ hNnd i _ tyC hni htN
      · intro k j c hc
        exact hkeepM _ _ hc (hnonbase k j)
      · intro k hk
        cases hb : (blk.map (·.name)).contains k with
        | false =>
          rw [hout k hb] at hk
          obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hk
          exact Option.isSome_iff_exists.mpr ⟨c, hextS.find hc⟩
        | true =>
          obtain ⟨ci, hci, rfl⟩ := hmemb k hb
          have hci' : ci ∈ nonrecsOf blk ++ recsOf blk := by rw [← hF.split]; exact hci
          rcases List.mem_append.mp hci' with hci' | hci'
          · refine storeMembers_isSome_keep _ _ _ _ ?_
            obtain ⟨c, hc, -⟩ := hstoredN ci hci'
            rw [hc]
            rfl
          · exact storeMembers_isSome_mem _ _ _ (MembersFacts.length_eq _ _ hmfs.2) ci hci'
    obtain ⟨out, hfold, hkeep, hstoredR, hstoredF⟩ := indRecsFoldRenRunJ_of_aliased hR
      (recsOf blk) (tys.drop (nonrecsOf blk).length) rhsss adv.thms
      (storeMembers ⟨as ++ env.consts⟩ (nonrecsOf blk) (tys.take (nonrecsOf blk).length))
      hrecsA hmfs.2
      (fun ci hci => hblk ci (hRmem ci hci)) hRnd
    refine ⟨aliasMap tbl, as, out, hg, hroots, hnames, htgt, ?_, ?_, ?_, ?_⟩
    · set_option smartUnfolding false in
      exact ⟨hF.split, _, hmem, Or.inr ⟨fun he => hrecs he, heqM, _, _, hprov, hfold⟩⟩
    · intro ci hci
      have hci' : ci ∈ nonrecsOf blk ++ recsOf blk := by rw [← hF.split]; exact hci
      rcases List.mem_append.mp hci' with hci' | hci'
      · obtain ⟨c, hc, hs⟩ := hstoredN ci hci'
        exact ⟨c, (hkeep _ (hdisj ci hci')).trans hc, hs⟩
      · exact hstoredR ci hci'
    · intro i ci tyA hi hty
      exact (hkeep _ (hdisj ci (List.mem_of_getElem? hi))).trans
        (storeMembers_find _ _ _ hNnd i ci tyA hi (htake hi hty))
    · intro i cv mI rP rules tyA rhss hi hty hrh
      have hty' : (tys.drop (nonrecsOf blk).length)[i]? = some tyA := by
        rw [List.getElem?_drop]
        exact hty
      exact hstoredF i cv mI rP rules tyA rhss hi hty' hrh

/-- **The family step's record from the family check's facts** (module docstring). -/
theorem familyRecord_of_facts {env : Env .anon} {blk : List (ConstantInfo .anon)}
    {adv : FamilyAdvice} {tys : List KExpr} {rhsss : List (List KExpr)}
    (hF : FamilyCheckFacts env blk adv tys rhsss) (hsi : Ix.Kernel.Open.StoreInv env)
    (hnd : (blk.map (·.name)).Nodup)
    (hkey : ∀ ci ∈ blk, isBaseKey ci.name = true ∧
      Ix.Kernel.reservedBasisNames.contains ci.name = false)
    (hfresh : ∀ ci ∈ blk, env.find? ci.name = none)
    (hnewM : ∀ ci ∈ blk, env.find? (auxKey ci.name .model) = none)
    (hnewI : ∀ ci ∈ blk, ∀ j, env.find? (iotaKey ci.name j) = none)
    (heq : env.find? eqName = some eqA) :
    ∃ (h : KKey → KKey) (aliases : List (ConstantInfo .anon)) (env₂ : Env .anon),
      AliasGroup env h aliases ∧
      (∀ a ∈ aliases, ∃ ci ∈ blk, a.name.base = ci.name) ∧
      DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ blk env₂ ∧
      (∀ ci ∈ blk, ∃ c, env₂.find? ci.name = some c ∧ IxVM.Consistency.StoredAs c ci) ∧
      (∀ (i : Nat) (ci : ConstantInfo .anon) (tyA : KExpr), (nonrecsOf blk)[i]? = some ci →
        tys[i]? = some tyA → env₂.find? ci.name = some (storedMember ci tyA)) ∧
      (∀ (i : Nat) (cv : ConstantVal .anon) (mI rP : Nat) (rules : List (RecRule .anon))
        (tyA : KExpr) (rhss : List KExpr),
        (recsOf blk)[i]? = some (.recInfo cv mI rP rules) →
        tys[(nonrecsOf blk).length + i]? = some tyA → rhsss[i]? = some rhss →
        ∃ rules' : List (RecRule .anon),
          env₂.find? cv.name = some (.recInfo ⟨cv.name, cv.levelParams, tyA⟩ mI rP rules') ∧
          List.Forall₂ IxVM.Consistency.RuleStored rules' rules ∧
          List.Forall₂ (fun (r' : RecRule .anon) rhsA => r'.rhs = rhsA) rules' rhss) := by
  obtain ⟨h, as, env₂, hg, hroots, -, -, hd, hst, hN, hR⟩ :=
    familyRecord_of_facts_full hF hsi hnd hkey hfresh hnewM hnewI heq
  exact ⟨h, as, env₂, hg, hroots, hd, hst, hN, hR⟩

end IxVM.Refinement.Decl.FamilyAlias

namespace IxVM.Refinement.Typing.FamilyAlias

open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)
open Ix.Kernel.Semantics (DeclIndRenRunJ)
open IxVM.Refinement.Decl.FamilyAlias (AliasGroup famJ FamilyAdvice FamilyCheckFacts
  familyRecord_of_facts familyRecord_of_facts_full)

/-- **The family step's record from the family check's facts, with installed members and alias
naming/target facts**. -/
theorem famStepConclusion_installed_full {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {B rb : _root_.Address} {cb crb : Ixon.Constant} {env : Ix.Kernel.Env .anon}
    {blk : List (ConstantInfo .anon)} {adv : FamilyAdvice}
    {tys : List IxVM.Refinement.Core.KExpr} {rhsss : List (List IxVM.Refinement.Core.KExpr)}
    (hF : FamilyCheckFacts env blk adv tys rhsss)
    (hreads : FamDeclReads t E₀ B cb rb crb blk)
    (hsi : Ix.Kernel.Open.StoreInv env) (hroot : Decl.AuxRootSynced env)
    (heq : env.find? Ix.Kernel.eqName = some Ix.Kernel.eqA)
    (hfresh : ∀ x, FamAddr B cb rb crb x → env.find? (keyOf t x) = none)
    (hfree : ∀ x, FamAddr B cb rb crb x → Decl.KeyFree (keyOf t x)) :
    ∃ (h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon)
      (aliases : List (ConstantInfo .anon)) (env₂ : Ix.Kernel.Env .anon),
      AliasGroup env h aliases ∧
      (∀ a ∈ aliases, ∃ ci ∈ blk, a.name.base = ci.name) ∧
      (∀ a ∈ aliases, ∃ ci ∈ blk,
        a.name = Ix.Kernel.auxKey ci.name .model ∨
          ∃ j, a.name = Decl.FamilyAlias.iotaKey ci.name j) ∧
      (∀ ci ∈ blk, h (Ix.Kernel.auxKey ci.name .model) = adv.ren ci.name) ∧
      DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ blk env₂ ∧
      (∀ ci ∈ blk, ∃ c, env₂.find? ci.name = some c ∧ StoredAs c ci) ∧
      (∀ (i : Nat) (ci : ConstantInfo .anon) (tyA : IxVM.Refinement.Core.KExpr),
        (Decl.FamilyAlias.nonrecsOf blk)[i]? = some ci → tys[i]? = some tyA →
        env₂.find? ci.name = some (Decl.FamilyAlias.storedMember ci tyA)) ∧
      (∀ (i : Nat) (cv : ConstantVal .anon) (mI rP : Nat)
        (rules : List (Ix.Kernel.RecRule .anon)) (tyA : IxVM.Refinement.Core.KExpr)
        (rhss : List IxVM.Refinement.Core.KExpr),
        (Decl.FamilyAlias.recsOf blk)[i]? = some (.recInfo cv mI rP rules) →
        tys[(Decl.FamilyAlias.nonrecsOf blk).length + i]? = some tyA → rhsss[i]? = some rhss →
        ∃ rules' : List (Ix.Kernel.RecRule .anon),
          env₂.find? cv.name = some (.recInfo ⟨cv.name, cv.levelParams, tyA⟩ mI rP rules') ∧
          List.Forall₂ RuleStored rules' rules ∧
          List.Forall₂ (fun (r' : Ix.Kernel.RecRule .anon) rhsA => r'.rhs = rhsA) rules' rhss) := by
  have hmem : ∀ ci ∈ blk, ∃ x, FamAddr B cb rb crb x ∧ ci.name = keyOf t x := by
    intro ci hci
    obtain ⟨x, hx, hk, -⟩ := hreads.2.1 ci hci
    exact ⟨x, hx, hk⟩
  have hbase : ∀ ci ∈ blk, Decl.isBaseKey ci.name = true := by
    intro ci hci
    obtain ⟨x, -, hk⟩ := hmem ci hci
    rw [hk]
    exact Decl.isBaseKey_keyOf t x
  have hfr : ∀ ci ∈ blk, env.find? ci.name = none := by
    intro ci hci
    obtain ⟨x, hx, hk⟩ := hmem ci hci
    rw [hk]
    exact hfresh x hx
  have hkey : ∀ ci ∈ blk, Decl.isBaseKey ci.name = true ∧
      Ix.Kernel.reservedBasisNames.contains ci.name = false := by
    intro ci hci
    obtain ⟨x, hx, hk⟩ := hmem ci hci
    refine ⟨hbase ci hci, ?_⟩
    rw [hk]
    exact (hfree x hx).1
  exact familyRecord_of_facts_full hF hsi hreads.1 hkey hfr
    (fun ci hci => hroot.fresh_auxKey (hbase ci hci) (hfr ci hci) .model)
    (fun ci hci j => hroot.fresh_auxKey2 (hbase ci hci) (hfr ci hci) .model (.iota j))
    heq

/-- **The family step's record from the family check's facts, with the installed members**: the
alias group, the roots, IxCK's renamed record and each member stored as its reading, from the facts
at the family as read (`FamDeclReads`), the prefix's store invariant and root synchronization, the
pinned equality, and the target's own freshness and key-freedom hypotheses on the family's
addresses; and the members as the record installs them from the selected annotated types `tys`
and right-hand sides `rhsss`: each type and constructor at its position as `storedMember` of its
`tys` entry, each recursor at its type's `tys` entry with rules whose right-hand sides are its
`rhsss` entry. -/
theorem famStepConclusion_installed {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {B rb : _root_.Address} {cb crb : Ixon.Constant} {env : Ix.Kernel.Env .anon}
    {blk : List (ConstantInfo .anon)} {adv : FamilyAdvice}
    {tys : List IxVM.Refinement.Core.KExpr} {rhsss : List (List IxVM.Refinement.Core.KExpr)}
    (hF : FamilyCheckFacts env blk adv tys rhsss)
    (hreads : FamDeclReads t E₀ B cb rb crb blk)
    (hsi : Ix.Kernel.Open.StoreInv env) (hroot : Decl.AuxRootSynced env)
    (heq : env.find? Ix.Kernel.eqName = some Ix.Kernel.eqA)
    (hfresh : ∀ x, FamAddr B cb rb crb x → env.find? (keyOf t x) = none)
    (hfree : ∀ x, FamAddr B cb rb crb x → Decl.KeyFree (keyOf t x)) :
    ∃ (h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon)
      (aliases : List (ConstantInfo .anon)) (env₂ : Ix.Kernel.Env .anon),
      AliasGroup env h aliases ∧
      (∀ a ∈ aliases, ∃ ci ∈ blk, a.name.base = ci.name) ∧
      DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ blk env₂ ∧
      (∀ ci ∈ blk, ∃ c, env₂.find? ci.name = some c ∧ StoredAs c ci) ∧
      (∀ (i : Nat) (ci : ConstantInfo .anon) (tyA : IxVM.Refinement.Core.KExpr),
        (Decl.FamilyAlias.nonrecsOf blk)[i]? = some ci → tys[i]? = some tyA →
        env₂.find? ci.name = some (Decl.FamilyAlias.storedMember ci tyA)) ∧
      (∀ (i : Nat) (cv : ConstantVal .anon) (mI rP : Nat)
        (rules : List (Ix.Kernel.RecRule .anon)) (tyA : IxVM.Refinement.Core.KExpr)
        (rhss : List IxVM.Refinement.Core.KExpr),
        (Decl.FamilyAlias.recsOf blk)[i]? = some (.recInfo cv mI rP rules) →
        tys[(Decl.FamilyAlias.nonrecsOf blk).length + i]? = some tyA → rhsss[i]? = some rhss →
        ∃ rules' : List (Ix.Kernel.RecRule .anon),
          env₂.find? cv.name = some (.recInfo ⟨cv.name, cv.levelParams, tyA⟩ mI rP rules') ∧
          List.Forall₂ RuleStored rules' rules ∧
          List.Forall₂ (fun (r' : Ix.Kernel.RecRule .anon) rhsA => r'.rhs = rhsA) rules' rhss) := by
  have hmem : ∀ ci ∈ blk, ∃ x, FamAddr B cb rb crb x ∧ ci.name = keyOf t x := by
    intro ci hci
    obtain ⟨x, hx, hk, -⟩ := hreads.2.1 ci hci
    exact ⟨x, hx, hk⟩
  have hbase : ∀ ci ∈ blk, Decl.isBaseKey ci.name = true := by
    intro ci hci
    obtain ⟨x, -, hk⟩ := hmem ci hci
    rw [hk]
    exact Decl.isBaseKey_keyOf t x
  have hfr : ∀ ci ∈ blk, env.find? ci.name = none := by
    intro ci hci
    obtain ⟨x, hx, hk⟩ := hmem ci hci
    rw [hk]
    exact hfresh x hx
  have hkey : ∀ ci ∈ blk, Decl.isBaseKey ci.name = true ∧
      Ix.Kernel.reservedBasisNames.contains ci.name = false := by
    intro ci hci
    obtain ⟨x, hx, hk⟩ := hmem ci hci
    refine ⟨hbase ci hci, ?_⟩
    rw [hk]
    exact (hfree x hx).1
  exact familyRecord_of_facts hF hsi hreads.1 hkey hfr
    (fun ci hci => hroot.fresh_auxKey (hbase ci hci) (hfr ci hci) .model)
    (fun ci hci j => hroot.fresh_auxKey2 (hbase ci hci) (hfr ci hci) .model (.iota j))
    heq

/-- **The family step's conclusion from the family check's facts**: `FamilyStepTarget`'s
conclusion, from the facts at the family as read (`FamDeclReads`), the prefix's store invariant
and root synchronization, the pinned equality, and the target's own freshness and key-freedom
hypotheses on the family's addresses (`famStepConclusion_installed`). -/
theorem famStepConclusion_of_facts {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {B rb : _root_.Address} {cb crb : Ixon.Constant} {env : Ix.Kernel.Env .anon}
    {blk : List (ConstantInfo .anon)} {adv : FamilyAdvice}
    {tys : List IxVM.Refinement.Core.KExpr} {rhsss : List (List IxVM.Refinement.Core.KExpr)}
    (hF : FamilyCheckFacts env blk adv tys rhsss)
    (hreads : FamDeclReads t E₀ B cb rb crb blk)
    (hsi : Ix.Kernel.Open.StoreInv env) (hroot : Decl.AuxRootSynced env)
    (heq : env.find? Ix.Kernel.eqName = some Ix.Kernel.eqA)
    (hfresh : ∀ x, FamAddr B cb rb crb x → env.find? (keyOf t x) = none)
    (hfree : ∀ x, FamAddr B cb rb crb x → Decl.KeyFree (keyOf t x)) :
    ∃ (h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon)
      (aliases blk' : List (ConstantInfo .anon)) (env₂ : Ix.Kernel.Env .anon),
      AliasGroup env h aliases ∧
      (∀ a ∈ aliases, ∃ ci ∈ blk', a.name.base = ci.name) ∧
      FamDeclReads t E₀ B cb rb crb blk' ∧
      DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ blk' env₂ ∧
      (∀ ci ∈ blk', ∃ c, env₂.find? ci.name = some c ∧ StoredAs c ci) := by
  obtain ⟨h, as, env₂, hg, hroots, hd, hst, -, -⟩ :=
    famStepConclusion_installed hF hreads hsi hroot heq hfresh hfree
  exact ⟨h, as, blk, env₂, hg, hroots, hreads, hd, hst⟩

end IxVM.Refinement.Typing.FamilyAlias
