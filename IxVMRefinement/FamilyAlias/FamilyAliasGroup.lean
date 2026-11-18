import IxVMRefinement.FamilyAlias.RuleAliasGroup
import IxVMRefinement.FamilyAlias.MemberAliasGroup

/-! # The alias group of a family, from the family check's facts

`aliasGroup_family`: the aliases of a family (for each type, constructor and recursor the
definition at its model key by its advice model; then, for each rule of each recursor, the
definition at its `iota` key by its advice theorem, whose type is the rule copy of the advice
statement) are an alias group over the prefix, in that order of installation.

From `FamilyCheckFacts` and four facts about the prefix and the names: the prefix stores
well-formed constants; the family's names are distinct; the prefix stores no model key and no
`iota` key of a member. With the group come what the record installed over it reads: the
renaming sends each member's model key to the member's model; each member's alias is found at
its model key; each alias sits at a member's model key or at an `iota` key of a member; and
each rule's facts with the rule's alias as found (`RecsAliased`).

The lemmas before it are the bookkeeping of the members' aliases (`modelAliases`, `modelTable`:
accumulating recursions) that `aliasGroup_members_of_facts` did not need to state. -/

namespace IxVM.Refinement.Decl.FamilyAlias

open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel (Env Expr Key Level ConstantInfo ConstantVal RecRule LevelParam EnvWF Derived
  auxKey)

set_option linter.unusedVariables false

/-! ## The members' aliases and their table -/

section Members

variable {g : KKey → KKey} {bn : List KKey}

/-- An earlier alias stays among the members' aliases. -/
theorem modelAliases_keep :
    ∀ (ms : List (ConstantInfo .anon)) (tys : List KExpr) (as : List (ConstantInfo .anon))
      (a : ConstantInfo .anon), a ∈ as → a ∈ modelAliases g bn ms tys as
  | [], _, _, _, ha => ha
  | _ :: _, [], _, _, ha => ha
  | ci :: rest, tyA :: tys, _, a, ha =>
    modelAliases_keep rest tys _ a (List.mem_cons_of_mem _ ha)

/-- Each of the members' aliases is an earlier alias, or sits at a member's model key. -/
theorem modelAliases_name :
    ∀ (ms : List (ConstantInfo .anon)) (tys : List KExpr) (as : List (ConstantInfo .anon))
      (a : ConstantInfo .anon), a ∈ modelAliases g bn ms tys as →
      a ∈ as ∨ ∃ ci ∈ ms, a.name = auxKey ci.name .model
  | [], _, _, _, ha => Or.inl ha
  | _ :: _, [], _, _, ha => Or.inl ha
  | ci :: rest, tyA :: tys, as, a, ha => by
    rcases modelAliases_name rest tys (modelAlias g bn ci tyA :: as) a ha with h | ⟨c, hc, hn⟩
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr ⟨ci, List.mem_cons_self, rfl⟩
      · exact Or.inl h
    · exact Or.inr ⟨c, List.mem_cons_of_mem _ hc, hn⟩

/-- The alias of the `i`-th member is among the members' aliases. -/
theorem modelAlias_mem :
    ∀ (ms : List (ConstantInfo .anon)) (tys : List KExpr) (as : List (ConstantInfo .anon))
      (i : Nat) (ci : ConstantInfo .anon) (tyA : KExpr), ms[i]? = some ci →
      tys[i]? = some tyA → modelAlias g bn ci tyA ∈ modelAliases g bn ms tys as
  | [], _, _, _, _, _, hc, _ => by simp at hc
  | _ :: _, [], _, _, _, _, _, ht => by simp at ht
  | c₀ :: rest, t₀ :: tys, as, 0, ci, tyA, hc, ht => by
    have hc' : c₀ = ci := Option.some.inj hc
    have ht' : t₀ = tyA := Option.some.inj ht
    subst hc'
    subst ht'
    exact modelAliases_keep rest tys _ _ List.mem_cons_self
  | c₀ :: rest, t₀ :: tys, as, i + 1, ci, tyA, hc, ht =>
    modelAlias_mem rest tys (modelAlias g bn c₀ t₀ :: as) i ci tyA hc ht

/-- The members' table says of a key that is no listed member's model key what the earlier
table says. -/
theorem modelTable_keep :
    ∀ (ms : List (ConstantInfo .anon)) (tys : List KExpr) (tbl : List (KKey × KKey)) (k : KKey),
      (∀ ci ∈ ms, k ≠ auxKey ci.name .model) →
      aliasMap (modelTable g ms tys tbl) k = aliasMap tbl k
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, _, _ => rfl
  | ci :: rest, _ :: tys, tbl, k, hk =>
    (modelTable_keep rest tys _ k (fun c hc => hk c (List.mem_cons_of_mem _ hc))).trans
      (ite_eq_right (hk ci List.mem_cons_self))

/-- The members' table sends the `i`-th member's model key to the member's model, where the
names are distinct. -/
theorem modelTable_target :
    ∀ (ms : List (ConstantInfo .anon)) (tys : List KExpr) (tbl : List (KKey × KKey)),
      (ms.map (·.name)).Nodup → ∀ (i : Nat) (ci : ConstantInfo .anon), ms[i]? = some ci →
      i < tys.length → aliasMap (modelTable g ms tys tbl) (auxKey ci.name .model) = g ci.name
  | [], _, _, _, _, _, hc, _ => by simp at hc
  | _ :: _, [], _, _, _, _, _, hi => by simp at hi
  | c₀ :: rest, _ :: tys, tbl, hnd, 0, ci, hc, _ => by
    have hc' : c₀ = ci := Option.some.inj hc
    subst hc'
    obtain ⟨hhead, -⟩ := List.nodup_cons.mp hnd
    refine (modelTable_keep rest tys _ _ (fun c hcr heq => ?_)).trans (ite_eq_left rfl)
    have h1 : c₀.name = c.name :=
      (Key.aux.inj (heq : Key.aux c₀.name Derived.model = Key.aux c.name Derived.model)).1
    have h2 : c₀.name ∈ rest.map (·.name) := by
      rw [h1]
      exact List.mem_map.mpr ⟨c, hcr, rfl⟩
    exact hhead h2
  | c₀ :: rest, _ :: tys, tbl, hnd, i + 1, ci, hc, hi =>
    modelTable_target rest tys _ (List.nodup_cons.mp hnd).2 i ci hc (by simpa using hi)

end Members

/-- A key no listed constant sits at, and the environment does not store, is not stored with
the constants. -/
theorem find?_append_none {env : Env .anon} {k : KKey} :
    ∀ (as : List (ConstantInfo .anon)), (∀ a ∈ as, a.name ≠ k) → env.find? k = none →
      (⟨as ++ env.consts⟩ : Env .anon).find? k = none
  | [], _, he => he
  | a :: as, hn, he =>
    (Ix.Kernel.EnvExt.find?_cons_ne (env := (⟨as ++ env.consts⟩ : Env .anon))
      (hn a List.mem_cons_self)).trans
      (find?_append_none as (fun b hb => hn b (List.mem_cons_of_mem _ hb)) he)

/-! ## The family -/

/-- **The alias group of a family** (module docstring). -/
theorem aliasGroup_family {env : Env .anon} {blk : List (ConstantInfo .anon)}
    {adv : FamilyAdvice} {tys : List KExpr} {rhsss : List (List KExpr)}
    (hF : FamilyCheckFacts env blk adv tys rhsss) (hwf : EnvWF env)
    (hnd : (blk.map (·.name)).Nodup)
    (hnewM : ∀ ci ∈ blk, env.find? (auxKey ci.name .model) = none)
    (hnewI : ∀ ci ∈ blk, ∀ j, env.find? (iotaKey ci.name j) = none) :
    ∃ (as : List (ConstantInfo .anon)) (tbl : List (KKey × KKey)),
      AliasGroup env (aliasMap tbl) as ∧
      (∀ ci ∈ blk, aliasMap tbl (auxKey ci.name .model) = adv.ren ci.name) ∧
      (∀ (i : Nat) (ci : ConstantInfo .anon) (tyA : KExpr), blk[i]? = some ci →
        tys[i]? = some tyA →
        (⟨as ++ env.consts⟩ : Env .anon).find? (auxKey ci.name .model) =
          some (modelAlias adv.ren (blk.map (·.name)) ci tyA)) ∧
      (∀ a ∈ as, ∃ ci ∈ blk,
        a.name = auxKey ci.name .model ∨ ∃ j, a.name = iotaKey ci.name j) ∧
      RecsAliased env ⟨as ++ env.consts⟩ adv.ren blk tys (blk.map (·.name)) (recsOf blk)
        (tys.drop (nonrecsOf blk).length) rhsss adv.thms := by
  have hgM := aliasGroup_members_of_facts hF hwf hnd hnewM
  have hout : ∀ k, (blk.map (·.name)).contains k = false → adv.ren k = k := by
    intro k hk
    have hk' : k ∉ blk.map (·.name) := by simpa using hk
    exact aliasMap_of_not_key adv.models k (by rw [hF.table]; exact hk')
  have hblk : ∀ ci ∈ blk, (blk.map (·.name)).contains ci.name = true := by
    intro ci hci
    have hm : ci.name ∈ blk.map (·.name) := List.mem_map.mpr ⟨ci, hci, rfl⟩
    simpa using hm
  have hlen := MembersFacts.length_eq blk tys hF.members
  have hl2 := congrArg List.length hF.split
  rw [List.length_append] at hl2
  -- the recursors' part of the members' facts
  have hmfR : MembersFacts env adv.ren (recsOf blk) (tys.drop (nonrecsOf blk).length) := by
    have h0 : MembersFacts env adv.ren (nonrecsOf blk ++ recsOf blk)
        (tys.take (nonrecsOf blk).length ++ tys.drop (nonrecsOf blk).length) := by
      rw [List.take_append_drop, ← hF.split]
      exact hF.members
    exact (MembersFacts.split _ _ _ _ (by rw [List.length_take]; omega) h0).2
  have hRmem : ∀ ci ∈ recsOf blk, ci ∈ blk := fun ci hci => (List.mem_filter.mp hci).1
  have hRnd : ((recsOf blk).map (·.name)).Nodup := by
    have h0 : ((nonrecsOf blk).map (·.name) ++ (recsOf blk).map (·.name)).Nodup := by
      rw [← List.map_append, ← hF.split]
      exact hnd
    exact (List.nodup_append.mp h0).2.1
  -- the members' table sends each member's model key to the member's model
  have htargetM : ∀ k, (blk.map (·.name)).contains k = true →
      aliasMap (modelTable adv.ren blk tys []) (auxKey k .model) = adv.ren k := by
    intro k hk
    have hk' : k ∈ blk.map (·.name) := by simpa using hk
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hk'
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hci
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hi
    exact modelTable_target blk tys [] hnd i ci hi (by omega)
  -- the `iota` keys are fresh over the members' aliases
  have hfreshI : ∀ ci ∈ blk, ∀ j,
      (⟨modelAliases adv.ren (blk.map (·.name)) blk tys [] ++ env.consts⟩ :
        Env .anon).find? (iotaKey ci.name j) = none := by
    intro ci hci j
    refine find?_append_none _ (fun a ha heq => ?_) (hnewI ci hci j)
    rcases modelAliases_name blk tys [] a ha with h | ⟨c, -, hn⟩
    · exact nomatch h
    · rw [hn] at heq
      exact iotaKey_ne_model ci.name j c.name heq.symm
  obtain ⟨as, tbl, hg, hmap, hfind, hnames, hrecs⟩ :=
    aliasGroup_recs hwf hout hblk (recsOf blk) (tys.drop (nonrecsOf blk).length) rhsss adv.thms
      _ _ hF.recs hmfR (fun ci hci => hblk ci (hRmem ci hci)) hRnd hgM htargetM
      (fun ci hci j => hfreshI ci (hRmem ci hci) j)
  refine ⟨as, tbl, hg, ?_, ?_, ?_, hrecs⟩
  · intro ci hci
    exact (hmap (auxKey ci.name .model)
      (fun c _ j heq => iotaKey_ne_model c.name j ci.name heq.symm)).trans
      (htargetM ci.name (hblk ci hci))
  · intro i ci tyA hci hty
    exact (hfind (auxKey ci.name .model)
      (fun c _ j heq => iotaKey_ne_model c.name j ci.name heq.symm)).trans
      (hgM.find_alias _ (modelAlias_mem blk tys [] i ci tyA hci hty))
  · intro a ha
    rcases hnames a ha with h | ⟨c, hc, j, hj⟩
    · rcases modelAliases_name blk tys [] a h with h' | ⟨c, hc, hn⟩
      · exact nomatch h'
      · exact ⟨c, hc, Or.inl hn⟩
    · exact ⟨c, hRmem c hc, Or.inr ⟨j, hj⟩⟩

end IxVM.Refinement.Decl.FamilyAlias
