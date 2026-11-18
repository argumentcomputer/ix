import IxVMRefinement.FamilyAlias.AliasesFromScope

/-! # The alias group of a family's members, from the family check's facts

`aliasGroup_members_of_facts`: the model aliases of a family's members (`modelAliases`: for
each type, constructor and recursor the definition at its model key by its advice model) are an
alias group over the prefix, from `FamilyCheckFacts` and three facts about the prefix and the
names:

* the prefix stores well-formed constants (`EnvWF`, a field of the prefix invariant's store
  part);
* the family's names are distinct (a conjunct of the family's reading);
* the prefix stores no model key of a member. The prefix invariant gives this from the
  freshness of the family's names: a stored derived key has its root stored
  (`AuxRootSynced`).

The aliases of the rules' theorems are not in this group; they come after it. -/

namespace IxVM.Refinement.Decl.FamilyAlias

open IxVM.Refinement.Core
open Ix.Kernel (Env Expr Key ConstantInfo EnvWF auxKey)

set_option linter.unusedVariables false

/-- A key that is no key of the table is not moved. -/
theorem aliasMap_of_not_key :
    ∀ (tbl : List (KKey × KKey)) (k : KKey), k ∉ tbl.map (·.1) → aliasMap tbl k = k
  | [], _, _ => rfl
  | p :: rest, k, hk => by
    have h1 : ¬ k = p.1 := fun heq => hk (by rw [heq]; exact List.mem_cons_self)
    have h2 : k ∉ rest.map (·.1) := fun hin => hk (List.mem_cons_of_mem _ hin)
    exact (ite_eq_right h1).trans (aliasMap_of_not_key rest k h2)

/-- **The members' model aliases are an alias group over the prefix**, from the family check's
facts, the prefix's well-formedness, the distinctness of the family's names, and the freshness
of the members' model keys. The group's renaming sends each member's model key to the member's
advice model. -/
theorem aliasGroup_members_of_facts {env : Env .anon} {blk : List (ConstantInfo .anon)}
    {adv : FamilyAdvice} {tys : List KExpr} {rhsss : List (List KExpr)}
    (hF : FamilyCheckFacts env blk adv tys rhsss) (hwf : EnvWF env)
    (hnd : (blk.map (·.name)).Nodup)
    (hnew : ∀ ci ∈ blk, env.find? (auxKey ci.name .model) = none) :
    AliasGroup env (aliasMap (modelTable adv.ren blk tys []))
      (modelAliases adv.ren (blk.map (·.name)) blk tys []) := by
  have hout : ∀ k, (blk.map (·.name)).contains k = false → adv.ren k = k := by
    intro k hk
    have hk' : k ∉ blk.map (·.name) := by simpa using hk
    exact aliasMap_of_not_key adv.models k (by rw [hF.table]; exact hk')
  have hnew' : ∀ k, (blk.map (·.name)).contains k = true →
      env.find? (auxKey k .model) = none := by
    intro k hk
    have hk' : k ∈ blk.map (·.name) := by simpa using hk
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hk'
    exact hnew ci hci
  exact aliasGroup_modelAliases hwf blk tys [] [] (AliasGroup.nil (fun _ => rfl)) hF.members
    (aliasesReady_of_scope hwf hout hnew' blk tys [] [] [] hF.members hF.typesScoped hnd
      (fun k hk => Or.inr (by simpa using hk))
      (fun k hk => by simpa using hk)
      (fun _ hk => nomatch hk)
      (AliasStage.start env adv.ren)
      (fun k hk => by
        obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hk
        exact hnew ci hci))

end IxVM.Refinement.Decl.FamilyAlias
