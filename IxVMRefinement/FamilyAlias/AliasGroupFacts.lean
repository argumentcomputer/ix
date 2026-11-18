import IxVMRefinement.FamilyAlias.AliasesFromScope

/-! # What an alias group gives, read off the group

Facts of every alias group `AliasGroup env h as` (`FamilyAlias/Install.lean`), by induction on
the group. They are what a producer of a further alias, and of the record installed over the
group, reads of the aliases already installed:

* `find_prefix`: what the prefix finds, the prefix with the aliases finds;
* `find_alias`: each alias is found under its own key;
* `moved`: a key the renaming moves is an alias's (stored with the aliases, not in the prefix);
* `fixes_prefix`: the renaming fixes every key the prefix stores;
* `stored_of_target`: a key whose image the prefix stores is stored with the aliases. So a
  term whose renaming resolves in the prefix resolves with the aliases
  (`constsResolve_of_renamed`).

* `comp_of_renamed_resolves`: on a term whose renaming to the advice resolves in the prefix,
  the block renaming followed by a renaming that sends each member's model key to the member's
  model and fixes what the prefix stores is the renaming to the advice. -/

namespace IxVM.Refinement.Decl.FamilyAlias

open IxVM.Refinement.Core
open Ix.Kernel (Env Expr Key ConstantInfo auxKey)

set_option linter.unusedVariables false

section Group

variable {env : Env .anon} {h : KKey → KKey} {as : List (ConstantInfo .anon)}

/-- What the prefix finds, the prefix with the aliases finds. -/
theorem AliasGroup.find_prefix (hg : AliasGroup env h as) :
    ∀ (k : KKey) (c : ConstantInfo .anon), env.find? k = some c →
      (⟨as ++ env.consts⟩ : Env .anon).find? k = some c := by
  induction hg with
  | nil _ => exact fun _ _ hc => hc
  | cons _ _ hfresh _ _ _ _ _ _ _ _ _ _ ih =>
    exact fun k c hc => Ix.Kernel.Env.find?_cons_of_fresh hfresh (ih k c hc)

/-- Each alias is found under its own key. -/
theorem AliasGroup.find_alias (hg : AliasGroup env h as) :
    ∀ a ∈ as, (⟨as ++ env.consts⟩ : Env .anon).find? a.name = some a := by
  induction hg with
  | nil _ => exact fun _ ha => nomatch ha
  | @cons h₀ h' as' n d lps ty tgt ci _ _ hfresh _ _ _ _ _ _ _ _ _ _ ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Ix.Kernel.Env.find?_cons_self _ (⟨as' ++ env.consts⟩ : Env .anon)
    · exact Ix.Kernel.Env.find?_cons_of_fresh hfresh (ih a ha)

/-- A key the renaming moves is an alias's: stored with the aliases, and not in the prefix. -/
theorem AliasGroup.moved (hg : AliasGroup env h as) :
    ∀ k, h k ≠ k →
      ((⟨as ++ env.consts⟩ : Env .anon).find? k).isSome = true ∧ env.find? k = none := by
  induction hg with
  | nil hid => exact fun k hk => absurd (hid k) hk
  | @cons h₀ h' as' n d lps ty tgt ci hg' _ hfresh _ _ _ _ _ _ _ _ hk' hrest ih =>
    intro k hk
    by_cases hkn : k = auxKey n d
    · subst hkn
      refine ⟨?_, ?_⟩
      · exact Option.isSome_iff_exists.mpr
          ⟨_, Ix.Kernel.Env.find?_cons_self _ (⟨as' ++ env.consts⟩ : Env .anon)⟩
      · cases hf : env.find? (auxKey n d) with
        | none => rfl
        | some c =>
          rw [hg'.find_prefix _ c hf] at hfresh
          exact nomatch hfresh
    · rw [hrest k hkn] at hk
      obtain ⟨hs, hn⟩ := ih k hk
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hs
      exact ⟨Option.isSome_iff_exists.mpr ⟨c, Ix.Kernel.Env.find?_cons_of_fresh hfresh hc⟩, hn⟩

/-- The renaming fixes every key the prefix stores. -/
theorem AliasGroup.fixes_prefix (hg : AliasGroup env h as) :
    ∀ k, (env.find? k).isSome = true → h k = k := by
  intro k hs
  by_cases hk : h k = k
  · exact hk
  · rw [(hg.moved k hk).2] at hs
    exact nomatch hs

/-- What the prefix stores, the prefix with the aliases stores. -/
theorem AliasGroup.stored_prefix (hg : AliasGroup env h as) :
    ∀ k, (env.find? k).isSome = true →
      ((⟨as ++ env.consts⟩ : Env .anon).find? k).isSome = true := by
  intro k hs
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hs
  exact Option.isSome_iff_exists.mpr ⟨c, hg.find_prefix k c hc⟩

/-- A key whose image the prefix stores is stored with the aliases. -/
theorem AliasGroup.stored_of_target (hg : AliasGroup env h as) :
    ∀ k, (env.find? (h k)).isSome = true →
      ((⟨as ++ env.consts⟩ : Env .anon).find? k).isSome = true := by
  intro k hs
  by_cases hk : h k = k
  · rw [hk] at hs
    exact hg.stored_prefix k hs
  · exact (hg.moved k hk).1

end Group

/-- **The block renaming followed by the aliases' renaming is the renaming to the advice**, on
a term whose renaming to the advice resolves in the prefix: `g` moves members only, `h` sends
each member's model key to the member's model and fixes what the prefix stores. -/
theorem comp_of_renamed_resolves {env : Env .anon} {g h : KKey → KKey} {bn : List KKey}
    (hout : ∀ k, bn.contains k = false → g k = k)
    (htarget : ∀ k, bn.contains k = true → h (auxKey k .model) = g k)
    (hfixed : ∀ k, (env.find? k).isSome = true → h k = k)
    {e : KExpr} (hres : (e.renameConsts g).constsResolve env = true) :
    (e.renameConsts (blockRen bn)).renameConsts h = e.renameConsts g := by
  rw [renameConsts_comp]
  exact renameConsts_congr_mentions e (fun k hmk => by
    show h (blockRen bn k) = g k
    cases hb : bn.contains k with
    | true =>
      have hk : blockRen bn k = auxKey k .model := ite_eq_left hb
      rw [hk]
      exact htarget k hb
    | false =>
      have hk : blockRen bn k = k := ite_eq_right (by rw [hb]; exact Bool.false_ne_true)
      rw [hk, hout k hb]
      rcases stored_of_mentions e hres hmk with hs | hs
      · rw [hout k hb] at hs
        exact hfixed k hs
      · exact hfixed k hs)

end IxVM.Refinement.Decl.FamilyAlias
