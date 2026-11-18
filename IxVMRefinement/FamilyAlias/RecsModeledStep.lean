import IxVMRefinement.FamilyAlias.Assembly
import IxVMRefinement.TwinFamily.Target

/-! # The family recursors' companions across the family step

`FamilyRecsModeled` (`TwinFamily/Target.lean`): where the environment stores a constant at a
constant address of a claimed family record, it is a recursor with a model companion. The family
row asks it after the step, beside the target's conclusion. `familyRecsModeled_famStep` gives it
from the clause before the step and the target's conclusion (`FamilyRecsModeled.step`):

* the step keeps every stored constant (the alias group and the record extend the prefix);
* a key the step newly stores at the key of a claimed record's constant address is a member's
  (an alias sits at a derived key, the key of an address is a base key); that member is a
  recursor (`hclaim`, a fact of the family graph: a block shares a constant address with a
  claimed family record only at its own record's recursors); it is stored as a recursor
  (`StoredAs`) and has a model companion (`modelSide_of_target`'s second conjunct). -/

universe u

namespace IxVM.Refinement.Typing.FamilyAlias

open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)
open Ix.Kernel.Semantics (DeclIndRenRunJ)
open IxVM.Refinement.Decl.FamilyAlias (AliasGroup famJ isRecursor auxKey_ne_of_isBaseKey
  find?_append_none)

set_option linter.unusedVariables false

/-- Every alias of a group sits at a derived key. -/
theorem AliasGroup.name_aux {env : Ix.Kernel.Env .anon} {h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon}
    {as : List (ConstantInfo .anon)} (hg : AliasGroup env h as) :
    ∀ a ∈ as, ∃ n d, a.name = Ix.Kernel.auxKey n d := by
  induction hg with
  | nil _ => exact fun _ ha => nomatch ha
  | @cons h₀ h' as' n d lps ty tgt ci _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨n, d, rfl⟩
    · exact ih a ha

/-- **The family recursors' companions after the family step** (module docstring). `hclaim`:
a member of the block at the key of a claimed family record's constant address is a
recursor. -/
theorem familyRecsModeled_famStep {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {fam : _root_.Address → Option _root_.Address} {A rb : _root_.Address}
    {c crb : Ixon.Constant} {env env₂ : Ix.Kernel.Env .anon}
    {h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon} {aliases blk : List (ConstantInfo .anon)}
    (hX : FamilyRecsModeled t E₀ fam env)
    (hg : AliasGroup env h aliases)
    (hd : DeclIndRenRunJ (famJ h) ⟨aliases ++ env.consts⟩ blk env₂)
    (hst : ∀ ci ∈ blk, ∃ c', env₂.find? ci.name = some c' ∧ StoredAs c' ci)
    (hclaim : ∀ (B' rb' x : _root_.Address) (crb' : Ixon.Constant), fam B' = some rb' →
      recordOf E₀ rb' = some crb' → ConstAddrOf rb' crb' x →
      ∀ ci ∈ blk, ci.name = keyOf t x → isRecursor ci = true) :
    FamilyRecsModeled t E₀ fam env₂ := by
  have hext : Ix.Kernel.EnvExt env env₂ :=
    hg.envExt.trans (Ix.Kernel.Semantics.declIndRenRunJ_envExt hd)
  obtain ⟨new, henv₂, hnew, -⟩ := famStep_consts hd
  refine FamilyRecsModeled.step hX (fun hc => hext.find hc) ?_
  intro B' rb' x crb' hrb hcrb hx hs hold
  have hbase : Decl.isBaseKey (keyOf t x) = true := Decl.isBaseKey_keyOf t x
  -- the new key is a member's
  have hex : ∃ a ∈ new ++ aliases, a.name = keyOf t x := by
    refine Classical.byContradiction (fun hne => ?_)
    have hall : ∀ a ∈ new ++ aliases, a.name ≠ keyOf t x := fun a ha he => hne ⟨a, ha, he⟩
    have h0 := find?_append_none (env := env) (new ++ aliases) hall hold
    have h1 : (⟨(new ++ aliases) ++ env.consts⟩ : Ix.Kernel.Env .anon) = env₂ := henv₂.symm
    rw [h1] at h0
    rw [h0] at hs
    exact Bool.false_ne_true hs
  obtain ⟨a, ha, han⟩ := hex
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨ci, hci, hcn⟩ := hnew a ha
    have hk : ci.name = keyOf t x := hcn.symm.trans han
    have hrec := hclaim B' rb' x crb' hrb hcrb hx ci hci hk
    obtain ⟨c', hc', hS⟩ := hst ci hci
    rw [hk] at hc'
    cases ci with
    | recInfo cv mI rP rules =>
      cases c' with
      | recInfo cv' mI' rP' rules' =>
        refine ⟨⟨cv', mI', rP', rules', hc'⟩, ?_⟩
        refine Decl.FamilyAlias.hasModel_declIndRenJ hd hc' ?_
        refine find?_append_none aliases (fun b hb heq => ?_) hold
        obtain ⟨n, d, hn⟩ := AliasGroup.name_aux hg b hb
        rw [hn] at heq
        exact auxKey_ne_of_isBaseKey hbase heq
      | _ => exact hS.2.elim
    | _ => exact absurd hrec Bool.false_ne_true
  · exfalso
    obtain ⟨n, d, hn⟩ := AliasGroup.name_aux hg a ha
    rw [hn] at han
    exact auxKey_ne_of_isBaseKey hbase han

end IxVM.Refinement.Typing.FamilyAlias
