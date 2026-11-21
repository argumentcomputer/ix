import IxVMRefinement.FamilyAlias.ModelAliases

/-! # The types and constructors of a family, installed from their facts

IxC's renamed record installs a family's types and constructors in order, each at its annotated
type (`IndMembersRunJ`). This module gives that run from the members' facts.

* `storedMember`: a member as the record stores it, at its annotated type (a recursor without
  rules).
* `MembersReady`: what each member needs of the environment it is stored in, given the members
  stored before it: its name is fresh and is no reserved, projection or model key; its annotated
  type resolves; on it the block renaming followed by the alias renaming is the renaming to the
  advice; and the environment stores its alias.
* `storeMembers`: the environment after the listed members are stored.
* `indMembersRunJ_of_facts`: from the members' facts and `MembersReady`, the run of the record
  over the family package to that environment, and that it extends the prefix and stores the
  aliases the renaming moves.

`MembersReady`, like `AliasesReady`, is a condition on names and on what an environment stores;
its derivation from the facts' scope field and the freshness of the family's names is in
`FamilyAlias/MembersFromScope.lean`. -/

namespace IxVM.Refinement.Decl.FamilyAlias

open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel.Model
open Ix.Kernel (Env Expr Key Level ConstantInfo ConstantVal RecRule LevelParam ReducibilityHint
  EnvExt EnvWF auxKey)

set_option linter.unusedVariables false

/-- **A member as the record stores it**: at its annotated type; a type at the empty capability
record, a recursor without rules. -/
def storedMember : ConstantInfo .anon → KExpr → ConstantInfo .anon
  | .indInfo cv _, tyA => .indInfo ⟨cv.name, cv.levelParams, tyA⟩ {}
  | .ctorInfo cv nP nF, tyA => .ctorInfo ⟨cv.name, cv.levelParams, tyA⟩ nP nF
  | .recInfo cv mI rP _, tyA => .recInfo ⟨cv.name, cv.levelParams, tyA⟩ mI rP []
  | ci, _ => ci

theorem storedMember_name (ci : ConstantInfo .anon) (tyA : KExpr) :
    (storedMember ci tyA).name = ci.name := by
  cases ci <;> rfl

/-- **What each member needs of the environment it is stored in** (`env'`), given that the
members before it are stored as the record stores them. -/
def MembersReady (g h : KKey → KKey) (bn : List KKey) :
    Env .anon → List (ConstantInfo .anon) → List KExpr → Prop
  | env', ci :: rest, tyA :: tys =>
    env'.find? ci.toConstantVal.name = none ∧
    Ix.Kernel.reservedBasisNames.contains ci.toConstantVal.name = false ∧
    ci.toConstantVal.name.isProjFnShape = false ∧
    ci.toConstantVal.name.isModelSuffix = false ∧
    (∀ T, ci.toConstantVal.name ≠ Ix.Kernel.projTableName T) ∧
    (tyA.renameConsts (blockRen bn)).renameConsts h = tyA.renameConsts g ∧
    tyA.constsResolve env' = true ∧
    (∃ (mval : KExpr) (hint : ReducibilityHint),
      env'.find? (auxKey ci.toConstantVal.name .model) = some (.defnInfo
        ⟨auxKey ci.toConstantVal.name .model, ci.toConstantVal.levelParams,
          tyA.renameConsts (blockRen bn)⟩ mval hint)) ∧
    MembersReady g h bn ⟨storedMember ci tyA :: env'.consts⟩ rest tys
  | _, _, _ => True

/-- **The environment after the listed members are stored**, each as the record stores it, in
the list's order (the last member is the newest constant). -/
def storeMembers : Env .anon → List (ConstantInfo .anon) → List KExpr → Env .anon
  | env', ci :: rest, tyA :: tys => storeMembers ⟨storedMember ci tyA :: env'.consts⟩ rest tys
  | env', _, _ => env'

/-- **The types and constructors of a family, installed from their facts.** `env` is the prefix,
`env'` the environment the first member is stored in; the run leaves the members stored as the
record stores them (`storeMembers`). -/
theorem indMembersRunJ_of_facts {env : Env .anon} {g h : KKey → KKey} {bn : List KKey}
    (hwf : EnvWF env) :
    ∀ (ms : List (ConstantInfo .anon)) (tys : List KExpr) (env' : Env .anon),
      ms.all isTypeOrCtor = true → MembersFacts env g ms tys →
      EnvExt env env' → AliasEnv env' h → MembersReady g h bn env' ms tys →
      IndMembersRunJ (renameJ (blockRen bn) (famJ h)) bn {} env' ms (storeMembers env' ms tys) ∧
        EnvExt env (storeMembers env' ms tys) ∧ AliasEnv (storeMembers env' ms tys) h
  | [], [], env', _, _, hext, hA, _ => ⟨rfl, hext, hA⟩
  | [], _ :: _, _, _, hm, _, _, _ => nomatch hm
  | _ :: _, [], _, _, hm, _, _, _ => nomatch hm
  | ci :: rest, tyA :: tys, env', hk, hm, hext, hA, hr => by
    obtain ⟨hF, hrestF⟩ := hm
    obtain ⟨hfresh, hres, hprj, hsuf, hnpt, hcomp, hresolve, halias, hready⟩ := hr
    have hmv := memberValRunJ_of_facts (bn := bn) hF hwf hext hA hfresh hres hprj hsuf hcomp
      hresolve halias
    have hk' : isTypeOrCtor ci = true ∧ rest.all isTypeOrCtor = true := by
      simpa [List.all_cons, Bool.and_eq_true] using hk
    have hfresh' : env'.find? (storedMember ci tyA).name = none := by
      rw [storedMember_name]
      exact hfresh
    have hnpt' : ∀ T, (storedMember ci tyA).name ≠ Ix.Kernel.projTableName T := by
      intro T
      rw [storedMember_name]
      exact hnpt T
    have hext' : EnvExt env ⟨storedMember ci tyA :: env'.consts⟩ :=
      hext.trans (envExt_cons_fresh hfresh' hnpt')
    have hA' : AliasEnv ⟨storedMember ci tyA :: env'.consts⟩ h :=
      hA.mono (fun hf => Ix.Kernel.Env.find?_cons_of_fresh hfresh' hf)
    obtain ⟨hrun, hextM, hAM⟩ :=
      indMembersRunJ_of_facts hwf rest tys _ hk'.2 hrestF hext' hA' hready
    have hcons : storeMembers env' (ci :: rest) (tyA :: tys) =
        storeMembers ⟨storedMember ci tyA :: env'.consts⟩ rest tys := rfl
    rw [hcons]
    refine ⟨?_, hextM, hAM⟩
    cases ci with
    | indInfo cv caps => exact ⟨_, hmv, hrun⟩
    | ctorInfo cv nP nF => exact ⟨_, hmv, hrun⟩
    | axiomInfo _ => exact absurd hk'.1 (by simp [isTypeOrCtor])
    | defnInfo _ _ _ => exact absurd hk'.1 (by simp [isTypeOrCtor])
    | thmInfo _ _ => exact absurd hk'.1 (by simp [isTypeOrCtor])
    | recInfo _ _ _ _ => exact absurd hk'.1 (by simp [isTypeOrCtor])
    | projInfo _ => exact absurd hk'.1 (by simp [isTypeOrCtor])

end IxVM.Refinement.Decl.FamilyAlias
