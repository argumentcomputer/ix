import IxVMRefinement.FamilyAlias.MembersRun

/-! # The recursors of a family, provisioned from their facts

IxC's renamed record first stores a family's recursors without rules, each at its annotated type
(`ProvisionRecsRunJ`), and lists what the install fold then walks. This module gives that run
from the recursors' facts, as `MembersRun.lean` gives the run of the types and constructors: a
recursor before its rules is a member like the others, with the same front door and the same
alias at its model key.

* `provisioned`: the list the install fold walks: each recursor's stored value, its two counts
  and its rules as read.
* `provisionRecsRunJ_of_facts`: from the recursors' facts and `MembersReady`, the run over the
  family package, the environment it leaves (every recursor stored without rules), and that this
  environment extends the prefix and stores the aliases the renaming moves. -/

namespace IxVM.Refinement.Decl.FamilyAlias

open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel.Model
open Ix.Kernel (Env Expr Key Level ConstantInfo ConstantVal RecRule LevelParam ReducibilityHint
  EnvExt EnvWF auxKey)

set_option linter.unusedVariables false

/-- Whether a member is a recursor. -/
def isRecursor : ConstantInfo .anon → Bool
  | .recInfo _ _ _ _ => true
  | _ => false

/-- **What the install fold walks**: each recursor's stored value (at its annotated type), the
position of its major premise, the length of its rule prefix, and its rules as read. -/
def provisioned : List (ConstantInfo .anon) → List KExpr →
    List (ConstantVal .anon × Nat × Nat × List (RecRule .anon))
  | .recInfo cv mI rP rules :: rest, tyA :: tys =>
    (⟨cv.name, cv.levelParams, tyA⟩, mI, rP, rules) :: provisioned rest tys
  | _, _ => []

/-- **The recursors of a family, provisioned from their facts.** `env` is the prefix, `envAcc`
the environment the first recursor is stored in. -/
theorem provisionRecsRunJ_of_facts {env : Env .anon} {g h : KKey → KKey} {bn : List KKey}
    (hwf : EnvWF env) :
    ∀ (recs : List (ConstantInfo .anon)) (tys : List KExpr) (envAcc : Env .anon),
      recs.all isRecursor = true → MembersFacts env g recs tys →
      EnvExt env envAcc → AliasEnv envAcc h → MembersReady g h bn envAcc recs tys →
      ∃ envSelf : Env .anon,
        ProvisionRecsRunJ (renameJ (blockRen bn) (famJ h)) bn envAcc recs envSelf
          (provisioned recs tys) ∧
        EnvExt env envSelf ∧ AliasEnv envSelf h
  | [], [], envAcc, _, _, hext, hA, _ => ⟨envAcc, ⟨rfl, rfl⟩, hext, hA⟩
  | [], _ :: _, _, _, hm, _, _, _ => nomatch hm
  | _ :: _, [], _, _, hm, _, _, _ => nomatch hm
  | ci :: rest, tyA :: tys, envAcc, hk, hm, hext, hA, hr => by
    obtain ⟨hF, hrestF⟩ := hm
    obtain ⟨hfresh, hres, hprj, hsuf, hnpt, hcomp, hresolve, halias, hready⟩ := hr
    have hmv := memberValRunJ_of_facts (bn := bn) hF hwf hext hA hfresh hres hprj hsuf hcomp
      hresolve halias
    have hk' : isRecursor ci = true ∧ rest.all isRecursor = true := by
      simpa [List.all_cons, Bool.and_eq_true] using hk
    have hfresh' : envAcc.find? (storedMember ci tyA).name = none := by
      rw [storedMember_name]
      exact hfresh
    have hnpt' : ∀ T, (storedMember ci tyA).name ≠ Ix.Kernel.projTableName T := by
      intro T
      rw [storedMember_name]
      exact hnpt T
    have hext' : EnvExt env ⟨storedMember ci tyA :: envAcc.consts⟩ :=
      hext.trans (envExt_cons_fresh hfresh' hnpt')
    have hA' : AliasEnv ⟨storedMember ci tyA :: envAcc.consts⟩ h :=
      hA.mono (fun hf => Ix.Kernel.Env.find?_cons_of_fresh hfresh' hf)
    obtain ⟨envSelf, hrun, hextS, hAS⟩ :=
      provisionRecsRunJ_of_facts hwf rest tys _ hk'.2 hrestF hext' hA' hready
    cases ci with
    | recInfo cv mI rP rules =>
      exact ⟨envSelf, ⟨_, mI, rP, rules, _, rfl, hmv, hrun, rfl⟩, hextS, hAS⟩
    | axiomInfo _ => exact absurd hk'.1 (by simp [isRecursor])
    | defnInfo _ _ _ => exact absurd hk'.1 (by simp [isRecursor])
    | thmInfo _ _ => exact absurd hk'.1 (by simp [isRecursor])
    | indInfo _ _ => exact absurd hk'.1 (by simp [isRecursor])
    | ctorInfo _ _ _ => exact absurd hk'.1 (by simp [isRecursor])
    | projInfo _ => exact absurd hk'.1 (by simp [isRecursor])

end IxVM.Refinement.Decl.FamilyAlias
