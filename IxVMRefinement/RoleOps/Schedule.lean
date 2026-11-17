import IxVMRefinement.RoleOps.Companions
import Ix.SpecDigest.Schedule

/-! # An operation's validation group

Each of the fifteen operations is validated in a group of its own (`Ix.SpecDigest.groups`), so
the roles in force at the limit just past an operation's group are those in force at its group
and the operation. `coreCompanions_succ_group` raises the companions' group limit past the
group of an operation that is stored with its companion facts.
-/

namespace IxVM.Refinement.RoleOps

open IxVM.Refinement.Core (KKey Ctx)
open IxVM.Refinement.Decl (CoreCompanions)
open Ix.Kernel (Env Role)
open Ix.SpecDigest (groupOf)

set_option linter.unusedVariables false

/-- The fifteen operation roles. -/
def opRoles : List Role :=
  [.natPred, .natAdd, .natSub, .natMul, .natPow, .natBeq, .natBle, .natDiv, .natMod, .natGcd,
    .natLand, .natLor, .natXor, .natShiftLeft, .natShiftRight]

theorem opNames_eq_map : opNames = opRoles.map (fun r => (Ix.Kernel.Key.role r : KKey)) := rfl

private theorem opGroups_singleton_all :
    (Role.all.all fun r' => opRoles.all fun r => groupOf r' != groupOf r || r' == r) = true := by
  decide +kernel

/-- **An operation's group holds that operation alone.** -/
theorem opGroup_singleton {r r' : Role} (hop : (Ix.Kernel.Key.role r : KKey) ∈ opNames)
    (hg : groupOf r' = groupOf r) : r' = r := by
  rw [opNames_eq_map] at hop
  obtain ⟨r₀, hr₀, heq⟩ := List.mem_map.mp hop
  have heq' : (Ix.Kernel.Key.role r₀ : KKey) = Ix.Kernel.Key.role r := heq
  have hr : r₀ = r := Ix.Kernel.Key.role.inj heq'
  rw [hr] at hr₀
  have h : (groupOf r' != groupOf r || r' == r) = true :=
    List.all_eq_true.mp (List.all_eq_true.mp opGroups_singleton_all r' (Role.mem_all r')) r hr₀
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  rcases h with h | h
  · exact absurd hg h
  · exact h

/-- **The companions just past an operation's group**: the companions at the limit of the
operation's group, and the operation's companion facts, give the companions at the next
limit. -/
theorem coreCompanions_succ_group {E : Ixon.Env} {env : Env .anon} {t : Ix.Kernel.RoleTable}
    {r : Role} (hop : (Ix.Kernel.Key.role r : KKey) ∈ opNames)
    (h : CoreCompanions ⟨E, env, t, some (groupOf r)⟩) (hc : OpCompanion env r) :
    CoreCompanions ⟨E, env, t, some (groupOf r + 1)⟩ := by
  refine coreCompanions_withOps h ?_
  intro r' hf
  by_cases hlt : groupOf r' < groupOf r
  · refine Or.inl ⟨hf.1, ?_⟩
    intro n hn
    have hn' : some (groupOf r) = some n := hn
    injection hn' with hn'
    rw [← hn']
    exact hlt
  · have hle : groupOf r' < groupOf r + 1 := hf.2 (groupOf r + 1) rfl
    have heq : groupOf r' = groupOf r := by omega
    rw [opGroup_singleton hop heq]
    exact Or.inr hc

end IxVM.Refinement.RoleOps
