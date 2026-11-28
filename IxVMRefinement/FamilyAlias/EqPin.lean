import IxVMRefinement.Assembly.TypingSkeleton

/-! # The pinned equality at every extension of a valid table's environment

IxCK's record of a family with a recursor asks that the pinned equality be stored. The family
check reads the equality's address only inside a rule's statement, and the prefix invariant
speaks of the equality only where its role is in force. What stores it is the table: a valid
table's environment holds every pinned block whole (`TableShape.pins`), and a unit's step is
asked only at environments that extend it and have distinct names. -/

namespace IxVM.Refinement.Typing.FamilyAlias

open IxVM.Consistency
open Ix.Kernel (ConstantInfo)

universe u

/-- **The pinned equality is stored at every extension of a valid table's environment** with
distinct names: the pinned block is in the witness's environment (`TableShape.pins`). -/
theorem eqPin_of_shape {t : Ix.Kernel.RoleTable} {G : Nat → Prop} {R : Ixon.Env}
    {envT env : Ix.Kernel.Env .anon} (hshape : TableShape.{u} t G R envT)
    (hext : ∀ ci ∈ envT.consts, ci ∈ env.consts) (hnd : (env.consts.map (·.name)).Nodup) :
    env.find? Ix.Kernel.eqName = some Ix.Kernel.eqA := by
  have hm : (Ix.Kernel.eqA : ConstantInfo .anon) ∈ env.consts :=
    hext _ (hshape.pins .eqK _ List.mem_cons_self)
  have hf := find_of_mem_nodup hnd hm
  have hn : (Ix.Kernel.eqA : ConstantInfo .anon).name = Ix.Kernel.eqName := by
    decide +kernel
  rw [hn] at hf
  exact hf

end IxVM.Refinement.Typing.FamilyAlias
