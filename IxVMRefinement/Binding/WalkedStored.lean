import IxVMRefinement.Binding.Defs
import Ix.IxVM.Consistency.TableValid

/-! # The run's checked records stored

`WalkedStored ρ t G R env`: the closure's coverage of what a binding run checked. Every record of
the store that is no block, that the run checked under a role context, and that is in Lean's
logic with its block, is stored at its key in the environment; and so is the role of every
walked role of a group of `G`. The operations' validation facts read it at the references the
validation walks; the closure of a group establishes it.
-/

namespace IxVM.Refinement.Binding

open IxVM.Consistency

/-- **The run's checked records are stored**: every record of `R` that is no block, that the run
checked under a role context at some limit, and that is in Lean's logic with its block, is
stored at its key in `env`; and the role of every walked role of a group of `G` is stored. The
closure of a group establishes it for the records its walk reached; the operations' validation
facts read it at the references of the operation's record and of its certificates' proofs,
which the validation walks. -/
def WalkedStored (ρ : BRun) (t : Ix.Kernel.RoleTable) (G : Nat → Prop) (R : Ixon.Env)
    (env : Ix.Kernel.Env .anon) : Prop :=
  (∀ (x : _root_.Address) (c : Ixon.Constant) (n : Nat), recordOf R x = some c →
    (∀ ms, c.info ≠ .muts ms) → InLogic c →
    (∀ cb, recordOf R (Ix.Cert.ownerOf x c) = some cb → InLogic cb) → ρ.checked x n →
    (env.find? (keyOf t x)).isSome = true) ∧
  (∀ (r : Ix.Kernel.Role) (x : _root_.Address), walkedRole r = true →
    G (Ix.SpecDigest.groupOf r) → t.addressOf? r = some x →
    (env.find? (keyOf t x)).isSome = true)

end IxVM.Refinement.Binding
