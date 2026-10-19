import Ix.Cert.Compile
import IxC.Kernel.Ixon.Prelude
import Ix.RoleEvidence

/-! # Roles in a compiled artifact (Route A, B5a)

Source mode binds a role by its Lean name; Ixon mode binds it by the role
table's address. They agree on `sub` when every role whose Lean name `sub`
declares is published at the table's address for it: `RolesBound`, decided
by `rolesBound` (`rolesBound_iff`). This is the binding `kernel-pin-gen`
checks when it writes the default table (`Benchmarks/Kernel/PinGen.lean`);
here it is a property of a compile's artifact. -/

namespace Ix.Cert.Roles

open Ix.Kernel

/-- The name a role's constant is published under (`kernel-pin-gen`'s). -/
def roleName (r : Role) : Ix.Name :=
  Ix.Name.fromLeanName (Ix.RoleEvidence.toLeanName (roleKey (md := .anon) r))

/-- Every role whose Lean name `sub` declares is published at `t`'s address
for it. -/
def RolesBound (t : RoleTable) (ixe : Ixon.Env) (sub : Ix.Environment) : Prop :=
  ∀ r ∈ Role.all, sub.consts.contains (roleName r) = true →
    (ixe.named.get? (roleName r)).map (·.addr) = t.addressOf? r

/-- `RolesBound`, decided. -/
def rolesBound (t : RoleTable) (ixe : Ixon.Env) (sub : Ix.Environment) : Bool :=
  Role.all.all fun r =>
    !sub.consts.contains (roleName r) || (ixe.named.get? (roleName r)).map (·.addr) == t.addressOf? r

theorem rolesBound_iff (t : RoleTable) (ixe : Ixon.Env) (sub : Ix.Environment) :
    rolesBound t ixe sub = true ↔ RolesBound t ixe sub := by
  simp only [rolesBound, RolesBound, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq]
  constructor
  · intro h r hr hc
    rcases h r hr with h | h
    · rw [hc] at h; cases h
    · exact h
  · intro h r hr
    cases hc : sub.consts.contains (roleName r)
    · exact Or.inl rfl
    · exact Or.inr (h r hr hc)

end Ix.Cert.Roles
