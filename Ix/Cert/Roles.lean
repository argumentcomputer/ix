import Ix.Cert.Compile
import Ix.Cert.Statement
import IxC.Kernel.Ixon.Prelude
import Ix.RoleEvidence

/-! # Roles in a compiled artifact (Route A, B5a)

Source mode binds a role by its Lean name; Ixon mode binds it by the role
table's address. They agree on `sub` when every role whose Lean name `sub`
declares is published at the table's address for it: `RolesBound`, decided
by `rolesBound` (`rolesBound_iff`). This is the binding `kernel-pin-gen`
checks when it writes the default table (`Benchmarks/Kernel/PinGen.lean`);
here it is a property of a compile's artifact. Stated over the compile's whole
input, it is what the artifact's alias fibers need (`Ix.LeanIngress.fiberAlias`
ranges over every published name), and every closure inherits it
(`RolesBound.of_closure`).

`RolesBound` looks the declared roles' names up by their stored hashes. On an
artifact whose names' hashes need not be their own (the prover's), the form that
gives the agreement is `Ix.Cert.PublishedRolesBound`: by ingress name, over every
published name (`Ix.Cert.publishedAddress_role`, and the table rule's premise
`Ix.Cert.tableBound_of`). -/

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

/-- **The closure's role bindings follow from the whole input's.** `RolesBound` over
the compile's whole input is the one the artifact's alias fibers need
(`Ix.LeanIngress.fiberAlias` ranges over every published name, not only the
closure's); the closure `sub` of any roots inherits it, every constant of `sub` being
the input's. -/
theorem RolesBound.of_closure {t : RoleTable} {ixe : Ixon.Env} {env : Ix.Environment}
    {roots : List Ix.Name} {sub : Ix.Environment} (h : RolesBound t ixe env)
    (closure : Ix.Cert.IsClosure env roots sub) : RolesBound t ixe sub := by
  intro r hr hc
  apply h r hr
  rw [Std.HashMap.contains_eq_isSome_getElem?] at hc ⊢
  change (env.consts.get? (roleName r)).isSome = true
  change (sub.consts.get? (roleName r)).isSome = true at hc
  by_cases reach : Ix.Cert.Reaches env roots (roleName r)
  · rw [← (closure _).1 reach]
    exact hc
  · rw [(closure _).2 reach] at hc
    cases hc

end Ix.Cert.Roles
