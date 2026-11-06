module

public import Ix.RoleBinding.ArtifactTiered

/-! # User axioms in the host drivers (uncertified)

`ix check-lean --allow-user-axioms` and `kernel-check-ixe --allow-user-axioms`
admit safe axioms beyond Lean's standard three: an `.axiomDecl` whose key is an
input constant's (`Ix.Kernel.Key.isCustomAxiomEligible`). Without the flag both
are strict, and such an axiom declines.

The kernel decides what is admitted and lists it. Its entries under
`AxiomPolicy.allowUser` (`Admission.checkBytesUnder`,
`checkBytesTieredUsingUnder`, run by `Artifact.checkConditional` and
`checkTieredConditional`) refuse a role table that leaves an axiom role
unbound (`Admission.admitAxiomPolicy`) and return the user axioms of the
declarations they ran over. What is left here is the host's part:

* `requireAxiomRoles`: the kernel's role-table check, `admitAxiomPolicy
  .allowUser`, on the artifact's binding, with the host's message, before a
  driver checks any declaration. The record-by-record drivers
  (`Ix/KernelCheck/{Step,Pool}.lean`, through `annotDeclStepWithUserAxioms`)
  never reach admission, so every driver runs it first
  (`CheckLeanCmd.prepareInput`, `CheckIxe.run`).
* `addresses`, `ofDecls`: the input keys of the kernel's list, for the
  drivers' `CONDITIONAL` listings; names come from the artifact's metadata.

Nothing here is trusted; the kernel's own checks are the boundary. -/

@[expose] public section

namespace Ix.RoleBinding.UserAxioms

/-- Refuse user axioms unless the artifact's binding passes the kernel's
check (`Admission.admitAxiomPolicy .allowUser`: `sorryAx`, `propext` and
`Classical.choice` bound), the binding admitted as the entries admit it; an
artifact with no binding is refused too. A binding that leaves an axiom role
out keys Lean's own constant as an input constant, which the user-axiom checks
would admit. -/
def requireAxiomRoles (binding? : Option Ixon.RoleBinding) : Except String Unit := do
  let names := ", ".intercalate (Ix.Kernel.Admission.userAxiomRoles.map (toString ·.leanName))
  let some binding := binding?
    | throw s!"user axioms require a role binding that binds {names}; the artifact carries none"
  let table ← (Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨binding.address, binding.bytes⟩).mapError
    fun e => toString (Ix.Kernel.Admission.Error.binding e)
  match Ix.Kernel.Admission.admitAxiomPolicy .allowUser table with
  | .ok () => pure ()
  | .error (.axiomRoleUnbound role) =>
    throw s!"user axioms require a role binding that binds {names}; this binding leaves \
      {role.leanName} unbound"
  | .error e => throw (toString e)

/-- The input keys of the kernel's list of user axioms, in order. -/
def addresses (axioms : List (Ix.Kernel.ConstantVal .anon)) : Array Address :=
  axioms.toArray.filterMap fun cv =>
    match cv.name with
    | .id address => some address
    | _ => none

/-- The addresses of the user axioms among `decls` (`userAxiomsOfDecls`), in
order. -/
def ofDecls (decls : List (Ix.Kernel.Declaration .anon)) : Array Address :=
  addresses (Ix.Kernel.userAxiomsOfDecls decls)

end Ix.RoleBinding.UserAxioms

end
