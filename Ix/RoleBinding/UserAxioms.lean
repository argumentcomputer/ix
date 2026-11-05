module

public import Ix.RoleBinding.ArtifactTiered

/-! # User axioms at the conditional entries (host side, uncertified)

`ix check-lean --allow-user-axioms` and `kernel-check-ixe --allow-user-axioms`
admit safe axioms beyond Lean's standard three: an `.axiomDecl` whose key is an
input constant's (`Ix.Kernel.Key.isCustomAxiomEligible`). Without the flag both
are strict, and such an axiom declines. The conditional entries
(`Artifact.checkConditional`, `Artifact.checkTieredConditional`) have no
theorem and no host statement, so a run that admits a user axiom reports its
verdict as conditional on the axioms listed here.

* `requireAxiomRoles`: the binding must bind `sorryAx`, `propext` and
  `Classical.choice`. A binding that leaves one of them out keys Lean's own
  constant as an input constant, and the conditional entries would admit it as
  a user axiom.
* `ofPrepared`: the user axioms among the declarations the conditional entry
  reads from the artifact: the same reading (`Admission.readStream`) of the
  same prepared records, the logical part of the tier partition, with the
  prelude in front. Opaques are definitions here, not axioms.

Nothing here is trusted; the kernel's own checks are the boundary. -/

@[expose] public section

namespace Ix.RoleBinding.UserAxioms

open Ix.Kernel (Role RoleTable)

/-- The axiom roles a binding must bind before user axioms are admitted. -/
def axiomRoles : List Role := [.sorryAx, .propext, .choice]

/-- The axiom roles `table` leaves unbound. -/
def unboundAxiomRoles (table : RoleTable) : List Role :=
  axiomRoles.filter fun r => (table.addressOf? r).isNone

/-- Refuse a binding that leaves an axiom role unbound, and an artifact with no
binding. The binding is admitted as the entries admit it. -/
def requireAxiomRoles (binding? : Option Ixon.RoleBinding) : Except String Unit := do
  let names := ", ".intercalate (axiomRoles.map (toString ·.leanName))
  let some binding := binding?
    | throw s!"user axioms require a role binding that binds {names}; the artifact carries none"
  let table ← (Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨binding.address, binding.bytes⟩).mapError
    fun e => toString (Ix.Kernel.Admission.Error.binding e)
  let missing := unboundAxiomRoles table
  unless missing.isEmpty do
    throw s!"user axioms require a role binding that binds {names}; this binding leaves \
      {", ".intercalate (missing.map (toString ·.leanName))} unbound"

/-- The addresses of the user axioms among `decls`, in order. -/
def ofDecls (decls : List (Ix.Kernel.Declaration .anon)) : Array Address :=
  (Ix.Kernel.userAxiomsOfDecls decls).toArray.filterMap fun cv =>
    match cv.name with
    | .id address => some address
    | _ => none

/-- The user axioms among the declarations the conditional entry reads from a
prepared artifact: its logical part, read under its own table and prelude. -/
def ofPrepared (input : Artifact.PreparedRecords) : Except String (Array Address) := do
  let p := input.prepared
  let (logical, _) := Ix.Kernel.Admission.partitionTier input.constants
  let (_, decls) ← (Ix.Kernel.Admission.readStream Address.admissionHash p.table p.pre logical p.blobs
    p.hints.lookup).mapError toString
  return ofDecls (Ix.Kernel.Frontend.preparePrelude p.pre.ix decls).toList

end Ix.RoleBinding.UserAxioms

end
