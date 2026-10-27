import Ix.Cert.AcceptedKeys
import Ix.Cert.ReadingKeys
import Ix.Cert.SourceStoredNames

/-! # Source totality

`Obligation.SourceTotal`: quotient Source installs each key once
(`AcceptedKeys.sourceKeys_unique`), and every constant the closure stores, except
those represented by the inert `sorryAx` role, has a constant of quotient Source's
environment under its quotient key, at the address the artifact publishes it at.

* **Declared**: the prepared stream declares the name's quotient key
  (`SourceDeclares.preparedAt_declares`).
* **Installed**: the reference accept installs every name its declarations declare,
  `sorryAx`'s role aside, its stream's front declaring the quotient type
  (`SourceInstalls.accepts_names`, `SourceInstalls.prepared_quot`).
* **Published**: the name is published under that exact spelling
  (`SourceStoredNames.stored_published`), so the artifact gives its quotient key the
  name's published address (`AddressEquation`, the reader's address equation). -/

namespace Ix.Cert.SourceTotality

/-- **The address equation**: the artifact gives the quotient key of a name it publishes
that name's published address, under a checked role table that binds the published role
names and an address map the published names agree with. -/
def AddressEquation : Prop :=
  ∀ (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable), t.check = .ok () → PublishedRolesBound t ixe →
    PublishedAgree ixe → ∀ (m : Ix.Name) (named : Ixon.Named), (m, named) ∈ ixe.named.toList →
      keyAddress ixe t (quotientKey ixe t m) = some named.addr

/-- **Source totality, from the address equation.** -/
theorem sourceTotal_of_address (address : AddressEquation) : Obligation.SourceTotal := by
  intro env roots sub ixe failures t envQ hP
  refine ⟨AcceptedKeys.sourceKeys_unique hP, fun n ci hn hsorry => ?_⟩
  obtain ⟨-, pre, ds, hpre, hprep, hacc⟩ := hP.source
  obtain ⟨d, hd, hk⟩ := SourceDeclares.preparedAt_declares hprep hn
  obtain ⟨st, decls, -, -, hds⟩ :=
    Ix.LeanIngress.prepareSourceCollapsed_keepsPrelude (SourceDeclares.preparedAt_collapsed hprep)
  have hquot : ∃ d₀ ∈ ds.toList, (Ix.Kernel.quotName : Ix.Kernel.Key .source) ∈ d₀.names := by
    rw [hds]
    exact SourceInstalls.prepared_quot hpre decls
  obtain ⟨c, hc, hname⟩ :=
    SourceInstalls.accepts_names (k := quotientKey ixe t n) hacc hquot hd hk hsorry
  obtain ⟨named, hmem, hget⟩ := SourceStoredNames.stored_published hP hn
  refine ⟨c, hc, hname, ?_⟩
  rw [hname, hget, Option.map_some]
  exact address ixe t (defaultTable_check hP.table) hP.bound hP.agree n named hmem

/-- info: 'Ix.Cert.SourceTotality.sourceTotal_of_address' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sourceTotal_of_address

/-- **Source totality**: the address equation is the reader's
`ReadingKeys.keyAddress_quotientKey`. -/
theorem sourceTotal : Obligation.SourceTotal :=
  sourceTotal_of_address fun _ _ c b a _ _ h => ReadingKeys.keyAddress_quotientKey c b a h

/-- info: 'Ix.Cert.SourceTotality.sourceTotal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sourceTotal

end Ix.Cert.SourceTotality
