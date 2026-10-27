import IxC.Kernel.Audit.Axioms
import Ix.Cert.Closure
import Ix.Cert.PrefixCore
import Ix.Cert.RecursorSupport
import Ix.Cert.SourceContext.Check
import Ix.Cert.SourceContext.Maps
import Ix.Cert.SourceContext.Observations
import Ix.Cert.SourceContext.Rows
import Ix.Cert.SourceContext.Stores
import Ix.Cert.SourceGroupPlan
import Ix.Cert.SourceGroupView
import Ix.Cert.SourceInput
import Ix.Cert.SourceInput.Prepared
import Ix.Cert.SourceMetadata
import Ix.Cert.SourceOrder
import Ix.Cert.SourceOwnership
import Ix.Cert.SourceUses
import Ix.CompileCert.SourceFamily
import Ix.CompileCert.SourceFamilyTraversal
import Ix.CompileCert.SourceIdentity
import Ix.Compile.SourceInput.GroupPlan
import Ix.Compile.SourceInput.GroupView
import Ix.Compile.SourceInput.Metadata
import Ix.Compile.SourceInput.Ownership
import Ix.Compile.SourceInput.Uses
import Ix.HostAdmission.Theorems
import Ix.RoleBinding.ArtifactOrderTheorems
import Ix.RoleBinding.ArtifactTheorems
import Ix.RoleBinding.ArtifactTieredTheorems

/-! # Axioms of the proof modules outside the statement roots

`Ix/Cert/Audit.lean` fixes the axioms of the certification statements, and so
bounds every declaration they reach. The modules named here are reached by
none of them, or only in part:
* the Source-side grouping, ownership, metadata and use facts
  (`Ix.Compile.SourceInput.*`, `Ix.Cert.Source*`);
* recursor-family support (`Ix.Cert.RecursorSupport`);
* the computed closure (`Ix.Cert.Closure`), the Source order's enumeration
  (`Ix.Cert.SourceOrder`), and the stored prefix's readings at a final
  interpretation (`Ix.Cert.PrefixCore`, with the reference fronts, conversion
  values and value rows it imports);
* the Source family and identity checks (`Ix.CompileCert.Source*`);
* the theorems of the artifact and host admission entries
  (`Ix.RoleBinding.Artifact*Theorems`, `Ix.HostAdmission.Theorems`).

`lake lint` (`check-modules`) and `lake run check-kernel` build this module.

Every safe declaration of each named module, and of every `Ix.Cert` and
`Ix.CompileCert` module this module imports, depends on no axiom beyond
`propext`, `Classical.choice` and `Quot.sound` (`#guard_module_axioms`,
`IxC/Kernel/Audit/Axioms.lean`). A named module fails if it is no longer
imported or declares nothing. -/

#guard_module_axioms
  Ix.Cert.Closure
  Ix.Cert.PrefixCore
  Ix.Cert.RecursorSupport
  Ix.Cert.SourceContext.Check
  Ix.Cert.SourceContext.Maps
  Ix.Cert.SourceContext.Observations
  Ix.Cert.SourceContext.Rows
  Ix.Cert.SourceContext.Stores
  Ix.Cert.SourceGroupPlan
  Ix.Cert.SourceGroupView
  Ix.Cert.SourceInput
  Ix.Cert.SourceInput.Prepared
  Ix.Cert.SourceMetadata
  Ix.Cert.SourceOrder
  Ix.Cert.SourceOwnership
  Ix.Cert.SourceUses
  Ix.CompileCert.SourceFamily
  Ix.CompileCert.SourceFamilyTraversal
  Ix.CompileCert.SourceIdentity
  Ix.Compile.SourceInput.GroupPlan
  Ix.Compile.SourceInput.GroupView
  Ix.Compile.SourceInput.Metadata
  Ix.Compile.SourceInput.Ownership
  Ix.Compile.SourceInput.Uses
  Ix.HostAdmission.Theorems
  Ix.RoleBinding.ArtifactOrderTheorems
  Ix.RoleBinding.ArtifactTheorems
  Ix.RoleBinding.ArtifactTieredTheorems

#guard_module_axioms_under Ix.Cert Ix.CompileCert
