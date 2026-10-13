import Ix.CompileCert.Audit
import Ix.CompileCert.TypeRows

/-! The axiom audit of the installed type rows (`Ix.CompileCert.TypeRows`).
Elaboration fails unless every root exists, none is listed twice, and each
depends only on the standard axioms (`Ix.CompileCert.Audit.checkAuditRoots`). -/

run_cmd (Ix.CompileCert.Audit.checkAuditRoots #[
  ``Ix.CompileCert.installedTypeRowF,
  ``Ix.CompileCert.installedTypeRowF_spec,
  ``Ix.CompileCert.checkInstalledTypesRowsF,
  ``Ix.CompileCert.checkInstalledTypesRows,
  ``Ix.CompileCert.checkInstalledTypesRows_member,
  ``Ix.CompileCert.checkInstalledTypesRows_sound,
  ``Ix.CompileCert.checkedTypeRowsModel,
  ``Ix.CompileCert.checkedTypeRowsValueModel
] Ix.CompileCert.Audit.allowedAxioms)
