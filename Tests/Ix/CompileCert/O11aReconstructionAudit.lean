import Ix.CompileCert.Audit
import Ix.CompileCert.Opt.FreshTelescope
import Ix.CompileCert.Opt.O11aReconstruction

/-! The axiom audit of `Ix.CompileCert.Opt.O11aReconstruction` and the fresh-telescope
lemmas it uses.
Elaboration fails unless every root exists, none is listed twice, and each
depends only on the standard axioms (`Ix.CompileCert.Audit.checkAuditRoots`). -/

run_cmd (Ix.CompileCert.Audit.checkAuditRoots #[
  ``Ix.CompileCert.Opt.FreshTelescope.openRequests_grows,
  ``Ix.CompileCert.Opt.FreshTelescope.openRequests_protects,
  ``Ix.CompileCert.Opt.FreshTelescope.openRequests_close_of_protected,
  ``Ix.CompileCert.Opt.FreshTelescope.protected_openRequests_close,
  ``Ix.CompileCert.Opt.FreshTelescope.openRequests_reserved,
  ``Ix.CompileCert.Opt.FreshTelescope.er_mkLambda,
  ``Ix.CompileCert.Opt.FreshTelescope.mkLambda_er_congr,
  ``Ix.CompileCert.Opt.FreshTelescope.mkLambda_singleton,
  ``Ix.CompileCert.Opt.FreshTelescope.closeDecls_append,
  ``Ix.CompileCert.Opt.FreshTelescope.closeDecls_er_congr,
  ``Ix.CompileCert.Opt.FreshTelescope.fresh_lambda_close,
  ``Ix.CompileCert.Opt.O11aReconstruction.binderStep_retained_close,
  ``Ix.CompileCert.Opt.O11aReconstruction.binderList_retained_close,
  ``Ix.CompileCert.Opt.O11aReconstruction.binderLoop_field_prefix_close,
  ``Ix.CompileCert.Opt.O11aReconstruction.prepared_field_prefix_close,
  ``Ix.CompileCert.Opt.O11aReconstruction.sizeOfMinorWith_erased,
  ``Ix.CompileCert.Opt.O11aReconstruction.sizeOfMinorWith_reconstruction
] Ix.CompileCert.Audit.allowedAxioms)
