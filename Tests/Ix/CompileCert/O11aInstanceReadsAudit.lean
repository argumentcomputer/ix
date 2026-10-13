import Ix.CompileCert.Audit
import Ix.CompileCert.Opt.O11aInstanceReads

/-! The axiom audit of `Ix.CompileCert.Opt.O11aInstanceReads`.
Elaboration fails unless every root exists, none is listed twice, and each
depends only on the standard axioms (`Ix.CompileCert.Audit.checkAuditRoots`). -/

run_cmd (Ix.CompileCert.Audit.checkAuditRoots #[
  ``Ix.CompileCert.Opt.O11aInstanceReads.sizeOfInstanceE_success,
  ``Ix.CompileCert.Opt.O11aInstanceReads.sizeOfInstanceE_returnedName,
  ``Ix.CompileCert.Opt.O11aInstanceReads.functionRead_spelling,
  ``Ix.CompileCert.Opt.O11aInstanceReads.functionSpelling_apply,
  ``Ix.CompileCert.Opt.O11aInstanceReads.functionBody_beta,
  ``Ix.CompileCert.Opt.O11aInstanceReads.actual_function_application,
  ``Ix.CompileCert.Opt.O11aInstanceReads.instanceBody_inst_spine,
  ``Ix.CompileCert.Opt.O11aInstanceReads.recursorArgs_last,
  ``Ix.CompileCert.Opt.O11aInstanceReads.instanceBody_inst_last,
  ``Ix.CompileCert.Opt.O11aInstanceReads.sizeOfInstanceE_local_function,
  ``Ix.CompileCert.Opt.O11aInstanceReads.sizeOfReplacement_instance_delta
] Ix.CompileCert.Audit.allowedAxioms)
