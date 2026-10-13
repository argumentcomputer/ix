import Ix.CompileCert.Audit
import Ix.CompileCert.Opt.O11aBatchClosing

/-! The axiom audit of `Ix.CompileCert.Opt.O11aBatchClosing`.
Elaboration fails unless every root exists, none is listed twice, and each
depends only on the standard axioms (`Ix.CompileCert.Audit.checkAuditRoots`). -/

run_cmd (Ix.CompileCert.Audit.checkAuditRoots #[
  ``Ix.CompileCert.Opt.O11aBatchClosing.declarationTable_push,
  ``Ix.CompileCert.Opt.O11aBatchClosing.declarationTable_bound,
  ``Ix.CompileCert.Opt.O11aBatchClosing.declarationTable_absent,
  ``Ix.CompileCert.Opt.O11aBatchClosing.babs_insert_inactive,
  ``Ix.CompileCert.Opt.O11aBatchClosing.babs_insert_last,
  ``Ix.CompileCert.Opt.O11aBatchClosing.erasedLambda_push,
  ``Ix.CompileCert.Opt.O11aBatchClosing.mkLambda_push_er,
  ``Ix.CompileCert.Opt.O11aBatchClosing.mkLambda_eq_closeDecls,
  ``Ix.CompileCert.Opt.O11aBatchClosing.binderStep_scope,
  ``Ix.CompileCert.Opt.O11aBatchClosing.binderLoop_scope,
  ``Ix.CompileCert.Opt.O11aBatchClosing.binderLoop_batch_eq_sequential,
  ``Ix.CompileCert.Opt.O11aBatchClosing.prepared_field_prefix_batch_close,
  ``Ix.CompileCert.Opt.O11aBatchClosing.sizeOfMinorWith_batch_eq_sequential
] Ix.CompileCert.Audit.allowedAxioms)
