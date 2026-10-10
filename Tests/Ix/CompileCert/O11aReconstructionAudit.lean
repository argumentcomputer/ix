import Ix.CompileCert.Opt.FreshTelescope
import Ix.CompileCert.Opt.O11aReconstruction

-- Prospective additive roots only; no accepted audit is changed.
#print axioms Ix.CompileCert.Opt.FreshTelescope.openRequests_grows
#print axioms Ix.CompileCert.Opt.FreshTelescope.openRequests_protects
#print axioms Ix.CompileCert.Opt.FreshTelescope.openRequests_close_of_protected
#print axioms Ix.CompileCert.Opt.FreshTelescope.protected_openRequests_close
#print axioms Ix.CompileCert.Opt.FreshTelescope.openRequests_reserved
#print axioms Ix.CompileCert.Opt.FreshTelescope.er_mkLambda
#print axioms Ix.CompileCert.Opt.FreshTelescope.mkLambda_er_congr
#print axioms Ix.CompileCert.Opt.FreshTelescope.mkLambda_singleton
#print axioms Ix.CompileCert.Opt.FreshTelescope.closeDecls_append
#print axioms Ix.CompileCert.Opt.FreshTelescope.closeDecls_er_congr
#print axioms Ix.CompileCert.Opt.FreshTelescope.fresh_lambda_close
#print axioms Ix.CompileCert.Opt.O11aReconstruction.binderStep_retained_close
#print axioms Ix.CompileCert.Opt.O11aReconstruction.binderList_retained_close
#print axioms Ix.CompileCert.Opt.O11aReconstruction.binderLoop_field_prefix_close
#print axioms Ix.CompileCert.Opt.O11aReconstruction.prepared_field_prefix_close
#print axioms Ix.CompileCert.Opt.O11aReconstruction.sizeOfMinorWith_erased
#print axioms Ix.CompileCert.Opt.O11aReconstruction.sizeOfMinorWith_reconstruction
