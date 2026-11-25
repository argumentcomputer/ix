import IxCCCorrect.Shape2
import IxCC.Shape.Src.Check

/-!
# `IxCCCorrect.Shape2Check`: re-exports

Moved to production as `IxCC.Shape.Src.Check` (namespace `IxCC.SrcShape`), which needs no
model. Every name is re-exported here under `IxCC.Correct.Shape2`, so modules written against
the old names build unchanged; `#print axioms` of an old name prints the production name.
-/

namespace IxCC.Correct.Shape2

export IxCC.SrcShape (
  Cert lookupEnum mem_of_lookupEnum Cert.sig mem_of_lookup wordEntryOk wordEntryOk_sound
  wordOk instsOf mem_instsOf appRes mem_appRes projRes mem_projRes Exp parts
  hasShape_parts isLam isLam_eq chkWith chkWith_sound readsExp wants fnExp appStep synth
  synth_sound argAt resAfter argsUpTo fldsOf fldsOf_sound isOrdinary isOrdinary_sound
  predOk predOk_sound casesOk casesOk_sound casesSubOkAt casesSubOk casesSubOkAt_sound
  rulesOk rulesOk_sound recrOkAt recrOk recrOkAt_sound recrOk_sound recrSubOkAt recrSubOk
  recrSubOkAt_sound zeroOk succOk enumCtorOk dataCtorAt dataCtorScan dataCtorScan_sound
  dataCtorOk ctorAnyOk dataCtorOk_sound ctorsOk ctorsOk_sound structOk structOk_sound enumOk
  enumOk_sound entryOk entryOk_sound certOk sigOk_of_cert neverWrong_of_cert_nat
  neverWrong_of_cert_enum)

end IxCC.Correct.Shape2
