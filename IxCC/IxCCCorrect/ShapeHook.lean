import IxCCCorrect.Shape2Check
import IxCC.Shape.Src.Hook

/-!
# `IxCCCorrect.ShapeHook`: re-exports

Moved to production as `IxCC.Shape.Src.Hook` (namespace `IxCC.SrcShape`), which needs no
model. Every name is re-exported here under `IxCC.Correct.Shape2`, so modules written against
the old names build unchanged; `#print axioms` of an old name prints the production name.
-/

namespace IxCC.Correct.Shape2

export IxCC.SrcShape (
  tys_nat_of_resultTy natRootOk rootsOk rootsOk_get neverWrong_of_check neverStuck_checked
  enumRootOk neverWrong_of_enumRoot rootOk frontRootsOk frontRootsOk_get Refusal
  checkShaped checkShaped_sound runShaped runShaped_ok runShaped_sound
  neverWrong_of_shape_view rc_tys_nat_of_resultTy rc_view_nat_ok rc_neverWrong_of_check
  rc_sound_of_shape rcRunShaped rcRunShaped_sound)

end IxCC.Correct.Shape2
