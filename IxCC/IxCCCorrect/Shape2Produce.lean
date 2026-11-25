import IxCCCorrect.Shape2Check
import IxCC.Shape.Src.Produce

/-!
# `IxCCCorrect.Shape2Produce`: re-exports

Moved to production as `IxCC.Shape.Src.Produce` (namespace `IxCC.SrcShape.Produce`). Every
name is re-exported here under `IxCC.Correct.Shape2.Produce`.
-/

namespace IxCC.Correct.Shape2.Produce

export IxCC.SrcShape.Produce (
  TV TV.shape Atom TV.atoms St M finalSort sortish polyTy predParams piDom? wordOf recordWord
  tyEval tyApply
  tyConst mkData fieldShapes piShape refix bodyOf peel projFn addInst addSite ctorSites
  walk step loop interOf produceAllWith produceWith produce produceAll Limits Declined
  Declined.render loopCapped propose
  holdsWord mentions prune rangeShape variants withRanges rangeRes natWrappers )

end IxCC.Correct.Shape2.Produce
