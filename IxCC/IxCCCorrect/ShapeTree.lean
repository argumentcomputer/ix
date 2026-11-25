import IxCCCorrect.ShapeHook
import IxCC.Shape.Src.Tree

/-!
# `IxCCCorrect.ShapeTree`: re-exports

Moved to production as `IxCC.Shape.Src.Tree` (namespace `IxCC.SrcShape`), which needs no
model. Every name is re-exported here under `IxCC.Correct.Shape2`, so modules written against
the old names build unchanged; `#print axioms` of an old name prints the production name.
-/

namespace IxCC.Correct.Shape2

export IxCC.SrcShape (
  readsOk fieldsRead ctorReads mapReads Reads ReadsAll treeView_ctor fieldsView_cons
  eraseVal_con reads_fields reads_lt reads_val rc_view_tree_ok treeRootOk
  rc_neverWrong_of_treeRoot view_enum_ok_any rcEnumRootOk rc_neverWrong_of_enumRoot
  rcRootOk rcRootsOk rcRootsOk_get rcCheckShaped rcCheckShaped_sound rcRunShapedTree
  rcRunShapedTree_sound pairsOf treeMap natParamsOf treeMapsFor aritiesFor)

end IxCC.Correct.Shape2
