module

public import Tests.Aiur.Common
public import Ix.IxVM.RBTreeMap

public section

public def rbTreeMapTestCases : List AiurTestCase := [
  -- Data-structure logic test: asserts insert/lookup outputs. The
  -- constraint machinery it compiles to (match, load/store, compares) is
  -- proven by the `aiur-prove` suite, so execute + interpret is the whole
  -- signal here.
  .interp `rbtree_map_test #[] #[
      42,
      50, 100, 200,
      999,
      10, 20, 30, 40, 50,
      10, 20, 30, 40, 50,
      200, 300, 400, 500, 600, 700, 800],
]

end
