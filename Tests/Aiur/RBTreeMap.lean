module

public import Tests.Aiur.Common
public import Ix.IxVM.RBTreeMap

public section

public def rbTreeMapTestCases : List AiurTestCase := [
  .noIO `rbtree_map_test #[] #[
    42,
    50, 100, 200,
    999,
    10, 20, 30, 40, 50,
    10, 20, 30, 40, 50,
    200, 300, 400, 500, 600, 700, 800],
]

end
