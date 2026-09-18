module

public import LSpec
public import Ix.Aiur.Stages.Codegen

public section

open LSpec Aiur

namespace AiurTests.Codegen

private def renderOp (op : Bytecode.Op) (sizes : Array Nat) : String :=
  Aiur.Codegen.stmtsToStr 0 (Aiur.Codegen.emitOp 2 op sizes)

def tests : TestSeq := Id.run do
  -- Deliberately non-sorted: slots follow the toplevel, not width order.
  let sizes := #[7, 2, 0]
  let store := renderOp (.store #[0, 1]) sizes
  let load := renderOp (.load 2 0) sizes
  let empty := renderOp (.store #[]) sizes
  let reordered := renderOp (.load 2 0) #[2, 7, 0]
  let standalone := renderOp (.load 2 0) #[]
  let dispatch := Aiur.Codegen.emitDispatch
    { functions := #[], memorySizes := sizes } |>.toStr
  return (
    test "store uses the table slot, not the width as an index"
      (store.contains "get_index_mut(1)" && !store.contains "get_mut(&2)") ++
    test "load and store use the same slot"
      (load.contains "get_index_mut(1)" && !load.contains "get_mut(&2)") ++
    test "zero-width memory has its own slot"
      (empty.contains "get_index_mut(2)") ++
    test "slots follow the supplied table order"
      (reordered.contains "get_index_mut(0)") ++
    test "standalone emission retains checked width lookup"
      (standalone.contains "get_mut(&2)" &&
        standalone.contains "InvalidMemorySize(2)") ++
    test "pointer validation and multiplicity recording are retained"
      (load.contains "UnboundPointer" && load.contains "PointerTooLarge" &&
        load.contains "if !unconstrained { __mq.bump_multiplicity") ++
    test "all slots are validated before dispatch"
      ((dispatch.splitOn "match fun_idx as u64").head!.contains
        "get_index(0).map(|(size, _)| *size) != Some(7)" &&
       (dispatch.splitOn "match fun_idx as u64").head!.contains
        "get_index(1).map(|(size, _)| *size) != Some(2)" &&
       (dispatch.splitOn "match fun_idx as u64").head!.contains
        "get_index(2).map(|(size, _)| *size) != Some(0)")
  )

end AiurTests.Codegen
