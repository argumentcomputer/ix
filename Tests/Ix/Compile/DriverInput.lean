import LSpec
import Ix.CompileDriver

/-! The compile drivers' input checks: a condensation with a block that has
no reference set is refused by both drivers (`Ix.CompileM.missingBlockRefs?`)
instead of being scheduled as if it had no dependencies. -/

namespace Tests.Ix.Compile.DriverInput

open LSpec
open _root_.Ix (Name)

private def missing : Name := Name.fromLeanName `DriverInput.missing
private def present : Name := Name.fromLeanName `DriverInput.present

/-- Two singleton blocks; only `present` has a reference set. -/
private def blocks : _root_.Ix.CondensedBlocks :=
  { lowLinks := ({} : _root_.Ix.Map Name Name).insert missing missing |>.insert present present
    blocks := ({} : _root_.Ix.Map Name (_root_.Ix.Set Name))
      |>.insert missing (({} : _root_.Ix.Set Name).insert missing)
      |>.insert present (({} : _root_.Ix.Set Name).insert present)
    blockRefs := ({} : _root_.Ix.Map Name (_root_.Ix.Set Name)).insert present {} }

private def expected : String := "block DriverInput.missing has no condensation reference set"

def suite : List TestSeq := [
  test "missingBlockRefs? names the block without references"
    (_root_.Ix.CompileM.missingBlockRefs? blocks == some expected),
  test "missingBlockRefs? accepts a complete condensation"
    (_root_.Ix.CompileM.missingBlockRefs?
      { blocks with blockRefs := blocks.blockRefs.insert missing {} } == none),
  test "the sequential driver refuses a block without references"
    (show Bool from match _root_.Ix.CompileM.compileEnvAux { consts := {} } blocks with
      | .error why => why == expected
      | .ok _ => false),
  .individualIO "the parallel driver refuses a block without references" none (do
    let result ← _root_.Ix.CompileM.compileEnvParallelAux { consts := {} } blocks
      (numWorkers := 1)
    let ok := match result with
      | .error why => why == expected
      | .ok _ => false
    return (ok, if ok then 1 else 0, 1,
      if ok then none else some "the parallel driver did not refuse the condensation")) .done]

end Tests.Ix.Compile.DriverInput
