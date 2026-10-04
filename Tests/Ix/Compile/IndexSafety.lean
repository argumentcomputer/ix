import LSpec
import Ix.CompileM
import Ix.Compile.Image.Build

namespace Tests.Ix.Compile.IndexSafety

open LSpec
open _root_.Ix (Name Level Expr)
open _root_.Ix.Compile.Image

private def rootName : Name := Name.fromLeanName `D8.missing

private def missingReferences : _root_.Ix.CondensedBlocks :=
  let blocks : _root_.Ix.CondensedBlocks := default
  let members := (blocks.blocks.getD rootName {}).insert rootName
  { blocks with blocks := blocks.blocks.insert rootName members }

private def checkedUpdate (values : Array Nat) (index value : Nat) : Except String (Array Nat) := do
  let cenv := _root_.Ix.CompileM.CompileEnv.new { consts := {} }
  let blockEnv : _root_.Ix.CompileM.BlockEnv :=
    { all := {}, current := rootName, mutCtx := default, univCtx := [] }
  let (out, _) ← (_root_.Ix.CompileM.CompileM.run cenv blockEnv {}
    (_root_.Ix.CompileM.arrSet values index value "index-safety update")).mapError toString
  return out

def suite : List TestSeq := [
  test "image type packing rejects every empty slot class"
    ([Pack.single, .lift, .tuple 2].all fun pack =>
      !(wrapTy pack Level.mkZero #[]).isOk)
  ++ test "image value packing rejects every empty slot class"
    ([Pack.single, .lift, .tuple 2].all fun pack =>
      !(wrapVal pack Level.mkZero #[]).isOk)
  ++ test "singleton packing retains the actual type and value"
    (let term := Expr.mkSort Level.mkZero
     (wrapTy .single Level.mkZero #[term]).toOption == some term
       && (wrapVal .single Level.mkZero #[(term, term)]).toOption == some term)
  ++ test "checked writes retain all other slots and reject missing slots"
    ((checkedUpdate #[3, 5] 1 7 == .ok #[3, 7]
      && checkedUpdate #[3] 1 7 == .error
        "invalidMutualBlock: internal error in block 'D8.missing': index-safety update: index 1 out of range (size 1)"
      && checkedUpdate #[] 0 7 == .error
        "invalidMutualBlock: internal error in block 'D8.missing': index-safety update: index 0 out of range (size 0)" : Bool))
  ++ test "sequential compiler reports missing condensation references"
    (show Bool from match _root_.Ix.CompileM.compileEnv { consts := {} } missingReferences with
      | .error why => why == "compileEnv: block D8.missing has no condensation reference set"
      | .ok _ => false),
  .individualIO "parallel compiler reports missing condensation references" none (do
    let result ← _root_.Ix.CompileM.compileEnvParallel { consts := {} } missingReferences (numWorkers := 1)
    let ok := match result with
      | .error error => error.systemError ==
          some "compileEnvParallel: block D8.missing has no condensation reference set"
      | .ok _ => false
    return (ok, if ok then 1 else 0, 1,
      if ok then none else some "missing references were not reported by the scheduler")) .done
]

end Tests.Ix.Compile.IndexSafety
