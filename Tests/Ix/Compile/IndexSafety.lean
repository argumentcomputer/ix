import LSpec
import Ix.CompileM
import Ix.Compile.Image.Build

namespace Tests.Ix.Compile.IndexSafety

open LSpec
open _root_.Ix (Name Level Expr)
open _root_.Ix.Compile.Image

private def rootName : Name := Name.fromLeanName `D8.missing

private def missingReferences : _root_.Ix.CondensedBlocks :=
  { lowLinks := {}, blocks := ({}).insert rootName (({}).insert rootName), blockRefs := {} }

def suite : List TestSeq := [
  test "image type packing rejects every empty slot class"
    ([Pack.single, .lift, .tuple 2].all fun pack =>
      (wrapTy pack Level.mkZero #[]).isError)
  ++ test "image value packing rejects every empty slot class"
    ([Pack.single, .lift, .tuple 2].all fun pack =>
      (wrapVal pack Level.mkZero #[]).isError)
  ++ test "singleton packing retains the actual type and value"
    (let term := Expr.mkSort Level.mkZero
     (wrapTy .single Level.mkZero #[term]).toOption == some term
       && (wrapVal .single Level.mkZero #[(term, term)]).toOption == some term)
  ++ test "sequential compiler reports missing condensation references"
    (match _root_.Ix.CompileM.compileEnv default missingReferences with
      | .error why => why == "compileEnv: block D8.missing has no condensation reference set"
      | .ok _ => false),
  .individualIO "parallel compiler reports missing condensation references" none (do
    let result ← _root_.Ix.CompileM.compileEnvParallel default missingReferences (numWorkers := 1)
    let ok := match result with
      | .error error => error.systemError ==
          some "compileEnvParallel: block D8.missing has no condensation reference set"
      | .ok _ => false
    return (ok, if ok then 1 else 0, 1,
      if ok then none else some "missing references were not reported by the scheduler")) .done
]

end Tests.Ix.Compile.IndexSafety
