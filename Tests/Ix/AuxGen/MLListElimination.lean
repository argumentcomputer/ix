import Tests.Ix.AuxGen.BelowIxc

namespace Tests.Ix.AuxGen.MLListElimination
open _root_.Ix _root_.Ix.AuxGen
private def need (ok : Bool) (why : String) : IO Unit := unless ok do throw (IO.userError s!"MLList elimination: {why}")
/-- Direct checked decision, with correspondence to the actual producer's
positive-sort branch; this is not an intercepted generator answer. -/
def check (env : Environment) (cenv : CompileM.CompileEnv) (lo owner : Name)
    (members : Array Name) (oracle : AuxOracle) : IO Unit := do
  let some (.inductInfo ind) := env.get? owner | throw (IO.userError "MLList elimination: original absent")
  let ctors ← ind.ctors.mapM fun n => do
    let some (.ctorInfo c) := env.get? n | throw (IO.userError "MLList elimination: constructor absent")
    return c
  let (expanded, _) ← IO.ofExcept (Tests.Ix.AuxGen.BelowIxc.runIn cenv lo do
    let some (_, sorted, _, _) ← Tests.Ix.AuxGen.BelowIxc.tailArgs lo members
      | throw (.unsupportedExpr "MLList elimination: actual tail absent")
    let classes := sorted.toArray.map fun cls => cls.toArray.map (·.name)
    unless classes.size == 1 && classes[0]!.size == 1 && Compile.ExactKey.nameEq classes[0]![0]! owner do
      throw (.unsupportedExpr "MLList elimination: actual singleton class changed")
    let aliases : Std.HashMap Name Name := classes.foldl (fun m cls =>
      cls.toList.drop 1 |>.foldl (fun m n => m.insert n cls[0]!) m) {}
    unless aliases.isEmpty do throw (.unsupportedExpr "MLList elimination: actual alias map is nonempty")
    expandNestedBlock (classes.map (·[0]!)) aliases true)
  need (expanded.nOriginals == 1 && expanded.types.size == 2) "actual original/expanded member counts changed"
  let original := expanded.types[0]!
  need (Compile.ExactKey.nameEq original.name owner && original.nParams == 2 && original.nIndices == 0 &&
    ind.numParams == original.nParams && ind.numIndices == original.nIndices && expanded.levelParams.isEqv ind.cnst.levelParams Compile.ExactKey.nameEq &&
    Compile.ExactKey.exprEq original.typ ind.cnst.type) "producer/header/level/parameter/index correspondence changed"
  let (_, params, result) := forallTelescope original.typ original.nParams "ml-elimination" 0
  let .sort (.succ (.param u _) _) _ := result | throw (IO.userError "MLList elimination: expected Sort(succ u)")
  need (params.size == 2 && expanded.levelParams.size == 1 && Compile.ExactKey.nameEq u expanded.levelParams[0]!) "actual successor-level binding changed"
  need (oracle.mode == .failClosed && oracle.recursors && oracle.retry.isNone &&
    oracle.blockStatus () == some AuxOracle.tierBlockStatus) "actual checked unsafe capability changed"
  -- With this identical header, ixcElimDecision peels the same two parameters
  -- and returns at levelNeverZero, before reading rewritten constructor data.
  let (decision, forced) ← IO.ofExcept (AuxKernel.ixcElimDecision oracle #[(ind, ctors)] original.nParams expanded.types.size)
  need (decision.isLarge && !decision.isProp && !forced) "actual large/prop/forced decision changed"
  IO.println "MLList elimination: actual classes/expansion/header; large=true, prop=false, forced=false; branch correspondence"

end Tests.Ix.AuxGen.MLListElimination
