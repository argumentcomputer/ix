module
public import Ix.CompileDriver
public section

namespace Tests.Ix.AuxGen

/-- Diagnostic patch generation uses the compilation's retained original
source capability, including checked generation-only preparation where the
original input was not logically accepted. No absent provider selects Tc. -/
def checkedFamilyKernel (cenv : _root_.Ix.CompileM.CompileEnv)
    (maps : _root_.Ix.AuxGen.AddrMaps) (originalAll : Array _root_.Ix.Name) :
    _root_.Ix.CompileM.CompileM _root_.Ix.AuxGen.AuxKernel := do
  let some owner := originalAll[0]?
    | throw (.unsupportedExpr "AuxGen diagnostic: original mutual family is empty")
  match cenv.familyOracle owner with
  | .error why => throw (.unsupportedExpr why)
  | .ok oracle =>
    unless oracle.mode == .failClosed && oracle.recursors && oracle.retry.isNone do
      throw (.unsupportedExpr s!"AuxGen diagnostic: {owner.pretty}: failClosed recursor capability without retry required")
    return .ixc maps oracle

end Tests.Ix.AuxGen
