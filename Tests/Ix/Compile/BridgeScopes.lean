import LSpec
import Tests.Ix.AuxGen.PortableKernel
namespace Tests.Ix.Compile.BridgeScopes
open LSpec
def suite : List TestSeq := [
  .individualIO "checked scope queries, exact refusals and immutable caught-failure isolation" none
    (do Tests.AuxGen.PortableKernel.evaluateScopes; return (true, 1, 0, none)) .done]
end Tests.Ix.Compile.BridgeScopes
