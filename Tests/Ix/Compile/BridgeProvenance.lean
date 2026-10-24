import LSpec
import Tests.Ix.Compile.BridgePortable
namespace Tests.Ix.Compile.BridgeProvenance
open LSpec
def suite : List TestSeq := [
  .individualIO "checked Source identities, shared addresses, overlay replay and batch isolation" none
    (do BridgePortable.evaluate; return (true, 1, 0, none)) .done]
end Tests.Ix.Compile.BridgeProvenance
