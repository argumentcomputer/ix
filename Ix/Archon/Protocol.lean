import Ix.Archon.Circuit
import Ix.Archon.Witness
import Ix.Binius.Boundary

namespace Archon

open Binius

@[never_extract, extern "c_rs_validate_witness"]
opaque validateWitness : @& Array CircuitModule → @& Witness →
  @& Array Boundary → Except String Unit

end Archon
