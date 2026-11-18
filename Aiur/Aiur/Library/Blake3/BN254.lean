import Aiur.Library.Blake3
import Aiur.Library.Field.BN254

/-! BLAKE3 over the BN254 scalar field. Byte and word arithmetic retains the
same checked tables and bounded integer formulas as the Goldilocks instance. -/
namespace Aiur.Library.Blake3.BN254
open Aiur

abbrev F := Library.Field.BN254.F

def program : Modules.Program F :=
  U32.program F Library.Field.BN254.u32_compatible
    |>.append (U64.specialize F Library.Field.BN254.u64_compatible)
    |>.append (List.declarations.toField F)
    |>.append (Field.declarations.toField F)
    |>.append (Bytes.declarations.toField F)
    |>.append (Blake3.declarations.toField F)

end Aiur.Library.Blake3.BN254
