import Aiur.Library.Blake3
import Aiur.Library.U32.Goldilocks

namespace Aiur.Library.Blake3.Goldilocks
open Aiur

theorem u64_compatible : U64.Compatible U32.Goldilocks.F :=
  U64.compatible_of_charP U32.Goldilocks.F U32.Goldilocks.modulus (by decide)

def program : Modules.Program U32.Goldilocks.F :=
  U32.Goldilocks.program.append (U64.specialize U32.Goldilocks.F u64_compatible)
    |>.append (List.declarations.toField U32.Goldilocks.F)
    |>.append (Field.declarations.toField U32.Goldilocks.F)
    |>.append (Bytes.declarations.toField U32.Goldilocks.F)
    |>.append (Blake3.declarations.toField U32.Goldilocks.F)

end Aiur.Library.Blake3.Goldilocks
