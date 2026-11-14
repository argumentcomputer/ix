import Aiur.Modules
import Aiur.Library.Frontend

namespace Aiur.Library.Field
open Aiur

def declarations : Modules.Program Nat := aiur_library% ⟦
module Fields {
    inline fn is_zero(x: Field) -> Field { match x { 0 => 1, _ => 0 } }
}
⟧

end Aiur.Library.Field
