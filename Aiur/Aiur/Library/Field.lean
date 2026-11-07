import Aiur.Modules

namespace Aiur.Library.Field
open Aiur

def declarations : Modules.Program Nat := aiur% "
module Fields {
    inline fn is_zero(x: Field) -> Field { match x { 0 => 1, _ => 0 } }
}"

end Aiur.Library.Field
