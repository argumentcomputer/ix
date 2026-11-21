import Aiur.Modules
import Aiur.Library.Frontend

namespace Aiur.Library.Option
open Aiur

/-- Constructor order matches the legacy library's wire representation. -/
def declarations : Modules.Program Nat := aiur_library% ⟦
module Options {
    enum Option<T> { Some(T), None }
}
⟧

end Aiur.Library.Option
