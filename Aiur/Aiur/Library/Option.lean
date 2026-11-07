import Aiur.Modules

namespace Aiur.Library.Option
open Aiur

/-- Constructor order matches the legacy library's wire representation. -/
def declarations : Modules.Program Nat := aiur% "
module Options {
    enum Option<T> { Some(T), None }
}"

end Aiur.Library.Option
