import Aiur.Hints
import Aiur.Library.U64

namespace Aiur.Library.U64

/-- Optional semantic provider. The library checks the returned raw fields;
this dispatcher cannot construct opaque bytes. -/
def hints {F : Type} [NatCast F] (toNat : F → Nat)
    (fallback : HintDispatcher F := fun _ _ => .error .unavailable) : HintDispatcher F :=
  fun channel key => match channel, key with
    | "bytes_le", .field value =>
      .ok (.tuple ((List.range 8).map fun i => .field (((toNat value / 256^i) % 256 : Nat) : F)))
    | "bytes_le", _ => .error (.message "invalid byte decomposition key")
    | _, _ => fallback channel key

end Aiur.Library.U64
