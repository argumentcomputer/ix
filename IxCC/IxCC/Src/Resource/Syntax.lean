import IxCC.Ixon.V3.Contracts
import IxCC.Ixon.Address

/-! Untrusted resource-selection records. These describe addresses and written
headers, not a resource-safety verdict. -/

namespace IxCC.Src.Resource

structure Header where
  position : Nat
  contract : Ixon.V3.BinderContract
  deriving BEq, Repr, Inhabited

structure Pair where
  definition : Ixon.Address
  equation : Ixon.Address
  profile : Ixon.Address
  contracts : List Header := []
  deriving BEq, Repr, Inhabited

structure Context where
  address : Ixon.Address
  bytes : ByteArray
  pairs : List Pair := []
  deriving BEq, Inhabited

end IxCC.Src.Resource
