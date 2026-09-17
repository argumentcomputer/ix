import Lean
import Ix.Ixby

namespace Compilatrix.Ixby.Runtime.Native.Code

open Lean Ix.Ixby

/-- A private runtime symbol and its complete machine-level body. -/
structure Entry where
  id : FunctionId
  name : Name
  body : Function
  deriving Inhabited

end Compilatrix.Ixby.Runtime.Native.Code
