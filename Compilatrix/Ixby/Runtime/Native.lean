import Compilatrix.Ixby.Runtime.Native.Image
import Compilatrix.Ixby.Runtime.Native.Scalars
import Compilatrix.Ixby.Runtime.Native.NatLoops
import Compilatrix.Ixby.Runtime.Native.Fields
import Compilatrix.Ixby.Runtime.Native.Words
import Compilatrix.Ixby.Runtime.Native.USize
import Compilatrix.Ixby.Runtime.Native.ArrayAccess
import Compilatrix.Ixby.Runtime.Native.ArrayAppend
import Compilatrix.Ixby.Runtime.Native.ArrayExtract
import Compilatrix.Ixby.Runtime.Native.ByteLoops
import Compilatrix.Ixby.Runtime.Native.PackedArray
import Compilatrix.Ixby.Runtime.Native.ArrayRead
import Compilatrix.Ixby.Runtime.Native.WireWrite
import Compilatrix.Ixby.Runtime.Native.WireEncode
import Compilatrix.Ixby.Runtime.Native.RowHash

/-! Current runtime body certificates and compositional execution proofs.
This aggregate is for proof checks; the frontend imports only its certificate
interface and does not elaborate these execution proofs while compiling. -/
