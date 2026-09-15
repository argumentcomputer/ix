import Compilatrix.Ixon.CatalogIO
import Compilatrix.Ixon.Sharing.Indexed
import Compilatrix.IxIR0.Decode
import Compilatrix.IxIR1.Decode
import Compilatrix.Pipeline
import Compilatrix.Modular.Build
import Compilatrix.Modular.Wire
import Compilatrix.IxIR2.Pipeline
import Compilatrix.IxIR2.WireIO
import Compilatrix.X86.ScalarSourceObject
import Compilatrix.X86.PhysicalScalarSourceObject
import Compilatrix.X86.PhysicalScalarCapturedSourceObject
import Compilatrix.X86.PhysicalHeapSourceObject
import Compilatrix.UniqueReuse.NativeObject
import Compilatrix.UniqueReuse.RuntimeObjectSpace
import Compilatrix.UniqueReuse.AllocatingObjectSpace
import Compilatrix.Borrow.RuntimeInput
import Compilatrix.Ixby.Source
import Compilatrix.Ixby.Lean
import Compilatrix.Ixby.Runtime.Run

/-! Production compiler API. The complete regression and proof collection is
built explicitly through `CompilatrixTests` and `CompilatrixTests.Proofs`. -/
